package net.vwzq.polca;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Random;
import java.util.stream.IntStream;

import de.learnlib.api.oracle.MembershipOracle.MealyMembershipOracle;
import de.learnlib.api.query.Query;
import net.automatalib.words.Alphabet;
import net.automatalib.words.Word;
import net.automatalib.words.WordBuilder;
import org.checkerframework.checker.nullness.qual.NonNull;

public class CacheSULOracle implements MealyMembershipOracle<String, String> {

    private final CacheSUL sul;
	private final String label;
    private NoiseType noise;
    private float probability;
	private Config config;

    public CacheSULOracle(CacheSUL sul, Config conf, String label, NoiseType noise, float probability) {
        this.sul = sul;
		this.config = conf;
		this.label = label;
		this.noise = noise;
		this.probability = probability;
    }

    @Override
    public void processQueries(Collection<? extends Query<String, Word<String>>> queries) {
		synchronized (sul) {
                processQueries(sul, queries, this.config, label, noise, probability);
        }
    }

    private static void processQueries(CacheSUL sul, Collection<? extends Query<String, Word<String>>> queries, Config config, String label, NoiseType noise, float probability) {
        for (Query<String, Word<String>> q : queries) {
			if (config.verbose) System.out.println("(" + label + ") " + "processQuery: " + q);
			Word<String> output = answerQuery(sul, q.getPrefix(), q.getSuffix(), config.ways, noise, probability);
            q.answer(output);
        }
    }

    @NonNull
    public static Word<String> answerQuery(CacheSUL sul, Word<String> prefix, Word<String> suffix, int ways, NoiseType noise, float probability) {
        sul.pre();
        try {
            //Pre noise introduced
            if (noise == NoiseType.PRE){
                Random random = new Random();
                if (random.nextFloat() < probability) { // Probability
                    int noiseIndex = random.nextInt(prefix.length() + 1);
                    
                    Alphabet<String> alphabet = sul.getAlphabet();
                    int noiseInputIndex = random.nextInt(alphabet.size());
                    
                    ArrayList<String> prefixList = new ArrayList<String>(prefix.asList());
                    prefixList.add(noiseIndex, alphabet.getSymbol(noiseInputIndex));
                    prefix = Word.fromList(prefixList);
                    System.out.println("prefix after noise: " + prefix);
                }
            }

            // Prefix: Execute symbols, don't record output
            for (String sym : prefix) {
                sul.step(sym);
            }

            // Suffix: Execute symbols, outputs constitute output word
            WordBuilder<String> wb = new WordBuilder<>(suffix.length());
            for (String sym : suffix) {
                wb.add(sul.step(sym));
            }

            //Post noise introduced
            if (noise == NoiseType.POST){
                Random random = new Random();
                if (random.nextFloat() < probability) { // Probability
                    ArrayList<Integer> indexes = new ArrayList<>();

                    for (int i = 0; i < wb.size(); i++) {
                        if (!wb.get(i).equals("_"))
                            indexes.add(i);
                    }
                    System.out.println(indexes);
                    if (!indexes.isEmpty()) {
                        // get value to change
                        int noiseIndex = indexes.get(random.nextInt(indexes.size()));
                        int initVal = Integer.parseInt(wb.get(noiseIndex));

                        // choose new value
                        int[] output = IntStream.concat(IntStream.range(0, initVal), IntStream.range(initVal+1, ways)).toArray();
                        int finalVal = output[random.nextInt(output.length)];

                        System.out.println("output before noise: " + wb.toString());
                        wb.set(noiseIndex, String.valueOf(finalVal));
                        System.out.println("output after noise: " + wb.toString());
                    }
                }
            }

            return wb.toWord();
        } finally {
            sul.post();
        }
    }
}
