package net.vwzq.polca;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Random;

import de.learnlib.api.SUL;
import de.learnlib.api.oracle.MembershipOracle.MealyMembershipOracle;
import de.learnlib.api.query.Query;
import net.automatalib.words.Alphabet;
import net.automatalib.words.Word;
import net.automatalib.words.WordBuilder;
import org.checkerframework.checker.nullness.qual.NonNull;

public class NoiseCacheSULOracle implements MealyMembershipOracle<String, String> {

    private final NoiseCacheSUL sul;
	private final String label;
	private Config config;

    public NoiseCacheSULOracle(SUL<String,String> sul, Config conf, String label) {
        this.sul = (NoiseCacheSUL) sul;
		this.config = conf;
		this.label = label;
    }

    @Override
    public void processQueries(Collection<? extends Query<String, Word<String>>> queries) {
		synchronized (sul) {
                processQueries(sul, queries, this.config, label);
        }
    }

    private static void processQueries(NoiseCacheSUL sul, Collection<? extends Query<String, Word<String>>> queries, Config config, String label) {
        for (Query<String, Word<String>> q : queries) {
			if (config.verbose) System.out.println("(" + label + ") " + "processQuery: " + q);
			Word<String> output = answerQuery(sul, q.getPrefix(), q.getSuffix());
            q.answer(output);
        }
    }

    @NonNull
    public static Word<String> answerQuery(NoiseCacheSUL sul, Word<String> prefix, Word<String> suffix) {
        sul.pre();
        try {
            // Prefix: Execute symbols, don't record output

            //Noise introduced
            Random random = new Random();
            if (random.nextFloat() < 0.5) { // Probability 50%
                int noiseIndex = random.nextInt(prefix.length() + 1);

                Alphabet<String> alphabet = sul.getAlphabet();
                int noiseInputIndex = random.nextInt(alphabet.size());

                ArrayList<String> prefixList = new ArrayList<String>(prefix.asList());
                prefixList.add(noiseIndex, alphabet.getSymbol(noiseInputIndex));
                prefix = Word.fromList(prefixList);
                System.out.println("prefix after noise: " + prefix);
            }
            for (String sym : prefix) {
                sul.step(sym);
            }

            // Suffix: Execute symbols, outputs constitute output word
            WordBuilder<String> wb = new WordBuilder<>(suffix.length());
            for (String sym : suffix) {
                wb.add(sul.step(sym));
            }

            return wb.toWord();
        } finally {
            sul.post();
        }
    }
}
