/* Copyright (C) 2013-2019 TU Dortmund
 * This file is part of LearnLib, http://www.learnlib.de/.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package net.vwzq.polca;

import java.io.IOException;
import java.util.List;
import java.util.Random;
import java.util.function.Function;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;

import org.apache.commons.cli.*;

import java.io.PrintStream;

import de.learnlib.algorithms.kv.mealy.KearnsVaziraniMealy;
import de.learnlib.algorithms.lstar.ce.ObservationTableCEXHandlers;
import de.learnlib.algorithms.lstar.closing.ClosingStrategies;
import de.learnlib.algorithms.lstar.mealy.ExtensibleLStarMealy;
import de.learnlib.algorithms.lstar.mealy.ExtensibleLStarMealyBuilder;
import de.learnlib.algorithms.malerpnueli.MalerPnueliMealy;
import de.learnlib.algorithms.rivestschapire.RivestSchapireMealy;
import de.learnlib.algorithms.ttt.mealy.TTTLearnerMealyBuilder;
import de.learnlib.api.algorithm.LearningAlgorithm;
import de.learnlib.api.oracle.MembershipOracle;
import de.learnlib.api.oracle.EquivalenceOracle.MealyEquivalenceOracle;
import de.learnlib.api.oracle.MembershipOracle.MealyMembershipOracle;
import de.learnlib.api.query.DefaultQuery;
import de.learnlib.counterexamples.LocalSuffixFinders;
import de.learnlib.acex.analyzers.AcexAnalyzers;
import de.learnlib.algorithms.continuous.base.PAR;
import de.learnlib.algorithms.dhc.mealy.MealyDHC;
import de.learnlib.algorithms.discriminationtree.mealy.DTLearnerMealy;
import de.learnlib.filter.cache.mealy.MealyCacheOracle;
import de.learnlib.filter.cache.mealy.MealyCaches;
import de.learnlib.filter.statistic.oracle.MealyCounterOracle;
import de.learnlib.oracle.equivalence.MealyEQOracleChain;
import de.learnlib.oracle.equivalence.MealyRandomWordsEQOracle;
import de.learnlib.oracle.equivalence.MealyRandomWpMethodEQOracle;
import de.learnlib.oracle.equivalence.MealyWpMethodEQOracle;
import de.learnlib.oracle.equivalence.RandomWordsEQOracle;
import de.learnlib.oracle.membership.ProbabilisticOracle;
import de.learnlib.util.statistics.SimpleProfiler;
import net.automatalib.automata.transducers.MealyMachine;
import net.automatalib.automata.transducers.impl.compact.CompactMealy;
import net.automatalib.commons.util.Pair;
import net.automatalib.serialization.dot.GraphDOT;
import net.automatalib.util.automata.equivalence.DeterministicEquivalenceTest;
import net.automatalib.visualization.Visualization;
import net.automatalib.words.Alphabet;
import net.automatalib.words.Word;
import net.automatalib.words.impl.Alphabets;

enum PolicyType {
	LRU,
	LIP,
	PLIP,
	FIFO,
	PLRU,
	MRU,
	SRRIPHP,
	SRRIPFP,
	HW,
	SKYL3,
	SKYL2,
}

enum LearnAlgorithmType {
	PAS,
	LSTAR,
	TTT,
	KV,
	MP,
	DT,
	DHC,
	RS,
}

enum NoiseType {
	PRE,
	POST,
	CLEAN,
}

class Config {

	public int max_depth;
	public int ways;
	public PolicyType policy;
	public boolean is_random;
	public boolean no_cache;
	public boolean verbose;
	public boolean temp_model;
	public boolean silent;
	public boolean is_hw;
	public String proxy_path;
	public String output_path;
	public int r_min, r_len, r_bound;
	public int repetitions;
	public Float hit_ratio, miss_ratio;
	public String prefix;
	public int max_size;
	public LearnAlgorithmType learner;
	public int votes;
	public double revision_ratio;
	public double length_factor;
	public NoiseType noise;
	public float probability;

	public Config (CommandLine cmd) throws Exception {
		this.max_depth = Integer.parseInt(cmd.getOptionValue("depth", "1"));
		this.ways = Integer.parseInt(cmd.getOptionValue("ways", "4"));
		this.r_min = Integer.parseInt(cmd.getOptionValue("r_min", "10"));
		this.r_len = Integer.parseInt(cmd.getOptionValue("r_len", "30"));
		this.r_bound = Integer.parseInt(cmd.getOptionValue("r_bound", "200"));
		this.repetitions = Integer.parseInt(cmd.getOptionValue("repetitions", "100"));
		this.max_size = Integer.parseInt(cmd.getOptionValue("max_size", "2147483647"));
		this.hit_ratio = Float.parseFloat(cmd.getOptionValue("hit_ratio", "0.8"));
		this.miss_ratio = Float.parseFloat(cmd.getOptionValue("miss_ratio", "0.2"));
		this.votes = Integer.parseInt(cmd.getOptionValue("votes", "1"));
		this.prefix = cmd.getOptionValue("prefix", "@");
		this.is_hw = false;

		String noise = cmd.getOptionValue("n");
		if (noise == null)
			this.noise = null;
		else if (noise.toLowerCase().equals("pre"))
			this.noise = NoiseType.PRE;
		else if (noise.toLowerCase().equals("post"))
			this.noise = NoiseType.POST;
		else
			throw new Exception("unsupported noise type");
		
		this.probability = Float.parseFloat(cmd.getOptionValue("prob", "0"));

		this.revision_ratio = Double.parseDouble(cmd.getOptionValue("revision_ratio", "0.99"));
		this.length_factor = Double.parseDouble(cmd.getOptionValue("length_factor", "0.99"));

		switch (cmd.getOptionValue("policy", "fifo").toLowerCase()) {
			case "hw":
				this.policy = PolicyType.HW;
				this.is_hw = true;
				break;
			case "lru":
				this.policy = PolicyType.LRU;
				break;
			case "plru":
				this.policy = PolicyType.PLRU;
				break;
			case "mru":
				this.policy = PolicyType.MRU;
				break;
			case "srriphp":
				this.policy = PolicyType.SRRIPHP;
				break;
			case "srripfp":
				this.policy = PolicyType.SRRIPFP;
				break;
			case "fifo":
				this.policy = PolicyType.FIFO;
				break;
			case "lip":
				this.policy = PolicyType.LIP;
				break;
			case "plip":
				this.policy = PolicyType.PLIP;
				break;
			case "new2":
				this.policy = PolicyType.SKYL3;
				break;
			case "new1":
				this.policy = PolicyType.SKYL2;
				break;
			default:
				throw new Exception("unsupported policy");
		}

		switch (cmd.getOptionValue("learner", "pas").toLowerCase()) {
			case "pas":
				this.learner = LearnAlgorithmType.PAS;
				break;
			case "ttt":
				this.learner = LearnAlgorithmType.TTT;
				break;
			case "kv":
				this.learner = LearnAlgorithmType.KV;
				break;
			case "dhc":
				this.learner = LearnAlgorithmType.DHC;
				break;
			case "mp":
				this.learner = LearnAlgorithmType.MP;
				break;
			case "rs":
				this.learner = LearnAlgorithmType.RS;
				break;
			case "dt":
				this.learner = LearnAlgorithmType.DT;
				break;
			case "lstar":
				this.learner = LearnAlgorithmType.LSTAR;
				break;
			default:
				throw new Exception("unsupported learning algorithm");
		}

		if (this.policy == PolicyType.HW && !cmd.hasOption("binary")) {
			throw new Exception("no path to proxy for 'hw' policy");
		}
		this.proxy_path = cmd.getOptionValue("binary", "");
		this.output_path = cmd.getOptionValue("output", "");
		this.is_random = cmd.hasOption("random");
		this.no_cache = cmd.hasOption("no_cache");
		this.verbose = cmd.hasOption("verbose") && !cmd.hasOption("silent");
		this.temp_model = cmd.hasOption("temp");
		this.silent = cmd.hasOption("silent");
	}

}

public final class Polca {

	private static final String Set = null;
	private Config config;
	private long count;

    public Polca (CommandLine cmd) throws Exception {
		this.config = new Config(cmd);
    }

	public static void main(String[] args) throws Exception {

		// Options
		Options options = new Options();

		// cache settings
		options.addOption(new Option("d", "depth", true, "max_depth for membership queries (default: 1)"));
		options.addOption(new Option("w", "ways", true, "cache associativity (default: 4)"));
		options.addOption(new Option("p", "policy", true,
				"simulator cache policy: fifo|lru|plru|lip|plip|mru|srriphp|srripfp|new1|new2|hw (default: 'fifo')"));
		options.addOption(new Option("b", "binary", true, "path to proxy for 'hw' policy"));
		//noise
		options.addOption(new Option("n", "noise", true, "type of noise pre|post|clean"));
		options.addOption(new Option("prob", "noise probability", true, "probability of noise"));
		// general
		options.addOption(new Option("o", "output", true, "write learnt .dot model into output file"));
		// other
		options.addOption(new Option("prefix", true, "prefix before every query, used to fill cache (default: '@')"));
		options.addOption(new Option("r", "repetitions", true, "number of measurements by cachequery (default: 100)"));
		options.addOption(new Option("votes", true, "number of votes for deciding result (default: 1)"));
		options.addOption(new Option("hit_ratio", true, "ratio of hits to consider a HIT (default: 0.8)"));
		options.addOption(new Option("miss_ratio", true, "ratio of misses to consider a MISS (default: 0.2)"));
		options.addOption(new Option("revision_ratio", true, "NEW"));
		options.addOption(new Option("length_factor", true, "NEW"));
		// learning settings
		options.addOption(
				new Option("l", "learner", true, "learning algorithm pas|lstar|kv|mp|rs|dhc|dt|ttt (default: 'pas')"));
		options.addOption(new Option("m", "max_size", true, "maximum number of states of SUL"));
		options.addOption(new Option("r_min", true, "minimal length of random word (default: 10)"));
		options.addOption(new Option("r_len", true, "expected length of random word (r_min + r_len) (default: 30)"));
		options.addOption(new Option("r_bound", true,
				"bound on queries for equivalence, set to 0 for unbounded (default: 1000)"));
		options.addOption(new Option("r_rand", true, "TODO: select custom random generator"));
		// flags
		options.addOption(new Option("random", false, "use random wp-method as equivalence query"));
		options.addOption(new Option("temp", false, "write partial model into '.model.tmp' file"));
		options.addOption(new Option("verbose", false, "output verbose information"));
		options.addOption(new Option("no_cache", false, "don't use cache for membership queries"));
		options.addOption(new Option("h", "help", false, "show this help message"));
		options.addOption(new Option("s", "silent", false, "remove stdout info"));

		CommandLineParser parser = new DefaultParser();
		HelpFormatter formatter = new HelpFormatter();
		CommandLine cmd = null;

		try {
			cmd = parser.parse(options, args);
		} catch (ParseException e) {
			System.out.println(e.getMessage());
			formatter.printHelp("Polca", options);
			System.exit(1);
		}

		// show help menu
		if (cmd.hasOption("help")) {
			formatter.printHelp("Polca", options);
			System.exit(1);
		}

		// check config
		Polca learn = null;
		try {
			learn = new Polca(cmd);
		} catch (Exception e) {
			System.out.println(e.getMessage());
			formatter.printHelp("Polca", options);
			System.exit(1);
		}

		// execute
		try {
			learn.run();
		} catch (Exception e) {
			throw e;
		}

	}

	public MealyMachine<?, String, ?, String> learnReference() throws Exception {
		String[] alphabet1 = {
				"h(0)", "h(1)", "h(2)", "h(3)", "h(4)", "h(5)", "h(6)", "h(7)", "h(8)",
				"h(9)", "h(10)", "h(11)", "h(12)", "h(13)", "h(14)", "h(15)", "h(16)", "h(17)",
				"h(18)", "h(19)", "h(20)", "h(21)", "h(22)", "h(23)", "h(24)", "h(25)", "h(26)",
		};
		alphabet1 = Arrays.copyOfRange(alphabet1, 0, this.config.ways + 1);
		alphabet1[alphabet1.length - 1] = "m()";
		Alphabet<String> abstractInputAlphabet1 = Alphabets.fromArray(alphabet1);
		Alphabet<String> alphabet = abstractInputAlphabet1;

		Random random = new Random();

		CacheSUL cacheSul = new CacheSUL(this.config, alphabet);
		CacheSULOracle cacheSulOracle = new CacheSULOracle(cacheSul, this.config, "mq", NoiseType.CLEAN,
				this.config.probability, random);

		return activeLearning(cacheSulOracle, alphabet, NoiseType.CLEAN, this.config.probability, random, 20000);
	}

	public void run() throws Exception {

		String[] alphabet1 = {
			"h(0)", "h(1)", "h(2)", "h(3)", "h(4)", "h(5)", "h(6)", "h(7)", "h(8)",
			"h(9)", "h(10)", "h(11)", "h(12)", "h(13)", "h(14)", "h(15)", "h(16)", "h(17)",
			"h(18)", "h(19)", "h(20)", "h(21)", "h(22)", "h(23)", "h(24)", "h(25)", "h(26)",
		};
		alphabet1 = Arrays.copyOfRange(alphabet1, 0, this.config.ways+1);
		alphabet1[alphabet1.length-1] = "m()";
		Alphabet<String> abstractInputAlphabet1 = Alphabets.fromArray(alphabet1);
		Alphabet<String> alphabet = abstractInputAlphabet1;

		Random random = new Random();
		Long seed = random.nextLong();
		random.setSeed(seed);

		CacheSUL cacheSul = new CacheSUL(this.config, alphabet);
		CacheSULOracle cacheSulOracle = new CacheSULOracle(cacheSul, this.config, "mq", this.config.noise, this.config.probability, random);
		MealyCounterOracle<String, String> counterOracle = new MealyCounterOracle<>(cacheSulOracle,
				"Membership Queries");
		// great results with 5 0.7 20
		// Number of repeats needed grows exponentially(?) with noise removal
		// percentage.
		ProbabilisticOracle<String, String> queryOracle = new ProbabilisticOracle<>(counterOracle, 10, 0.7, 20);
		
		MealyMachine<?, String, ?, String> hyp;

		if (this.config.learner == LearnAlgorithmType.PAS)	{
			Function<MembershipOracle.MealyMembershipOracle<String, String>, LearningAlgorithm.MealyLearner<String, String>> constructor;
			constructor = (sulOracle -> new ExtensibleLStarMealy<>(alphabet, sulOracle, Collections.emptyList(),
					ObservationTableCEXHandlers.RIVEST_SCHAPIRE, ClosingStrategies.CLOSE_SHORTEST));

			System.out.println("# Learning reference...");
			MealyMachine<?, String, ?, String> reference = learnReference();
			System.out.println("# Finished learning reference.");

			PAR learn = new PAR(constructor, queryOracle, alphabet, this.config.r_bound, this.config.revision_ratio,
					this.config.length_factor, false, random, counterOracle.getCounter());
			List<Pair<Integer, MealyMachine<?, String, ?, String>>> res = learn.run();

			res = toLifetime(res, this.config.r_bound);

			Integer correct = 0;
			for (Pair<Integer, MealyMachine<?, String, ?, String>> pair : res) {
				if (DeterministicEquivalenceTest.findSeparatingWord(reference, pair.getSecond(), alphabet) == null) {
					correct += pair.getFirst();
				}
			}

			System.out.println("# CORRECT RATIO: " + correct + " / " + this.config.r_bound);
			System.out.println("# SEED: " + seed);

			hyp = res.get(res.size()-1).getSecond();
		}
		else 
			hyp = activeLearning(queryOracle, alphabet, this.config.noise, this.config.probability, random,
					this.config.r_bound);

		count = counterOracle.getCount();

		if (this.config.temp_model) {
			try {
				PrintStream fileOut = new PrintStream(".model.tmp");
				GraphDOT.write(hyp, alphabet, fileOut); // may throw IOException!
				fileOut.close();
			} catch (IOException e) {}
		}

        if (!this.config.silent) System.out.println("-------------------------------------------------------");
		SimpleProfiler.stop("learn");
		System.out.println("\t" + SimpleProfiler.getResults());
        System.out.println("-------------------------------------------------------");
		System.out.println("--> Hypothesis: " + hyp.getStates() + " - " + hyp.size());
        System.out.println("-------------------------------------------------------");
//		System.out.println("Total HW queries: " + totalHwQueries);
		System.out.println("Summary Statistics: ");
		System.out.println("\t" + count);

		if (hyp != null) {
			// model statistics
			System.out.println("\ttotal states: " + hyp.size());
			System.out.println("\talphabet size: " + alphabet.size());
			System.out.println("-------------------------------------------------------");

			// show model
			System.out.println();
			System.out.println("Model: ");
			if (this.config.output_path.isEmpty()) {
				Visualization.visualize(hyp, alphabet);
			} else {
				PrintStream fileOut = new PrintStream(this.config.output_path);
				GraphDOT.write(hyp, alphabet, System.out); // may throw IOException!
				GraphDOT.write(hyp, alphabet, fileOut); // may throw IOException!
			}
		}

        System.out.println("-------------------------------------------------------");

    }



	private List<Pair<Integer, MealyMachine<?, String, ?, String>>> toLifetime(
			List<Pair<Integer, MealyMachine<?, String, ?, String>>> in, Integer limit) {
		List<Pair<Integer, MealyMachine<?, String, ?, String>>> out = new LinkedList<>();
		for (int i = 0; i < in.size(); i++) {
			int nextLimit = limit;
			if (i != in.size() - 1) {
				nextLimit = in.get(i + 1).getFirst();
			}

			out.add(Pair.of(nextLimit - in.get(i).getFirst(), in.get(i).getSecond()));
		}

		return out;

	}

	private MealyMachine<?, String, ?, String> activeLearning(MealyMembershipOracle<String, String> queryOracle,
			Alphabet<String> alphabet, NoiseType noise, float probability, Random random, Integer limit)
			throws Exception {
		// instantiate test driver
        System.out.println("-------------------------------------------------------");

		// Membership Queries
		MealyCounterOracle<String, String> statsMemOracle = new MealyCounterOracle<String, String>(queryOracle, "membership queries");
		MealyCacheOracle<String, String> cachedMemOracle = MealyCaches.createDAGCache(alphabet, statsMemOracle);
		MealyCounterOracle<String, String> statsCachedMemOracle = new MealyCounterOracle<String, String>(cachedMemOracle, "membership queries hit cache");
		MembershipOracle.MealyMembershipOracle<String, String> effMemOracle = this.config.no_cache ? statsMemOracle : statsCachedMemOracle;

		
		LearningAlgorithm.MealyLearner<String,String> learn;
		switch (this.config.learner) {
			case TTT:
				learn = new TTTLearnerMealyBuilder<String, String>().withAlphabet(alphabet).withOracle(effMemOracle).withAnalyzer(AcexAnalyzers.LINEAR_FWD).create();
				break;
			case DHC:
				learn = new MealyDHC<String, String>(alphabet, effMemOracle);
				break;
			case KV:
				learn = new KearnsVaziraniMealy<String, String>(alphabet, effMemOracle, true, AcexAnalyzers.LINEAR_FWD);
				break;
			case MP:
				learn = new MalerPnueliMealy<String, String>(alphabet, effMemOracle);
				break;
			case RS:
				learn = new RivestSchapireMealy<String, String>(alphabet, effMemOracle);
				break;
			case DT:
				learn = new DTLearnerMealy<String, String>(alphabet, effMemOracle, LocalSuffixFinders.RIVEST_SCHAPIRE, true);
				break;
			case LSTAR:
			default:
				learn = new ExtensibleLStarMealyBuilder<String,String>().withAlphabet(alphabet).withOracle(effMemOracle).create();
			break;
		
		}

		MealyMachine<?, String, ?, String> hyp = null;
		DefaultQuery<String, Word<String>> ce = null;

		// Main learning loop
		SimpleProfiler.start("learn");
		do {
			if (ce == null) {
				learn.startLearning();
			} else {
				boolean refined = learn.refineHypothesis(ce);
				if (!refined) {
					System.err.println("No refinement effected by counterexample!");
				}
			}

			hyp = learn.getHypothesisModel();
			if (!this.config.silent) System.out.println("--> Hypothesis: " + hyp.getStates() + " - " + hyp.size());
			// update depth with patch from: https://github.com/LearnLib/automatalib/issues/32

			// if reach max size, we can skip comformance testing (learning is sound refinement)
			if (hyp.size() >= this.config.max_size) {
				break;
			}

			if (this.config.temp_model) {
				try {
					PrintStream fileOut = new PrintStream(".model.tmp");
					GraphDOT.write(hyp, alphabet, fileOut); // may throw IOException!
					fileOut.close();
				} catch (IOException e) {
				}
			}

			MealyEquivalenceOracle<String, String> eqOracle = new MealyRandomWordsEQOracle<>(effMemOracle,
					this.config.r_min, this.config.r_len, limit);
			ce = eqOracle.findCounterExample(hyp, alphabet);

			if (!this.config.silent) System.out.println("ce : " + ce);

		} while (ce != null);

		System.out.println("Reference queries: " + (statsMemOracle.getCount() * this.config.repetitions));
		return hyp;
	}
}

