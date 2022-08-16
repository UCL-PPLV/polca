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
import java.util.Arrays;

import org.apache.commons.cli.*;

import java.io.PrintStream;

import de.learnlib.algorithms.kv.mealy.KearnsVaziraniMealy;
import de.learnlib.api.SUL;
import de.learnlib.api.oracle.MembershipOracle.MealyMembershipOracle;
import de.learnlib.acex.analyzers.AcexAnalyzers;
import de.learnlib.algorithms.continuous.base.PAS;
import de.learnlib.filter.statistic.oracle.MealyCounterOracle;
import de.learnlib.util.statistics.SimpleProfiler;
import net.automatalib.automata.transducers.impl.compact.CompactMealy;
import net.automatalib.commons.util.Pair;
import net.automatalib.serialization.dot.GraphDOT;
import net.automatalib.visualization.Visualization;
import net.automatalib.words.Alphabet;
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
	public int votes;
	public int limit;
	public double revision_ratio;
	public double length_factor;
	public boolean noise;

	public Config (CommandLine cmd) throws Exception {
		this.max_depth = Integer.parseInt(cmd.getOptionValue("depth", "1"));
		this.ways = Integer.parseInt(cmd.getOptionValue("ways", "4"));
		this.r_min = Integer.parseInt(cmd.getOptionValue("r_min", "10"));
		this.r_len = Integer.parseInt(cmd.getOptionValue("r_len", "30"));
		this.r_bound = Integer.parseInt(cmd.getOptionValue("r_len", "1000"));
		this.repetitions = Integer.parseInt(cmd.getOptionValue("repetitions", "100"));
		this.max_size = Integer.parseInt(cmd.getOptionValue("max_size", "2147483647"));
		this.hit_ratio = Float.parseFloat(cmd.getOptionValue("hit_ratio", "0.8"));
		this.miss_ratio = Float.parseFloat(cmd.getOptionValue("miss_ratio", "0.2"));
		this.votes = Integer.parseInt(cmd.getOptionValue("votes", "1"));
		this.prefix = cmd.getOptionValue("prefix", "@");
		this.is_hw = false;
		this.noise = cmd.hasOption("n");
		if (!cmd.hasOption("limit") || !cmd.hasOption("revision_ratio") || !cmd.hasOption("length_factor")) {
			throw new Exception("missing new flags");
		}
		this.limit = Integer.parseInt(cmd.getOptionValue("limit"));
		this.revision_ratio = Double.parseDouble(cmd.getOptionValue("revision_ratio"));
		this.length_factor = Double.parseDouble(cmd.getOptionValue("length_factor"));

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

	private Config config;

    public Polca (CommandLine cmd) throws Exception {
		this.config = new Config(cmd);
    }

    public static void main(String[] args) throws Exception {

		// Options
        Options options = new Options();

		// cache settings
		options.addOption(new Option("d", "depth", true, "max_depth for membership queries (default: 1)"));
		options.addOption(new Option("w", "ways", true, "cache associativity (default: 4)"));
		options.addOption(new Option("p", "policy", true, "simulator cache policy: fifo|lru|plru|lip|plip|mru|srriphp|srripfp|new1|new2|hw (default: 'fifo')"));
		options.addOption(new Option("b", "binary", true, "path to proxy for 'hw' policy"));
		// general
		options.addOption(new Option("o", "output", true, "write learnt .dot model into output file"));
		// other
		options.addOption(new Option("prefix",  true, "prefix before every query, used to fill cache (default: '@')"));
		options.addOption(new Option("r", "repetitions", true, "number of measurements by cachequery (default: 100)"));
		options.addOption(new Option("votes", true, "number of votes for deciding result (default: 1)"));
		options.addOption(new Option("hit_ratio", true, "ratio of hits to consider a HIT (default: 0.8)"));
		options.addOption(new Option("miss_ratio", true, "ratio of misses to consider a MISS (default: 0.2)"));
		options.addOption(new Option("limit", true, "NEW"));
		options.addOption(new Option("revision_ratio", true, "NEW"));
		options.addOption(new Option("length_factor", true, "NEW"));
		// learning settings
		options.addOption(new Option("m", "max_size", true, "maximum number of states of SUL"));
		options.addOption(new Option("r_min", true, "minimal length of random word (default: 10)"));
		options.addOption(new Option("r_len", true, "expected length of random word (r_min + r_len) (default: 30)"));
		options.addOption(new Option("r_bound", true, "bound on queries for equivalence, set to 0 for unbounded (default: 1000)"));
		options.addOption(new Option("r_rand", true, "TODO: select custom random generator"));
		// flags
		options.addOption(new Option("random", false, "use random wp-method as equivalence query"));
		options.addOption(new Option("temp", false, "write partial model into '.model.tmp' file"));
		options.addOption(new Option("verbose", false, "output verbose information"));
		options.addOption(new Option("no_cache", false, "don't use cache for membership queries"));
		options.addOption(new Option("h", "help", false, "show this help message"));
		options.addOption(new Option("s", "silent", false, "remove stdout info"));
		options.addOption(new Option("n", "noise", false, "add noise in the oracle"));

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
		try{
			learn.run();
		} catch (Exception e) {
			throw e;
		}

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

		SUL<String, String> memSul;
		MealyMembershipOracle<String, String> cacheSulOracle;

		memSul = this.config.noise ? new NoiseCacheSUL(this.config, alphabet) : new CacheSUL(this.config, alphabet);
		cacheSulOracle = this.config.noise ? new NoiseCacheSULOracle(memSul, this.config, "mq") : new CacheSULOracle(memSul, this.config, "mq");

		MealyCounterOracle<String, String> queryOracle = new MealyCounterOracle<>(cacheSulOracle, "Number of total queries");
	
		Random random = new Random();
		random.setSeed(System.nanoTime());
		
		// Learner from membership oracle
		PAS learn = new PAS(sulOracle -> new KearnsVaziraniMealy<String, String>(alphabet, sulOracle, true,
         	AcexAnalyzers.BINARY_SEARCH_BWD), queryOracle, alphabet, this.config.limit * 2, this.config.revision_ratio, this.config.length_factor, random);
		
		List<Pair<Integer, CompactMealy<String, String>>> result = learn.run();

		CompactMealy<String, String> hyp = result.get(result.size()-1).getSecond();

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
		System.out.println("\t" + queryOracle.getStatisticalData().getSummary());

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

}

