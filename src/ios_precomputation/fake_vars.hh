#pragma once

#include "utils/transition_enumerator.hh"

namespace ios_precomputation {
  namespace detail {
    template <typename RetSet, typename FormSet, typename Projection>
    auto power_fakevars (const FormSet& crossings,
                         const Projection& projection) {
      RetSet powset;
      powset[bddtrue] = typename RetSet::mapped_type ({});

      int cur_var = 0;
      int var_available = 0;
      std::vector<bdd> fvar_to_input;
      bdd all_fvars = bddtrue;

#define MORE_VARS 1024

      auto get_fresh_var = [&] () {
        if (var_available--)
          return ++cur_var;
        var_available = MORE_VARS - 1;
        auto new_var = bdd_extvarnum (MORE_VARS);
        assert (cur_var == 0 or cur_var == new_var - 1);
        cur_var = new_var;
        for (int i = cur_var; i < cur_var + MORE_VARS; ++i)
          all_fvars &= bdd_ithvar (i);
        fvar_to_input.resize (cur_var + MORE_VARS);
        return cur_var;
      };

      int true_fvar = get_fresh_var ();
      bdd all_inputs_with_fvars = bdd_ithvar (true_fvar);
      fvar_to_input[true_fvar] = bddtrue;

      for (const auto& [crossing, trans] : crossings) {
        auto crossing_inputs = projection (crossing);
        auto fvars = bdd_existcomp (crossing_inputs & all_inputs_with_fvars, all_fvars);

        auto not_crossing_inputs = !crossing_inputs;
        // fvars is a disjunction of fake vars.
        while (fvars != bddfalse) {
          auto var = bdd_var (fvars);
          auto input = fvar_to_input[var];
          auto input_and_not_crossing_inputs = input & not_crossing_inputs;
          if (input_and_not_crossing_inputs != bddfalse) { // Split
            auto input_and_crossing_inputs = input & crossing_inputs;
            assert (input_and_crossing_inputs != input && input_and_crossing_inputs != bddfalse);
            //assert (input == bdd_existcomp (input, input_support));
            auto it = powset.find (input);
            assert (it != powset.end ());
            powset.emplace (input_and_not_crossing_inputs, it->second);
            it->second.push_back (trans);
            powset.emplace (input_and_crossing_inputs, std::move (it->second));
            powset.erase (it);

            auto ianc_var = get_fresh_var ();
            //fvars_available = bdd_high (fvars_available);
            // all_inputs_with_fvars = bdd_forall (all_inputs_with_fvars, bdd_ithvar (var)); // improve?
            all_inputs_with_fvars = bdd_restrict (all_inputs_with_fvars, bdd_nithvar (var));
            all_inputs_with_fvars |= ((bdd_ithvar (var) & input_and_crossing_inputs) |
                                      (bdd_ithvar (ianc_var) & input_and_not_crossing_inputs));
            //all_fvars &= bdd_ithvar (ianc_var);
            fvar_to_input[var] = input_and_crossing_inputs;
            fvar_to_input[ianc_var] = input_and_not_crossing_inputs;
            //assert (input_and_not_crossing_inputs == bdd_existcomp (input_and_not_crossing_inputs, input_support));
            //assert (input_and_crossing_inputs == bdd_existcomp (input_and_crossing_inputs, input_support));
          }
          else
            powset[input].push_back (trans);
#warning Discussion point
          fvars = bdd_low (fvars);
        }
      }
      //aut->get_dict ()->unregister_all_my_variables (this);

      return powset;
    }

    template <typename Aut, typename TransSet>
    class fake_vars {
      public:
        fake_vars (Aut aut, bdd input_support, bdd output_support, int verbose) :
          aut {aut}, input_support {input_support}, output_support {output_support}, verbose {verbose}
        {}

        auto operator() () const
        {
          using crossings_t = typename std::map<bdd_t, TransSet>;
          using input_to_ios_t = typename std::map<bdd_t, std::list<TransSet>>;

          auto crossings = power_fakevars<crossings_t> (transition_enumerator (aut),
                                                        [] (bdd b) { return b; });

          return power_fakevars<input_to_ios_t> (crossings,
                                                 [this] (bdd b) {
                                                   return bdd_exist (b, output_support);
                                                 });
        }

      private:
        Aut aut;
        const bdd input_support, output_support;
        const int verbose;
    };

  }

  struct fake_vars {
      template <typename Aut, typename TransSet = std::vector<std::pair<unsigned, unsigned>>>
      static auto make (Aut aut, bdd input_support, bdd output_support, int verbose) {
        return detail::fake_vars<Aut, TransSet> (aut, input_support, output_support, verbose);
      }
  };
}
