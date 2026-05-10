# TODO

Improvement plan for `franklin.v`. Items are ordered by logical dependency: earlier items unblock or simplify later ones.

1. Replace `Require Import NArith List Lia` with `From Stdlib Require Import NArith List Lia` to clear the Rocq 9 deprecation warnings.
2. Renumber the body's section headers so they match the table-of-contents header at the top of the file.
3. Fix every in-comment reference to a nonexistent subsection, including the dangling "Section 5.1.1 Consumption Tracking" pointer.
4. Add archive.org snapshots and DOIs for every external URL in the in-file bibliography.
5. Add an `iv_sub` operation (saturating at zero over `N`) with validity and containment lemmas.
6. Prove the missing algebraic lemmas: `iv_add_comm`, `iv_add_assoc`, `iv_mul_comm`, `iv_mul_assoc`, and `iv_distrib`.
7. Generalize `iv_div_interval` to handle `iv_lo denom = 0 < iv_hi denom` by introducing a saturating-with-infinity interval type, and prove the soundness lemma for the new case.
8. Generalize the interval library to an ordered-semiring module type so the development ports cleanly to `Z` and beyond.
9. Prove a soundness statement for `iv_mul_correlated` that genuinely involves dependence, deriving a bound on `E[XY] - E[X]E[Y]` from a stated covariance hypothesis.
10. Derive the `+1`, `/2000`, `/2` constants in `iv_mul_correlated` from a stated probability bound, and prove the resulting interval is the tightest sound bound under that hypothesis.
11. Derive the `cv_b^2 / (cv_w^2 + cv_b^2)` variance-decomposition formula from first principles in an in-file appendix.
12. Add ADM 114/17 folio numbers to each manifest item so quantities are individually traceable.
13. Add precise table and page references for every kcal/oz figure attributed to Battarbee 1980.
14. Cite Hodges 1971 Table 3 explicitly for the 10 mg/day vitamin C anti-scurvy threshold, with confirmatory cross-cite to the WHO standard, and add an interval around it.
15. Cite Cyriax 1939 Chapter 10 for the Victorian naval TB prevalence figure with a proper confidence interval drawn from his prevalence tables.
16. Replace Tier 4 citations (Smithsonian Magazine, canadaehx.com) supporting quantitative claims with primary sources for each affected figure (cannibalism count, Inuit population).
17. Cite the primary Admiralty Goldner contract records for `goldner_batch_count := 3`.
18. Cite primary sources for `cv_within_batch_permille` and `cv_between_batch_permille`, drawing on Goldner factory records or contemporary canning-industry trials.
19. Cite a primary source (Parks Canada wreck surveys, McClintock inventory) for `coal_accessibility_percentage_point := 59`.
20. Trace `coal_consumption_per_day_interval := [500, 1500]` to ADM 7/619 steam-trial figures with folio references.
21. Convert `inuit_population_1847`, `kwi_carrying_capacity`, `terror_drift_distance_km`, and `boat_actual_cargo_kg` from point values to intervals consistent with the rest of the file.
22. Replace `human_body_kcal := 125000` with an interval `[80000, 150000]` and subtract a fuel cost for rendering.
23. Replace `coal_energy_density_j_per_kg := 25000000` with an interval `[20e6, 30e6]` reflecting variable coal grade.
24. Propagate the cited 100-300 permille stove efficiency range into all downstream calculations instead of using the single point 200 permille.
25. Designate `accessible_coal_exhaustion_interval` as the canonical coal model in the headline survival theorems and label the total-coal model explicitly as a theoretical maximum.
26. Designate the death-adjusted consumption model as canonical and reconcile the 30-day vs 96-day Victory Point survival figures explicitly.
27. State which of `aggregate_daily_need` or `crew_initial * min_daily_need_per_man` is canonical for survival theorems and use it consistently.
28. Define a single `canonical_survival_interval` referenced from a summary section, with the relationships between the food-only, accessible-coal-integrated, and point-estimate numbers stated in one place.
29. Rename `monte_carlo_universal_doom` to `monte_carlo_grid_doom` and flag `survival_upper_bound_from_interval` as the genuine continuous-space result.
30. Rename `sigmoidal_universally_bounded_*` to `sigmoidal_bounded_to_1100_days_*` to reflect the actual proof domain.
31. Recompute `variance_determines_fate` using non-tinned interval bounds, and report tin-attributable variance separately from total variance.
32. Add the missing ice sensible-heat term (warming sub-freezing ice to 0 °C before melting) to the energy budget for ice-to-water fuel.
33. Couple the cold metabolic multiplier to coal availability so that exhaustion of coal raises the multiplier further.
34. Replace constant role activity hours with an integration over a daily schedule (sleep, eating, transitions, primary activity).
35. Define `bmr_interval_by_role` and aggregate caloric need from per-role BMR rather than a uniform value.
36. Define `net_hunting_yield := gross_yield - hunters * hunt_hours * activity_kcal_per_hour Hunting` and use the net figure in survival extension theorems.
37. Add `body_fat_reserve_kcal` per crew member with depletion before lean-tissue catabolism.
38. Add a `bmr_starvation_multiplier` that decays BMR with consecutive deficit days to model metabolic suppression.
39. Replace the uniform `+200 permille` scurvy efficiency loss with a piecewise function: zero loss before day 60, then accelerating loss to a plateau, with citations.
40. Compute zinc depletion from the manifest's zinc-per-ounce by provision type instead of from time alone.
41. Anchor the TB reactivation risk to documented Victorian-era data on stress-induced TB conversion.
42. Add deficiency models for thiamine, niacin, and vitamin D with diet-coupled depletion curves.
43. Increase modeled water requirement when protein fraction of diet is high (urea-excretion water cost).
44. Fit `mortality_rate_early` to the Beechey first-winter deaths and `mortality_rate_late` to Keys 1950 Vol. 2 Chapter 36 mortality curves, replacing narrative calibration.
45. Add a `mortality_rate_calibrated_to_beechey` lemma showing the early rate predicts approximately three deaths in the first ~220 days from 129 men.
46. Add a section computing Ross 1829-33 expedition survival under the same model and showing it correctly predicts survival, as a control case.
47. Add a model-inversion theorem characterizing exactly the parameter region that admits 105 alive at day 584.
48. Distinguish `caloric_exhaustion_day` from `expected_death_day` with an offset for non-caloric mortality (infection, hypothermia, accidents).
49. Prove that the produced survival interval is the tightest bound consistent with the input intervals.
50. Tighten the input intervals for re-occupation, Inuit-trade, and cache-recovery scenarios using primary archival sources (Parks Canada surveys, Schwatka 1881 inventories, McClintock cairn records).
51. Replace trivial pro-forma `_counterexample` lemmas with genuine boundary tests one step past the interval edge.
52. Replace every `vm_compute` proof with a structural lemma capturing the underlying invariant, eliminating brute-force evaluation from the build.
53. Add `Extraction "franklin.ml" canonical_survival_interval ...` so the canonical survival numbers are callable from OCaml or Haskell.
