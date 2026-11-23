import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerInfMemLocSpan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerIndicatorCutMulOpenSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerCutInductionStepOfOpenSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MirabolicCutoffsOfRestrictionCutoffsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlaceStandardCharLocallyConstantNontrivialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MirabolicCellFiniteUnionLocalDoubleCosetsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompositeCutOperatorsProductLocalCellsMirabolicStatement

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW.Cut

open GlobalTheory.JSW.KirFin GlobalTheory.SmGL

theorem cuts_mir {F : Type} [NormedField F] [ProperSpace F] [IsUltrametricDist F] (ψ : AddChar F ℂ)
    (hψ : IsLocallyConstant ψ) (hψ1 : ψ ≠ 1) (m : ℕ) (U : Subgroup (GL (Fin (m + 1)) F))
    (hUc : IsCompact (U : Set (GL (Fin (m + 1)) F))) (hUo : IsOpen (U : Set (GL (Fin (m + 1)) F)))
    (z : GL (Fin (m + 1)) F) : Cuts ψ (U : Set (GL (Fin (m + 1)) F)) (cell z (U : Set (GL (Fin (m + 1)) F)))
      {p | lr p = lr 1} := by
  induction m with
  | zero =>
    classical
    have h1 : ∀ q : GL (Fin (0 + 1)) F, lr q = lr 1 → q = 1 := fun q hq => by
      obtain ⟨h, x, rfl⟩ := exists_mir hq
      rw [Subsingleton.elim h 1, Subsingleton.elim x 0, mir_one]
    refine ⟨Finsupp.single 1 (if (1 : GL (Fin (0 + 1)) F) ∈ cell z (U : Set (GL (Fin (0 + 1)) F)) then 1 else 0),
      fun f _ _ g hg => ?_⟩
    rw [h1 g hg, act_single, mul_one]
    by_cases h : (1 : GL (Fin (0 + 1)) F) ∈ cell z (U : Set (GL (Fin (0 + 1)) F))
    · rw [if_pos h, one_mul, Set.indicator_of_mem h]
    · rw [if_neg h, zero_mul, Set.indicator_of_notMem h]
  | succ m ih =>
    refine GlobalTheory.T.mirabolic_cutoffs_of_restriction_cutoffs ψ hψ hψ1 m (GlobalTheory.T.exists_whittakerCut_inductionStep_of_open_subgroup ψ hψ hψ1 m (fun V hVc hVo z' => ?_)) U hUc hUo z
    refine GlobalTheory.T.whittakerIndicatorCut_mul_open_subgroup ψ V hVo _ _ (fun x hx u hu => ?_) (ih V hVc hVo z')
    obtain ⟨n, hn, k, hk, rfl⟩ := hx
    exact ⟨n, hn, k * u, V.mul_mem hk hu, by rw [mul_assoc]⟩

end GlobalTheory.JSW.Cut

open GlobalTheory.JSW.Cut in

theorem GlobalTheory.JSW.MirPatch.cut_operators : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (K : Subgroup (GL (Fin (m + 1)) (Af E))), IsOpen (K : Set (GL (Fin (m + 1)) (Af E))) → IsCompact (K : Set (GL (Fin (m + 1)) (Af E))) → ∀ q : GA E (m + 1), ∃ (n : ℕ) (h : Fin n → GA E (m + 1)) (c : Fin n → ℂ), (∀ i, h i ∈ GlobalTheory.JSW.supS E (m + 1) S) ∧ ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ p ∈ GlobalTheory.JSW.mirS E S m, ∑ i, c i * W (p * h i) = (GlobalTheory.JSW.MirPatch.cell K q).indicator W p := by
  intro E _ _ _ m S K hKo hKc q
  classical
  obtain ⟨U, N, z, hU, hdisj, hchar⟩ := GlobalTheory.T.mirabolic_cell_finite_union_local_double_cosets E m S K hKo hKc q
  choose ψ hψv hψl hψ1 using GlobalTheory.T.finitePlace_standardChar_locallyConstant_nontrivial E
  have hcut : ∀ i : Fin N, ∃ T : GA E (m + 1) →₀ ℂ, (∀ h ∈ T.support, h ∈ GlobalTheory.JSW.supS E (m + 1) S ∧
      GeneralLinearGroup.map (pInf E) h = 1) ∧ ∀ W : GA E (m + 1) → ℂ,
      (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) →
      (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ p ∈ GlobalTheory.JSW.mirS E S m,
      act T W p = {x : GA E (m + 1) | ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x ∈
        GlobalTheory.JSW.Cut.cell (z i w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))}.indicator W p := by
    intro i
    refine GlobalTheory.T.composite_cut_operators_product_local_cells_mirabolic E m S ψ hψv K U (z i) (fun w hw => (hU w hw).2.2) fun w hw => ?_
    haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion E w
    haveI : IsUltrametricDist (w.adicCompletion E) :=
      inferInstanceAs (@IsUltrametricDist (w.adicCompletion E)
        (Valued.toNormedField (w.adicCompletion E) (WithZero (Multiplicative ℤ))).toDist)
    exact cuts_mir (ψ w) (hψl w) (hψ1 w) m (U w) (hU w hw).1 (hU w hw).2.1 (z i w)
  choose T hTs hT using hcut
  obtain ⟨n, h, c, hh, he⟩ := exists_fin (∑ i, T i)
  refine ⟨n, h, c, fun j => ?_, fun W hW hWK p hp => ?_⟩
  · obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum (hh j))
    exact (hTs i _ hi).1
  · rw [← he, act_finset_sum]
    simp_rw [fun i => hT i W hW hWK p hp]
    by_cases hc : p ∈ GlobalTheory.JSW.MirPatch.cell K q
    · obtain ⟨i, hi⟩ := (hchar p hp).1 hc
      rw [Set.indicator_of_mem hc, Finset.sum_eq_single i]
      · exact Set.indicator_of_mem (s := {x : GA E (m + 1) | _}) hi _
      · intro j _ hj
        exact Set.indicator_of_notMem (s := {x : GA E (m + 1) | _}) (fun hj' => hj (hdisj p hp j i hj' hi)) _
      · simp
    · rw [Set.indicator_of_notMem hc]
      refine Finset.sum_eq_zero fun i _ => Set.indicator_of_notMem (s := {x : GA E (m + 1) | _}) (fun hi => hc ((hchar p hp).2 ⟨i, hi⟩)) _
