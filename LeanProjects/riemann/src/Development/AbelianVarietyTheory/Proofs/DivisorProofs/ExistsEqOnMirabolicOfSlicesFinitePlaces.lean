import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerInfMemLocSpan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCutOperatorsMirabolicFinitePlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDisjointUnipotentCellsCoverCompactMiraboliStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOnDoubleCosetOfEqOnArchimedeanSliceStatement

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

theorem GlobalTheory.JSW.MirPatch.exists_eq_on_mirS_of_slices : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b : GA E (m + 1) → ℂ) (𝒲 : Submodule ℂ (GA E (m + 1) → ℂ)), (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ GlobalTheory.JSW.mirS E S m, b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * p ∈ C) → (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (m + 1) u) = b g) → (∀ W ∈ 𝒲, ∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ W ∈ 𝒲, ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, (fun g => W (g * h)) ∈ 𝒲) → (∀ W ∈ 𝒲, ∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, W (g * finGL E (m + 1) u) = W g) → (∀ q ∈ GlobalTheory.JSW.mirS E S m, GeneralLinearGroup.map (pInf E) q = 1 → ∃ W ∈ 𝒲, ∀ y : GL (Fin (m + 1)) (Cinf E), q * infGL E (m + 1) y ∈ GlobalTheory.JSW.mirS E S m → W (q * infGL E (m + 1) y) = b (q * infGL E (m + 1) y)) → ∃ W ∈ 𝒲, ∀ p ∈ GlobalTheory.JSW.mirS E S m, W p = b p := by
  intro E _ _ _ m S b 𝒲 hb ⟨C, hC, hbC⟩ ⟨Ub, hUbo, hUb⟩ hWe hWt hWU H
  classical
  have hsel : ∀ q : GA E (m + 1), ∃ W ∈ 𝒲, (q ∈ GlobalTheory.JSW.mirS E S m ∧ GeneralLinearGroup.map (pInf E) q = 1 →
      ∀ y : GL (Fin (m + 1)) (Cinf E), q * infGL E (m + 1) y ∈ GlobalTheory.JSW.mirS E S m →
        W (q * infGL E (m + 1) y) = b (q * infGL E (m + 1) y)) := by
    intro q
    by_cases hq : q ∈ GlobalTheory.JSW.mirS E S m ∧ GeneralLinearGroup.map (pInf E) q = 1
    · obtain ⟨W, hW, h⟩ := H q hq.1 hq.2
      exact ⟨W, hW, fun _ => h⟩
    · exact ⟨0, 𝒲.zero_mem, fun h => absurd h hq⟩
  choose Wq hWq hWqb using hsel
  choose Uq hUqo hUq using fun q => hWU _ (hWq q)
  obtain ⟨K, R, j, hKo, hKc, hR, hcov, huniq⟩ :=
    GlobalTheory.T.exists_disjoint_unipotentCells_cover_compact_mirabolic E m S C hC (fun q => Ub ⊓ Uq q) (fun q => hUbo.inter (hUqo q))
  choose n hh c hhS hcutEq using fun x => GlobalTheory.T.exists_cutOperators_mirabolic_finitePlaces E m S K hKo hKc x
  refine ⟨∑ x ∈ R, ∑ i, c x i • (fun g => Wq (j x) (g * hh x i)), ?_, ?_⟩
  · exact 𝒲.sum_mem fun x _ => 𝒲.sum_mem fun i _ => 𝒲.smul_mem _ (hWt _ (hWq _) _ (hhS x i))
  · intro p hp
    have e1 : (∑ x ∈ R, ∑ i, c x i • (fun g => Wq (j x) (g * hh x i))) p =
        ∑ x ∈ R, (GlobalTheory.JSW.MirPatch.cell K x).indicator (Wq (j x)) p := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun x hx => ?_
      refine hcutEq x (Wq (j x)) (hWe _ (hWq _)) (fun u hu g => hUq _ u ((hR x hx).2.2.1 hu).2 g) p hp
    have e2 : ∀ x ∈ R, (GlobalTheory.JSW.MirPatch.cell K x).indicator (Wq (j x)) p =
        (GlobalTheory.JSW.MirPatch.cell K x).indicator (fun _ => b p) p := by
      intro x hx
      by_cases hpx : p ∈ GlobalTheory.JSW.MirPatch.cell K x
      · rw [Set.indicator_of_mem hpx, Set.indicator_of_mem hpx]
        obtain ⟨hj1, hj2, -, hj4⟩ := hR x hx
        exact GlobalTheory.T.eq_on_doubleCoset_of_eq_on_archimedeanSlice E m S b (Wq (j x)) (Ub ⊓ Uq (j x)) (j x) hj1 hj2 hb (hWe _ (hWq _))
          (fun u hu g => hUb u hu.1 g) (fun u hu g => hUq _ u hu.2 g) (hWqb _ ⟨hj1, hj2⟩) p hp (hj4 hpx)
      · rw [Set.indicator_of_notMem hpx, Set.indicator_of_notMem hpx]
    rw [e1, Finset.sum_congr rfl e2]
    by_cases hbp : b p = 0
    · rw [hbp]; simp
    · obtain ⟨x0, hx0, hpx0⟩ := hcov p hp (hbC p hp hbp)
      rw [Finset.sum_eq_single x0 (fun x hx hne => Set.indicator_of_notMem
        (fun hpx => hne (huniq x hx x0 hx0 p hp hpx hpx0)) _) (fun h => absurd hx0 h),
        Set.indicator_of_mem hpx0]
