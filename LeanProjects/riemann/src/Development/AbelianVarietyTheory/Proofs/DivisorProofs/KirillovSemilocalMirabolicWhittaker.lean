import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerInfMemLocSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanKernelSpanCuspFormRightInvariantOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiLocalSpanRightInvariantOfTrivialInfinityFinsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerRelationPassesToSemiLocalSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormSemiLocalWhittakerSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KirillovSemiLocalMirabolicAbstractStatement

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix

namespace GlobalTheory.JSW.MirSemi

theorem kirillov_semilocal : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b : GA E (m + 1) → ℂ), (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ GlobalTheory.JSW.mirS E S m, b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * p ∈ C) → (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (m + 1) u) = b g) → (∀ g, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chart b g) (invSet E (m + 1))) → ∀ (π : CuspSub E (m + 1)) (φ : Sm E (m + 1)), φ ∈ π.V → (∃ p ∈ GlobalTheory.JSW.mirS E S m, GlobalTheory.JSW.whit φ.1 p ≠ 0) → ∃ F ∈ GlobalTheory.JSW.mspanR π, (∀ p ∈ GlobalTheory.JSW.mirS E S m, GlobalTheory.JSW.whit F p = b p) ∧ (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, F (g * finGL E (m + 1) u) = F g) ∧ (∀ k : GA E (m + 1), GeneralLinearGroup.map (pInf E) k = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) k = 1) → (∀ g, φ.1 (g * k) = φ.1 g) → ∀ g, F (g * k) = F g) ∧ ∀ (t : GA E (m + 1)) (c : ℂ), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ x ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit φ.1 (x * t) = c * GlobalTheory.JSW.whit φ.1 x) → ∀ x ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit F (x * t) = c * GlobalTheory.JSW.whit F x := by
  intro E _ _ _ m S b hbe hbC hbU hbs π φ hφ hnz
  obtain ⟨𝒲, hw0, h1, h2, h3, h4, h5, hback⟩ := GlobalTheory.T.exists_cusp_form_semi_local_whittaker_space E m S π φ hφ
  obtain ⟨W, hW, hWb⟩ := GlobalTheory.T.kirillov_semiLocal_mirabolic_abstract E m S b hbe hbC hbU hbs 𝒲 h1 h2 h3 h4 h5 ⟨_, hw0, hnz⟩
  obtain ⟨F, hF, hFW⟩ := hback W hW
  exact ⟨F, locSpan_le_mspanR hφ hF, fun p hp => by rw [hFW, hWb p hp],
    GlobalTheory.T.archimedeanKernelSpan_cuspForm_right_invariant_open E (m + 1) S π φ hφ F hF, fun k hk1 hk2 hk3 => GlobalTheory.T.semiLocalSpan_rightInvariant_of_trivial_infinity_finset E (m + 1) S φ.1 k hk1 hk2 hk3 F hF,
    fun t c ht1 ht2 ht3 => GlobalTheory.T.whittaker_relation_passes_to_semi_local_span E (m + 1) S π φ hφ t c ht1 ht2 ht3 F hF⟩

end GlobalTheory.JSW.MirSemi
