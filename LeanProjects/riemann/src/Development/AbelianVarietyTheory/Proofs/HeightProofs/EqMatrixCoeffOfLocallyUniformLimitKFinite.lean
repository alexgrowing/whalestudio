import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotMemOfMulExp
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContinuousOnRightDerivativeFamilyModerateGrowthStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CoeffSumSmoothRightDerivWordsStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RightDerivativeRelationOfLocallyUniformLimitStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsMapsOfRelationsStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSobolevContinuousFormOfModerateGrowthMapStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CoeffWordModerateGrowthBoundStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos

theorem GlobalTheory.TypeSum.CoefClos.eq_coef_of_closure : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : GlobalTheory.TypeSum.Mx n → (H →L[ℂ] H)), GlobalTheory.TypeSum.Std ε σ →
    ∀ (d : ℕ) (w : Fin d → H), (∀ a, IsKFin ε σ (w a)) →
    ∀ h : GlobalTheory.TypeSum.Mx n → ℂ, ContinuousOn h (UJset ε) → GlobalTheory.TypeSum.UMG ε h →
    (∀ C : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact C → ∀ δ : ℝ, 0 < δ →
        ∃ L : Fin d → (H →ₗ[ℂ] ℂ), (∀ a, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (L a)) ∧
          ∀ y ∈ C, y ∈ UJset ε → ‖h y - ∑ a, L a (σ y (w a))‖ < δ) →
    ∃ L : Fin d → (H →ₗ[ℂ] ℂ), (∀ a, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (L a)) ∧
      ∀ y ∈ UJset ε, h y = ∑ a, L a (σ y (w a)) := by
  intro hHC hCW n ε H _ _ _ σ hstd d w hw h hcont humg happ
  obtain ⟨N, Φ, hΦ0, hΦD, hΦG⟩ := humg
  have hCh : CSm ε h := ⟨Φ, hΦ0, hΦD, GlobalTheory.T.continuousOn_rightDerivativeFamily_moderateGrowth n ε N Φ hΦD hΦG⟩
  set h0 : Mx n → ℂ := (UJset ε).indicator h with hh0def
  have hh0 : ∀ g ∈ UJset ε, h g = h0 g := fun g hg => (Set.indicator_of_mem hg h).symm
  have hm0 : h0 ∈ Smo ε := ⟨fun g hg => Set.indicator_of_notMem hg h, hCh.congr hh0⟩
  have hwS : ∀ a, Sm ε σ (w a) := fun a => hstd.2.2.1 _ (hw a)
  have hrel : ∀ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List (Ltr ε)), (∀ a, ∑ i, c i • wordV σ (u i) (w a) = 0) →
      ∑ i, c i • wordE ltrM (u i) (⟨h0, hm0⟩ : Smo ε) = 0 := by
    intro m c u hcu
    have hA := GlobalTheory.T.rightDerivativeRelation_of_locallyUniformLimit n ε h hCh m c u (fun C hC δ hδ => by
      obtain ⟨L, hL, hLa⟩ := happ C hC δ hδ
      obtain ⟨hB1, hB2⟩ := GlobalTheory.T.coeffSum_smooth_rightDerivWords n ε H σ hstd d L hL w hwS
      refine ⟨_, hB1, hLa, fun y hy => ?_⟩
      simp only [fun i => hB2 (u i) y hy]
      rw [← Finset.sum_eq_zero (s := (Finset.univ : Finset (Fin d))) (f := fun a => L a (σ y (∑ i, c i • wordV σ (u i) (w a))))
        (fun a _ => by rw [hcu a, map_zero, map_zero])]
      simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_comm)
    apply Subtype.ext
    funext g
    simp only [Submodule.coe_sum, Submodule.coe_smul, coe_wordE, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Submodule.coe_zero, Pi.zero_apply]
    by_cases hg : g ∈ UJset ε
    · rw [← hA g hg]
      exact Finset.sum_congr rfl fun i _ => by rw [wordF_congr hh0 (u i) g hg]
    · refine Finset.sum_eq_zero fun i _ => ?_
      have := (wordE ltrM (u i) (⟨h0, hm0⟩ : Smo ε)).2.1 g hg
      rw [coe_wordE] at this
      rw [this, mul_zero]
  obtain ⟨T, hT1, hT2, hT3⟩ := GlobalTheory.T.exists_maps_of_relations_alt hHC n ε H σ hstd d w hw (Smo ε) ltrM ⟨h0, hm0⟩ hrel
  have hD : ∀ a, ∃ L : H →ₗ[ℂ] ℂ, Sobolev₂ (lieSet ε) σ L ∧ ∀ v, IsKFin ε σ v → ∀ y ∈ UJset ε,
      ((Smo ε).subtype ∘ₗ T a) v y = L (σ y v) := by
    intro a
    refine GlobalTheory.T.exists_sobolevContinuous_form_of_moderateGrowthMap hCW n ε H σ hstd N ((Smo ε).subtype ∘ₗ T a) (fun v hv => ?_) (fun v hv k hk g hg => ?_)
      (fun v hv X hX g hg => ?_)
    · obtain ⟨m, c, u, e⟩ := hT3 a v hv
      have hb := fun i => GlobalTheory.T.coeffWord_moderateGrowth_bound n ε N h Φ hΦ0 hΦD hΦG (u i)
      choose C hC using hb
      refine ⟨∑ i, ‖c i‖ * C i, fun g hg => ?_⟩
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, e, Submodule.coe_sum, Submodule.coe_smul, coe_wordE,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_mul, mul_assoc, ← wordF_congr hh0 (u i) g hg]
      exact mul_le_mul_of_nonneg_left (hC i g hg) (norm_nonneg _)
    · have := hT1 a v hv (Sum.inr ⟨k, hk⟩)
      simp only [LinearMap.comp_apply, Submodule.subtype_apply]
      rw [show σ k v = ltrV σ (Sum.inr ⟨k, hk⟩ : Ltr ε) v from rfl, this]
      rfl
    · have := hT1 a v hv (Sum.inl ⟨X, hX⟩)
      simp only [LinearMap.comp_apply, Submodule.subtype_apply]
      rw [show dRep σ X v = ltrV σ (Sum.inl ⟨X, hX⟩ : Ltr ε) v from rfl, this]
      exact (T a v).2.2.hasDerivAt hX hg
  choose L hL1 hL2 using hD
  refine ⟨L, hL1, fun y hy => ?_⟩
  rw [hh0 y hy, show h0 = ((⟨h0, hm0⟩ : Smo ε) : Mx n → ℂ) from rfl, ← hT2, Submodule.coe_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => hL2 a (w a) (hw a) y hy
