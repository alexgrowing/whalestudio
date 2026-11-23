import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StepExactNS
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnfoldingSchurOrthogonalityDefiniteCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

noncomputable section

namespace GlobalTheory.ChainTwNorm

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem orZero_of {X : Type} [Zero X] {p : X → Prop} {x : X} (hx : p x) : OrZero p x :=
  ⟨fun _ => hx, fun hn => absurd ⟨x, hx⟩ hn⟩

theorem baseW_of_given (hG : Given R F) : R.BaseW F := by
  obtain ⟨lev, grp, fam, models, chain, thP⟩ := hG.core
  exact ⟨lev, grp, fam, models,
    ⟨chain.ωY, chain.ωX, chain.vY, chain.vX, chain.ptY, chain.ptX, fun k hk => orZero_of fun t => chain.ItY t k hk,
      orZero_of chain.ItX, fun t k hk => orZero_of (chain.ioY t k (by omega)), fun t => orZero_of (chain.ioX t),
      fun t => orZero_of (chain.Th t)⟩,
    ⟨thP.ωP, thP.vP, thP.pt_theta, fun i => orZero_of (thP.ioP i), fun i t => orZero_of ⟨thP.thF_mem i t, thP.thF i t⟩,
      fun i t => orZero_of (thP.thG i t)⟩⟩

theorem alg_step {d I aa xy ipv P P' na : ℂ} (hna : na ≠ 0) (e1 : aa = na ^ 2) (e2 : P = P') (h1 : d * I = aa * xy)
    (h2 : I = ipv * P) : xy = d * P' / na ^ 2 * ipv := by
  subst e1 e2 h2
  field_simp
  linear_combination -h1

theorem riesz {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (ℓ : W →ₗ[ℂ] ℂ) : ∃ a : W, ∀ w, ℓ w = ⟪a, w⟫_ℂ :=
  ⟨(InnerProductSpace.toDual ℂ W).symm (LinearMap.toContinuousLinearMap ℓ), fun w => by
    rw [InnerProductSpace.toDual_symm_apply]; rfl⟩

theorem normX : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∀ h : RangeX R, NormX R h := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG h
  have hB := baseW_of_given R F hG
  have hm := hG.core.models
  obtain ⟨w0, v0, hw0⟩ : ∃ (w : R.cX.W) (v : R.MX.Vec), R.prX w (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hm.prX.1
    refine LinearMap.ext fun w => LinearMap.ext fun x => ?_
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v => simp [hc w v]
    | add x y hx hy => simp [map_add, hx, hy]
  obtain ⟨a, ha⟩ := riesz (R.prX.flip (PiTensorProduct.tprod ℂ v0))
  have ha' : ∀ w, R.prX w (PiTensorProduct.tprod ℂ v0) = ⟪a, w⟫_ℂ := fun w => ha w
  have hna : a ≠ 0 := by
    rintro rfl
    exact hw0 (by rw [ha']; simp)
  have hv : ∀ τ, (v0 τ : R.MX.H τ) ≠ 0 := by
    intro τ h0
    apply hw0
    have : v0 τ = 0 := Subtype.ext h0
    rw [(PiTensorProduct.tprod ℂ).map_coord_zero τ this, map_zero]
  haveI : Nontrivial R.cX.W := hm.cX.2.2.2.1
  have hd : (0 : ℝ) < Module.finrank ℂ R.cX.W := by exact_mod_cast Module.finrank_pos
  have hP : (0 : ℝ) < ∏ τ, ‖(v0 τ : R.MX.H τ)‖ ^ 2 :=
    Finset.prod_pos fun τ _ => pow_pos (norm_pos_iff.2 (hv τ)) 2
  have hA : (0 : ℝ) < ‖a‖ ^ 2 := pow_pos (norm_pos_iff.2 hna) 2
  refine ⟨(Module.finrank ℂ R.cX.W : ℝ) * (∏ τ, ‖(v0 τ : R.MX.H τ)‖ ^ 2) / ‖a‖ ^ 2, by positivity, fun t => ⟨?_, ?_⟩⟩
  · have hi := GlobalTheory.DefiniteMult.top_injective R hm.inf hm.cX hm.prX hm.HX t
    refine ⟨fun x y e => ?_, fun z => ?_⟩
    · have e2 := (LinearEquiv.ofEq _ _ (h t)).injective e
      exact hi (congrArg Subtype.val e2)
    · obtain ⟨u, hu⟩ := (LinearMap.surjective_rangeRestrict _) ((LinearEquiv.ofEq _ _ (h t)).symm z)
      refine ⟨u, ?_⟩
      simp only [toCC, hu]
      exact (LinearEquiv.ofEq _ _ (h t)).apply_symm_apply z
  · intro ipD ip hM x y
    have hS := hM.schur (toCC R h t y) (toCC R h t x) (PiTensorProduct.tprod ℂ v0) (PiTensorProduct.tprod ℂ v0)
    have hS' := hS.trans (congrArg _ (hM.pure v0 v0))
    have hI := (GlobalTheory.T.unfolding_schur_orthogonality_definite_coefficients D G Pl0 T A Ks R F hB t x y a a).2
    have hJ : (∫ g in R.fdX t, star ⟪a, R.cX.ext ((R.HX t).e x) g⟫_ℂ * ⟪a, R.cX.ext ((R.HX t).e y) g⟫_ℂ ∂(R.νX t)) =
        ip (toCC R h t y) (toCC R h t x) * ∏ τ, ⟪(v0 τ : R.MX.H τ), (v0 τ : R.MX.H τ)⟫_ℂ := by
      refine Eq.trans ?_ hS'
      unfold Lift.pet
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      have e3 : (((toCC R h t y : (stX R t).CC (comR R t)) : SmT (stX R t).M →ₗ[ℂ] (GA D (stX R t).V → ℂ))
          (PiTensorProduct.tprod ℂ v0)) g = R.prX (R.cX.ext ((R.HX t).e y) g) (PiTensorProduct.tprod ℂ v0) := rfl
      have e4 : (((toCC R h t x : (stX R t).CC (comR R t)) : SmT (stX R t).M →ₗ[ℂ] (GA D (stX R t).V → ℂ))
          (PiTensorProduct.tprod ℂ v0)) g = R.prX (R.cX.ext ((R.HX t).e x) g) (PiTensorProduct.tprod ℂ v0) := rfl
      simp only [e3, e4, ha', starRingEnd_apply]
      exact mul_comm _ _
    have e1 : ⟪a, a⟫_ℂ = ((‖a‖ : ℂ)) ^ 2 := inner_self_eq_norm_sq_to_K a
    have e2 : (∏ τ, ⟪(v0 τ : R.MX.H τ), (v0 τ : R.MX.H τ)⟫_ℂ) = ∏ τ, ((‖(v0 τ : R.MX.H τ)‖ : ℂ)) ^ 2 :=
      Finset.prod_congr rfl fun τ _ => inner_self_eq_norm_sq_to_K _
    have hA' : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hna).ne'
    have H := alg_step hA' e1 e2 hI hJ
    rw [H]
    push_cast
    ring
end GlobalTheory.ChainTwNorm
