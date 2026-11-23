import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultOfNotMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInterior
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtEqOfPtOfFrameEq
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option autoImplicit false

theorem GlobalTheory.ShFam.chart_lift_periods_of_openPart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (X : Var F) (j : X.X ⟶ gen T.Z) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∃ (i : Fin Fu.n) (B : Set (ReciprocityTheory.L2DbarEstimates.V X.dim)) (P : ReciprocityTheory.L2DbarEstimates.V X.dim → ((Fu.Di i).La →+ (Fin g → ℂ))), IsOpen B ∧ c'.e y ∈ B ∧ B ⊆ c'.e.target ∧ (∀ b ∈ B, IsPeriod (Fu.Di i) ty (P b)) ∧ (∀ x, DifferentiableOn ℂ (fun b => P b x) B) ∧ ∀ b ∈ B, ∃ q : FrPt Xo c (Formalism.L2.Pj.CAt σ), cxPt T.Z q = cxOf e σ hj (c'.e.symm b) ∧ Fu.u i (P b) = q.x := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ g ty Fu X j hj hjo y hy c' hyc
  have := T.Z.jQ_open
  have : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
  let L := EuclideanSpace.equiv (Fin X.dim) ℂ
  have hsy := GlobalTheory.TrueCx.TorHolo.isHolTo_symm c'
  have hsj := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp hsy j
  have hB₀ := (hsj T.Z.jQ.opensRange 0).1
  set B₀ := {b ∈ c'.e.target | ⊤ ≤ ((c'.e.symm b).1 ≫ j) ⁻¹ᵁ T.Z.jQ.opensRange} with hB₀def
  have hb₀ : c'.e y ∈ B₀ := by
    refine ⟨c'.e.map_source hyc, ?_⟩
    rw [c'.e.left_inv hyc]
    intro s _
    have h1 : y.1 s ∈ openPart j := hy (Set.mem_univ s)
    exact not_not.1 h1
  have hw : ∀ b ∈ B₀, ∃ w : Sp ℂ ⟶ Xo.XF c, w ≫ T.Z.jQ = (c'.e.symm b).1 ≫ j := fun b hb =>
    ⟨IsOpenImmersion.lift T.Z.jQ _ (by rintro _ ⟨s, rfl⟩; exact hb.2 (Set.mem_univ s)), IsOpenImmersion.lift_fac _ _ _⟩
  have : Nonempty (Sp ℂ ⟶ Xo.XF c) := ⟨(hw _ hb₀).choose⟩
  choose! w hw using hw
  have hwh : IsHolTo B₀ w := GlobalTheory.TrueCx.TorHolo.isHolTo_of_openImmersion T.Z.jQ
    (LocLift.isHolTo_congr (LocLift.isHolTo_mono hsj hB₀ fun b hb => hb.1) hw)
  have hyh := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp hwh (Limits.pullback.fst _ _)
  have hsnd : ∀ b ∈ B₀, w b ≫ Limits.pullback.snd _ _ = spMap σ := fun b hb => by
    rw [← T.Z.jQ_over, ← Category.assoc, hw b hb]
    exact (Category.assoc _ _ _).trans (cxOf e σ hj (c'.e.symm b)).2
  have hB₁ : IsOpen (L.symm ⁻¹' B₀) := hB₀.preimage L.symm.continuous
  obtain ⟨B', i, P, hB', hb', hsub, hP, hu⟩ := Fu.lift X.dim (L.symm ⁻¹' B₀) (fun x => w (L.symm x) ≫ Limits.pullback.fst _ _) hB₁
    (fun x hx => by
      rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hsnd _ hx, ← Spec.map_comp]
      rfl)
    (LocLift.isHolTo_comp hyh hB₁ L.symm.differentiableOn fun x hx => hx) (L (c'.e y))
    (by simpa only [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hb₀)
  refine ⟨i, L ⁻¹' B', fun v => P (L v), hB'.preimage L.continuous, hb', fun v hv => ?_, fun v hv => hP.1 _ hv,
    fun x => (hP.2 x).comp L.differentiableOn fun v hv => hv, fun b hb => ?_⟩
  · have := hsub hv
    simp only [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply] at this
    exact this.1
  · have hb1 := hsub hb
    simp only [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply] at hb1
    have h2 := hu _ hb
    simp only [ContinuousLinearEquiv.symm_apply_apply] at h2
    have ho : (w b ≫ Limits.pullback.fst _ _) ≫ Xo.s = sOf c (CAt σ) := by
      rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hsnd b hb1]
      exact OpenReg.spMap_comp _ _
    obtain ⟨q, hq⟩ : ∃ q : FrPt Xo c (CAt σ), q.x = w b ≫ Limits.pullback.fst _ _ := GlobalTheory.FlagTan.exists_frPt _ ho
    refine ⟨q, Subtype.ext ?_, h2.trans hq.symm⟩
    have h3 : GlobalTheory.AllWt.ptF (S := CAt σ) q = w b :=
      Limits.pullback.hom_ext ((ptF_fst q).trans hq) ((ptF_snd q).trans (hsnd b hb1).symm)
    exact (congrArg (· ≫ T.Z.jQ) h3).trans (hw b hb1)
