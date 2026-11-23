import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformizedFamilyChartIndex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramSmoothOfHolomorphicFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExponentialModelFiberOfUniformisationExp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedComplexPointOfEigenFrameOffBoundaryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpCoordinatesTangentFieldHolomorphicPeriodMapStatement
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.ArcQ
open scoped ContDiff

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ShFam.ExpCoord

open ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows (isDerivAt0_comp_hom isDerivAt0_unique)
open GlobalTheory.TrueCx.TorFrHolo (isDerivAt0_of_cart isHolTo_lift)
open GlobalTheory.ShFam.Hor.LogCh

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) {σ : c.F →+* ℂ}

theorem base_eq [Mono (genι Z)] (q : FrPt Xo c (CAt σ)) {w : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left}
    {v : Sp (DualNumber ℂ) ⟶ Z.t.G.left} (hv : IsTanAtG Z.t ((cxPt Z q).1 ≫ genι Z) v) (hw : w ≫ Z.m.φ = v) :
    w ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ GlobalTheory.AllWt.ptF (S := CAt σ) q := by
  have := Z.jQ_open
  refine (cancel_mono (Z.jQ ≫ genι Z)).1 ?_
  have h1 : w ≫ Z.oF.t.G.hom ≫ Z.jQ ≫ genι Z = v ≫ Z.t.G.hom := by
    rw [← hw, Category.assoc, Z.m.cart.1.w]
  rw [Category.assoc, h1, hv.1]
  rfl

theorem mono_genι_of_ringOfIntegers {Xo : Moduli Dw l} {c : Coeff l} (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) :
    Mono (genι Z) := by
  have : Epi (CommRingCat.ofHom (algebraMap (𝓞 c.F) c.F)) := IsLocalization.epi (nonZeroDivisors (𝓞 c.F)) c.F
  have : Mono (spMap (algebraMap (𝓞 c.F) c.F)) := Scheme.Spec.map_mono (CommRingCat.ofHom _).op
  infer_instance

theorem exists_expCoord : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (d g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (ch : AlgChart (genStr Z) σ d) (i : Fin Fu.n) (B : Set (ReciprocityTheory.L2DbarEstimates.V d)) (P : ReciprocityTheory.L2DbarEstimates.V d → ((Fu.Di i).La →+ (Fin g → ℂ))), IsOpen B → B ⊆ ch.e.target → (∀ b ∈ B, IsPeriod (Fu.Di i) ty (P b)) → (∀ v, DifferentiableOn ℂ (fun b => P b v) B) → (∀ b ∈ B, ∀ y : FrPt Xo c (CAt σ), ch.e.symm b = cxPt Z y → Fu.u i (P b) = y.x) → Mono (genι Z) → ∀ (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (F : EigFrame Z φ (LogKS.chart V ≫ genι Z)), LogKS.chart V ≫ genStr Z = spMap φ → ∃ z : ReciprocityTheory.L2DbarEstimates.V d → ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin g → ℂ), (∀ τ k, DifferentiableOn ℂ (fun b => z b τ k) {b ∈ B | ch.e.symm b ∈ ptsIn (genStr Z) σ V.1 ∧ ¬ LiesIn (ch.e.symm b) (genBd Z)}) ∧ ∀ b ∈ B, ∀ (hy : ch.e.symm b ∈ ptsIn (genStr Z) σ V.1) (f : EigFrame Z σ ((ch.e.symm b).1 ≫ genι Z)), F.IsMap (evHom hy) f → ∀ q : FrPt Xo c (CAt σ), cxPt Z q = ch.e.symm b → (∀ τ k, ∃ w : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left, w ≫ Z.m0.toSABMap.φ = q.u τ k ∧ w ≫ Z.m.φ = f.v τ k) → ∀ τ k, IsDerivAt0 (fun w => (Fu.ex i (P b) w).left) (z b τ k) (q.u τ k) := by
  classical
  intro E _ _ _ H Dw l Xo c O _ β Z σ d g ty Fu ch i B P hB hBt hPer hPd hPu hmono V φ F hstr
  set R := {b ∈ B | ch.e.symm b ∈ ptsIn (genStr Z) σ V.1 ∧ ¬ LiesIn (ch.e.symm b) (genBd Z)} with hR
  rcases B.eq_empty_or_nonempty with hBe | ⟨b₀, hb₀⟩
  · refine ⟨0, fun τ k => ?_, fun b hb => by simp [hBe] at hb⟩
    have : R = ∅ := by
      ext b
      simp [hR, hBe]
    rw [this]
    exact differentiableOn_empty
  let L := EuclideanSpace.equiv (Fin d) ℂ
  set B₁ : Set (Fin d → ℂ) := L.symm ⁻¹' B with hB₁
  have hB₁o : IsOpen B₁ := hB.preimage L.symm.continuous
  let P₂ : (Fin d → ℂ) → ((Fu.Di i).La →+ (Fin g → ℂ)) := fun x => if L.symm x ∈ B then P (L.symm x) else P b₀
  have hP₂ : ∀ x, IsPeriod (Fu.Di i) ty (P₂ x) := fun x => by
    by_cases h : L.symm x ∈ B
    · simp only [P₂, if_pos h]; exact hPer _ h
    · simp only [P₂, if_neg h]; exact hPer _ hb₀
  have hP₂d : ∀ a, DifferentiableOn ℂ (fun x => P₂ x a) B₁ := fun a =>
    ((hPd a).comp L.symm.differentiableOn fun x hx => hx).congr fun x hx => by
      simp only [P₂, if_pos (show L.symm x ∈ B from hx), Function.comp_apply]
  have hP₂L : ∀ b ∈ B, P₂ (L b) = P b := fun b hb => by
    simp only [P₂, ContinuousLinearEquiv.symm_apply_apply, if_pos hb]
  have hover : ∀ x, Fu.u i (P₂ x) ≫ Xo.s = spMap σ ≫ spMap (IntermediateField.inclusion c.le).toRingHom := fun x => by
    rw [Fu.over_σ i _ (hP₂ x), ← Spec.map_comp]
    rfl
  let p : (Fin d → ℂ) → (Sp ℂ ⟶ Xo.XF c) := fun x => pullback.lift _ _ (hover x)
  have hu : ∀ x, Fu.u i (P₂ x) = p x ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) :=
    fun x => (pullback.lift_fst _ _ _).symm
  have hs : ∀ x, p x ≫ pullback.snd _ _ = spMap σ := fun x => pullback.lift_snd _ _ _
  have hpq : ∀ b ∈ B, ∀ q : FrPt Xo c (CAt σ), cxPt Z q = ch.e.symm b → p (L b) = GlobalTheory.AllWt.ptF (S := CAt σ) q :=
    fun b hb q hq => by
      refine pullback.hom_ext ?_ ?_
      · rw [← hu, hP₂L b hb, hPu b hb q hq.symm]
        exact (GlobalTheory.TrueCx.ptC_fst q).symm
      · rw [hs]
        exact (GlobalTheory.TrueCx.ptC_snd q).symm
  have hσφ : ∀ {y : CxPts (genStr Z) σ} (h : y ∈ ptsIn (genStr Z) σ V.1), σ = (evHom h).comp φ := fun {y} h => by
    have e : spMap σ = spMap ((evHom h).comp φ) := by
      rw [← y.2, ← spMap_evHom h, Category.assoc, hstr, ← Spec.map_comp]
      rfl
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  have hRV : ∀ b ∈ R, ⊤ ≤ (p (L b) ≫ Z.jQ) ⁻¹ᵁ V.1 := fun b hb => by
    have hx : (ch.e.symm b).1 ≫ genι Z = spMap (evHom hb.2.1) ≫ LogKS.chart V ≫ genι Z := by
      rw [← Category.assoc, spMap_evHom hb.2.1]
    obtain ⟨f, -⟩ := F.exists_isMap (evHom hb.2.1) (hσφ hb.2.1) hx
    obtain ⟨q, hq, -⟩ := GlobalTheory.T.exists_framedComplexPoint_of_eigenFrame_off_boundary _ _ _ _ _ _ _ _ Z σ _ hb.2.2 f
    rw [hpq b hb.1 q hq]
    show ⊤ ≤ (cxPt Z q).1 ⁻¹ᵁ V.1
    rw [hq]
    exact hb.2.1
  choose W hW hWd using fun (a : Σ τ : E →+* ℂ, Fin (Dw.mult τ)) =>
    GlobalTheory.T.expCoordinates_tangentField_holomorphic_periodMap _ _ _ _ _ _ _ _ Z σ g ty Fu i d B₁ P₂ p hu V (F.v a.1 a.2) hB₁o hP₂ hP₂d hs (F.tan a.1 a.2)
  refine ⟨fun b τ k => W ⟨τ, k⟩ (L b), fun τ k => ?_, fun b hb hy f hf q hq hw τ k => ?_⟩
  · exact (hW ⟨τ, k⟩).comp L.differentiableOn fun b hb =>
      ⟨by simpa [hB₁] using hb.1, hRV b hb⟩
  · obtain ⟨w, hw1, hw2⟩ := hw τ k
    have hd := hWd ⟨τ, k⟩ (L b) (by simpa [hB₁] using hb) (ch.e.symm b) hy (by rw [hpq b hb q hq, ← hq]; rfl)
    have hfv : spMap (dualMap (evHom hy)) ≫ F.v τ k = w ≫ Z.m.φ := by rw [hw2, hf τ k]
    rw [hfv] at hd
    have hbase : w ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ p (L b) := by
      rw [hpq b hb q hq]
      exact base_eq Z q (by rw [hq]; exact f.tan τ k) hw2
    have h := isDerivAt0_ex_of_push Z Fu (p (L b)) i (P₂ (L b)) (hP₂ _) (hu _) hbase hd
    rw [hw1, hP₂L b hb] at h
    exact h

end GlobalTheory.ShFam.ExpCoord
