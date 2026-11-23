import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricOnSet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformizedFamilyChartIndex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFamilyChartDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedComplexPointOfEigenFrameOffBoundary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFamilyChartHolomorphic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenframeGramNearPoint
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ComponentEqOfMatchedLatticesMarkings
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyUnifWitnessDataOfIsUnf

set_option autoImplicit false

noncomputable section

section SlopeTestRemainingChoices

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ProjVar.Var GlobalTheory.ShFam.Pad
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie GlobalTheory.ShFam GlobalTheory.LieBase
open scoped ComplexOrder ContDiff

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HodgeSmooth

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ} {r : ℕ}

theorem unfFam_self (U : Formalism.L2.PjFree.Unf Xo c σ r) : unfFam U σ = U := by
  simp [unfFam]

theorem exists_unfWit_inj {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (h1 : 1 ≤ r) : ∃ W : UnfWit U, Function.Injective W.ik := by
  have hinj := fun (W : GlobalTheory.Dict.UW U) => GlobalTheory.Dict.UW.ik_injective hσ hU h1 W
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, hiso, hP⟩ := hU
  have h := hinj ⟨g, e, F, ik, φ, hiso, hP⟩
  have hP2 := hP
  choose Pm h1' h2' h3' h4' h5' using hP2
  exact ⟨⟨g, e, F, ik, φ, hiso, Pm, h1', h2', fun k x => ⟨h3' k x, h4' k x⟩, h5'⟩, h⟩

theorem hodgeFrame_comp {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ) {y : CxPts (genStr Z) σ}
    {g : EigFrame Z σ (y.1 ≫ genι Z)} (h : IsHodgeFrame (unfFam U) y g) :
    ∃ (k : (unfFam U σ).Comp) (x : ((unfFam U σ).X k).dom), IsOrth ((unfFam U σ).X k) x.1 ∧
      cxPt Z ((unfFam U σ).un k x) = y ∧ ∀ τ i, g.v τ i = (cxFrame Z ((unfFam U σ).un k x)).v τ i := by
  obtain ⟨ψ, σ', k, x, rfl | rfl, h2, h3, h4, h5, h6⟩ := h
  · obtain rfl : σ' = σ := h2
    refine ⟨k, x, h4, Subtype.ext (h5.trans ((congrArg (· ≫ y.1) (Spec.map_id _)).trans (Category.id_comp _))),
      fun τ i => by rw [h6 τ i, spMap_dualMap_id, Category.id_comp]⟩
  · exact (not_good_conj c (σ := σ) hσ (h2 ▸ h3)).elim

theorem exists_orth {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U)
    {y : CxPts (genStr Z) σ} (hy : ¬ LiesIn y (genBd Z)) :
    ∃ (k : U.Comp) (x : (U.X k).dom), IsOrth (U.X k) x.1 ∧ cxPt Z (U.un k x) = y := by
  have hr : Set.range y.1 ⊆ Set.range Z.jQ := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    exact not_not.1 hy
  have := Z.jQ_open
  let xF := IsOpenImmersion.lift Z.jQ y.1 hr
  have hxF : xF ≫ Z.jQ = y.1 := IsOpenImmersion.lift_fac _ _ _
  have hs : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F (CAt σ)) := by
    have h2 := y.2
    rw [← hxF, Category.assoc, Z.jQ_over] at h2
    exact h2
  have ho : (xF ≫ pullback.fst _ _) ≫ Xo.s = sOf c (CAt σ) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs]
    exact OpenReg.spMap_comp _ _
  have : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
  obtain ⟨z, hz⟩ : ∃ z : FrPt Xo c (CAt σ), z.x = xF ≫ pullback.fst _ _ := GlobalTheory.FlagTan.exists_frPt _ ho
  obtain ⟨k, f, t, hb⟩ := hU.2.2.1 z
  obtain ⟨x, hx, b, hb', e⟩ := ortho_holds r _ f.1 f.2
  obtain ⟨t', ht⟩ := (hU.2.2.2.1 k k ⟨x, KU.orth_dom _ hx⟩ f).2 ⟨1, one_mem _, b, hb', by rw [KU.lact_one, ← e]⟩
  refine ⟨k, ⟨x, KU.orth_dom _ hx⟩, hx, ?_⟩
  rw [cxPt_congr (ht.1.symm.trans hb.1.symm)]
  exact Subtype.ext (Eq.trans (congrArg (· ≫ Z.jQ)
    (pullback.hom_ext ((ptF_fst z).trans hz) ((ptF_snd z).trans hs.symm))) hxF)

theorem exists_lift_comb (q : FrPt Xo c (CAt σ)) {y : CxPts (genStr Z) σ} (hq : cxPt Z q = y)
    (g f : EigFrame Z σ (y.1 ≫ genι Z)) (hg : ∀ τ i, g.v τ i = (cxFrame Z q).v τ i) (τ : E →+* ℂ)
    (b : Fin (Dw.mult τ)) : ∃ w : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left,
      IsTanAtG Z.oF.t (GlobalTheory.AllWt.ptF (S := CAt σ) q) w ∧ w ≫ Z.m.φ = f.v τ b ∧
        IsCombAt q.x (q.u τ) (show Fin (Dw.mult τ) → CAt σ from fun j => g.co f τ j b) (w ≫ Z.m0.toSABMap.φ) := by
  subst hq
  have hco : g.co f τ = (cxFrame Z q).co f τ := by
    have h1 : g.co (cxFrame Z q) τ = 1 := by
      refine EigFrame.co_eq fun k => ?_
      rw [← hg τ k]
      convert isCombAtG_single _ _ (g.tan τ) k using 1
      funext a
      simp [Matrix.one_apply, Pi.single_apply]
    rw [← EigFrame.co_mul g (cxFrame Z q) f τ, h1, Matrix.one_mul]
  have hx : GlobalTheory.AllWt.ptF (S := CAt σ) q ≫ Z.jQ ≫ genι Z = (cxPt Z q).1 ≫ genι Z := (Category.assoc _ _ _).symm
  let L := lieEquiv (S := CAt σ) Z q hx
  refine ⟨(tv ((pushE Z.m (GlobalTheory.AllWt.ptF (S := CAt σ) q) hx).symm (f.vec τ b))).left, isTan_tv _, ?_, ?_⟩
  · have h2 := left_pushE Z.m (GlobalTheory.AllWt.ptF (S := CAt σ) q) hx
      ((pushE Z.m (GlobalTheory.AllWt.ptF (S := CAt σ) q) hx).symm (f.vec τ b))
    exact h2.symm.trans (congrArg (fun v => (tv v).left)
      (LinearEquiv.apply_symm_apply (pushE Z.m (GlobalTheory.AllWt.ptF (S := CAt σ) q) hx) (f.vec τ b)))
  · show IsCombAt q.x (q.u τ) _ (tv (L.symm (f.vec τ b))).left
    refine (isComb_iff (t := Xo.univ.t) (S := CAt σ) (fun i => tanOf (q.tan τ i)) _ (L.symm (f.vec τ b))).2
      (L.injective ?_)
    rw [hco]
    have e1 := (cxFrame Z q).vec_eq f τ b
    refine (LinearEquiv.apply_symm_apply L _).trans ?_
    rw [map_sum, e1]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (LinearEquiv.map_smul L _ _).symm

end GlobalTheory.HodgeSmooth

end SlopeTestRemainingChoices

section AuxExp

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.ArcQ
open scoped ContDiff

namespace GlobalTheory.ShFam.ExpCoord

open ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows (isDerivAt0_comp_hom isDerivAt0_unique)
open GlobalTheory.TrueCx.TorFrHolo (isDerivAt0_of_cart isHolTo_lift)
open GlobalTheory.ShFam.Hor.LogCh

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_expCoord_of_base : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (d g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (ch : AlgChart (genStr Z) σ d) (i : Fin Fu.n) (B : Set (ReciprocityTheory.L2DbarEstimates.V d)) (P : ReciprocityTheory.L2DbarEstimates.V d → ((Fu.Di i).La →+ (Fin g → ℂ))), IsOpen B → B ⊆ ch.e.target → (∀ b ∈ B, IsPeriod (Fu.Di i) ty (P b)) → (∀ v, DifferentiableOn ℂ (fun b => P b v) B) → (∀ b ∈ B, ∀ y : FrPt Xo c (CAt σ), ch.e.symm b = cxPt Z y → Fu.u i (P b) = y.x) → ∀ (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (F : EigFrame Z φ (LogKS.chart V ≫ genι Z)), LogKS.chart V ≫ genStr Z = spMap φ → ∃ z : ReciprocityTheory.L2DbarEstimates.V d → ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin g → ℂ), (∀ τ k, DifferentiableOn ℂ (fun b => z b τ k) {b ∈ B | ch.e.symm b ∈ ptsIn (genStr Z) σ V.1 ∧ ¬ LiesIn (ch.e.symm b) (genBd Z)}) ∧ ∀ b ∈ B, ∀ (hy : ch.e.symm b ∈ ptsIn (genStr Z) σ V.1) (f : EigFrame Z σ ((ch.e.symm b).1 ≫ genι Z)), F.IsMap (evHom hy) f → ∀ q : FrPt Xo c (CAt σ), cxPt Z q = ch.e.symm b → ∀ τ k (w : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left), IsTanAtG Z.oF.t (GlobalTheory.AllWt.ptF (S := CAt σ) q) w → w ≫ Z.m.φ = f.v τ k → IsDerivAt0 (fun v => (Fu.ex i (P b) v).left) (z b τ k) (w ≫ Z.m0.toSABMap.φ) := by
  classical
  intro E _ _ _ H Dw l Xo c O _ β Z σ d g ty Fu ch i B P hB hBt hPer hPd hPu V φ F hstr
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
  refine ⟨fun b τ k => W ⟨τ, k⟩ (L b), fun τ k => ?_, fun b hb hy f hf q hq τ k w hwt hw2 => ?_⟩
  · exact (hW ⟨τ, k⟩).comp L.differentiableOn fun b hb =>
      ⟨by simpa [hB₁] using hb.1, hRV b hb⟩
  · have hd := hWd ⟨τ, k⟩ (L b) (by simpa [hB₁] using hb) (ch.e.symm b) hy (by rw [hpq b hb q hq, ← hq]; rfl)
    have hfv : spMap (dualMap (evHom hy)) ≫ F.v τ k = w ≫ Z.m.φ := by rw [hw2, hf τ k]
    rw [hfv] at hd
    have hbase : w ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ p (L b) := by
      rw [hpq b hb q hq]
      exact hwt.1
    have h := isDerivAt0_ex_of_push Z Fu (p (L b)) i (P₂ (L b)) (hP₂ _) (hu _) hbase hd
    rw [hP₂L b hb] at h
    exact h

end GlobalTheory.ShFam.ExpCoord

end AuxExp

section AuxRiem

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ProjVar.Var GlobalTheory.ShFam.Pad
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie GlobalTheory.ShFam
open scoped ComplexOrder

namespace GlobalTheory.HodgeSmooth

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem exists_diag_riem {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (W : UnfWit U) :
    ∃ d : U.Comp → (E →+* ℂ) → ℂ, (∀ k τ, d k τ ≠ 0) ∧
      ∀ (k : U.Comp) (x : (U.X k).dom), IsOrth (U.X k) x.1 →
      ∀ (i : Fin W.F.n) (P : (W.F.Di i).La →+ (Fin W.g → ℂ)),
        IsPeriod (W.F.Di i) (fun j => Formalism.L2.PjFree.relab c σ (W.e j).1) P →
      ∀ (Hm : Matrix (Fin W.g) (Fin W.g) ℂ), (∀ v w, (hermForm Hm (P v) (P w)).im = (W.F.Di i).EF v w) →
        W.F.u i P = (U.un k x).x →
      ∀ (τ : E →+* ℂ) (zz : Fin (Dw.mult τ) → (Fin W.g → ℂ))
        (uu : Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left))
        (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ),
        (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz b) (uu b)) →
        (∀ b, IsCombAt (U.un k x).x ((U.un k x).u τ) (show Fin (Dw.mult τ) → CAt σ from fun b' => T b' b) (uu b)) →
        (of fun b b' => hermForm Hm (zz b') (zz b)) = d k τ • (Tᴴ * T) := by
  classical
  let ρ : U.Comp → (E →+* ℂ) → (E →+* ℂ) := fun k τ =>
    if Formalism.L2.PjFree.relab c σ τ ∈ (U.X k).Ψ then Formalism.L2.PjFree.relab c σ τ
    else ComplexEmbedding.conjugate (Formalism.L2.PjFree.relab c σ τ)
  refine ⟨fun k τ => ((2 * ((ρ k τ) (-(U.X k).ξ0)).im : ℝ) : ℂ), fun k τ h => ?_, ?_⟩
  · have h1 : ((ρ k τ) (-(U.X k).ξ0)).im = 0 := by
      have h' : (((2 * ((ρ k τ) (-(U.X k).ξ0)).im : ℝ) : ℂ)) = 0 := h
      have : 2 * ((ρ k τ) (-(U.X k).ξ0)).im = 0 := by exact_mod_cast h'
      linarith
    have h2 : (ρ k τ) (-(U.X k).ξ0) = 0 := Complex.ext (re_xi (U.X k) _) h1
    exact (U.X k).ξ0_ne (neg_eq_zero.1 ((map_eq_zero _).1 h2))
  intro k x hx i P hP Hm hH hPu τ zz uu T hder hT
  obtain ⟨hp0, hty⟩ := hU.2.1 k
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨f, hf⟩ := FrameUnif.exists_letter_equiv (U.X k).Ψ (U.X k).cmType Dw.p Dw.q r hU.1
    (Formalism.L2.PjFree.relab c σ) hbij Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  rw [← hp0] at hf
  have hper (v) : W.Pm k x v = perVec (U.X k) (W.e.trans f) x.1 (W.φ k v : Fin r → E) := funext fun j => by
    rw [W.Pm_eq, perVec, Equiv.trans_apply]
    have h := hf (W.e j)
    generalize f (W.e j) = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    dsimp only at h ⊢
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega), Formalism.L2.PjFree.perFr, dif_pos a, dif_pos hn]
    · rw [if_pos (by omega), Formalism.L2.PjFree.perFr, dif_neg a,
        dif_pos (show conjEmb (Formalism.L2.PjFree.relab c σ (W.e j).1) ∈ (U.X k).Ψ from hτ), dif_pos hn]
      rfl
  set D := diagXi (U.X k) (W.e.trans f) with hDdef
  have hD : ∀ j : Fin (Dw.mult τ), D (W.e.symm ⟨τ, j⟩) = ((2 * ((ρ k τ) (-(U.X k).ξ0)).im : ℝ) : ℂ) := by
    intro j
    rw [hDdef, diagXi, Equiv.trans_apply, Equiv.apply_symm_apply]
    rcases hf ⟨τ, j⟩ with ⟨a, h1, -⟩ | ⟨a, h1, -, -⟩
    · rw [h1]
      simp only [ρ, if_pos a]
    · rw [h1]
      simp only [ρ, if_neg a]
  have him : ∀ v w, (hermForm (diagonal D) (W.Pm k x v) (W.Pm k x w)).im = (W.F.Di (W.ik k)).EF v w := by
    intro v w
    rw [hper, hper, im_diag_ortho _ _ _ hx, ← W.iso]
    simp
  have p := W.period k x
  obtain ⟨hPx, hv⟩ := W.lie k x
  obtain ⟨h, gam, hex, hh, hiso, -⟩ := familyUnif_exp_unique E H Dw l Xo _ _ _ W.F i (W.ik k) P _ hP p
    (by rw [← hPx]; exact hPu)
  set A := LinearMap.toMatrix' h.toLinearMap with hA
  have hAv : ∀ z, A *ᵥ z = h z := fun z => by rw [hA, LinearMap.toMatrix'_mulVec]; rfl
  have hcol (b) : A *ᵥ zz b = ∑ j, T j b • (Pi.single (W.e.symm ⟨τ, j⟩) 1 : Fin W.g → ℂ) := by
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ _ _ W.F _ _ p _ ((U.un k x).u τ) _ (hv τ) _
      (uu b)).1 (hPx ▸ hT b)
    have d2 := (ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ _ _ W.F _ P hP _ _ h.toLinearMap p hex _ _).1 (hder b)
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ _ _ W.F _ _ p
    rw [hAv]
    exact (tn.2.2 _ (tn.1 _ _ d2)).unique d2 d1
  have key := UnitDet.eq_of_im_hermForm_eq _ hP.2.2.2.1
    (Aᵀ * (diagonal D * A.map (starRingEnd ℂ))) Hm (by
      rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
      rw [← UnitDet.hermForm_mulVec, hAv, hAv, ← hh, ← hh, him, hiso, hH])
  have hsupp : ∀ b, diagonal D *ᵥ star (∑ j, T j b • (Pi.single (W.e.symm ⟨τ, j⟩) 1 : Fin W.g → ℂ)) =
      (((2 * ((ρ k τ) (-(U.X k).ξ0)).im : ℝ) : ℂ) • (1 : Matrix (Fin W.g) (Fin W.g) ℂ)) *ᵥ
        star (∑ j, T j b • (Pi.single (W.e.symm ⟨τ, j⟩) 1 : Fin W.g → ℂ)) := by
    intro b
    simp only [smul_mulVec, Matrix.one_mulVec]
    funext p'
    rw [mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    by_cases hp : ∃ j, W.e.symm ⟨τ, j⟩ = p'
    · obtain ⟨j, rfl⟩ := hp
      rw [hD j]
    · push_neg at hp
      have : (∑ j, T j b • (Pi.single (W.e.symm ⟨τ, j⟩) 1 : Fin W.g → ℂ)) p' = 0 := by
        rw [Finset.sum_apply]
        exact Finset.sum_eq_zero fun j _ => by rw [Pi.smul_apply, Pi.single_eq_of_ne (hp j).symm, smul_zero]
      simp [Pi.star_apply, this]
  ext b b'
  rw [of_apply, ← key, ← UnitDet.hermForm_mulVec, hcol, hcol, hermForm, hsupp, ← hermForm]
  beta_reduce
  generalize (((2 * ((ρ k τ) (-(U.X k).ξ0)).im : ℝ) : ℂ)) = dd
  clear hsupp key hcol hAv hiso hh hex hper him hD hf hT hder hH hPu
  have hi : ∀ j j' : Fin (Dw.mult τ), W.e.symm ⟨τ, j⟩ = W.e.symm ⟨τ, j'⟩ ↔ j = j' := fun j j' => by simp
  simp [hermForm, smul_mulVec, sum_dotProduct, dotProduct_sum, star_sum, Pi.single_apply, hi, mul_apply, mul_comm]

end GlobalTheory.HodgeSmooth

end AuxRiem

section AuxLocal

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LieBase
open GlobalTheory.ArcQ
open scoped ContDiff

namespace GlobalTheory.HodgeSmooth

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  [SmoothOfRelativeDimension Dw.dim (genStr Z)] {σ : c.F →+* ℂ}

theorem gram_smooth_near {U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1))
    (F : EigFrame Z φ (LogKS.chart V ≫ genι Z)) (τ : E →+* ℂ) (a b : Fin (Dw.mult τ))
    (hstr : LogKS.chart V ≫ genStr Z = spMap φ) (y₀ : CxPts (genStr Z) σ) (hbd : ¬ LiesIn y₀ (genBd Z))
    (hV : y₀ ∈ ptsIn (genStr Z) σ V.1) :
    ∃ (T : Set (CxPts (genStr Z) σ)) (g : CxPts (genStr Z) σ → ℂ), IsOpen T ∧ y₀ ∈ T ∧
      (manifold Z σ).SmoothOn T (fun y => (g y).re) ∧ (manifold Z σ).SmoothOn T (fun y => (g y).im) ∧
      ∀ y ∈ T, ∀ (hy : y ∈ ptsIn (genStr Z) σ V.1) (f : EigFrame Z σ (y.1 ≫ genι Z)), F.IsMap (evHom hy) f →
        (hodgeMet Z U).gram y f τ a b = g y := by
  classical
  set U' := unfFam U σ with hU'def
  have hU' : Formalism.L2.PjFree.IsUnf U' := by rw [hU'def, unfFam_self]; exact hU
  have h1 : 1 ≤ Dw.p + Dw.q := by
    have := a.2
    unfold Datum.mult at this
    split_ifs at this <;> omega
  obtain ⟨W, hinj⟩ := exists_unfWit_inj hσ hU' h1
  obtain ⟨d, hd0, hd⟩ := exists_diag_riem hσ hU' W
  obtain ⟨k₀, x₀, -, hq₀⟩ := exists_orth (Z := Z) hσ hU' hbd
  obtain ⟨ch, hch⟩ := AlgChart.exists_mem_source (p := genStr Z) (σ := σ) (D := Dw.dim) y₀
  obtain ⟨i, B, P, hB, hb₀, hBt, hPer, hPhol, hPu⟩ :=
    GlobalTheory.ShFam.chart_lift_periods _ _ _ _ _ _ _ _ Z σ Dw.dim W.g _ W.F ch (U'.un k₀ x₀) (hq₀ ▸ hch)
  rw [hq₀] at hb₀
  obtain ⟨Hm, hHm, hHs⟩ := GlobalTheory.RiemSmooth.exists_riem_contDiffOn _ _ _ _ _ _ σ W.g _ W.F i Dw.dim B P hB hPer hPhol
  obtain ⟨z, hz, hzl⟩ := GlobalTheory.ShFam.ExpCoord.exists_expCoord_of_base _ _ _ _ _ _ _ _ Z σ Dw.dim W.g _ W.F ch i B P hB
    hBt hPer hPhol hPu V φ F hstr
  have hik : ∀ c0 ∈ B, ∀ k (x : (U'.X k).dom), cxPt Z (U'.un k x) = ch.e.symm c0 → W.ik k = i :=
    fun c0 hc0 k x hkx => W.F.disj _ _ _ _ (W.period k x) (hPer c0 hc0)
      ((W.lie k x).1.symm.trans (hPu c0 hc0 _ hkx.symm).symm)
  have hk₀ : W.ik k₀ = i := hik _ hb₀ k₀ x₀ (by rw [ch.e.left_inv hch]; exact hq₀)
  set B' : Set (ReciprocityTheory.L2DbarEstimates.V Dw.dim) := {c ∈ B | ch.e.symm c ∈ ptsIn (genStr Z) σ V.1 ∧
    ¬ LiesIn (ch.e.symm c) (genBd Z)} with hB'
  have hB'o : IsOpen B' := by
    have h1 := ch.e.continuousOn_symm.isOpen_inter_preimage ch.e.open_target
      ((isOpen_ptsIn (p := genStr Z) (σ := σ) V.1).inter (isOpen_not_liesIn (p := genStr Z) (σ := σ) (genBd Z)))
    have e : B' = B ∩ (ch.e.target ∩ ch.e.symm ⁻¹' (ptsIn (genStr Z) σ V.1 ∩ {y | ¬ LiesIn y (genBd Z)})) := by
      ext c
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, hBt h1, h2, h3⟩
      · rintro ⟨h1, -, h2, h3⟩
        exact ⟨h1, h2, h3⟩
    rw [e]
    exact hB.inter h1
  have hz' : ∀ τ k p, ContDiffOn ℝ ∞ (fun c => z c τ k p) B' := fun τ k p =>
    GlobalTheory.ChartGlue.contDiffOn_real hB'o ((differentiableOn_pi.1 (hz τ k)) p)
  let G : ReciprocityTheory.L2DbarEstimates.V Dw.dim → ℂ := fun c =>
    ((2 * Real.pi : ℝ) : ℂ) / d k₀ τ * hermForm (Hm c) (z c τ b) (z c τ a)
  have hG : ContDiffOn ℝ ∞ G B' := by
    have hc : ∀ p, ContDiffOn ℝ ∞ (fun c => star (z c τ a p)) B' := fun p =>
      Complex.conjCLE.contDiff.comp_contDiffOn (hz' τ a p)
    have e : G = fun c => ((2 * Real.pi : ℝ) : ℂ) / d k₀ τ * ∑ p, z c τ b p * ∑ q, Hm c p q * star (z c τ a q) := by
      funext c
      simp only [G, hermForm, dotProduct, Matrix.mulVec, Pi.star_apply]
    rw [e]
    exact contDiffOn_const.mul (ContDiffOn.sum fun p _ => (hz' τ b p).mul
      (ContDiffOn.sum fun q _ => ((hHs p q).mono fun c hc => hc.1).mul (hc q)))
  refine ⟨ch.e.source ∩ ch.e ⁻¹' B', fun y => G (ch.e y), ch.e.isOpen_inter_preimage hB'o,
    ⟨hch, hb₀, by rw [ch.e.left_inv hch]; exact hV, by rw [ch.e.left_inv hch]; exact hbd⟩, ?_, ?_, ?_⟩
  · intro c'
    have ht : ContDiffOn ℝ ∞ (ch.e ∘ c'.e.symm) (c'.e.target ∩ c'.e.symm ⁻¹' ch.e.source) :=
      (contDiffOn_piLp 2).2 fun a => GlobalTheory.ChartGlue.contDiffOn_real (GlobalTheory.ChartGlue.isOpen_over c'.e ch.e.open_source)
        (differentiableOn_euclidean.1 (AlgChart.holo_trans c' ch) a)
    exact (Complex.reCLM.contDiff.comp_contDiffOn hG).comp (ht.mono fun v hv => ⟨hv.1, hv.2.1⟩) fun v hv => hv.2.2
  · intro c'
    have ht : ContDiffOn ℝ ∞ (ch.e ∘ c'.e.symm) (c'.e.target ∩ c'.e.symm ⁻¹' ch.e.source) :=
      (contDiffOn_piLp 2).2 fun a => GlobalTheory.ChartGlue.contDiffOn_real (GlobalTheory.ChartGlue.isOpen_over c'.e ch.e.open_source)
        (differentiableOn_euclidean.1 (AlgChart.holo_trans c' ch) a)
    exact (Complex.imCLM.contDiff.comp_contDiffOn hG).comp (ht.mono fun v hv => ⟨hv.1, hv.2.1⟩) fun v hv => hv.2.2
  · rintro y ⟨hys, hyB⟩ hy f hf
    show _ = G (ch.e y)
    obtain ⟨c0, hc0, rfl⟩ : ∃ c0 ∈ B', ch.e.symm c0 = y := ⟨ch.e y, hyB, ch.e.left_inv hys⟩
    rw [ch.e.right_inv (hBt hc0.1)]
    have hex : ∃ g, IsHodgeFrame (unfFam U) (ch.e.symm c0) g := by
      obtain ⟨k, x, hx, hkx⟩ := exists_orth (Z := Z) hσ hU' hc0.2.2
      rw [← hkx]
      exact ⟨_, isHodgeFrame_cxFrame (U := unfFam U) hσ hx⟩
    have hg : (hodgeMet Z U).gram (ch.e.symm c0) f τ =
        ((2 * Real.pi : ℝ) : ℂ) • ((hex.choose.co f τ)ᴴ * hex.choose.co f τ) := dif_pos hex
    obtain ⟨k, x, hx, hkx, hv⟩ := hodgeFrame_comp hσ hex.choose_spec
    have hk : k = k₀ := hinj ((hik c0 hc0.1 k x hkx).trans hk₀.symm)
    subst hk
    choose w hwt hwm hwc using fun bb => exists_lift_comb (U'.un k x) hkx hex.choose f hv τ bb
    have hder : ∀ bb, IsDerivAt0 (fun v => (W.F.ex i (P c0) v).left) (z c0 τ bb) (w bb ≫ Z.m0.toSABMap.φ) :=
      fun bb => hzl c0 hc0.1 hy f hf (U'.un k x) hkx τ bb (w bb) (hwt bb) (hwm bb)
    have hmat := hd k x hx i (P c0) (hPer c0 hc0.1) (Hm c0) (hHm c0 hc0.1).2.2 (hPu c0 hc0.1 _ hkx.symm) τ
      (z c0 τ) (fun bb => w bb ≫ Z.m0.toSABMap.φ) (hex.choose.co f τ) hder hwc
    have e := congrFun (congrFun hmat a) b
    simp only [of_apply, Matrix.smul_apply, smul_eq_mul] at e
    rw [hg, Matrix.smul_apply, smul_eq_mul]
    show _ = ((2 * Real.pi : ℝ) : ℂ) / d k τ * hermForm (Hm c0) (z c0 τ b) (z c0 τ a)
    rw [e]
    field_simp [hd0 k τ]

end GlobalTheory.HodgeSmooth

end AuxLocal

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase GlobalTheory.CxPts GlobalTheory.Cartier

theorem GlobalTheory.LieBase.hodgeMet_smoothOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) [SmoothOfRelativeDimension Dw.dim (genStr Z)] (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (hodgeMet Z U).SmoothOn (manifold Z σ) {y | ¬ LiesIn y (genBd Z)} := by
  intro E _ _ _ H Dw l Xo c O _ β Z _ σ U hσ hU
  exact GlobalTheory.ShFam.EigMet.smoothOn_of_locally (hodgeMet Z U) _ fun V φ F τ a b hV y₀ hy₀ hV₀ =>
    GlobalTheory.HodgeSmooth.gram_smooth_near hσ hU V φ F τ a b hV y₀ hy₀ hV₀
