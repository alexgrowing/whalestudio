import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtOfEigFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentialDerivativeAtZeroIsTangent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtIffIsDerivAt0
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsEigAtIffOfIsDerivAt0

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor

open GlobalTheory.ShFam.OpenReg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ} {g : ℕ} {e : Fin g ≃ Letter Dw} {Fu : Fam Xo c σ e} {a : CxFr Z σ} {i : Fin Fu.n}
  {P : (Fu.Di i).La →+ (Fin g → ℂ)} {W : Letter Dw → Fin g → ℂ} {y : Sp ℂ ⟶ Xo.XF c}

section Directions

variable (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P)
  (hu : y ≫ pullback.fst _ _ = Fu.u i P) (hy : y ≫ Z.jQ = a.1.1)
  (hW : ∀ z : Letter Dw, ∃ v₀ : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left,
      v₀ ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y ∧ v₀ ≫ Z.m.φ = a.2.v z.1 z.2 ∧
      IsDerivAt0 (fun w => (Fu.ex i P w).left) (W z) (v₀ ≫ Z.m0.toSABMap.φ))

include hP hu hy hW in

theorem dirs_exists_comb (τ : E →+* ℂ) (w : Fin g → ℂ) (hw : ∀ j, w j ≠ 0 → (e j).1 = τ) :
    ∃ cf : Fin (Dw.mult τ) → ℂ, w = ∑ k, cf k • W ⟨τ, k⟩ := by
  choose v₀ h1 h2 h3 using hW
  have hx : y ≫ Z.jQ ≫ pullback.fst _ _ = a.1.1 ≫ genι Z := by rw [← Category.assoc, hy]
  obtain ⟨t1, t2, t3⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P hP
  obtain ⟨v, hv, -⟩ := t2 w
  have ht := t1 w v hv
  have he := (GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e Fu i P hP w v τ hv).2 hw
  obtain ⟨v', k1, rfl⟩ := exists_lift Z.m0.toSABMap (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) v
    (by rw [ht.1, ← hu, Category.assoc])
  obtain ⟨cf, hcf, -⟩ := a.2.basis τ (v' ≫ Z.m.φ) ((tan_iff Z.m hx k1).2 ((tan_iff Z.m0.toSABMap hu k1).1 ht))
    fun b => (eig_iff Z.m k1 b _).2 ((eig_iff Z.m0.toSABMap k1 b _).1 (he b))
  have e1 : a.2.v τ = fun k => v₀ ⟨τ, k⟩ ≫ Z.m.φ := funext fun k => (h2 ⟨τ, k⟩).symm
  rw [e1] at hcf
  have hc := (comb_iff Z.m0.toSABMap hu (fun k => h1 ⟨τ, k⟩) cf k1).2 ((comb_iff Z.m hx (fun k => h1 ⟨τ, k⟩) cf k1).1 hcf)
  exact ⟨cf, (t3 _ ht).unique hv ((GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ Fu i P hP _ _
    (fun k => W ⟨τ, k⟩) (fun k => h3 ⟨τ, k⟩) cf _).1 hc)⟩

include hP hu hy hW in

theorem dirs_span : ⊤ ≤ Submodule.span ℂ (Set.range W) := by
  rw [← (Pi.basisFun ℂ (Fin g)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  obtain ⟨cf, h⟩ := dirs_exists_comb hP hu hy hW (e j).1 (Pi.basisFun ℂ (Fin g) j) fun k hk => by
    by_contra hne
    exact hk (by rw [Pi.basisFun_apply]; exact Pi.single_eq_of_ne (fun h => hne (by rw [h])) _)
  rw [h]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

include hP hu hy hW in

theorem dirs_basis : ∃ b : Module.Basis (Letter Dw) ℂ (Fin g → ℂ), ⇑b = W :=
  ⟨basisOfTopLeSpanOfCardEqFinrank W (dirs_span hP hu hy hW) (by
    rw [Module.finrank_fin_fun, ← Fintype.card_congr e, Fintype.card_fin]), coe_basisOfTopLeSpanOfCardEqFinrank _ _ _⟩

end Directions

theorem Inner.exists_lift {x : CxPts (genStr Z) σ} (h : Inner x) : ∃ y : Sp ℂ ⟶ Xo.XF c, y ≫ Z.jQ = x.1 := by
  have := Z.jQ_open
  have hr : Set.range x.1 ⊆ Set.range Z.jQ := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    exact not_not.1 h
  exact ⟨IsOpenImmersion.lift Z.jQ _ hr, IsOpenImmersion.lift_fac _ _ _⟩

theorem exists_dirs (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P)
    (hu : y ≫ pullback.fst _ _ = Fu.u i P) (hy : y ≫ Z.jQ = a.1.1) :
    ∃ W : Letter Dw → Fin g → ℂ, ∀ z : Letter Dw, ∃ v₀ : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left,
      v₀ ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y ∧ v₀ ≫ Z.m.φ = a.2.v z.1 z.2 ∧
      IsDerivAt0 (fun w => (Fu.ex i P w).left) (W z) (v₀ ≫ Z.m0.toSABMap.φ) := by
  have hx : y ≫ Z.jQ ≫ pullback.fst _ _ = a.1.1 ≫ genι Z := by rw [← Category.assoc, hy]
  choose v₀ h1 h2 using fun z : Letter Dw => exists_lift Z.m (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) (a.2.v z.1 z.2)
    (by rw [(a.2.tan z.1 z.2).1, ← hx, Category.assoc])
  choose W hW using fun z : Letter Dw => ((GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P hP).2.2 _
    ((tan_iff Z.m0.toSABMap hu (h1 z)).2 ((tan_iff Z.m hx (h1 z)).1 (h2 z ▸ a.2.tan z.1 z.2)))).exists
  exact ⟨W, fun z => ⟨v₀ z, h1 z, h2 z, hW z⟩⟩

theorem exists_per_of_isPeriod (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P)
    (hu : y ≫ pullback.fst _ _ = Fu.u i P) (hy : y ≫ Z.jQ = a.1.1) : ∃ Q, Per Fu a i Q := by
  obtain ⟨W, hW⟩ := exists_dirs hP hu hy
  obtain ⟨b, rfl⟩ := dirs_basis hP hu hy hW
  exact ⟨b.equivFun.toLinearMap.toAddMonoidHom.comp P, P, b, y, hP, hu, hy, hW, fun v => (b.sum_equivFun (P v)).symm⟩

theorem exists_per : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (a : CxFr Z σ), Inner a.1 → ∃ i Q, Per Fu a i Q := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ g e Fu a ha
  obtain ⟨y, hy⟩ := ha.exists_lift
  have hs : y ≫ pullback.snd _ _ = spMap σ := by
    rw [← Z.jQ_over, ← Category.assoc, hy]
    exact a.1.2
  obtain ⟨i, P, hP, hu⟩ := Fu.onto (y ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, OpenReg.spMap_comp])
  exact ⟨i, exists_per_of_isPeriod hP hu.symm hy⟩

end GlobalTheory.ShFam.Hor
