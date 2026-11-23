import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtOfEigFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentialDerivativeAtZeroIsTangent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtIffIsDerivAt0
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0CompLinear
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsEigAtIffOfIsDerivAt0
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniformizationPeriodLatticeChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsInvariantNatLengthLattice

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor.TwoMarkings

open GlobalTheory.ShFam.OpenReg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ} {g : ℕ} {e : Fin g ≃ Letter Dw} {Fu : Fam Xo c σ e} {a : CxFr Z σ}

theorem linearIndependent_dirs {i : Fin Fu.n} {P : (Fu.Di i).La →+ (Fin g → ℂ)} {W : Letter Dw → Fin g → ℂ}
    {y : Sp ℂ ⟶ Xo.XF c} (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P)
    (hy : y ≫ pullback.fst _ _ = Fu.u i P) (hj : y ≫ Z.jQ = a.1.1)
    {v₀ : Letter Dw → (Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left)}
    (h1 : ∀ z, v₀ z ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y)
    (h2 : ∀ z, v₀ z ≫ Z.m.φ = a.2.v z.1 z.2)
    (h3 : ∀ z, IsDerivAt0 (fun w => (Fu.ex i P w).left) (W z) (v₀ z ≫ Z.m0.toSABMap.φ)) :
    LinearIndependent ℂ W := by
  have hx : y ≫ Z.jQ ≫ pullback.fst _ _ = a.1.1 ≫ genι Z := by rw [← Category.assoc, hj]
  have hty : ∀ z j, W z j ≠ 0 → (e j).1 = z.1 := fun z =>
    (GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e Fu i P hP _ _ z.1 (h3 z)).1 fun b =>
      (eig_iff Z.m0.toSABMap (h1 z) b _).2 ((eig_iff Z.m (h1 z) b _).1 (h2 z ▸ a.2.eig z.1 z.2 b))
  obtain ⟨t1, t2, -⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P hP
  obtain ⟨v, hv, -⟩ := t2 0
  obtain ⟨v', k1, rfl⟩ := exists_lift Z.m0.toSABMap (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) v
    (by rw [(t1 _ _ hv).1, ← hy, Category.assoc])
  rw [Fintype.linearIndependent_iff]
  rintro cf hc ⟨τ, k⟩
  have hb := a.2.basis τ (v' ≫ Z.m.φ) ((tan_iff Z.m hx k1).2 ((tan_iff Z.m0.toSABMap hy k1).1 (t1 _ _ hv)))
    fun b => (eig_iff Z.m k1 b _).2 ((eig_iff Z.m0.toSABMap k1 b _).1
      ((GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e Fu i P hP _ _ τ hv).2 (fun j hj => absurd rfl hj) b))
  have e1 : a.2.v τ = fun k => v₀ ⟨τ, k⟩ ≫ Z.m.φ := funext fun k => (h2 ⟨τ, k⟩).symm
  rw [e1] at hb
  have hcomb : ∀ d : Fin (Dw.mult τ) → ℂ, ∑ k, d k • W ⟨τ, k⟩ = 0 →
      IsCombAtG Z.t (a.1.1 ≫ genι Z) (fun k => v₀ ⟨τ, k⟩ ≫ Z.m.φ) d (v' ≫ Z.m.φ) := fun d hd =>
    (comb_iff Z.m hx (fun k => h1 ⟨τ, k⟩) d k1).2 ((comb_iff Z.m0.toSABMap hy (fun k => h1 ⟨τ, k⟩) d k1).1
      ((GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ Fu i P hP _ _ _ (fun k => h3 ⟨τ, k⟩) d _).2 (hd ▸ hv)))
  have hτ : ∑ k, cf ⟨τ, k⟩ • W ⟨τ, k⟩ = 0 := by
    funext j
    have hz : ∀ ρ, (e j).1 ≠ ρ → (∑ k, cf ⟨ρ, k⟩ • W ⟨ρ, k⟩) j = 0 := fun ρ hρ => by
      rw [Finset.sum_apply]
      exact Finset.sum_eq_zero fun k _ => by
        rw [Pi.smul_apply, by_contra fun h => hρ (hty ⟨ρ, k⟩ j h), smul_zero]
    by_cases h : (e j).1 = τ
    · have := congrFun hc j
      rw [Fintype.sum_sigma, Finset.sum_apply, Finset.sum_eq_single τ (fun ρ _ hρ => hz ρ (h ▸ hρ.symm)) (by simp)] at this
      exact this
    · exact hz τ h
  exact congrFun (hb.unique (hcomb _ hτ) (hcomb 0 (by simp))) k

theorem per_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (a : CxFr Z σ), (∀ i j Q Q', Per Fu a i Q → Per Fu a j Q' → i = j) ∧ ∀ i Q Q', Per Fu a i Q → Per Fu a i Q' → ∃ gm : (Fu.Di i).La ≃ₗ[𝓞 E] (Fu.Di i).La, IsIsom (Fu.Di i) gm ∧ IsLev l (Fu.Di i) gm ∧ ∀ v, Q' (gm v) = Q v := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ g e Fu a
  haveI := Z.jQ_open
  refine ⟨?_, ?_⟩
  · rintro i j Q Q' ⟨P, W, y, hP, hy, hj, -⟩ ⟨P', W', y', hP', hy', hj', -⟩
    obtain rfl : y = y' := (cancel_mono Z.jQ).1 (hj.trans hj'.symm)
    exact Fu.disj i j P P' hP hP' (hy.symm.trans hy')
  · rintro i Q Q' ⟨P, W, y, hP, hy, hj, hv, hQ⟩ ⟨P', W', y', hP', hy', hj', hv', hQ'⟩
    obtain rfl : y = y' := (cancel_mono Z.jQ).1 (hj.trans hj'.symm)
    choose v₀ h1 h2 h3 using hv
    choose v₁ k1 k2 k3 using hv'
    obtain rfl : v₀ = v₁ := funext fun z =>
      Z.m.cart.1.hom_ext ((h2 z).trans (k2 z).symm) ((h1 z).trans (k1 z).symm)
    obtain ⟨gam, h, g1, g2, g3, g4⟩ := (Fu.fibre i P P' hP hP').1 (hy.symm.trans hy')
    have hm : ∀ z, (LinearMap.toMatrix' h.toLinearMap).mulVec z = h z := fun z =>
      LinearMap.toMatrix'_mulVec _ z
    obtain ⟨-, -, h5⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ g _ Fu i P P' gam
      (LinearMap.toMatrix' h.toLinearMap) hP hP' g1 g2 g3 (fun a => by rw [hm, g4])
    simp only [hm] at h5
    obtain ⟨t1, -, t3⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P' hP'
    have hW : ∀ z, h (W z) = W' z := fun z => (t3 _ (t1 _ _ (k3 z))).unique
      ((GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ g _ Fu i P hP i P' h.toLinearMap hP' h5 _ _).1 (h3 z)) (k3 z)
    refine ⟨gam, g1, g2, fun v => funext fun z => ?_⟩
    refine Fintype.linearIndependent_iffₛ.1 (linearIndependent_dirs hP' hy' hj' k1 k2 k3) _ _ ?_ z
    rw [← hQ', g4, hQ, map_sum]
    simp only [map_smul, hW]

end GlobalTheory.ShFam.Hor.TwoMarkings
