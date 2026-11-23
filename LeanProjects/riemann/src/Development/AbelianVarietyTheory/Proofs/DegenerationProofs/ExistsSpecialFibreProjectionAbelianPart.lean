import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsionImports
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowEqTorus
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ProdSurjectiveGeometricPoints

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SpecialPoints

theorem exists_torsion_lift {T M N : Type} [CommGroup T] [CommGroup M] [Group N] (i : T →* M) (q : M →* N) (n : ℕ)
    (hqi : ∀ t, q (i t) = 1) (hker : ∀ x, q x = 1 → ∃ t, i t = x) (hq : Function.Surjective q)
    (hT : ∀ t : T, ∃ s : T, s ^ n = t) (b : N) (hb : b ^ n = 1) : ∃ x, x ^ n = 1 ∧ q x = b := by
  obtain ⟨x, rfl⟩ := hq b
  obtain ⟨t, ht⟩ := hker (x ^ n) (by rw [map_pow, hb])
  obtain ⟨s, rfl⟩ := hT t
  refine ⟨x * (i s)⁻¹, ?_, ?_⟩
  · rw [mul_pow, inv_pow, ← map_pow, ht, mul_inv_cancel]
  · rw [map_mul, map_inv, hqi, inv_one, _root_.mul_one]

theorem exists_projection :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegPre V) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (g : GtCoord (IsLocalRing.maximalIdeal V) D 0 G) (κ : Type) [Field κ] [IsAlgClosed κ] (f : V →+* κ), IsLocalHom f → ∃ π : (Over.mk (spMap f) ⟶ G) →* (Over.mk (spMap f) ⟶ D.P.A), (∀ x, ∃ y : Sp κ ⟶ (thickObj V (IsLocalRing.maximalIdeal V) 0 G).left, y ≫ (fstG (IsLocalRing.maximalIdeal V) 0 G).left = x.left ∧ y ≫ g.pG.left = (π x).left) ∧ ∀ n : ℕ, 1 ≤ n → ∀ b, b ^ n = 1 → ∃ x, x ^ n = 1 ∧ π x = b := by
  intro V _ _ _ D G _ _ _ c K _ _ f hf
  obtain ⟨r₀, hr₀⟩ : ∃ r₀ : Sp K ⟶ Sp (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)),
      r₀ ≫ thick V (IsLocalRing.maximalIdeal V) 0 = spMap f := by
    have h₂ : ∀ a ∈ IsLocalRing.maximalIdeal V ^ (0 + 1), f a = 0 := fun a ha => by
      rw [zero_add, pow_one] at ha
      by_contra h
      exact ha (hf.map_nonunit a (Ne.isUnit h))
    refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _ f h₂)), ?_⟩
    rw [← Spec.map_comp]
    rfl
  have := c.q_hom
  have := c.i_hom
  have := c.q_surj
  have hk := c.isKernel
  let T : Over (Sp (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1))) := Over.mk r₀
  let eG := TorsionLift.ptsEquiv (thick V (IsLocalRing.maximalIdeal V) 0) G T _ hr₀
  let eB := TorsionLift.ptsEquiv (thick V (IsLocalRing.maximalIdeal V) 0) D.P.A T _ hr₀
  let q := IsMonHom.monoidHom c.q T
  let i := IsMonHom.monoidHom c.i T
  let e := splitTorusPointsEquiv _ D.X T
  have hqi : ∀ t, q (i t) = 1 := fun t => by
    change (t ≫ c.i) ≫ c.q = 1
    rw [Category.assoc, hk.w, ← Category.assoc, comp_toUnit]
    rfl
  have hker : ∀ x, q x = 1 → ∃ t, i t = x := fun x hx =>
    ⟨hk.lift x (toUnit _) (by rw [show x ≫ c.q = 1 from hx, Hom.one_def]), hk.lift_fst _ _ _⟩
  have hq : Function.Surjective q := fun b => by
    have : LocallyOfFiniteType (c.q.left ≫ (thickObj V (IsLocalRing.maximalIdeal V) 0 D.P.A).hom) := by
      rw [Over.w c.q]
      exact inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom (thick V (IsLocalRing.maximalIdeal V) 0)))
    have : LocallyOfFiniteType c.q.left :=
      locallyOfFiniteType_of_comp _ (thickObj V (IsLocalRing.maximalIdeal V) 0 D.P.A).hom
    obtain ⟨x, hx⟩ := GeomSurj.exists_lift_of_surjective c.q.left b.left
    exact ⟨Over.homMk x (by rw [← Over.w c.q, ← Category.assoc, ← hx]; exact Over.w b),
      Over.OverMorphism.ext hx.symm⟩
  refine ⟨eB.toMonoidHom.comp (q.comp eG.symm.toMonoidHom), fun x => ?_, fun n hn b hb => ?_⟩
  · obtain ⟨x, rfl⟩ := eG.surjective x
    refine ⟨x.left, (TorsionLift.ptsEquiv_left _ _ _ _ _ x).symm, ?_⟩
    change _ = (eB (q (eG.symm (eG x)))).left
    rw [eG.symm_apply_apply]
    exact (Category.assoc _ _ _).symm.trans (TorsionLift.ptsEquiv_left _ _ _ _ _ (q x)).symm
  · obtain ⟨x, hx, hxb⟩ := exists_torsion_lift
      ((i.comp e.symm.toMonoidHom) : (Multiplicative D.X →* Γ(T.left, ⊤)ˣ) →* _) q n
      (fun t => hqi _) (fun x hx => by
        obtain ⟨t, ht⟩ := hker x hx
        exact ⟨e t, (congrArg i (e.symm_apply_apply t)).trans ht⟩) hq
      (TorsLift.exists_pow_eq_hom (M := Γ(T.left, ⊤)ˣ) n (TorsLift.exists_pow_eq_unit K n hn))
      (eB.symm b) (by rw [← map_pow, hb, map_one])
    refine ⟨eG x, by rw [← map_pow, hx, map_one], ?_⟩
    change eB (q (eG.symm (eG x))) = b
    rw [eG.symm_apply_apply, hxb, eB.apply_symm_apply]

end GlobalTheory.SpecialPoints
