import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg.SymCube

open GlobalTheory.UU

theorem sym_cube (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))
    (x y : T ⟶ D.P.A) (z : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) (hJ : Good D.P.L z J) :
    val D.sym (x * y).left z J * cubV D.cub z J y y⁻¹ x⁻¹ =
      val D.sym x.left z J * val D.sym y.left z J * cubV D.cub z J x x⁻¹ y := by
  let G := D.P.A
  let a := x3 G 0
  let b := x3 G 1
  let sy := fun p : G3 G ⟶ G => LB.pullGen D.P.L _ _ D.sym p.left
  let cu := fun p q r : G3 G ⟶ G => LB.pullGen D.P.L (thφ G (x3 G)) thε D.cub.t (lift p (lift q r)).left
  have gs : ∀ p, (sy p).IsGen := fun p => DVR.pullGen_isGen _ _ _ _ D.sym_gen _
  have gc : ∀ p q r, (cu p q r).IsGen := fun p q r => DVR.pullGen_isGen _ _ _ _ D.cub.isGen _
  have vs : ∀ {T' : Over (Spec (CommRingCat.of R))} (σ : T' ⟶ G3 G) {z : T'.left} {J}, Good D.P.L z J → ∀ p,
      val (sy p) σ.left z J = val D.sym (σ ≫ p).left z J := fun σ z J hJ p => val_pull hJ _ _ _
  let t₁ := LB.mulGen D.P.L _ _ _ _ (sy (a * b)) (cu b b⁻¹ a⁻¹)
  let t₂ := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (sy a) (sy b)) (cu a a⁻¹ b)
  have ev : ∀ {T' : Over (Spec (CommRingCat.of R))} (σ : T' ⟶ G3 G) {z : T'.left} {J}, Good D.P.L z J →
      val t₁ σ.left z J = val D.sym ((σ ≫ a) * (σ ≫ b)).left z J * cubV D.cub z J (σ ≫ b) (σ ≫ b)⁻¹ (σ ≫ a)⁻¹ ∧
      val t₂ σ.left z J = val D.sym (σ ≫ a).left z J * val D.sym (σ ≫ b).left z J *
        cubV D.cub z J (σ ≫ a) (σ ≫ a)⁻¹ (σ ≫ b) := fun σ z J hJ => by
    constructor
    · rw [← MonObj.comp_mul, ← GrpObj.comp_inv, ← GrpObj.comp_inv]
      exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vs σ hJ _) (val_cub D.cub σ hJ _ _ _))
    · rw [← GrpObj.comp_inv]
      exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (vs σ hJ _) (vs σ hJ _))) (val_cub D.cub σ hJ _ _ _))
  let e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G3 G := lift 1 (lift 1 1)
  have e₀ : e ≫ a = 1 := by simp [e, a, x3]
  have e₁ : e ≫ b = 1 := by simp [e, b, x3]
  let ρ : T ⟶ G3 G := lift x (lift y 1)
  have r₀ : ρ ≫ a = x := by simp [ρ, a, x3]
  have r₁ : ρ ≫ b = y := by simp [ρ, b, x3]
  have h3 := GlobalTheory.UU.surjective_cube GlobalTheory.globalFns_holds D.P.isAb
  have key : val t₁ ρ.left z J = val t₂ ρ.left z J := by
    refine gen_unique' D.P.isLB (fun V _ k => ?_) (G3 G).hom e.left (Over.w e) h3
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (gs _) (gc _ _ _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (gs _) (gs _)) (gc _ _ _))
      (fun y I hI => ?_) _ ρ.left z J hJ
    · refine (DVR.prod_sum₂ (K := Fin 2 ⊕ Fin 2) (K' := thK) (U := V) _
        (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (prod_sym a k) (prod_sym b k))
        (prod_cub a a⁻¹ b k)).trans (Eq.trans ?_
        (DVR.prod_sum₂ (K := Fin 2) (K' := thK) (U := V) _ (prod_sym (a * b) k) (prod_cub b b⁻¹ a⁻¹ k)).symm)
      have m₁ : b * b⁻¹ * a⁻¹ = a⁻¹ := by rw [mul_inv_cancel, _root_.one_mul]
      have m₂ : b * b⁻¹ = 1 := mul_inv_cancel b
      have m₃ : b * a⁻¹ = a⁻¹ * b := mul_comm _ _
      have m₄ : b⁻¹ * a⁻¹ = (a * b)⁻¹ := (mul_inv_rev a b).symm
      have m₅ : a * a⁻¹ * b = b := by rw [mul_inv_cancel, _root_.one_mul]
      have m₆ : a * a⁻¹ = 1 := mul_inv_cancel a
      rw [m₁, m₂, m₃, m₄, m₅, m₆]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    · have s1 : val D.sym (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G).left y I = 1 := by
        rw [one_left]
        exact (val_pull hI D.sym (eSec G) _).symm.trans ((val_corr hI D.sym_rig _).trans (val_one _))
      refine (ev e hI).1.trans (Eq.trans ?_ (ev e hI).2.symm)
      rw [e₀, e₁]
      simp only [inv_one, _root_.mul_one, s1, _root_.one_mul]
  have := (ev ρ hJ).1.symm.trans (key.trans (ev ρ hJ).2)
  rwa [r₀, r₁] at this

end GlobalTheory.PolDeg.SymCube
