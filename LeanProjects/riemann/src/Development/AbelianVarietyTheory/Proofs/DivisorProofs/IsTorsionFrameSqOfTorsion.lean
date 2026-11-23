import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaConstantsOverAlgClosedExtens
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsTorsFrameOfSymLift
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
noncomputable section

namespace GlobalTheory.USep

open GlobalTheory.TorsFrame

theorem isTorsFrame_sq : ∀ (S : Scheme.{0}) (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))) (n : ℕ) (T : Over S)
    (x : T ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))),
    IsTorsFrame P rig n x τ → IsTorsFrame P rig (n ^ 2) x τ := by
  intro S P rig n T x τ ⟨hx, hτ, α, hα, hN, hC⟩
  have hL := P.isLB
  have eN : (mulA P.A n).left ≫ (mulA P.A n).left = (mulA P.A (n ^ 2)).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, ← pow_mul, ← sq]
  have ex : x.left ≫ (mulA P.A n).left = T.hom ≫ eSec P.A := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, hx, one_left]
  obtain ⟨α', hα', vα'⟩ := exists_gen hL (φ' := ![𝟙 P.A.left, (mulA P.A (n ^ 2)).left])
    (ε' := ![((n ^ 2 : ℕ) : ℤ) ^ 2, -1])
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Category.comp_id, eN]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      push_cast
      module)
    (LB.mulGen P.L _ _ _ _ (LB.pullGen P.L _ _ α (mulA P.A n).left) (GeneratorPullback.powGen P.L _ _ α (n ^ 2)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα _) (DVR.powGen_isGen _ _ _ _ hα _))
  have vα₂ : ∀ (Z : Scheme.{0}) (r : Z ⟶ P.A.left) (z : Z) (J), Good P.L z J →
      val α' r z J = val α (r ≫ (mulA P.A n).left) z J * val α r z J ^ (n ^ 2) := fun Z r z J hJ => by
    rw [vα' _ _ z J hJ, val_mul hJ, val_pull hJ, val_powGen]
  refine ⟨by rw [sq, pow_mul, hx, one_pow], hτ, α', hα', corr_of_val hL fun z J hJ => ?_,
    corr_of_val hL fun z J hJ => ?_⟩
  · have h0 := val_corr hJ hN (𝟙 (𝟙_ (Over S)).left)
    rw [val_pull hJ, val_mul hJ, val_inv] at h0 ⊢
    rw [vα₂ _ _ z J hJ, Category.assoc, eSec_mulA, h0]
    have hp : ∀ k : ℤ, val (rigPow P.A P.L rig k) (𝟙 (𝟙_ (Over S)).left) z J =
        val (φ := fun _ : PUnit => eSec P.A) (ε := fun _ => 1) rig (𝟙 (𝟙_ (Over S)).left) z J ^ k := fun k => map_zpow _ _ _
    rw [hp, hp]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow]
    push_cast
    module
  · have h1 := val_corr hJ hC (𝟙 T.left)
    have h2 := val_corr hJ hN T.hom
    have hp : ∀ k : ℤ, val (rigPow P.A P.L rig k) T.hom z J =
        val (φ := fun _ : PUnit => eSec P.A) (ε := fun _ => 1) rig T.hom z J ^ k := fun k => map_zpow _ _ _
    have hf : ∀ k : ℤ, val (powFrame P.A P.L x τ k) (𝟙 T.left) z J = val τ (𝟙 T.left) z J ^ k :=
      fun k => map_zpow _ _ _
    rw [val_pull hJ, val_mul hJ, val_inv, hp] at h2
    rw [hf, val_mul hJ, val_pull hJ, val_rigT rig _ z hJ] at h1
    simp only [Category.id_comp] at h1
    rw [hf, val_mul hJ, val_pull hJ, val_rigT rig _ z hJ]
    simp only [Category.id_comp]
    rw [vα₂ _ _ z J hJ, ex, h2]
    have ha : val α x.left z J = val τ (𝟙 T.left) z J ^ ((n : ℤ) ^ 2) *
        (val (φ := fun _ : PUnit => eSec P.A) (ε := fun _ => 1) rig T.hom z J)⁻¹ := by
      rw [h1, mul_inv_cancel_right]
    rw [ha]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow]
    push_cast
    module

end GlobalTheory.USep
end
