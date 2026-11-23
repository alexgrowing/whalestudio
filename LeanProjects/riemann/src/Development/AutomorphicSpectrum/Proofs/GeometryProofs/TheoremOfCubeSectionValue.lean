import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SumMulFG
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.Transl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.Transl

theorem exists_lin_gen {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)
    {T : Over S} (x a : T ⟶ G) (m : ℕ) (hx : x ^ m = 1) :
    ∃ v : FG L.L T.left, (∀ (U : Type) [CommGroup U] (h : (T.left ⟶ G.left) → U),
        v.sum U h = h (x * a ^ m).left * (h (a ^ m).left)⁻¹ * (h x.left)⁻¹ * h (1 : T ⟶ G).left) ∧
      ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good L.L z J → ρ ≫ a = 1 → v.v ρ.left z J = 1 := by
  obtain ⟨t₂, ht₂, v₂⟩ := exists_cubN c (1 : T ⟶ G) a x m
  obtain ⟨t₁, ht₁, v₁⟩ := exists_cubN c (1 : T ⟶ G) x a m
  refine ⟨FG.mul ⟨Fin 8, _, _, t₂, ht₂⟩ (FG.inv ⟨Fin 8, _, _, t₁, ht₁⟩), fun U _ h => ?_, fun T' ρ z J hJ hρ => ?_⟩
  · rw [FG.sum_mul, FG.sum_inv]
    simp only [FG.sum, Fin.prod_univ_succ, Fin.prod_univ_zero]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, hx,
      _root_.one_mul, _root_.mul_one, mul_comm a x, mul_comm (a ^ m) x]
    apply Additive.ofMul.injective
    simp [ofMul_mul, ofMul_inv, ofMul_zpow]
    module
  · rw [FG.v_mul hJ, FG.v_inv]
    show val t₂ ρ.left z J * (val t₁ ρ.left z J)⁻¹ = 1
    rw [v₂ T' ρ z J hJ, v₁ T' ρ z J hJ, hρ, (isCub_cubV c hJ).N_one]
    have : cubN (cubV c z J) m (ρ ≫ (1 : T ⟶ G)) 1 (ρ ≫ x) = 1 :=
      Finset.prod_eq_one fun _ _ => (isCub_cubV c hJ).face₂ _ _ |>.symm ▸ rfl
    rw [this]
    simp

end GlobalTheory.CompanionTheory.Ar.Sl.Transl
