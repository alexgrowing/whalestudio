import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LTensorLeibniz
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroMove

theorem gen_hom {A C : Type} [CommRing A] [CommRing C] {g : ℕ} (ψ : A →+* C) (D : Fin g → A →+ A)
    (h1 : ∀ a, D a 1 = 0) (hL : ∀ a x y, D a (x * y) = x * D a y + y * D a x)
    (n : Fin g → C) (hn : ∀ a b, n a * n b = 0) :
    ∃ ψ' : A →+* C, ∀ x, ψ' x = ψ x + ∑ a, ψ (D a x) * n a := by
  have hsq : ∀ (u v : Fin g → C), (∑ a, u a * n a) * (∑ b, v b * n b) = 0 := by
    intro u v
    rw [Finset.sum_mul_sum]
    refine Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => ?_))
    calc u a * n a * (v b * n b) = u a * v b * (n a * n b) := by ring
      _ = 0 := by rw [hn a b, mul_zero]
  refine ⟨{ toFun := fun x => ψ x + ∑ a, ψ (D a x) * n a,
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, fun x => rfl⟩
  · simp [h1]
  · intro x y
    have e := hsq (fun a => ψ (D a x)) (fun a => ψ (D a y))
    simp only [hL, map_add, map_mul, add_mul, Finset.sum_add_distrib]
    have ex : ∑ a, ψ x * ψ (D a y) * n a = ψ x * ∑ a, ψ (D a y) * n a := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun a _ => by ring)
    have ey : ∑ a, ψ y * ψ (D a x) * n a = ψ y * ∑ a, ψ (D a x) * n a := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun a _ => by ring)
    rw [ex, ey]
    linear_combination (-1 : C) * e
  · simp
  · intro x y
    simp only [map_add, add_mul, Finset.sum_add_distrib]
    ring

theorem lTensor_leibniz {R S : Type} [CommRing R] [Algebra ℂ R] [CommRing S] [Algebra ℂ S]
    (d : Derivation ℂ S S) (x y : R ⊗[ℂ] S) :
    LinearMap.lTensor R d.toLinearMap (x * y) =
      x * LinearMap.lTensor R d.toLinearMap y + y * LinearMap.lTensor R d.toLinearMap x := by
  first
  | exact @_root_.GlobalTheory.TensorLeibnizRule.lTensor_leibniz
  | exact _root_.GlobalTheory.TensorLeibnizRule.lTensor_leibniz
  | (apply _root_.GlobalTheory.TensorLeibnizRule.lTensor_leibniz <;> assumption)
  | (intros; apply _root_.GlobalTheory.TensorLeibnizRule.lTensor_leibniz <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TensorLeibnizRule.lTensor_leibniz <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TensorLeibnizRule.lTensor_leibniz ..)

theorem lTensor_one {R S : Type} [CommRing R] [Algebra ℂ R] [CommRing S] [Algebra ℂ S]
    (d : Derivation ℂ S S) : LinearMap.lTensor R d.toLinearMap (1 : R ⊗[ℂ] S) = 0 := by
  rw [Algebra.TensorProduct.one_def, LinearMap.lTensor_tmul, Derivation.coeFn_coe, Derivation.map_one_eq_zero,
    TensorProduct.tmul_zero]

theorem sqZeroMove : ∀ {g : ℕ} {W₀ : Opens (Tot Empty g)} {R : Type} [CommRing R] [Algebra ℂ R] {C : Type} [CommRing C] (ψ : R ⊗[ℂ] Hol W₀ →+* C) (n : Fin g → C), (∀ a b, n a * n b = 0) → ∃ ψ' : R ⊗[ℂ] Hol W₀ →+* C, ∀ x, ψ' x = ψ x + ∑ a, ψ (LinearMap.lTensor R (dw a).toLinearMap x) * n a := by
  intro g W₀ R _ _ C _ ψ n hn
  exact gen_hom ψ (fun a => (LinearMap.lTensor R (dw (W := W₀) a).toLinearMap).toAddMonoidHom)
    (fun a => lTensor_one _) (fun a x y => lTensor_leibniz _ x y) n hn

end GlobalTheory.SqZeroMove
