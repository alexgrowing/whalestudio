import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralAdeleLimitCompatibleIntSystemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactSpaceIntegers

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

namespace GlobalTheory.LKGeo.ModLim

variable {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
theorem isIntAf_one : IsIntAf (1 : AfP p) := fun v => by rw [map_one]; exact one_mem _

omit [Fact p.Prime] in
theorem isIntAf_mul {a c : AfP p} (ha : IsIntAf a) (hc : IsIntAf c) : IsIntAf (a * c) := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hc v)

theorem inAf_mem (D : Datum p) (x : D.La) : inAf D x ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, x, isIntAf_one, rfl⟩

theorem smul_mem_laHat (D : Datum p) {a : AfP p} (ha : IsIntAf a) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) :
    a • v ∈ LaHat D := by
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, x, hc, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a * c, x, isIntAf_mul ha hc, ?_⟩
    rw [TensorProduct.smul_tmul', smul_eq_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

noncomputable def inAfHom (D : Datum p) : D.La →+ AfP p ⊗[ℚ] VQ D where
  toFun := inAf D
  map_zero' := by simp [inAf]
  map_add' x y := by simp [inAf, TensorProduct.tmul_add]

theorem exists_limit : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (g : ℕ → D.La →+ D.La), (∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ∃ z, g (n * m) x = g n x + n • z) → ∃ h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D), (∀ v ∈ LaHat D, h₀ v ∈ LaHat D) ∧ ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, h₀ (inAf D x) = inAf D (g n x) + n • w := by
  first
  | exact @_root_.GlobalTheory.AdelicLimitCompactness.main
  | exact _root_.GlobalTheory.AdelicLimitCompactness.main
  | (apply _root_.GlobalTheory.AdelicLimitCompactness.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdelicLimitCompactness.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdelicLimitCompactness.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdelicLimitCompactness.main ..)

end GlobalTheory.LKGeo.ModLim
