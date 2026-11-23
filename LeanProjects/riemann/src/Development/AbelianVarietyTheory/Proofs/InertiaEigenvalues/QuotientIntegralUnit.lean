import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommOfBezout
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormDetLeOneOfEntriesNormLeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitAndIntegInvOfNormDetEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UltrametricNormDetOneAddSmulStatement

open GlobalTheory.UnitDiscAlg

namespace GlobalTheory.UnitDiscAlg.QuotAlg

section Comm
variable {R : Type*} [CommRing R]

theorem eq_of_comp {e₁ e₂ e₃ x y : R} (hs : e₁ + e₂ + e₃ = 1)
    (h1 : x * e₁ = y * e₁) (h2 : x * e₂ = y * e₂) (h3 : x * e₃ = y * e₃) : x = y := by
  linear_combination h1 + h2 + h3 - (x - y) * hs

theorem cm_mul {e x y α β : R} (hx : x * e = α * e) (hy : y * e = β * e) :
    x * y * e = α * β * e := by
  linear_combination y * hx + α * hy

theorem comp1 {e₁ e₂ e₃ : R} (h11 : e₁ * e₁ = e₁) (h12 : e₁ * e₂ = 0) (h13 : e₁ * e₃ = 0)
    (α β γ : R) : (α * e₁ + β * e₂ + γ * e₃) * e₁ = α * e₁ := by
  linear_combination α * h11 + β * h12 + γ * h13

theorem comp2 {e₁ e₂ e₃ : R} (h12 : e₁ * e₂ = 0) (h22 : e₂ * e₂ = e₂) (h23 : e₂ * e₃ = 0)
    (α β γ : R) : (α * e₁ + β * e₂ + γ * e₃) * e₂ = β * e₂ := by
  linear_combination α * h12 + β * h22 + γ * h23

theorem comp3 {e₁ e₂ e₃ : R} (h13 : e₁ * e₃ = 0) (h23 : e₂ * e₃ = 0) (h33 : e₃ * e₃ = e₃)
    (α β γ : R) : (α * e₁ + β * e₂ + γ * e₃) * e₃ = γ * e₃ := by
  linear_combination α * h13 + β * h23 + γ * h33

theorem core (p pi c ci u a₂ a₃ b e₁ e₂ e₃ k11 k12 k13 k21 k22 k23 k31 k32 k33 k41 k42 k43 : R)
    (hp : p * pi = 1) (hci : c * ci = 1)
    (h11 : e₁ * e₁ = e₁) (h22 : e₂ * e₂ = e₂) (h33 : e₃ * e₃ = e₃)
    (h12 : e₁ * e₂ = 0) (h13 : e₁ * e₃ = 0) (h23 : e₂ * e₃ = 0) (hs : e₁ + e₂ + e₃ = 1)
    (hc1 : c * e₁ = u * e₁) (hc2 : c * e₂ = p * (a₂ * e₂)) (hc3 : ci * e₃ = p * (a₃ * e₃))
    (hk11 : (p + u ^ 2) * k11 = 1) (hk12 : (1 + p * a₂ ^ 2) * k12 = 1)
    (hk13 : (1 + p ^ 3 * a₃ ^ 2) * k13 = 1)
    (hk21 : (p + u ^ 3) * k21 = 1) (hk22 : (1 + p ^ 2 * a₂ ^ 3) * k22 = 1)
    (hk23 : (1 + p ^ 4 * a₃ ^ 3) * k23 = 1)
    (hk31 : (p * u ^ 2 + b ^ 2) * k31 = 1) (hk32 : (b ^ 2 + p ^ 3 * a₂ ^ 2) * k32 = 1)
    (hk33 : (1 + p * b ^ 2 * a₃ ^ 2) * k33 = 1)
    (hk41 : (p * u ^ 3 + b ^ 3) * k41 = 1) (hk42 : (b ^ 3 + p ^ 4 * a₂ ^ 3) * k42 = 1)
    (hk43 : (1 + p ^ 2 * b ^ 3 * a₃ ^ 3) * k43 = 1) :
    (p + c ^ 2) * (k11 * e₁ + (pi * k12) * e₂ + (ci ^ 2 * k13) * e₃) = 1 ∧
    (p + c ^ 3) * (k21 * e₁ + (pi * k22) * e₂ + (ci ^ 3 * k23) * e₃) = 1 ∧
    (p * c ^ 2 + b ^ 2) * (k31 * e₁ + k32 * e₂ + (pi * ci ^ 2 * k33) * e₃) = 1 ∧
    (p * c ^ 3 + b ^ 3) * (k41 * e₁ + k42 * e₂ + (pi * ci ^ 3 * k43) * e₃) = 1 ∧
    (p * c ^ 3 + b ^ 3) * (p + c ^ 2) =
      (((p * u ^ 3 + b ^ 3) * (p + u ^ 2) * k21 * k31) * e₁
        + ((b ^ 3 + p ^ 4 * a₂ ^ 3) * (1 + p * a₂ ^ 2) * k22 * k32) * e₂
        + ((1 + p ^ 2 * b ^ 3 * a₃ ^ 3) * (1 + p ^ 3 * a₃ ^ 2) * k23 * k33) * e₃)
        * ((p + c ^ 3) * (p * c ^ 2 + b ^ 2)) ∧
    (((p * u ^ 3 + b ^ 3) * (p + u ^ 2) * k21 * k31) * e₁
        + ((b ^ 3 + p ^ 4 * a₂ ^ 3) * (1 + p * a₂ ^ 2) * k22 * k32) * e₂
        + ((1 + p ^ 2 * b ^ 3 * a₃ ^ 3) * (1 + p ^ 3 * a₃ ^ 2) * k23 * k33) * e₃) *
      (((p + u ^ 3) * (p * u ^ 2 + b ^ 2) * k41 * k11) * e₁
        + ((1 + p ^ 2 * a₂ ^ 3) * (b ^ 2 + p ^ 3 * a₂ ^ 2) * k42 * k12) * e₂
        + ((1 + p ^ 4 * a₃ ^ 3) * (1 + p * b ^ 2 * a₃ ^ 2) * k43 * k13) * e₃) = 1 := by
  have hd3 : e₃ = p * c * a₃ * e₃ := by linear_combination c * hc3 - e₃ * hci

  have LargeParameterEstimates : (p + c ^ 2) * e₁ = ((p + u ^ 2) * 1) * e₁ := by linear_combination (c + u) * hc1
  have F12 : (p + c ^ 2) * e₂ = ((1 + p * a₂ ^ 2) * p) * e₂ := by
    linear_combination (c + p * a₂) * hc2
  have InertPlaceConditions : (p + c ^ 2) * e₃ = ((1 + p ^ 3 * a₃ ^ 2) * c ^ 2) * e₃ := by
    linear_combination p * (1 + p * c * a₃) * hd3
  have F21 : (p + c ^ 3) * e₁ = ((p + u ^ 3) * 1) * e₁ := by
    linear_combination (c ^ 2 + c * u + u ^ 2) * hc1
  have F22 : (p + c ^ 3) * e₂ = ((1 + p ^ 2 * a₂ ^ 3) * p) * e₂ := by
    linear_combination (c ^ 2 + c * p * a₂ + p ^ 2 * a₂ ^ 2) * hc2
  have F23 : (p + c ^ 3) * e₃ = ((1 + p ^ 4 * a₃ ^ 3) * c ^ 3) * e₃ := by
    linear_combination p * (1 + p * c * a₃ + (p * c * a₃) ^ 2) * hd3
  have F31 : (p * c ^ 2 + b ^ 2) * e₁ = ((p * u ^ 2 + b ^ 2) * 1) * e₁ := by
    linear_combination p * (c + u) * hc1
  have F32 : (p * c ^ 2 + b ^ 2) * e₂ = ((b ^ 2 + p ^ 3 * a₂ ^ 2) * 1) * e₂ := by
    linear_combination p * (c + p * a₂) * hc2
  have F33 : (p * c ^ 2 + b ^ 2) * e₃ = ((1 + p * b ^ 2 * a₃ ^ 2) * (p * c ^ 2)) * e₃ := by
    linear_combination b ^ 2 * (1 + p * c * a₃) * hd3
  have F41 : (p * c ^ 3 + b ^ 3) * e₁ = ((p * u ^ 3 + b ^ 3) * 1) * e₁ := by
    linear_combination p * (c ^ 2 + c * u + u ^ 2) * hc1
  have F42 : (p * c ^ 3 + b ^ 3) * e₂ = ((b ^ 3 + p ^ 4 * a₂ ^ 3) * 1) * e₂ := by
    linear_combination p * (c ^ 2 + c * p * a₂ + p ^ 2 * a₂ ^ 2) * hc2
  have F43 : (p * c ^ 3 + b ^ 3) * e₃ = ((1 + p ^ 2 * b ^ 3 * a₃ ^ 3) * (p * c ^ 3)) * e₃ := by
    linear_combination b ^ 3 * (1 + p * c * a₃ + (p * c * a₃) ^ 2) * hd3
  have c1 := comp1 h11 h12 h13
  have c2 := comp2 h12 h22 h23
  have c3 := comp3 h13 h23 h33
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine eq_of_comp hs ?_ ?_ ?_
    · rw [cm_mul LargeParameterEstimates (c1 _ _ _)]; linear_combination e₁ * hk11
    · rw [cm_mul F12 (c2 _ _ _)]; linear_combination e₂ * p * pi * hk12 + e₂ * hp
    · rw [cm_mul InertPlaceConditions (c3 _ _ _)]
      linear_combination e₃ * (c * ci) ^ 2 * hk13 + e₃ * (c * ci + 1) * hci
  · refine eq_of_comp hs ?_ ?_ ?_
    · rw [cm_mul F21 (c1 _ _ _)]; linear_combination e₁ * hk21
    · rw [cm_mul F22 (c2 _ _ _)]; linear_combination e₂ * p * pi * hk22 + e₂ * hp
    · rw [cm_mul F23 (c3 _ _ _)]
      linear_combination e₃ * (c * ci) ^ 3 * hk23 + e₃ * ((c * ci) ^ 2 + c * ci + 1) * hci
  · refine eq_of_comp hs ?_ ?_ ?_
    · rw [cm_mul F31 (c1 _ _ _)]; linear_combination e₁ * hk31
    · rw [cm_mul F32 (c2 _ _ _)]; linear_combination e₂ * hk32
    · rw [cm_mul F33 (c3 _ _ _)]
      linear_combination e₃ * p * pi * (c * ci) ^ 2 * hk33 + e₃ * (c * ci) ^ 2 * hp
        + e₃ * (c * ci + 1) * hci
  · refine eq_of_comp hs ?_ ?_ ?_
    · rw [cm_mul F41 (c1 _ _ _)]; linear_combination e₁ * hk41
    · rw [cm_mul F42 (c2 _ _ _)]; linear_combination e₂ * hk42
    · rw [cm_mul F43 (c3 _ _ _)]
      linear_combination e₃ * p * pi * (c * ci) ^ 3 * hk43 + e₃ * (c * ci) ^ 3 * hp
        + e₃ * ((c * ci) ^ 2 + c * ci + 1) * hci
  · refine eq_of_comp hs ?_ ?_ ?_
    · rw [cm_mul F41 LargeParameterEstimates, cm_mul (c1 _ _ _) (cm_mul F21 F31)]
      linear_combination (-(p * u ^ 3 + b ^ 3) * (p + u ^ 2) * e₁) * ((p * u ^ 2 + b ^ 2) * k31 * hk21 + hk31)
    · rw [cm_mul F42 F12, cm_mul (c2 _ _ _) (cm_mul F22 F32)]
      linear_combination (-(b ^ 3 + p ^ 4 * a₂ ^ 3) * (1 + p * a₂ ^ 2) * p * e₂) * ((b ^ 2 + p ^ 3 * a₂ ^ 2) * k32 * hk22 + hk32)
    · rw [cm_mul F43 InertPlaceConditions, cm_mul (c3 _ _ _) (cm_mul F23 F33)]
      linear_combination (-(1 + p ^ 2 * b ^ 3 * a₃ ^ 3) * (1 + p ^ 3 * a₃ ^ 2) * p * c ^ 5 * e₃) * ((1 + p * b ^ 2 * a₃ ^ 2) * k33 * hk23 + hk33)
  · refine eq_of_comp hs ?_ ?_ ?_
    · rw [cm_mul (c1 _ _ _) (c1 _ _ _)]
      linear_combination e₁ * ((p + u ^ 3) * k21 * (p * u ^ 2 + b ^ 2) * k31 * (p + u ^ 2) * k11 * hk41
        + (p + u ^ 3) * k21 * (p * u ^ 2 + b ^ 2) * k31 * hk11 + (p + u ^ 3) * k21 * hk31 + hk21)
    · rw [cm_mul (c2 _ _ _) (c2 _ _ _)]
      linear_combination e₂ * ((1 + p ^ 2 * a₂ ^ 3) * k22 * (b ^ 2 + p ^ 3 * a₂ ^ 2) * k32 * (1 + p * a₂ ^ 2) * k12 * hk42
        + (1 + p ^ 2 * a₂ ^ 3) * k22 * (b ^ 2 + p ^ 3 * a₂ ^ 2) * k32 * hk12 + (1 + p ^ 2 * a₂ ^ 3) * k22 * hk32 + hk22)
    · rw [cm_mul (c3 _ _ _) (c3 _ _ _)]
      linear_combination e₃ * ((1 + p ^ 4 * a₃ ^ 3) * k23 * (1 + p * b ^ 2 * a₃ ^ 2) * k33 * (1 + p ^ 3 * a₃ ^ 2) * k13 * hk43
        + (1 + p ^ 4 * a₃ ^ 3) * k23 * (1 + p * b ^ 2 * a₃ ^ 2) * k33 * hk13 + (1 + p ^ 4 * a₃ ^ 3) * k23 * hk33 + hk23)

end Comm
end GlobalTheory.UnitDiscAlg.QuotAlg

namespace GlobalTheory.UnitDiscAlg.QuotAlg

theorem eq_one_of_mul_eq_one {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (hab : a * b = 1) : a = 1 := by nlinarith

theorem inv_comm {E : Type} [Field E] {n : ℕ} {x N : Matrix (Fin n) (Fin n) E}
    (h : x * N = N * x) : x⁻¹ * N = N * x⁻¹ := by
  by_cases hd : IsUnit x.det
  · calc x⁻¹ * N = x⁻¹ * N * (x * x⁻¹) := by rw [Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
      _ = x⁻¹ * (x * N) * x⁻¹ := by rw [h]; simp only [Matrix.mul_assoc]
      _ = N * x⁻¹ := by rw [← Matrix.mul_assoc x⁻¹, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ hd]; simp

theorem quotient_integral_unit : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ) (N c b e₁ e₂ e₃ u a₂ a₃ : Matrix (Fin n) (Fin n) E) (ϖ : E), 0 < ‖ϖ‖ → ‖ϖ‖ < 1 → (∀ x y : Matrix (Fin n) (Fin n) E, x * N = N * x → y * N = N * y → x * y = y * x) → IsUnit c → c * N = N * c → b * N = N * b → (∀ i j, ‖b i j‖ ≤ 1) → ‖b.det‖ = 1 → (e₁ * N = N * e₁ ∧ e₂ * N = N * e₂ ∧ e₃ * N = N * e₃ ∧ u * N = N * u ∧ a₂ * N = N * a₂ ∧ a₃ * N = N * a₃) → (∀ i j, ‖e₁ i j‖ ≤ 1 ∧ ‖e₂ i j‖ ≤ 1 ∧ ‖e₃ i j‖ ≤ 1 ∧ ‖u i j‖ ≤ 1 ∧ ‖a₂ i j‖ ≤ 1 ∧ ‖a₃ i j‖ ≤ 1) → ‖u.det‖ = 1 → e₁ * e₁ = e₁ → e₂ * e₂ = e₂ → e₃ * e₃ = e₃ → e₁ * e₂ = 0 → e₁ * e₃ = 0 → e₂ * e₃ = 0 → e₁ + e₂ + e₃ = 1 → c * e₁ = u * e₁ → c * e₂ = ϖ • (a₂ * e₂) → c⁻¹ * e₃ = ϖ • (a₃ * e₃) → IsUnit (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) ∧ IsUnit (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) ∧ IsUnit (ϖ • c ^ 2 + b ^ 2) ∧ IsUnit (ϖ • c ^ 3 + b ^ 3) ∧ (∀ i j, ‖((ϖ • c ^ 3 + b ^ 3) * (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) * ((ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) * (ϖ • c ^ 2 + b ^ 2))⁻¹) i j‖ ≤ 1) ∧ ‖((ϖ • c ^ 3 + b ^ 3) * (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) * ((ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) * (ϖ • c ^ 2 + b ^ 2))⁻¹).det‖ = 1 := by
  intro E _ _ n N c b e₁ e₂ e₃ u a₂ a₃ ϖ hϖ0 hϖ1 hcomm hcu hcN hbN hbI hbd hN hI hud h11 h22 h33
    h12 h13 h23 hs hc1 hc2 hc3
  obtain ⟨he₁N, he₂N, he₃N, huN, ha₂N, ha₃N⟩ := hN
  have hϖne : ϖ ≠ 0 := norm_pos_iff.1 hϖ0
  have hϖle : ‖ϖ‖ ≤ 1 := hϖ1.le
  set S := Subalgebra.centralizer E ({N} : Set (Matrix (Fin n) (Fin n) E)) with hS
  have memN : ∀ x : S, x.1 * N = N * x.1 := fun x =>
    ((Subalgebra.mem_centralizer_iff E).1 x.2 N rfl).symm
  letI : CommRing S := { (inferInstance : Ring S) with
    mul_comm := fun x y => Subtype.ext (hcomm _ _ (memN x) (memN y)) }
  have mem : ∀ x : Matrix (Fin n) (Fin n) E, x * N = N * x → x ∈ S := fun x hx =>
    (Subalgebra.mem_centralizer_iff E).2
      (fun g hg => by rw [Set.mem_singleton_iff.1 hg]; exact hx.symm)
  have I_mul : ∀ x y : S, (∀ i j, ‖x.1 i j‖ ≤ 1) → (∀ i j, ‖y.1 i j‖ ≤ 1) →
      ∀ i j, ‖(x * y).1 i j‖ ≤ 1 := fun x y hx hy => integ_mul hx hy
  have I_add : ∀ x y : S, (∀ i j, ‖x.1 i j‖ ≤ 1) → (∀ i j, ‖y.1 i j‖ ≤ 1) →
      ∀ i j, ‖(x + y).1 i j‖ ≤ 1 := fun x y hx hy => integ_add hx hy
  have I_pow : ∀ (x : S) (k : ℕ), (∀ i j, ‖x.1 i j‖ ≤ 1) → ∀ i j, ‖(x ^ k).1 i j‖ ≤ 1 :=
    fun x k hx => integ_pow hx k
  have I_one : ∀ i j, ‖(1 : S).1 i j‖ ≤ 1 := integ_one
  have isU : ∀ x y : S, x * y = 1 → IsUnit x.1 := fun x y h =>
    (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse
      (congrArg Subtype.val h : x.1 * y.1 = 1))

  have hcd : IsUnit c.det := (Matrix.isUnit_iff_isUnit_det c).1 hcu
  obtain ⟨hu, huiI⟩ :=
    isUnit_and_integ_inv_of_norm_det_eq_one E n u (fun i j => (hI i j).2.2.2.1) hud
  obtain ⟨hb, hbiI⟩ := isUnit_and_integ_inv_of_norm_det_eq_one E n b hbI hbd
  obtain ⟨C, hCv⟩ : ∃ X : S, X.1 = c := ⟨⟨c, mem c hcN⟩, rfl⟩
  obtain ⟨Ci, hCiv⟩ : ∃ X : S, X.1 = c⁻¹ := ⟨⟨c⁻¹, mem _ (inv_comm hcN)⟩, rfl⟩
  obtain ⟨U, hUv⟩ : ∃ X : S, X.1 = u := ⟨⟨u, mem u huN⟩, rfl⟩
  obtain ⟨Ui, hUiv⟩ : ∃ X : S, X.1 = u⁻¹ := ⟨⟨u⁻¹, mem _ (inv_comm huN)⟩, rfl⟩
  obtain ⟨B, hBv⟩ : ∃ X : S, X.1 = b := ⟨⟨b, mem b hbN⟩, rfl⟩
  obtain ⟨Bi, hBiv⟩ : ∃ X : S, X.1 = b⁻¹ := ⟨⟨b⁻¹, mem _ (inv_comm hbN)⟩, rfl⟩
  obtain ⟨A2, hA2v⟩ : ∃ X : S, X.1 = a₂ := ⟨⟨a₂, mem _ ha₂N⟩, rfl⟩
  obtain ⟨A3, hA3v⟩ : ∃ X : S, X.1 = a₃ := ⟨⟨a₃, mem _ ha₃N⟩, rfl⟩
  obtain ⟨E1, hE1v⟩ : ∃ X : S, X.1 = e₁ := ⟨⟨e₁, mem _ he₁N⟩, rfl⟩
  obtain ⟨E2, hE2v⟩ : ∃ X : S, X.1 = e₂ := ⟨⟨e₂, mem _ he₂N⟩, rfl⟩
  obtain ⟨E3, hE3v⟩ : ∃ X : S, X.1 = e₃ := ⟨⟨e₃, mem _ he₃N⟩, rfl⟩
  obtain ⟨P, hPv⟩ : ∃ X : S, X.1 = ϖ • 1 :=
    ⟨⟨_, mem _ (by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one])⟩, rfl⟩
  obtain ⟨Pi, hPiv⟩ : ∃ X : S, X.1 = ϖ⁻¹ • 1 :=
    ⟨⟨_, mem _ (by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one])⟩, rfl⟩
  have IU : ∀ i j, ‖U.1 i j‖ ≤ 1 := by rw [hUv]; exact fun i j => (hI i j).2.2.2.1
  have IUi : ∀ i j, ‖Ui.1 i j‖ ≤ 1 := by rw [hUiv]; exact huiI
  have IB : ∀ i j, ‖B.1 i j‖ ≤ 1 := by rw [hBv]; exact hbI
  have IBi : ∀ i j, ‖Bi.1 i j‖ ≤ 1 := by rw [hBiv]; exact hbiI
  have IA2 : ∀ i j, ‖A2.1 i j‖ ≤ 1 := by rw [hA2v]; exact fun i j => (hI i j).2.2.2.2.1
  have NearKilling : ∀ i j, ‖A3.1 i j‖ ≤ 1 := by rw [hA3v]; exact fun i j => (hI i j).2.2.2.2.2
  have IE1 : ∀ i j, ‖E1.1 i j‖ ≤ 1 := by rw [hE1v]; exact fun i j => (hI i j).1
  have IE2 : ∀ i j, ‖E2.1 i j‖ ≤ 1 := by rw [hE2v]; exact fun i j => (hI i j).2.1
  have IE3 : ∀ i j, ‖E3.1 i j‖ ≤ 1 := by rw [hE3v]; exact fun i j => (hI i j).2.2.1
  have IP : ∀ i j, ‖P.1 i j‖ ≤ 1 := by rw [hPv]; exact integ_smul hϖle integ_one
  have hUd : ‖U.1.det‖ = 1 := by rw [hUv]; exact hud
  have hBd : ‖B.1.det‖ = 1 := by rw [hBv]; exact hbd

  have hp : P * Pi = 1 := Subtype.ext (by
    show P.1 * Pi.1 = 1
    rw [hPv, hPiv, Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hϖne, one_smul])
  have hci : C * Ci = 1 := Subtype.ext (by
    show C.1 * Ci.1 = 1
    rw [hCv, hCiv]; exact Matrix.mul_nonsing_inv c hcd)
  have hUi : U * Ui = 1 := Subtype.ext (by
    show U.1 * Ui.1 = 1
    rw [hUv, hUiv]; exact Matrix.mul_nonsing_inv u ((Matrix.isUnit_iff_isUnit_det u).1 hu))
  have hBi : B * Bi = 1 := Subtype.ext (by
    show B.1 * Bi.1 = 1
    rw [hBv, hBiv]; exact Matrix.mul_nonsing_inv b ((Matrix.isUnit_iff_isUnit_det b).1 hb))
  have h11S : E1 * E1 = E1 := Subtype.ext (by show E1.1 * E1.1 = E1.1; rw [hE1v]; exact h11)
  have h22S : E2 * E2 = E2 := Subtype.ext (by show E2.1 * E2.1 = E2.1; rw [hE2v]; exact h22)
  have h33S : E3 * E3 = E3 := Subtype.ext (by show E3.1 * E3.1 = E3.1; rw [hE3v]; exact h33)
  have h12S : E1 * E2 = 0 := Subtype.ext (by show E1.1 * E2.1 = 0; rw [hE1v, hE2v]; exact h12)
  have h13S : E1 * E3 = 0 := Subtype.ext (by show E1.1 * E3.1 = 0; rw [hE1v, hE3v]; exact h13)
  have h23S : E2 * E3 = 0 := Subtype.ext (by show E2.1 * E3.1 = 0; rw [hE2v, hE3v]; exact h23)
  have hsS : E1 + E2 + E3 = 1 := Subtype.ext (by
    show E1.1 + E2.1 + E3.1 = 1; rw [hE1v, hE2v, hE3v]; exact hs)
  have hc1S : C * E1 = U * E1 := Subtype.ext (by
    show C.1 * E1.1 = U.1 * E1.1; rw [hCv, hE1v, hUv]; exact hc1)
  have hc2S : C * E2 = P * (A2 * E2) := Subtype.ext (by
    show C.1 * E2.1 = P.1 * (A2.1 * E2.1)
    rw [hCv, hE2v, hPv, hA2v, Matrix.smul_mul, Matrix.one_mul]; exact hc2)
  have hc3S : Ci * E3 = P * (A3 * E3) := Subtype.ext (by
    show Ci.1 * E3.1 = P.1 * (A3.1 * E3.1)
    rw [hCiv, hE3v, hPv, hA3v, Matrix.smul_mul, Matrix.one_mul]; exact hc3)

  have mk : ∀ g w x : S, g = w * (1 + P * x) → (∀ i j, ‖w.1 i j‖ ≤ 1) → ‖w.1.det‖ = 1 →
      (∀ i j, ‖x.1 i j‖ ≤ 1) → ∃ k : S, g * k = 1 ∧ ∀ i j, ‖k.1 i j‖ ≤ 1 := by
    intro g w x hg hw hwd hx
    have hgv : g.1 = w.1 * (1 + ϖ • x.1) := by
      rw [hg]; show w.1 * (1 + P.1 * x.1) = _; rw [hPv, Matrix.smul_mul, Matrix.one_mul]
    have hgI : ∀ i j, ‖g.1 i j‖ ≤ 1 := by
      rw [hgv]; exact integ_mul hw (integ_add integ_one (integ_smul hϖle hx))
    have hgd : ‖g.1.det‖ = 1 := by
      rw [hgv, Matrix.det_mul, norm_mul, hwd, GlobalTheory.T.ultrametric_norm_det_one_add_smul E n x.1 ϖ hϖ1 hx, one_mul]
    obtain ⟨hgu, hgiI⟩ := isUnit_and_integ_inv_of_norm_det_eq_one E n g.1 hgI hgd
    refine ⟨⟨g.1⁻¹, mem _ (inv_comm (memN g))⟩, Subtype.ext ?_, hgiI⟩
    exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hgu)
  have wpow : ∀ w : S, (∀ i j, ‖w.1 i j‖ ≤ 1) → ‖w.1.det‖ = 1 → ∀ k : ℕ,
      (∀ i j, ‖(w ^ k).1 i j‖ ≤ 1) ∧ ‖(w ^ k).1.det‖ = 1 := fun w hw hd k =>
    ⟨integ_pow hw k, by show ‖(w.1 ^ k).det‖ = 1; rw [Matrix.det_pow, norm_pow, hd, one_pow]⟩
  have w1 : (∀ i j, ‖(1 : S).1 i j‖ ≤ 1) ∧ ‖(1 : S).1.det‖ = 1 :=
    ⟨integ_one, by show ‖(1 : Matrix (Fin n) (Fin n) E).det‖ = 1; simp⟩
  obtain ⟨k11, hk11, Ik11⟩ := mk (P + U ^ 2) (U ^ 2) (Ui ^ 2)
    (by linear_combination -P * (U * Ui + 1) * hUi) (wpow U IU hUd 2).1 (wpow U IU hUd 2).2
    (I_pow _ _ IUi)
  obtain ⟨k12, hk12, Ik12⟩ := mk (1 + P * A2 ^ 2) 1 (A2 ^ 2) (by ring) w1.1 w1.2 (I_pow _ _ IA2)
  obtain ⟨k13, hk13, Ik13⟩ := mk (1 + P ^ 3 * A3 ^ 2) 1 (P ^ 2 * A3 ^ 2) (by ring) w1.1 w1.2
    (I_mul _ _ (I_pow _ _ IP) (I_pow _ _ NearKilling))
  obtain ⟨k21, hk21, Ik21⟩ := mk (P + U ^ 3) (U ^ 3) (Ui ^ 3)
    (by linear_combination -P * ((U * Ui) ^ 2 + U * Ui + 1) * hUi) (wpow U IU hUd 3).1
    (wpow U IU hUd 3).2 (I_pow _ _ IUi)
  obtain ⟨k22, hk22, Ik22⟩ := mk (1 + P ^ 2 * A2 ^ 3) 1 (P * A2 ^ 3) (by ring) w1.1 w1.2
    (I_mul _ _ IP (I_pow _ _ IA2))
  obtain ⟨k23, hk23, Ik23⟩ := mk (1 + P ^ 4 * A3 ^ 3) 1 (P ^ 3 * A3 ^ 3) (by ring) w1.1 w1.2
    (I_mul _ _ (I_pow _ _ IP) (I_pow _ _ NearKilling))
  obtain ⟨k31, hk31, Ik31⟩ := mk (P * U ^ 2 + B ^ 2) (B ^ 2) (Bi ^ 2 * U ^ 2)
    (by linear_combination -P * U ^ 2 * (B * Bi + 1) * hBi) (wpow B IB hBd 2).1
    (wpow B IB hBd 2).2 (I_mul _ _ (I_pow _ _ IBi) (I_pow _ _ IU))
  obtain ⟨k32, hk32, Ik32⟩ := mk (B ^ 2 + P ^ 3 * A2 ^ 2) (B ^ 2) (P ^ 2 * (Bi ^ 2 * A2 ^ 2))
    (by linear_combination -P ^ 3 * A2 ^ 2 * (B * Bi + 1) * hBi) (wpow B IB hBd 2).1
    (wpow B IB hBd 2).2 (I_mul _ _ (I_pow _ _ IP) (I_mul _ _ (I_pow _ _ IBi) (I_pow _ _ IA2)))
  obtain ⟨k33, hk33, Ik33⟩ := mk (1 + P * B ^ 2 * A3 ^ 2) 1 (B ^ 2 * A3 ^ 2) (by ring) w1.1 w1.2
    (I_mul _ _ (I_pow _ _ IB) (I_pow _ _ NearKilling))
  obtain ⟨k41, hk41, Ik41⟩ := mk (P * U ^ 3 + B ^ 3) (B ^ 3) (Bi ^ 3 * U ^ 3)
    (by linear_combination -P * U ^ 3 * ((B * Bi) ^ 2 + B * Bi + 1) * hBi) (wpow B IB hBd 3).1
    (wpow B IB hBd 3).2 (I_mul _ _ (I_pow _ _ IBi) (I_pow _ _ IU))
  obtain ⟨k42, hk42, Ik42⟩ := mk (B ^ 3 + P ^ 4 * A2 ^ 3) (B ^ 3) (P ^ 3 * (Bi ^ 3 * A2 ^ 3))
    (by linear_combination -P ^ 4 * A2 ^ 3 * ((B * Bi) ^ 2 + B * Bi + 1) * hBi)
    (wpow B IB hBd 3).1 (wpow B IB hBd 3).2
    (I_mul _ _ (I_pow _ _ IP) (I_mul _ _ (I_pow _ _ IBi) (I_pow _ _ IA2)))
  obtain ⟨k43, hk43, Ik43⟩ := mk (1 + P ^ 2 * B ^ 3 * A3 ^ 3) 1 (P * (B ^ 3 * A3 ^ 3)) (by ring)
    w1.1 w1.2 (I_mul _ _ IP (I_mul _ _ (I_pow _ _ IB) (I_pow _ _ NearKilling)))
  obtain ⟨hX1, hX2, hX3, hX4, hQ, hYY⟩ := core P Pi C Ci U A2 A3 B E1 E2 E3
    k11 k12 k13 k21 k22 k23 k31 k32 k33 k41 k42 k43 hp hci h11S h22S h33S h12S h13S h23S hsS
    hc1S hc2S hc3S hk11 hk12 hk13 hk21 hk22 hk23 hk31 hk32 hk33 hk41 hk42 hk43
  set Y : S := ((P * U ^ 3 + B ^ 3) * (P + U ^ 2) * k21 * k31) * E1
        + ((B ^ 3 + P ^ 4 * A2 ^ 3) * (1 + P * A2 ^ 2) * k22 * k32) * E2
        + ((1 + P ^ 2 * B ^ 3 * A3 ^ 3) * (1 + P ^ 3 * A3 ^ 2) * k23 * k33) * E3 with hY
  set Y' : S := ((P + U ^ 3) * (P * U ^ 2 + B ^ 2) * k41 * k11) * E1
        + ((1 + P ^ 2 * A2 ^ 3) * (B ^ 2 + P ^ 3 * A2 ^ 2) * k42 * k12) * E2
        + ((1 + P ^ 4 * A3 ^ 3) * (1 + P * B ^ 2 * A3 ^ 2) * k43 * k13) * E3 with hY'
  have IY : ∀ i j, ‖Y.1 i j‖ ≤ 1 := by
    rw [hY]
    exact I_add _ _ (I_add _ _
      (I_mul _ _ (I_mul _ _ (I_mul _ _ (I_mul _ _ (I_add _ _ (I_mul _ _ IP (I_pow _ _ IU)) (I_pow _ _ IB))
        (I_add _ _ IP (I_pow _ _ IU))) Ik21) Ik31) IE1)
      (I_mul _ _ (I_mul _ _ (I_mul _ _ (I_mul _ _ (I_add _ _ (I_pow _ _ IB) (I_mul _ _ (I_pow _ _ IP) (I_pow _ _ IA2)))
        (I_add _ _ I_one (I_mul _ _ IP (I_pow _ _ IA2)))) Ik22) Ik32) IE2))
      (I_mul _ _ (I_mul _ _ (I_mul _ _ (I_mul _ _
        (I_add _ _ I_one (I_mul _ _ (I_mul _ _ (I_pow _ _ IP) (I_pow _ _ IB)) (I_pow _ _ NearKilling)))
        (I_add _ _ I_one (I_mul _ _ (I_pow _ _ IP) (I_pow _ _ NearKilling)))) Ik23) Ik33) IE3)
  have IY' : ∀ i j, ‖Y'.1 i j‖ ≤ 1 := by
    rw [hY']
    exact I_add _ _ (I_add _ _
      (I_mul _ _ (I_mul _ _ (I_mul _ _ (I_mul _ _ (I_add _ _ IP (I_pow _ _ IU))
        (I_add _ _ (I_mul _ _ IP (I_pow _ _ IU)) (I_pow _ _ IB))) Ik41) Ik11) IE1)
      (I_mul _ _ (I_mul _ _ (I_mul _ _ (I_mul _ _ (I_add _ _ I_one (I_mul _ _ (I_pow _ _ IP) (I_pow _ _ IA2)))
        (I_add _ _ (I_pow _ _ IB) (I_mul _ _ (I_pow _ _ IP) (I_pow _ _ IA2)))) Ik42) Ik12) IE2))
      (I_mul _ _ (I_mul _ _ (I_mul _ _ (I_mul _ _ (I_add _ _ I_one (I_mul _ _ (I_pow _ _ IP) (I_pow _ _ NearKilling)))
        (I_add _ _ I_one (I_mul _ _ (I_mul _ _ IP (I_pow _ _ IB)) (I_pow _ _ NearKilling)))) Ik43) Ik13) IE3)
  have hX1v : (P + C ^ 2).1 = ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2 := by
    show P.1 + C.1 ^ 2 = _; rw [hPv, hCv]
  have hX2v : (P + C ^ 3).1 = ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3 := by
    show P.1 + C.1 ^ 3 = _; rw [hPv, hCv]
  have hX3v : (P * C ^ 2 + B ^ 2).1 = ϖ • c ^ 2 + b ^ 2 := by
    show P.1 * C.1 ^ 2 + B.1 ^ 2 = _; rw [hPv, hCv, hBv, Matrix.smul_mul, Matrix.one_mul]
  have hX4v : (P * C ^ 3 + B ^ 3).1 = ϖ • c ^ 3 + b ^ 3 := by
    show P.1 * C.1 ^ 3 + B.1 ^ 3 = _; rw [hPv, hCv, hBv, Matrix.smul_mul, Matrix.one_mul]
  have u1 := isU _ _ hX1
  have u2 := isU _ _ hX2
  have u3 := isU _ _ hX3
  have u4 := isU _ _ hX4
  rw [hX1v] at u1; rw [hX2v] at u2; rw [hX3v] at u3; rw [hX4v] at u4
  have hdet23 : IsUnit ((P + C ^ 3).1 * (P * C ^ 2 + B ^ 2).1).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 ((isU _ _ hX2).mul (isU _ _ hX3))
  have hQv : (P * C ^ 3 + B ^ 3).1 * (P + C ^ 2).1 = Y.1 * ((P + C ^ 3).1 * (P * C ^ 2 + B ^ 2).1) :=
    congrArg Subtype.val hQ
  have Qm : (ϖ • c ^ 3 + b ^ 3) * (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) *
      ((ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) * (ϖ • c ^ 2 + b ^ 2))⁻¹ = Y.1 := by
    rw [← hX1v, ← hX2v, ← hX3v, ← hX4v, hQv, Matrix.mul_nonsing_inv_cancel_right _ _ hdet23]
  have hYYv : Y.1 * Y'.1 = 1 := congrArg Subtype.val hYY
  have hdY : ‖Y.1.det‖ = 1 := by
    have h1 := GlobalTheory.norm_det_le_one_of_entries_le_one E n Y.1 IY
    have h2 := GlobalTheory.norm_det_le_one_of_entries_le_one E n Y'.1 IY'
    have h3 : ‖Y.1.det‖ * ‖Y'.1.det‖ = 1 := by
      rw [← norm_mul, ← Matrix.det_mul, hYYv, Matrix.det_one, norm_one]
    exact eq_one_of_mul_eq_one (norm_nonneg _) (norm_nonneg _) h1 h2 h3
  exact ⟨u1, u2, u3, u4, by rw [Qm]; exact IY, by rw [Qm]; exact hdY⟩

end GlobalTheory.UnitDiscAlg.QuotAlg
