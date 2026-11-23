import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
namespace GlobalTheory.WittHyperbolicPairing

variable {E : Type} [Field E] {n : ℕ}

def hp (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (a b : Matrix (Fin n) (Fin 1) E) : E :=
  (Formalism.UG.cT σ a * J * b) 0 0

theorem hp_iff (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (a b : Matrix (Fin n) (Fin 1) E) :
    Formalism.UG.cT σ a * J * b = 0 ↔ hp σ J a b = 0 := by
  constructor
  · intro h; simp [hp, h]
  · intro h; ext i j
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simpa [hp] using h

theorem cT_add' (σ : E →+* E) (a a' : Matrix (Fin n) (Fin 1) E) :
    Formalism.UG.cT σ (a + a') = Formalism.UG.cT σ a + Formalism.UG.cT σ a' := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_smul' (σ : E →+* E) (c : E) (a : Matrix (Fin n) (Fin 1) E) :
    Formalism.UG.cT σ (c • a) = σ c • Formalism.UG.cT σ a := by
  ext i j; simp [Formalism.UG.cT]

theorem hp_add_left (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (a a' b : Matrix (Fin n) (Fin 1) E) :
    hp σ J (a + a') b = hp σ J a b + hp σ J a' b := by
  simp [hp, cT_add', Matrix.add_mul]

theorem hp_add_right (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (a b b' : Matrix (Fin n) (Fin 1) E) :
    hp σ J a (b + b') = hp σ J a b + hp σ J a b' := by
  simp [hp, Matrix.mul_add]

theorem hp_smul_left (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (c : E) (a b : Matrix (Fin n) (Fin 1) E) :
    hp σ J (c • a) b = σ c * hp σ J a b := by
  simp [hp, cT_smul', Matrix.smul_mul]

theorem hp_smul_right (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (c : E) (a b : Matrix (Fin n) (Fin 1) E) :
    hp σ J a (c • b) = c * hp σ J a b := by
  simp [hp, Matrix.mul_smul]

theorem hp_eq (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (a b : Matrix (Fin n) (Fin 1) E) :
    hp σ J a b = ∑ j, ∑ i, σ (a i 0) * J i j * b j 0 := by
  simp [hp, Formalism.UG.cT, Matrix.mul_apply, Finset.sum_mul]

theorem hp_symm (σ : E →+* E) (hσ : ∀ c, σ (σ c) = c) (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (a b : Matrix (Fin n) (Fin 1) E) :
    σ (hp σ J a b) = hp σ J b a := by
  rw [hp_eq, hp_eq]
  simp only [map_sum, map_mul, hσ, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem exists_hp_ne (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (hdet : J.det ≠ 0)
    (x : Matrix (Fin n) (Fin 1) E) (hx : x ≠ 0) : ∃ y, hp σ J x y ≠ 0 := by
  by_contra hall
  push_neg at hall
  have hR : Formalism.UG.cT σ x * J = 0 := by
    ext i j
    obtain rfl : i = 0 := Subsingleton.elim _ _
    have := hall (Matrix.of fun k _ => if k = j then 1 else 0)
    simpa [hp, Matrix.mul_apply] using this
  have hc : Formalism.UG.cT σ x = 0 := by
    have hu : IsUnit J.det := isUnit_iff_ne_zero.mpr hdet
    have := congrArg (· * J⁻¹) hR
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu] using this
  apply hx
  ext i j
  obtain rfl : j = 0 := Subsingleton.elim _ _
  have := congrFun (congrFun hc 0) i
  simpa [Formalism.UG.cT] using this

end GlobalTheory.WittHyperbolicPairing

open GlobalTheory.WittHyperbolicPairing in
theorem GlobalTheory.exists_isotropic_vector_pairing_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ x₀ x : Matrix (Fin n) (Fin 1) E, x₀ ≠ 0 → x ≠ 0 → Formalism.UG.cT (σ : E →+* E) x₀ * J * x₀ = 0 →
        Formalism.UG.cT (σ : E →+* E) x₀ * J * x = 0 →
        ∃ u : Matrix (Fin n) (Fin 1) E, Formalism.UG.cT (σ : E →+* E) u * J * u = 0 ∧
          Formalism.UG.cT (σ : E →+* E) x₀ * J * u ≠ 0 ∧ Formalism.UG.cT (σ : E →+* E) u * J * x ≠ 0 := by
  intro F E _ _ _ _ _ σ hcm n J hJ x₀ x hx₀ hx h00 h0x
  have hσ : ∀ c, (σ : E →+* E) ((σ : E →+* E) c) = c := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    intro c
    apply τ.injective
    have h1 := hcm.2.2.2 τ (σ c)
    have h2 := hcm.2.2.2 τ c
    simp only [AlgHom.coe_toRingHom] at *
    rw [h1, h2, star_star]
  set s : E →+* E := (σ : E →+* E) with hs
  have hJ' : ∀ i j, s (J j i) = J i j := hJ.1
  rw [hp_iff] at h00 h0x
  obtain ⟨y₀, hy₀⟩ := exists_hp_ne s J hJ.2 x₀ hx₀
  obtain ⟨y, hy⟩ := exists_hp_ne s J hJ.2 x hx
  obtain ⟨v, hv0, hv⟩ : ∃ v, hp s J x₀ v ≠ 0 ∧ hp s J x v ≠ 0 := by
    by_cases h1 : hp s J x₀ y ≠ 0
    · exact ⟨y, h1, hy⟩
    by_cases h2 : hp s J x y₀ ≠ 0
    · exact ⟨y₀, hy₀, h2⟩
    push_neg at h1 h2
    exact ⟨y₀ + y, by rw [hp_add_right, h1, add_zero]; exact hy₀,
      by rw [hp_add_right, h2, zero_add]; exact hy⟩
  set b := hp s J x₀ v with hb
  set c := hp s J v v with hc
  set r : E := -c / (2 * b) with hr
  have hcs : s c = c := hp_symm s hσ J hJ' v v
  have hvx0 : hp s J v x₀ = s b := (hp_symm s hσ J hJ' x₀ v).symm
  have hx0x0 : hp s J x₀ x₀ = 0 := h00
  have hrb : r * b = -c / 2 := by rw [hr]; field_simp
  have e1 : s r * s b = -c / 2 := by rw [← map_mul, hrb, map_div₀, map_neg, hcs, map_ofNat]
  clear_value r c b
  refine ⟨v + s r • x₀, ?_, ?_, ?_⟩
  · rw [hp_iff, hp_add_left, hp_add_right, hp_add_right, hp_smul_left, hp_smul_left,
      hp_smul_right, hp_smul_right, hσ, hx0x0, hvx0, ← hb, ← hc]
    linear_combination e1 + hrb
  · rw [ne_eq, hp_iff, hp_add_right, hp_smul_right, hx0x0, mul_zero, add_zero, ← hb]; exact hv0
  · rw [ne_eq, hp_iff, hp_add_left, hp_smul_left, hσ, h0x, mul_zero, add_zero,
      ← hp_symm s hσ J hJ' x v]
    exact (map_ne_zero s).mpr hv
