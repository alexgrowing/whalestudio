import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExcisionNbhdAdjoinRootStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdTransStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdAwayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosedStatement
open GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem unit_eq_mul_qth_power_near_zeroLocus : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A₂ : Type) [CommRing A₂] [Algebra B A₂], IsExcisionNbhd B A₂ f → ∀ c : (Localization.Away (algebraMap B A₂ f))ˣ, ∀ (b₁ : B) (m : ℕ) (e : A₂), e - 1 ∈ Ideal.span {algebraMap B A₂ f} → algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ b₁) = (c : Localization.Away (algebraMap B A₂ f)) * algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (e * algebraMap B A₂ f ^ m) → ∀ g : B, IsCoprime f g → ∀ (u : (Localization.Away (f * g))ˣ) (n d : B), IsCoprime f n → IsCoprime f d → algebraMap B (Localization.Away (f * g)) (b₁ * d) = (u : Localization.Away (f * g)) * algebraMap B (Localization.Away (f * g)) (n * f ^ m) → ∃ (A₃ : Type) (_ : CommRing A₃) (_ : Algebra B A₃) (_ : Algebra A₂ A₃) (_ : IsScalarTower B A₂ A₃), IsExcisionNbhd B A₃ f ∧ IsUnit (algebraMap B A₃ g) ∧ ∃ v : (Localization.Away (algebraMap B A₃ f))ˣ, ∀ (φ : Localization.Away (algebraMap B A₂ f) →+* Localization.Away (algebraMap B A₃ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₃ f)), φ.comp (algebraMap A₂ _) = (algebraMap A₃ _).comp (algebraMap A₂ A₃) → ψ.comp (algebraMap B _) = (algebraMap A₃ _).comp (algebraMap B A₃) → φ (c : Localization.Away (algebraMap B A₂ f)) = ψ (u : Localization.Away (f * g)) * (v : Localization.Away (algebraMap B A₃ f)) ^ q := by
  intro k B _ _ _ _ _ _ q hq f hf A₂ _ _ hA₂ c b₁ m e he hc g hg u n d hn hd hu
  have hq0 : q ≠ 0 := by
    rintro rfl; simp at hq
  obtain ⟨j, rfl⟩ : ∃ j, q = j + 1 := ⟨q - 1, by omega⟩
  obtain ⟨x₁, y₁, hxy₁⟩ := (hg.mul_right hn).mul_right hd
  obtain ⟨a, ha⟩ : ∃ a : A₂, a = algebraMap B A₂ (g * n * d) * e := ⟨_, rfl⟩
  have hab : a * algebraMap B A₂ y₁ - 1 ∈ Ideal.span {algebraMap B A₂ f} := by
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp he
    have h1 := congrArg (algebraMap B A₂) hxy₁
    simp only [map_add, map_mul, map_one] at h1
    rw [Ideal.mem_span_singleton, ha]
    refine ⟨-(algebraMap B A₂ x₁) * e + t, ?_⟩
    simp only [map_mul]
    linear_combination e * h1 + ht
  have hA₂' : IsExcisionNbhd B (Localization.Away a) f := GlobalTheory.T.isExcisionNbhd_away_of_inverse_mod B A₂ f hA₂ a (algebraMap B A₂ y₁) hab
  have hdvd : ∀ z : A₂, z ∣ a → IsUnit (algebraMap A₂ (Localization.Away a) z) := fun z hz =>
    isUnit_of_dvd_unit (map_dvd _ hz) (IsLocalization.Away.algebraMap_isUnit a)
  have hgu := hdvd (algebraMap B A₂ g) ⟨algebraMap B A₂ n * algebraMap B A₂ d * e, by rw [ha]; simp only [map_mul]; ring⟩
  have hnu := hdvd (algebraMap B A₂ n) ⟨algebraMap B A₂ g * algebraMap B A₂ d * e, by rw [ha]; simp only [map_mul]; ring⟩
  have hdu := hdvd (algebraMap B A₂ d) ⟨algebraMap B A₂ g * algebraMap B A₂ n * e, by rw [ha]; simp only [map_mul]; ring⟩
  have heu := hdvd e ⟨algebraMap B A₂ (g * n * d), by rw [ha]; ring⟩
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀ : A₂, ε₀ = algebraMap B A₂ n * (algebraMap B A₂ d * e) ^ j := ⟨_, rfl⟩
  have hεu : IsUnit (algebraMap A₂ (Localization.Away a) ε₀) := by
    rw [hε₀, map_mul, map_pow, map_mul]; exact hnu.mul ((hdu.mul heu).pow j)
  obtain ⟨x₂, y₂, h₂⟩ := hn.mul_right (hd.pow_right (n := j))
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_pow_sub_mem_span_of_isUnit_mod k B (j + 1) hq f hf (n * d ^ j) y₂
    (Ideal.mem_span_singleton.mpr ⟨-x₂, by linear_combination h₂⟩)
  have hcong : ε₀ - algebraMap B A₂ r ^ (j + 1) ∈ Ideal.span {algebraMap B A₂ f} := by
    have h1 : algebraMap B A₂ f ∣ algebraMap B A₂ (n * d ^ j - r ^ (j + 1)) :=
      map_dvd _ (Ideal.mem_span_singleton.mp hr)
    have h2 : algebraMap B A₂ f ∣ e ^ j - 1 :=
      (Ideal.mem_span_singleton.mp he).trans (by simpa using sub_dvd_pow_sub_pow e 1 j)
    have h3 : ε₀ - algebraMap B A₂ r ^ (j + 1) = algebraMap B A₂ (n * d ^ j - r ^ (j + 1)) +
        algebraMap B A₂ n * algebraMap B A₂ d ^ j * (e ^ j - 1) := by
      rw [hε₀]; simp only [map_sub, map_mul, map_pow]; ring
    rw [Ideal.mem_span_singleton, h3]; exact dvd_add h1 (dvd_mul_of_dvd_right h2 _)
  have hcong' : algebraMap A₂ (Localization.Away a) ε₀ - algebraMap B (Localization.Away a) r ^ (j + 1) ∈
      Ideal.span {algebraMap B (Localization.Away a) f} := by
    rw [IsScalarTower.algebraMap_apply B A₂ (Localization.Away a) r,
      IsScalarTower.algebraMap_apply B A₂ (Localization.Away a) f, ← map_pow, ← map_sub,
      Ideal.mem_span_singleton]
    exact map_dvd _ (Ideal.mem_span_singleton.mp hcong)
  have hqu : IsUnit ((j + 1 : ℕ) : Localization.Away a) := by
    have := hq.map ((algebraMap B (Localization.Away a)).comp (algebraMap k B)); rwa [map_natCast] at this
  obtain ⟨A₃, _, _, hA₃, x, hx⟩ := GlobalTheory.T.exists_excisionNbhd_with_root_of_isUnit (Localization.Away a) (algebraMap B (Localization.Away a) f)
    (j + 1) hqu _ _ hεu hcong'
  letI : Algebra B A₃ := RingHom.toAlgebra ((algebraMap (Localization.Away a) A₃).comp (algebraMap B (Localization.Away a)))
  letI : Algebra A₂ A₃ := RingHom.toAlgebra ((algebraMap (Localization.Away a) A₃).comp (algebraMap A₂ (Localization.Away a)))
  haveI t1 : IsScalarTower B (Localization.Away a) A₃ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI t3 : IsScalarTower B A₂ A₃ := IsScalarTower.of_algebraMap_eq (fun z => by
    show algebraMap (Localization.Away a) A₃ (algebraMap B (Localization.Away a) z) =
      algebraMap (Localization.Away a) A₃ (algebraMap A₂ (Localization.Away a) (algebraMap B A₂ z))
    rw [IsScalarTower.algebraMap_apply B A₂ (Localization.Away a) z])
  refine ⟨A₃, inferInstance, inferInstance, inferInstance, t3, GlobalTheory.T.isExcisionNbhd_trans' B (Localization.Away a) A₃ f hA₂' hA₃, ?_, ?_⟩
  · have : algebraMap B A₃ g = algebraMap (Localization.Away a) A₃
        (algebraMap A₂ (Localization.Away a) (algebraMap B A₂ g)) := by
      rw [← IsScalarTower.algebraMap_apply B A₂ (Localization.Away a)]; rfl
    rw [this]; exact hgu.map _
  have hDu : IsUnit (algebraMap A₃ (Localization.Away (algebraMap B A₃ f))
      (algebraMap A₂ A₃ (algebraMap B A₂ d * e))) := by
    have hde : IsUnit (algebraMap A₂ (Localization.Away a) (algebraMap B A₂ d * e)) := by
      rw [map_mul]; exact hdu.mul heu
    exact (hde.map (algebraMap (Localization.Away a) A₃)).map _
  have hX : algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) x ^ (j + 1) =
      algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ n)) *
      (algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ d)) *
       algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ e)) ^ j := by
    rw [← map_pow, ← hx]
    show algebraMap A₃ _ (algebraMap A₂ A₃ ε₀) = _
    rw [hε₀]; simp only [map_mul, map_pow]
  have hXu : IsUnit (algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) x) :=
    (isUnit_pow_iff (Nat.succ_ne_zero j)).mp (by rw [← map_pow, ← hx]; exact (hεu.map _).map _)
  have hFu : IsUnit (algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ f))) := by
    rw [← IsScalarTower.algebraMap_apply B A₂ A₃]; exact IsLocalization.Away.algebraMap_isUnit _
  refine ⟨hXu.unit * hDu.unit⁻¹, fun φ ψ hφ hψ => ?_⟩
  have hφ' : ∀ y, φ (algebraMap A₂ _ y) = algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ y) :=
    fun y => RingHom.congr_fun hφ y
  have hψ' : ∀ z, ψ (algebraMap B _ z) =
      algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ z)) := fun z => by
    have := RingHom.congr_fun hψ z
    simp only [RingHom.comp_apply] at this
    rw [this, IsScalarTower.algebraMap_apply B A₂ A₃ z]
  have H1 := congrArg φ hc
  have H2 := congrArg ψ hu
  simp only [map_mul, map_pow, hφ'] at H1
  simp only [map_mul, map_pow, hψ'] at H2
  have hW := hDu.mul_val_inv
  rw [Units.val_mul, IsUnit.unit_spec]
  generalize (↑hDu.unit⁻¹ : Localization.Away (algebraMap B A₃ f)) = W at hW ⊢
  simp only [map_mul] at hW hFu
  have key0 : φ c * algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ d)) *
      algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ e) =
      ψ u * algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ n)) := by
    apply (hFu.pow m).mul_right_cancel
    linear_combination -(algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ d))) * H1 + H2
  calc φ c = φ c * (algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ d)) *
        algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ e) * W) ^ (j + 1) := by
        rw [hW, one_pow, mul_one]
    _ = _ := by
      linear_combination (algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ d)) *
        algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ e)) ^ j * W ^ (j + 1) * key0 -
        ψ u * W ^ (j + 1) * hX

end GlobalTheory.EtC
