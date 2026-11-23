import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal

namespace GlobalTheory.LocM.TorCheck

theorem ordGe_pow_iff {R : Type} [CommRing R] [IsDomain R] {u : R} (h0 : u ≠ 0) (hu : ¬ IsUnit u) (e a b n : ℕ) (i : ℚ) :
    OrdGe (u ^ e) i n (Ideal.span {u ^ a}) (Ideal.span {u ^ b}) ↔ i * ((a : ℚ) - b) ≤ e * n := by
  rw [ordGe_span_iff]
  simp only [← pow_mul, ← pow_add]
  rw [pow_dvd_pow_iff h0 hu]
  have hd : (0 : ℚ) < i.den := by exact_mod_cast i.den_pos
  have hi : i * i.den = i.num := Rat.mul_den_eq_num i
  have hn : ((i.num.toNat : ℤ) : ℚ) - (((-i.num).toNat : ℤ) : ℚ) = i.num := by
    exact_mod_cast Int.toNat_sub_toNat_neg i.num
  simp only [Int.cast_natCast] at hn
  rw [← Nat.cast_le (α := ℚ), ← mul_le_mul_iff_of_pos_right (b := i * ((a : ℚ) - b)) hd]
  push_cast
  have : i * ((a : ℚ) - b) * i.den = ((i.num.toNat : ℚ) - ((-i.num).toNat : ℚ)) * ((a : ℚ) - b) := by
    rw [hn, ← hi]; ring
  rw [this]
  constructor <;> intro h <;> linarith

variable {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]

theorem minVal_eval (B : X → X → ℝ) : (InvFun.minVal O).eval X B = sInf {x | (∃ y, B y y = x) ∧ x ≠ B 0 0} := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [InvFun.eval_eq _ hr]
  change sInf _ = _
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, map_zero]
  exact and_congr_left' ⟨fun ⟨y, h⟩ => ⟨r y, h⟩, fun ⟨y, h⟩ => (hr y).elim fun z e => ⟨z, e ▸ h⟩⟩

theorem minVal_linearOn (γ : LinearMap.BilinForm ℤ X) : (InvFun.minVal O).LinearOn ![γ] := by
  intro c hc
  simp only [Fin.sum_univ_one, Matrix.cons_val_zero, InvFun.evalZ, minVal_eval, map_zero, Int.cast_zero, mul_zero,
    LinearMap.zero_apply]
  rcases (hc 0).eq_or_lt with h | h
  · rw [← h]
    simp only [zero_mul]
    convert Real.sInf_empty
    exact Set.eq_empty_of_forall_notMem fun x ⟨⟨_, h⟩, h'⟩ => h' h.symm
  · rw [← smul_eq_mul (c 0) (sInf _), ← Real.sInf_smul_of_nonneg (hc 0)]
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨⟨y, rfl⟩, hx⟩
      exact ⟨_, ⟨⟨y, rfl⟩, fun e => hx (by rw [e, mul_zero])⟩, rfl⟩
    · rintro ⟨_, ⟨⟨y, rfl⟩, hx⟩, rfl⟩
      exact ⟨⟨y, rfl⟩, mul_ne_zero h.ne' hx⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)

theorem eq_zero_of_apply_self {β : LinearMap.BilinForm ℤ (𝓞 E)} (hβ : β ∈ levelForms H 1 (𝓞 E))
    (hp : ∀ y, 0 ≤ β y y) {y₀ : 𝓞 E} (hy : y₀ ≠ 0) (h : β y₀ y₀ = 0) (y : 𝓞 E) : β y y = 0 := by
  have h1 : ∀ z, β y₀ z = 0 := fun z => by
    by_contra hz
    have k := hp ((-(β z z + 1) * β y₀ z) • y₀ + z)
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h, hβ.1 z y₀] at k
    have : 1 ≤ β y₀ z * β y₀ z := mul_self_pos.2 hz
    have := hp z
    nlinarith
  obtain ⟨N, hN, c, hc⟩ : ∃ N : ℤ, N ≠ 0 ∧ ∃ c : 𝓞 E, c * y₀ = N := by
    have hI : Ideal.span {y₀} ≠ ⊥ := by simpa using hy
    refine ⟨(Ideal.absNorm (Ideal.span {y₀}) : ℕ), ?_, ?_⟩
    · exact_mod_cast fun e => hI (Ideal.absNorm_eq_zero_iff.1 e)
    · have := Ideal.absNorm_mem (Ideal.span {y₀})
      simpa using Ideal.mem_span_singleton'.1 this
  have h2 : β ((y * c) • y₀) y = 0 := by rw [hβ.2.1, h1]
  have e : (y * c) • y₀ = N • y := by rw [smul_eq_mul, mul_assoc, hc, zsmul_eq_mul, mul_comm]
  rw [e, map_smul, LinearMap.smul_apply, smul_eq_mul] at h2
  exact (mul_eq_zero.1 h2).resolve_left hN

theorem exists_isPiece (M : ℕ) (hM : M ≠ 0) :
    0 < (InvFun.minVal (𝓞 E)).evalZ ((M : ℤ) • HostModel.trForm H) ∧
    (InvFun.minVal (𝓞 E)).LinearOn ![(M : ℤ) • HostModel.trForm H] ∧
    ∃ ℓ, IsPiece H (InvFun.minVal (𝓞 E)) 1 ![(M : ℤ) • HostModel.trForm H] ℓ := by
  set γ := (M : ℤ) • HostModel.trForm H with hγ
  have pos : ∀ y : 𝓞 E, y ≠ 0 → 0 < γ y y := fun y hy =>
    mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hM) (HostModel.trForm_pos H hy)
  obtain ⟨y₀, hy₀, hmin⟩ : ∃ y₀ : 𝓞 E, y₀ ≠ 0 ∧ ∀ y, y ≠ 0 → γ y₀ y₀ ≤ γ y y := by
    obtain ⟨y₀, h0, h⟩ := (measure fun y : 𝓞 E => (γ y y).toNat).wf.has_min {y | y ≠ 0} ⟨1, one_ne_zero⟩
    refine ⟨y₀, h0, fun y hy => ?_⟩
    have h1 : ¬ (γ y y).toNat < (γ y₀ y₀).toNat := h y hy
    have := pos y hy
    have := pos y₀ h0
    omega
  have hv : (InvFun.minVal (𝓞 E)).evalZ γ = γ y₀ y₀ := by
    rw [InvFun.evalZ, minVal_eval]
    refine IsLeast.csInf_eq ⟨⟨⟨y₀, rfl⟩, ?_⟩, ?_⟩
    · simpa using (pos y₀ hy₀).ne'
    · rintro _ ⟨⟨y, rfl⟩, h⟩
      exact_mod_cast hmin y fun e => h (by rw [e])
  refine ⟨hv ▸ by exact_mod_cast pos y₀ hy₀, minVal_linearOn γ,
    (LinearMap.applyₗ y₀) ∘ₗ (LinearMap.applyₗ y₀), fun i => ?_, fun β hβ hp => ?_⟩
  · fin_cases i
    simp [hv]
  · simp only [Nat.cast_one, one_mul, LinearMap.comp_apply, LinearMap.applyₗ_apply_apply, InvFun.evalZ, minVal_eval]
    by_cases h : β y₀ y₀ = 0
    · rw [h]
      refine le_of_eq ?_
      rw [Int.cast_zero]
      convert Real.sInf_empty
      exact Set.eq_empty_of_forall_notMem fun x ⟨⟨y, e⟩, h'⟩ => h' (by
        rw [← e, eq_zero_of_apply_self H hβ hp hy₀ h y]; simp)
    · refine csInf_le ⟨0, ?_⟩ ⟨⟨y₀, rfl⟩, by simpa using h⟩
      rintro _ ⟨⟨y, rfl⟩, -⟩
      exact_mod_cast hp y

end GlobalTheory.LocM.TorCheck
