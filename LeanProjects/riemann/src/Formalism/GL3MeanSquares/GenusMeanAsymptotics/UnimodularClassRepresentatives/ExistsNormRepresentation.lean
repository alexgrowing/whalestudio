import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomFrame
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AddMulInvMem

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.U0

open WA

variable {K : Type*} [Field K] [StarRing K]

def Dv (S : Subring K) (π a : K) : Prop := a * π⁻¹ ∈ S

structure IsUnif (S : Subring K) (π : K) : Prop where
  mem : π ∈ S
  fix : star π = π
  ne : π ≠ 0
  unit_or : ∀ s ∈ S, star s = s → IsUnitIn S s ∨ Dv S π s
  rad : ∀ s ∈ S, IsUnitIn S (1 + π * s)

variable {S : Subring K} {π : K}

theorem unit_mul {a b : K} (ha : IsUnitIn S a) (hb : IsUnitIn S b) : IsUnitIn S (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, S.mul_mem ha.2.1 hb.2.1, by
    rw [mul_inv]; exact S.mul_mem ha.2.2 hb.2.2⟩

theorem unit_inv {a : K} (ha : IsUnitIn S a) : IsUnitIn S a⁻¹ :=
  ⟨inv_ne_zero ha.1, ha.2.2, by rw [inv_inv]; exact ha.2.1⟩

theorem unit_star (hS : IsHermSemilocal S) {a : K} (ha : IsUnitIn S a) :
    IsUnitIn S (star a) :=
  ⟨star_ne_zero.mpr ha.1, hS.star_mem _ ha.2.1, by
    rw [← star_inv₀]; exact hS.star_mem _ ha.2.2⟩

theorem isUnitIn_one : IsUnitIn S (1 : K) := ⟨one_ne_zero, S.one_mem, by simp [S.one_mem]⟩

theorem isUnitIn_of_mul {a b : K} (ha : a ∈ S) (hb : b ∈ S) (hab : IsUnitIn S (a * b)) :
    IsUnitIn S b := by
  have hb0 : b ≠ 0 := right_ne_zero_of_mul hab.1
  have ha0 : a ≠ 0 := left_ne_zero_of_mul hab.1
  refine ⟨hb0, hb, ?_⟩
  have : b⁻¹ = a * (a * b)⁻¹ := by field_simp
  rw [this]
  exact S.mul_mem ha hab.2.2

theorem Dv.mem (hπ : IsUnif S π) {a : K} (ha : Dv S π a) : a ∈ S := by
  have : a = a * π⁻¹ * π := by field_simp [hπ.ne]
  rw [this]
  exact S.mul_mem ha hπ.mem

theorem Dv.add {a b : K} (ha : Dv S π a) (hb : Dv S π b) : Dv S π (a + b) := by
  first | exact GlobalTheory.AddMulInvMembership.add_mul_inv_mem .. | (apply GlobalTheory.AddMulInvMembership.add_mul_inv_mem <;> assumption) | (intros; apply GlobalTheory.AddMulInvMembership.add_mul_inv_mem <;> assumption) | (apply @GlobalTheory.AddMulInvMembership.add_mul_inv_mem <;> assumption) | (intros; apply @GlobalTheory.AddMulInvMembership.add_mul_inv_mem <;> assumption) | (apply @GlobalTheory.AddMulInvMembership.add_mul_inv_mem <;> first | assumption | infer_instance) | exact @GlobalTheory.AddMulInvMembership.add_mul_inv_mem K ‹_› ‹_› S π a b ha hb | exact @GlobalTheory.AddMulInvMembership.add_mul_inv_mem K ‹_› ‹_› S π a b ha | exact @GlobalTheory.AddMulInvMembership.add_mul_inv_mem K ‹_› ‹_› S π a b | exact @GlobalTheory.AddMulInvMembership.add_mul_inv_mem K ‹_› ‹_› S π a | exact @GlobalTheory.AddMulInvMembership.add_mul_inv_mem K ‹_› ‹_› S π | exact @GlobalTheory.AddMulInvMembership.add_mul_inv_mem K ‹_› ‹_› S | exact @GlobalTheory.AddMulInvMembership.add_mul_inv_mem K ‹_› ‹_› | exact @GlobalTheory.AddMulInvMembership.add_mul_inv_mem K ‹_› | exact @GlobalTheory.AddMulInvMembership.add_mul_inv_mem K

theorem Dv.neg {a : K} (ha : Dv S π a) : Dv S π (-a) := by
  unfold Dv
  rw [neg_mul]
  exact S.neg_mem ha

theorem Dv.sub {a b : K} (ha : Dv S π a) (hb : Dv S π b) : Dv S π (a - b) := by
  rw [sub_eq_add_neg]
  exact ha.add hb.neg

theorem Dv.mul_left {a : K} (ha : Dv S π a) {s : K} (hs : s ∈ S) : Dv S π (s * a) := by
  unfold Dv
  rw [mul_assoc]
  exact S.mul_mem hs ha

theorem Dv.mul_right {a : K} (ha : Dv S π a) {s : K} (hs : s ∈ S) : Dv S π (a * s) := by
  rw [mul_comm]
  exact ha.mul_left hs

theorem Dv.star (hS : IsHermSemilocal S) (hπ : IsUnif S π) {a : K} (ha : Dv S π a) :
    Dv S π (star a) := by
  have := hS.star_mem _ ha
  rw [star_mul', star_inv₀, hπ.fix] at this
  exact this

theorem dv_self_mul (hπ : IsUnif S π) {s : K} (hs : s ∈ S) : Dv S π (π * s) := by
  unfold Dv
  have : π * s * π⁻¹ = s := by field_simp [hπ.ne]
  rw [this]
  exact hs

theorem Dv.eq (hπ : IsUnif S π) {a : K} (ha : Dv S π a) : ∃ r ∈ S, a = π * r :=
  ⟨a * π⁻¹, ha, by field_simp [hπ.ne]⟩

theorem unit_add_dv (hπ : IsUnif S π) {s t : K} (hs : IsUnitIn S s) (ht : Dv S π t) :
    IsUnitIn S (s + t) := by
  obtain ⟨r, hr, rfl⟩ := ht.eq hπ
  have : s + π * r = s * (1 + π * (r * s⁻¹)) := by
    have := hs.1
    field_simp
  rw [this]
  exact unit_mul hs (hπ.rad _ (S.mul_mem hr hs.2.2))

theorem unit_not_dv (hπ : IsUnif S π) {s : K} (hs : IsUnitIn S s) : ¬ Dv S π s := by
  intro h
  have := (unit_add_dv hπ hs h.neg).1
  simp at this

theorem dv_of_not_unit (hπ : IsUnif S π) {s : K} (hs : s ∈ S) (hf : star s = s)
    (hn : ¬ IsUnitIn S s) : Dv S π s :=
  (hπ.unit_or s hs hf).resolve_left hn

theorem unit_of_not_dv (hπ : IsUnif S π) {s : K} (hs : s ∈ S) (hf : star s = s)
    (hn : ¬ Dv S π s) : IsUnitIn S s :=
  (hπ.unit_or s hs hf).resolve_right hn

theorem star_norm (a : K) : star (star a * a) = star a * a := by
  rw [star_mul', star_star, mul_comm]

theorem dv_norm_of_not_unit (hS : IsHermSemilocal S) (hπ : IsUnif S π) {a : K} (ha : a ∈ S)
    (hn : ¬ IsUnitIn S a) : Dv S π (star a * a) :=
  dv_of_not_unit hπ (S.mul_mem (hS.star_mem _ ha) ha) (star_norm a)
    fun h => hn (isUnitIn_of_mul (hS.star_mem _ ha) ha h)

theorem exists_trace_mul (hS : IsHermSemilocal S) (hπ : IsUnif S π) {σ : K} (hσ : σ ∈ S)
    (hn : ¬ Dv S π σ) {τ : K} (hτ : τ ∈ S) (hτf : star τ = τ) :
    ∃ s ∈ S, σ * s + star (σ * s) = τ := by
  obtain ⟨θ, hθ, hμ⟩ := hS.unram
  have key : ∀ t ∈ S, IsUnitIn S (σ * t + star (σ * t)) → ∃ s ∈ S, σ * s + star (σ * s) = τ := by
    intro t ht hu
    have hf : star (σ * t + star (σ * t)) = σ * t + star (σ * t) := by
      rw [star_add, star_star, add_comm]
    refine ⟨t * (τ * (σ * t + star (σ * t))⁻¹), S.mul_mem ht (S.mul_mem hτ hu.2.2), ?_⟩
    have e : star (σ * (t * (τ * (σ * t + star (σ * t))⁻¹))) =
        star (σ * t) * (τ * (σ * t + star (σ * t))⁻¹) := by
      rw [← mul_assoc, star_mul', star_mul' τ, star_inv₀, hf, hτf]
    rw [e]
    have := hu.1
    field_simp
  by_cases h1 : Dv S π (σ * 1 + star (σ * 1))
  · by_cases h2 : Dv S π (σ * θ + star (σ * θ))
    · exfalso
      apply hn
      have e : σ = ((σ * θ + star (σ * θ)) - star θ * (σ * 1 + star (σ * 1))) * (θ - star θ)⁻¹ := by
        have := hμ.1
        rw [eq_mul_inv_iff_mul_eq₀ this]
        simp only [star_mul', mul_one]
        ring
      rw [e]
      exact (h2.sub (h1.mul_left (hS.star_mem _ hθ))).mul_right hμ.2.2
    · refine key θ hθ (unit_of_not_dv hπ ?_ ?_ h2)
      · exact S.add_mem (S.mul_mem hσ hθ) (hS.star_mem _ (S.mul_mem hσ hθ))
      · rw [star_add, star_star, add_comm]
  · refine key 1 S.one_mem (unit_of_not_dv hπ ?_ ?_ h1)
    · exact S.add_mem (S.mul_mem hσ S.one_mem) (hS.star_mem _ (S.mul_mem hσ S.one_mem))
    · rw [star_add, star_star, add_comm]

theorem dv_of_dv_mul (hS : IsHermSemilocal S) (hπ : IsUnif S π) {a c : K} (hc : c ∈ S)
    (hn : ¬ Dv S π c) (h1 : Dv S π (a * c)) (h2 : Dv S π (star a * c)) : Dv S π a := by
  obtain ⟨s, hs, hs1⟩ := exists_trace_mul hS hπ hc hn S.one_mem (star_one K)
  have e : a = a * c * s + star (star a * c) * star s := by
    calc a = a * (c * s + star (c * s)) := by rw [hs1, mul_one]
      _ = _ := by simp only [star_mul', star_star]; ring
  rw [e]
  exact (h1.mul_right hs).add ((h2.star hS hπ).mul_right (hS.star_mem _ hs))

variable {V : Type*} [AddCommGroup V] [Module K V]

theorem norm_formula {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {y w : V} {a u ρ : K}
    (hy : h y y = star a * a * u) (hu : star u = u)
    (hρ : ρ * (h w y - u * a) + star (ρ * (h w y - u * a)) = u - h w w) :
    h (ρ • y + w) (ρ • y + w) = u * (star (1 + ρ * a) * (1 + ρ * a)) := by
  have hyw : h y w = star (h w y) := (hs.eq w y).symm
  simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hy, hyw,
    starRingEnd_apply, RingHom.id_apply]
  simp only [star_mul', star_sub, hu, star_add, star_one] at hρ ⊢
  linear_combination hρ

theorem exists_unit_norm (hS : IsHermSemilocal S) (hπ : IsUnif S π) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) {M : AddSubgroup V} (hM : ∀ a ∈ S, ∀ m ∈ M, a • m ∈ M)
    (hint : ∀ x ∈ M, ∀ y ∈ M, h x y ∈ S) {y w : V} (hy : y ∈ M) (hw : w ∈ M)
    (hn : ¬ Dv S π (h w y)) : ∃ x ∈ M, IsUnitIn S (h x x) := by
  by_cases h1 : IsUnitIn S (h y y)
  · exact ⟨y, hy, h1⟩
  by_cases h2 : IsUnitIn S (h w w)
  · exact ⟨w, hw, h2⟩
  have d1 := dv_of_not_unit hπ (hint y hy y hy) (hs.eq y y) h1
  have d2 := dv_of_not_unit hπ (hint w hw w hw) (hs.eq w w) h2
  obtain ⟨s, hsS, hs1⟩ := exists_trace_mul hS hπ (hint w hw y hy) hn S.one_mem (star_one K)
  refine ⟨s • y + w, M.add_mem (hM s hsS y hy) hw, ?_⟩
  have hyw : h y w = star (h w y) := (hs.eq w y).symm
  have e : h (s • y + w) (s • y + w) = 1 + (star s * s * h y y + h w w) := by
    simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hyw,
      starRingEnd_apply, RingHom.id_apply]
    simp only [star_mul'] at hs1
    linear_combination hs1
  rw [e]
  exact unit_add_dv hπ isUnitIn_one
    ((d1.mul_left (S.mul_mem (hS.star_mem _ hsS) hsS)).add d2)

theorem exists_norm_representation (hS : IsHermSemilocal S) (hπ : IsUnif S π) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) {M : AddSubgroup V} (hM : ∀ a ∈ S, ∀ m ∈ M, a • m ∈ M)
    (hint : ∀ x ∈ M, ∀ y ∈ M, h x y ∈ S) {y w : V} (hy : y ∈ M) (hw : w ∈ M) {a u ρ₀ : K}
    (ha : a ∈ S) (hu : IsUnitIn S u) (huf : star u = u) (hyy : h y y = star a * a * u)
    (hρ₀ : ρ₀ ∈ S) (h1 : Dv S π (ρ₀ * a)) (h2 : ¬ Dv S π (ρ₀ * h w y)) :
    ∃ X ∈ M, h X X = u := by
  have hσ : ρ₀ * (h w y - u * a) ∈ S :=
    S.mul_mem hρ₀ (S.sub_mem (hint w hw y hy) (S.mul_mem hu.2.1 ha))
  have hσn : ¬ Dv S π (ρ₀ * (h w y - u * a)) := by
    intro hd
    apply h2
    have e : ρ₀ * h w y = ρ₀ * (h w y - u * a) + u * (ρ₀ * a) := by ring
    rw [e]
    exact hd.add (h1.mul_left hu.2.1)
  obtain ⟨s, hsS, hs1⟩ := exists_trace_mul hS hπ hσ hσn
    (S.sub_mem hu.2.1 (hint w hw w hw)) (by rw [star_sub, huf, show star (h w w) = h w w from hs.eq w w])
  have hf := norm_formula hs (ρ := ρ₀ * s) hyy huf (by
    rw [← hs1]
    congr 1
    · ring
    · congr 1; ring)
  have hun : IsUnitIn S (1 + ρ₀ * s * a) := by
    have e : ρ₀ * s * a = ρ₀ * a * s := by ring
    rw [e]
    exact unit_add_dv hπ isUnitIn_one (h1.mul_right hsS)
  refine ⟨(1 + ρ₀ * s * a)⁻¹ • ((ρ₀ * s) • y + w),
    hM _ hun.2.2 _ (M.add_mem (hM _ (S.mul_mem hρ₀ hsS) y hy) hw), ?_⟩
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, RingHom.id_apply, hf]
  have h0 := hun.1
  have h0' : star (1 + ρ₀ * s * a) ≠ 0 := star_ne_zero.mpr h0
  rw [star_inv₀]
  field_simp

theorem exists_norm_of_not_dv (hS : IsHermSemilocal S) (hπ : IsUnif S π)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {M : AddSubgroup V}
    (hM : ∀ a ∈ S, ∀ m ∈ M, a • m ∈ M) (hint : ∀ x ∈ M, ∀ y ∈ M, h x y ∈ S) {y w : V}
    (hy : y ∈ M) (hw : w ∈ M) {a u : K} (ha : a ∈ S) (hu : IsUnitIn S u) (huf : star u = u)
    (hyy : h y y = star a * a * u) (hn : ¬ Dv S π (h w y)) : ∃ X ∈ M, h X X = u := by
  by_cases hau : IsUnitIn S a
  · refine ⟨a⁻¹ • y, hM _ hau.2.2 y hy, ?_⟩
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, RingHom.id_apply,
      hyy]
    have h0 := hau.1
    have h0' : star a ≠ 0 := star_ne_zero.mpr h0
    rw [star_inv₀]
    field_simp
  have hN := dv_norm_of_not_unit hS hπ ha hau
  by_cases h1 : Dv S π (a * h w y)
  · by_cases h2 : Dv S π (star a * h w y)
    · have hda := dv_of_dv_mul hS hπ (hint w hw y hy) hn h1 h2
      exact exists_norm_representation hS hπ hs hM hint hy hw ha hu huf hyy S.one_mem
        (by rwa [one_mul]) (by rwa [one_mul])
    · exact exists_norm_representation hS hπ hs hM hint hy hw ha hu huf hyy (hS.star_mem _ ha) hN h2
  · exact exists_norm_representation hS hπ hs hM hint hy hw (hS.star_mem _ ha) hu huf
      (by rw [hyy, star_star]; ring) ha (by rwa [mul_comm]) h1

theorem exists_norm_of_orth (hS : IsHermSemilocal S) (hπ : IsUnif S π)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {M : AddSubgroup V}
    (hM : ∀ a ∈ S, ∀ m ∈ M, a • m ∈ M) {y w : V}
    (hy : y ∈ M) (hw : w ∈ M) {a u : K} (ha : a ∈ S) (hu : IsUnitIn S u) (huf : star u = u)
    (hyy : h y y = star a * a * u) (hna : ¬ Dv S π a) (hN : Dv S π (star a * a))
    (hwy : h w y = 0) (hww : IsUnitIn S (h w w)) : ∃ X ∈ M, h X X = u := by
  have hσn : ¬ Dv S π (-(u * a)) := by
    intro hd
    apply hna
    have e : a = -(u * a) * (-u⁻¹) := by
      have := hu.1
      field_simp
    rw [e]
    exact hd.mul_right (S.neg_mem hu.2.2)
  obtain ⟨ρ, hρS, hρ⟩ := exists_trace_mul hS hπ (S.neg_mem (S.mul_mem hu.2.1 ha)) hσn
    (S.sub_mem hu.2.1 hww.2.1) (by rw [star_sub, huf, show star (h w w) = h w w from hs.eq w w])
  have hf := norm_formula hs (ρ := ρ) hyy huf (by
    rw [← hρ, hwy, zero_sub, mul_comm])
  have hNu : IsUnitIn S (star (1 + ρ * a) * (1 + ρ * a)) := by
    have e : star (1 + ρ * a) * (1 + ρ * a) = h w w * u⁻¹ + star ρ * ρ * (star a * a) := by
      have h0 := hu.1
      have e2 : u * (star (1 + ρ * a) * (1 + ρ * a)) =
          u * (h w w * u⁻¹ + star ρ * ρ * (star a * a)) := by
        have e3 : u * (h w w * u⁻¹) = h w w := by field_simp
        rw [mul_add u (h w w * u⁻¹), e3]
        simp only [star_mul', star_neg, huf, star_add, star_one] at hρ ⊢
        linear_combination -hρ
      exact mul_left_cancel₀ h0 e2
    rw [e]
    exact unit_add_dv hπ (unit_mul hww (unit_inv hu))
      (hN.mul_left (S.mul_mem (hS.star_mem _ hρS) hρS))
  have h1S : 1 + ρ * a ∈ S := S.add_mem S.one_mem (S.mul_mem hρS ha)
  have hun := isUnitIn_of_mul (hS.star_mem _ h1S) h1S hNu
  refine ⟨(1 + ρ * a)⁻¹ • (ρ • y + w), hM _ hun.2.2 _ (M.add_mem (hM _ hρS y hy) hw), ?_⟩
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, RingHom.id_apply, hf]
  have h0 := hun.1
  have h0' : star (1 + ρ * a) ≠ 0 := star_ne_zero.mpr h0
  rw [star_inv₀]
  field_simp

end Formalism.HermitianLattices.Ext.L3.U0
