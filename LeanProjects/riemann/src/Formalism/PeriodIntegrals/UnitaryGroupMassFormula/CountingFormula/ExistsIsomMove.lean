import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.GmapLocEqOfFrame

open NumberField

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.UG

open Formalism.HermitianLattices.Ext.L3.WA

section Abs

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K} {M : AddSubgroup V}

theorem star_h (hs : h.IsSymm) (u v : V) : star (h u v) = h v u := by
  first | exact hs u v | exact hs.eq u v

theorem exists_pair (hS : IsHermSemilocal S) (hM : IsSelfDualMod S h M) {ι : Type} [Fintype ι]
    (x : ι → V) (hxo : ∀ i j, i ≠ j → h (x i) (x j) = 0) (hxu : ∀ i, IsUnitIn S (h (x i) (x i)))
    (hxM : ∀ i, x i ∈ M) {r : V} (hr : ∃ v, h v r ≠ 0) (hrx : ∀ i, h (x i) r = 0) :
    ∃ α : K, α ≠ 0 ∧ α⁻¹ • r ∈ M ∧ ∃ w ∈ M, h w (α⁻¹ • r) = 1 ∧ ∀ i, h (x i) w = 0 := by
  classical
  obtain ⟨v, hv⟩ := hr
  let A : AddSubgroup K :=
    { carrier := {a | ∃ m ∈ M, h m r = a}
      add_mem' := by
        rintro _ _ ⟨m, hm, rfl⟩ ⟨m', hm', rfl⟩
        exact ⟨m + m', M.add_mem hm hm', by simp⟩
      zero_mem' := ⟨0, M.zero_mem, by simp⟩
      neg_mem' := by
        rintro _ ⟨m, hm, rfl⟩
        exact ⟨-m, M.neg_mem hm, by simp⟩ }
  have h1 : ∀ s ∈ S, ∀ a ∈ A, s * a ∈ A := by
    rintro s hs _ ⟨m, hm, rfl⟩
    refine ⟨star s • m, hM.smul_mem _ (hS.star_mem s hs) m hm, ?_⟩
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
  have h2 : ∃ a ∈ A, a ≠ 0 := by
    obtain ⟨t, ht, htv⟩ := hM.span v
    refine ⟨h (t • v) r, ⟨_, htv, rfl⟩, ?_⟩
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
    exact mul_ne_zero (star_ne_zero.mpr ht) hv
  have h3 : ∃ t : K, t ≠ 0 ∧ ∀ a ∈ A, t * a ∈ S := by
    obtain ⟨t, ht, htr⟩ := hM.span r
    refine ⟨t, ht, ?_⟩
    rintro _ ⟨m, hm, rfl⟩
    have := hM.int m hm _ htr
    rwa [map_smul, smul_eq_mul] at this
  obtain ⟨α, ⟨m₀, hm₀, hα⟩, hα0, hαS⟩ := hS.principal A h1 h2 h3
  have hrM : α⁻¹ • r ∈ M := hM.dual _ fun m hm => by
    rw [map_smul, smul_eq_mul, mul_comm]
    exact hαS _ ⟨m, hm, rfl⟩
  refine ⟨α, hα0, hrM, m₀ - ∑ i, (h (x i) m₀ * (h (x i) (x i))⁻¹) • x i, ?_, ?_, ?_⟩
  · refine M.sub_mem hm₀ (M.sum_mem fun i _ => hM.smul_mem _ ?_ _ (hxM i))
    exact S.mul_mem (hM.int _ (hxM i) _ hm₀) (hxu i).2.2
  · simp only [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply,
      map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply, hrx, mul_zero,
      Finset.sum_const_zero, sub_zero]
    rw [hα, inv_mul_cancel₀ hα0]
  · intro j
    rw [map_sub, map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [Finset.sum_eq_single j (fun i _ hij => by rw [hxo j i (Ne.symm hij), mul_zero])
      (by simp), mul_assoc, inv_mul_cancel₀ (hxu j).1, mul_one, sub_self]

theorem isSymm_smul (hs : h.IsSymm) {u : K} (hus : star u = u) : (u⁻¹ • h).IsSymm := by
  have H : ∀ a b : V, star ((u⁻¹ • h) a b) = (u⁻¹ • h) b a := by
    intro a b
    simp only [LinearMap.smul_apply, smul_eq_mul, star_mul', star_inv₀, hus, star_h hs]
  first | exact H | exact ⟨H⟩

theorem exists_of_ref (hS : IsHermSemilocal S) (hs : h.IsSymm) (hM : IsSelfDualMod S h M) {ι : Type}
    [Fintype ι] (x : ι → V) (hxo : ∀ i j, i ≠ j → h (x i) (x j) = 0) (hxu : ∀ i, IsUnitIn S (h (x i) (x i)))
    (hxM : ∀ i, x i ∈ M) {r : V} {u : K} (hu : IsUnitIn S u) (hus : star u = u) (hrr : h r r = u)
    (hrx : ∀ i, h (x i) r = 0) :
    ∃ z ∈ M, h z z = u ∧ ∀ i, h (x i) z = 0 := by
  have hu0 : u ≠ 0 := hu.1
  obtain ⟨α, hα0, hαM, w, hwM, hw1, hwx⟩ :=
    exists_pair hS hM x hxo hxu hxM ⟨r, by rw [hrr]; exact hu0⟩ hrx
  have hyy : h (α⁻¹ • r) (α⁻¹ • r) = star α⁻¹ * α⁻¹ * u := by
    simp only [map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, starRingEnd_apply, hrr, RingHom.id_apply]
    ring
  have hsa : star α⁻¹ * α⁻¹ ∈ S := by
    have h1 := S.mul_mem (hM.int _ hαM _ hαM) hu.2.2
    rw [hyy, mul_assoc, mul_inv_cancel₀ hu0, mul_one] at h1
    exact h1
  obtain ⟨b, hb, hab⟩ := Formalism.HermitianLattices.Ext.L3.WA.exists_norm_one_mul_mem hS hsa
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hb
  have hs' := isSymm_smul hs hus
  have hyw0 : h (α⁻¹ • r) w = 1 := by rw [← star_h hs, hw1, star_one]
  have hy' : (u⁻¹ • h) (α⁻¹ • r) (α⁻¹ • r) = star (α⁻¹ * b) * (α⁻¹ * b) := by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, hyy, star_mul']
    rw [mul_comm u⁻¹, mul_assoc, mul_inv_cancel₀ hu0, mul_one]
    linear_combination (-(star α⁻¹ * α⁻¹)) * hb
  have hyw' : (u⁻¹ • h) (α⁻¹ • r) (u • w) = 1 := by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, map_smul, smul_eq_mul, hyw0, mul_one,
      inv_mul_cancel₀ hu0]
  have hww : (u⁻¹ • h) (u • w) (u • w) = u * h w w := by
    simp only [LinearMap.smul_apply, map_smulₛₗ, map_smul, smul_eq_mul, starRingEnd_apply, hus, RingHom.id_apply]
    field_simp
  obtain ⟨c, hc, d, hd, hcd⟩ := Formalism.HermitianLattices.Ext.L3.WA.exists_norm_one_of_pair hS hs'
    (y := α⁻¹ • r) (w := u • w) (a := α⁻¹ * b) hab (mul_ne_zero (inv_ne_zero hα0) hb0) hy' hyw'
    (hww ▸ S.mul_mem hu.2.1 (hM.int w hwM w hwM))
  refine ⟨c • (u • w) + d • (α⁻¹ • r),
    M.add_mem (hM.smul_mem c hc _ (hM.smul_mem u hu.2.1 w hwM)) (hM.smul_mem d hd _ hαM), ?_, ?_⟩
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul] at hcd
    exact ((inv_mul_eq_one₀ (inv_ne_zero hu0 |> fun _ => hu0)).1 hcd).symm
  · intro i
    simp [map_add, map_smul, hwx i, hrx i]

theorem exists_quasi (hs : h.IsSymm) (w : V) {a : K} (ha : a + star a = a * star a * h w w) :
    ∃ τ ∈ Formalism.HermitianLatticesTheory.isom h, ∀ v, τ v = v - (a * h w v) • w := by
  let f : K → V →ₗ[K] V := fun b =>
    { toFun := fun v => v - (b * h w v) • w
      map_add' := fun x y => by
        simp only [map_add, mul_add, add_smul]
        abel
      map_smul' := fun c x => by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply, smul_sub, smul_smul]
        rw [mul_left_comm] }
  have hf : ∀ b v, f b v = v - (b * h w v) • w := fun _ _ => rfl
  have hcomp : ∀ b c : K, b + c = b * c * h w w → ∀ v : V,
      (v - (c * h w v) • w) - (b * h w (v - (c * h w v) • w)) • w = v := by
    intro b c hbc v
    rw [map_sub, map_smul, smul_eq_mul, sub_sub, ← add_smul]
    have : c * h w v + b * (h w v - c * h w v * h w w) = 0 := by
      linear_combination (h w v) * hbc
    rw [this, zero_smul, sub_zero]
  have ha' : star a + a = star a * a * h w w := by linear_combination ha
  let τ : V ≃ₗ[K] V := LinearEquiv.ofLinear (f a) (f (star a))
    (LinearMap.ext fun v => hcomp a (star a) ha v)
    (LinearMap.ext fun v => hcomp (star a) a ha' v)
  refine ⟨τ, ?_, fun v => rfl⟩
  intro x y
  change h (x - (a * h w x) • w) (y - (a * h w y) • w) = h x y
  have hsx : star (h w x) = h x w := star_h hs w x
  simp only [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
    starRingEnd_apply, RingHom.id_apply, star_mul', hsx]
  linear_combination (-(h w y * h x w)) * ha

theorem exists_isom_move (hS : IsHermSemilocal S) (hs : h.IsSymm) {x z : V} {u : K} (hu0 : u ≠ 0)
    (hus : star u = u) (hx : h x x = u) (hz : h z z = u) :
    ∃ τ ∈ Formalism.HermitianLatticesTheory.isom h, τ x = z ∧ ∀ v, h x v = 0 → h z v = 0 → τ v = v := by
  have hsy : ∀ a b : V, star (h a b) = h b a := star_h hs
  have key : ∀ y : V, h y y = u → h z y ≠ u →
      ∃ τ ∈ Formalism.HermitianLatticesTheory.isom h, τ y = z ∧ ∀ v, h y v = 0 → h z v = 0 → τ v = v := by
    intro y hy hne
    have hp : u - h z y ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have hsp : star (u - h z y) ≠ 0 := star_ne_zero.mpr hp
    have hww : h (y - z) (y - z) = (u - h z y) + star (u - h z y) := by
      simp only [map_sub, LinearMap.sub_apply]
      rw [hy, hz, star_sub, hus, hsy]
      ring
    obtain ⟨τ, hτ, hf⟩ := exists_quasi hs (y - z) (a := (u - h z y)⁻¹) (by
      rw [hww, star_inv₀]
      field_simp
      ring)
    refine ⟨τ, hτ, ?_, ?_⟩
    · have hyz : h (y - z) y = u - h z y := by
        simp only [map_sub, LinearMap.sub_apply, hy]
      rw [hf, hyz, inv_mul_cancel₀ hp, one_smul]
      abel
    · intro v hyv hzv
      rw [hf]
      simp only [map_sub, LinearMap.sub_apply, hyv, hzv, sub_zero, mul_zero, zero_smul]
  by_cases hne : h z x = u
  · obtain ⟨θ, -, hθ⟩ := hS.unram
    have hd : θ - star θ ≠ 0 := hθ.1
    have hθ0 : θ ≠ 0 := by
      rintro rfl
      simp at hd
    have hsθ : star θ ≠ 0 := star_ne_zero.mpr hθ0
    have hcc : θ * (star θ)⁻¹ * (star θ * θ⁻¹) = 1 := by field_simp
    have hc1 : θ * (star θ)⁻¹ ≠ 1 := by
      intro h1
      apply hd
      field_simp at h1
      exact sub_eq_zero.mpr h1
    obtain ⟨τ₁, hτ₁, hf₁⟩ := exists_quasi hs x (a := (1 - θ * (star θ)⁻¹) * u⁻¹) (by
      rw [hx]
      simp only [star_mul', star_sub, star_one, star_inv₀, star_star, hus]
      field_simp
      ring)
    have h1x : τ₁ x = (θ * (star θ)⁻¹) • x := by
      rw [hf₁, hx, mul_assoc, inv_mul_cancel₀ hu0, mul_one, sub_smul, one_smul]
      abel
    have hyy : h (τ₁ x) (τ₁ x) = u := by
      have hcx : ∀ c : K, h (c • x) (c • x) = star c * c * u := by
        intro c
        simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, starRingEnd_apply, hx]
        ring
      rw [h1x, hcx, star_mul', star_inv₀, star_star]
      have e1 : star θ * (star θ)⁻¹ = 1 := mul_inv_cancel₀ hsθ
      have e2 : θ * θ⁻¹ = 1 := mul_inv_cancel₀ hθ0
      linear_combination (θ * θ⁻¹ * u) * e1 + u * e2
    have hzy : h z (τ₁ x) ≠ u := by
      rw [h1x, map_smul, smul_eq_mul, hne]
      intro h2
      apply hc1
      have := mul_right_cancel₀ hu0 (h2.trans (one_mul u).symm)
      exact this
    obtain ⟨τ₂, hτ₂, h2y, h2v⟩ := key _ hyy hzy
    refine ⟨τ₂ * τ₁, (Formalism.HermitianLatticesTheory.isom h).mul_mem hτ₂ hτ₁, ?_, ?_⟩
    · exact h2y
    · intro v hxv hzv
      have h1v : τ₁ v = v := by
        rw [hf₁, hxv, mul_zero, zero_smul, sub_zero]
      change τ₂ (τ₁ v) = v
      rw [h1v]
      refine h2v v ?_ hzv
      rw [h1x, map_smulₛₗ, LinearMap.smul_apply, hxv, smul_zero]
  · exact key x hx hne

end Abs

end PI.UnitaryGroupMassFormula.CntFormula.UG
