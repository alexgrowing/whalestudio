import Mathlib
import Formalism.SatakeDualWeyl.Statement

open scoped Matrix
open Formalism.UG

namespace GlobalTheory.EvenLatIwasawa

variable {A : Type} [CommRing A] {n : ℕ} {σ : A →+* A} {J : Matrix (Fin n) (Fin n) A}

theorem hform_eq (u v : Fin n → A) : hform σ J u v = (σ ∘ u) ⬝ᵥ J *ᵥ v := by
  simp only [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, Function.comp_apply, mul_assoc]

theorem hform_add_right (u v w : Fin n → A) : hform σ J u (v + w) = hform σ J u v + hform σ J u w := by
  simp only [hform_eq, Matrix.mulVec_add, dotProduct_add]

theorem hform_smul_right (c : A) (u v : Fin n → A) : hform σ J u (c • v) = c * hform σ J u v := by
  simp only [hform_eq, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hform_add_left (u v w : Fin n → A) : hform σ J (u + v) w = hform σ J u w + hform σ J v w := by
  simp only [hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hform_smul_left (c : A) (u v : Fin n → A) : hform σ J (c • u) v = σ c * hform σ J u v := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem hform_swap (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (u v : Fin n → A) :
    hform σ J v u = σ (hform σ J u v) := by
  simp only [hform, map_sum, map_mul, hσ, hJ]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_mulVec (M : Matrix (Fin n) (Fin n) A) (u v : Fin n → A) :
    hform σ J (M *ᵥ u) (M *ᵥ v) = hform σ (cT σ M * J * M) u v := by
  have : σ ∘ (M *ᵥ u) = M.map σ *ᵥ (σ ∘ u) := funext fun i => RingHom.map_mulVec σ M u i
  rw [hform_eq, hform_eq, this, cT, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (σ ∘ u),
    Matrix.vecMul_transpose]

theorem hform_unitary {k : GL (Fin n) A} (hk : k ∈ UJ σ J) (u v : Fin n → A) :
    hform σ J (k.1 *ᵥ u) (k.1 *ᵥ v) = hform σ J u v := by
  rw [hform_mulVec]; exact congrArg (fun X => hform σ X u v) hk

theorem mem_UJ_of {k : GL (Fin n) A} (h : ∀ u v, hform σ J (k.1 *ᵥ u) (k.1 *ᵥ v) = hform σ J u v) : k ∈ UJ σ J := by
  have e : ∀ (X : Matrix (Fin n) (Fin n) A) i j, hform σ X (Pi.single i 1) (Pi.single j 1) = X i j := fun X i j => by
    have : σ ∘ (Pi.single i 1 : Fin n → A) = Pi.single i 1 := funext fun l => by
      by_cases hl : l = i
      · subst hl; simp
      · simp [hl]
    rw [hform_eq, this]; simp
  change cT σ k.1 * J * k.1 = J
  ext i j
  rw [← e (cT σ k.1 * J * k.1), ← hform_mulVec, h, e]

variable {R : Subring A} {L : Submodule R (Fin n → A)}

theorem smul_mem' {a : A} (ha : a ∈ R) {v : Fin n → A} (hv : v ∈ L) : a • v ∈ L := L.smul_mem ⟨a, ha⟩ hv

theorem exists_reflection (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (hR : ∀ a ∈ R, σ a ∈ R)
    (hL : ∀ u ∈ L, ∀ v ∈ L, hform σ J u v ∈ R) {u : Fin n → A} (hu : u ∈ L) {c : A} (hc : c ∈ R)
    (h : c + σ c + c * σ c * hform σ J u u = 0) :
    ∃ k ∈ UJ σ J ⊓ stabGL L, ∀ v, k.1 *ᵥ v = v + (c * hform σ J u v) • u := by
  let T : A → Matrix (Fin n) (Fin n) A := fun c => 1 + c • Matrix.vecMulVec u ((σ ∘ u) ᵥ* J)
  have hT : ∀ c v, T c *ᵥ v = v + (c * hform σ J u v) • u := fun c v => by
    simp only [T, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, hform_eq,
      Matrix.dotProduct_mulVec]
    funext i; simp; ring
  have hTT : ∀ a b, a + b + a * b * hform σ J u u = 0 → T a * T b = 1 := fun a b hab => by
    refine Matrix.ext_of_mulVec_single fun j => ?_
    rw [← Matrix.mulVec_mulVec, hT, hT, Matrix.one_mulVec, hform_add_right, hform_smul_right, add_assoc, ← add_smul]
    have : b * hform σ J u (Pi.single j 1) + a * (hform σ J u (Pi.single j 1) + b * hform σ J u (Pi.single j 1) *
      hform σ J u u) = 0 := by linear_combination hform σ J u (Pi.single j 1) * hab
    rw [this, zero_smul, add_zero]
  have hm : ∀ a ∈ R, ∀ v ∈ L, T a *ᵥ v ∈ L := fun a ha v hv => by
    rw [hT]; exact add_mem hv (smul_mem' (mul_mem ha (hL u hu v hv)) hu)
  have h' : T (σ c) * T c = 1 := hTT _ _ (by linear_combination h)
  refine ⟨⟨T c, T (σ c), hTT _ _ h, h'⟩, ⟨mem_UJ_of fun v w => ?_, fun v => ⟨hm c hc v, fun hv => ?_⟩⟩, hT c⟩
  · change hform σ J (T c *ᵥ v) (T c *ᵥ w) = _
    rw [hT, hT]
    simp only [hform_add_left, hform_add_right, hform_smul_left, hform_smul_right, map_mul, ← hform_swap hσ hJ]
    linear_combination hform σ J v u * hform σ J u w * h
  · have := hm _ (hR c hc) _ hv
    rwa [Matrix.mulVec_mulVec, h', Matrix.one_mulVec] at this

theorem exists_move (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (hR : ∀ a ∈ R, σ a ∈ R)
    (hL : ∀ u ∈ L, ∀ v ∈ L, hform σ J u v ∈ R) {x z : Fin n → A} (hx : x ∈ L) (hz : z ∈ L)
    (hxx : hform σ J x x = 0) (hzz : hform σ J z z = 0) {η d : A} (hη : η ∈ R) (hd : d ∈ R) (hηη : η * η = η)
    (hση : σ η = η) (h : η * hform σ J z x * d = η) :
    ∃ k ∈ UJ σ J ⊓ stabGL L, k.1 *ᵥ x = (1 - η) • x + η • z := by
  have h2 : η * hform σ J x z * σ d = η := by
    have := congrArg σ h
    rwa [map_mul, map_mul, hση, ← hform_swap hσ hJ] at this
  have hu : x + (-1 : A) • z ∈ L := add_mem hx (smul_mem' (neg_mem (one_mem _)) hz)
  obtain ⟨k, hk, hkv⟩ := exists_reflection hσ hJ hR hL hu (mul_mem hη hd) (by
    simp only [hform_add_left, hform_add_right, hform_smul_left, hform_smul_right, map_mul, hση, hxx, hzz, map_neg, map_one]
    linear_combination (-η * σ d) * h + (-η * d) * h2 + (- d - σ d) * hηη)
  refine ⟨k, hk, ?_⟩
  rw [hkv]
  simp only [hform_add_left, hform_smul_left, hxx, map_neg, map_one]
  have : η * d * (0 + -1 * hform σ J z x) = -η := by linear_combination -h
  rw [this]
  module

theorem exists_trans (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (hR : ∀ a ∈ R, σ a ∈ R)
    (hQ : ∀ p ∈ R, ∀ q ∈ R, ∃ s ∈ R, ∃ t ∈ R, ∃ d ∈ R, ∃ d' ∈ R, (s + t * p) * d = 1 ∧ (s * q + t) * d' = 1)
    (hS : ∀ c ∈ R, ∃ e ∈ R, ∃ d ∈ R, e * e = e ∧ e * c * d = e ∧
      ∀ m ∈ R, ∀ m' ∈ R, m * m' = 1 → ∀ a ∈ R, ∃ d' ∈ R, (m + (1 - e) * c * a) * d' = 1)
    (hL : ∀ u ∈ L, ∀ v ∈ L, hform σ J u v ∈ R) (hE : ∀ u ∈ L, ∃ b ∈ R, hform σ J u u = b + σ b)
    {x x' y y' : Fin n → A} (hx : x ∈ L) (hx' : x' ∈ L) (hy : y ∈ L) (hy' : y' ∈ L)
    (hxx : hform σ J x x = 0) (hxx' : hform σ J x' x' = 0) (hxy : hform σ J x y = 1) (hxy' : hform σ J x' y' = 1) :
    ∃ k ∈ UJ σ J ⊓ stabGL L, k.1 *ᵥ x = x' := by
  obtain ⟨e, he, d, hd, hee, hecd, hjac⟩ := hS _ (hL x' hx' x hx)
  set c := hform σ J x' x with hc
  have hee' : σ e * σ e = σ e := by rw [← map_mul, hee]
  have hη : e * σ e ∈ R := mul_mem he (hR e he)
  have hση : σ (e * σ e) = e * σ e := by rw [map_mul, hσ, mul_comm]
  have hηη : e * σ e * (e * σ e) = e * σ e := by linear_combination (σ e * σ e) * hee + e * hee'
  set η := e * σ e with hηd
  obtain ⟨k₁, hk₁, e₁⟩ := exists_move hσ hJ hR hL hx hx' hxx hxx' hη hd hηη hση (by linear_combination σ e * hecd)
  obtain ⟨s, hs, t, ht, m', hm', q', hq', hm, hq⟩ := hQ _ (hL x hx y' hy') _ (hL x' hx' y hy)
  set z₀ := s • y + t • y' with hz₀
  have hz₀L : z₀ ∈ L := add_mem (smul_mem' hs hy) (smul_mem' ht hy')
  have h1 : hform σ J x z₀ * m' = 1 := by rw [hz₀, hform_add_right, hform_smul_right, hform_smul_right, hxy, mul_one, hm]
  have h2 : hform σ J x' z₀ * q' = 1 := by rw [hz₀, hform_add_right, hform_smul_right, hform_smul_right, hxy', mul_one, hq]
  obtain ⟨b, hb, hbb⟩ := hE z₀ hz₀L
  set a := -(b + σ e * σ b) * σ m' with ha
  have haR : a ∈ R := mul_mem (neg_mem (add_mem hb (mul_mem (hR e he) (hR b hb)))) (hR _ hm')
  obtain ⟨d', hd', hdd'⟩ := hjac _ (hL x' hx' z₀ hz₀L) q' hq' h2 a haR
  have h1η : 1 - η ∈ R := sub_mem (one_mem _) hη
  have hσ1 : σ (1 - η) = 1 - η := by rw [map_sub, map_one, hση]
  have h11 : (1 - η) * (1 - η) = 1 - η := by linear_combination hηη
  set z := (1 - η) • (z₀ + ((1 - e) * a) • x) with hz
  have hzL : z ∈ L := smul_mem' h1η (add_mem hz₀L (smul_mem' (mul_mem (sub_mem (one_mem _) he) haR) hx))
  have h1' : hform σ J z₀ x * σ m' = 1 := by rw [hform_swap hσ hJ x z₀, ← map_mul, h1, map_one]
  have hzz : hform σ J z z = 0 := by
    simp only [hz, hform_add_left, hform_add_right, hform_smul_left, hform_smul_right, hσ1, hxx, hbb, ha, map_mul, map_sub,
      map_one, map_neg, map_add, hσ]
    rw [hηd] at *
    linear_combination (-(1 - e * σ e) * (1 - e * σ e) * (1 - e) * (b + σ e * σ b)) * h1' +
      (-(1 - e * σ e) * (1 - e * σ e) * (1 - σ e) * (σ b + e * b)) * h1 + ((1 - e * σ e) * (-(b + σ b))) * hηη
  have hx₁ : k₁.1 *ᵥ x ∈ L := (hk₁.2 x).1 hx
  obtain ⟨k₂, hk₂, e₂⟩ := exists_move hσ hJ hR hL hx₁ hzL (by rw [hform_unitary hk₁.1, hxx]) hzz h1η (hR _ hm') h11 hσ1 (by
    simp only [e₁, hz, hform_add_left, hform_add_right, hform_smul_left, hform_smul_right, hσ1, hxx]
    linear_combination (1 - η) ^ 3 * h1' + ((1 - η) * (- σ m' * (hform σ J z₀ x' + σ ((1 - e) * a) * hform σ J x x')) + (2 - η)) * hηη)
  have hx₂ : k₂.1 *ᵥ (k₁.1 *ᵥ x) ∈ L := (hk₂.2 _).1 hx₁
  obtain ⟨k₃, hk₃, e₃⟩ := exists_move hσ hJ hR hL hx₂ hx' (by rw [hform_unitary hk₂.1, hform_unitary hk₁.1, hxx]) hxx' h1η hd'
    h11 hσ1 (by
    rw [e₂, e₁]
    simp only [hz, hform_add_right, hform_smul_right, hxx', ← hc]
    linear_combination (1 - η) ^ 3 * hdd' + (-(1 - η) * c * d' + (2 - η)) * hηη)
  refine ⟨k₃ * k₂ * k₁, mul_mem (mul_mem hk₃ hk₂) hk₁, ?_⟩
  simp only [Units.val_mul, ← Matrix.mulVec_mulVec]
  rw [e₃, e₂, e₁]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-η * x i - z i + (η + 1) * x' i) * hηη

theorem exists_generator
    (hB : ∀ a b : A, ∃ u ∈ R, ∃ v ∈ R, ∃ r ∈ R, ∃ r' ∈ R, a = r * (u * a + v * b) ∧ b = r' * (u * a + v * b))
    {I : Submodule R A} (hI : I.FG) : ∃ s ∈ I, ∀ a ∈ I, ∃ r ∈ R, a = r * s := by
  obtain ⟨S, rfl⟩ := hI
  have key : ∃ s ∈ Submodule.span R (S : Set A), ∀ a ∈ S, ∃ r ∈ R, a = r * s := by
    classical
    induction S using Finset.induction_on with
    | empty => exact ⟨0, zero_mem _, by simp⟩
    | insert a S _ ih =>
      obtain ⟨s, hs, h⟩ := ih
      obtain ⟨u, hu, v, hv, r, hr, r', hr', e, e'⟩ := hB a s
      refine ⟨u * a + v * s, add_mem (Submodule.smul_mem _ (⟨u, hu⟩ : R) (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ (⟨v, hv⟩ : R) (Submodule.span_mono (by simp) hs)), fun b hb => ?_⟩
      rcases Finset.mem_insert.1 hb with rfl | hb
      · exact ⟨r, hr, e⟩
      · obtain ⟨c, hc, e''⟩ := h b hb
        exact ⟨c * r', mul_mem hc hr', by rw [mul_assoc, ← e', e'']⟩
  obtain ⟨s, hs, h⟩ := key
  refine ⟨s, hs, fun a ha => ?_⟩
  induction ha using Submodule.span_induction with
  | mem a ha => exact h a ha
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨r, hr, rfl⟩ := ha
    obtain ⟨r', hr', rfl⟩ := hb
    exact ⟨r + r', add_mem hr hr', by ring⟩
  | smul c a _ ha =>
    obtain ⟨r, hr, rfl⟩ := ha
    exact ⟨c * r, mul_mem c.2 hr, by rw [mul_assoc]; rfl⟩

theorem exists_scale (hσ : ∀ a, σ (σ a) = a)
    (hB : ∀ a b : A, ∃ u ∈ R, ∃ v ∈ R, ∃ r ∈ R, ∃ r' ∈ R, a = r * (u * a + v * b) ∧ b = r' * (u * a + v * b))
    (hfg : L.FG) (hfull : ∀ v, ∃ c : Aˣ, c.1 • v ∈ L)
    (hmax : ∀ x, hform σ J x x = 0 → (∀ v ∈ L, hform σ J x v ∈ R) → x ∈ L)
    {x y : Fin n → A} (hxx : hform σ J x x = 0) (hxy : hform σ J x y = 1) :
    ∃ s : Aˣ, s.1 • x ∈ L ∧ ∃ y ∈ L, hform σ J (s.1 • x) y = 1 := by
  let φ : (Fin n → A) →ₗ[R] A :=
    { toFun := hform σ J x, map_add' := hform_add_right x, map_smul' := fun c v => hform_smul_right c.1 x v }
  obtain ⟨s, ⟨w, hw, hws⟩, hs⟩ := exists_generator hB (hfg.map φ)
  obtain ⟨c, hc⟩ := hfull y
  obtain ⟨r, -, hr⟩ := hs _ ⟨_, hc, rfl⟩
  have hu : IsUnit s := by
    have : c.1 = r * s := by rw [← hr]; change _ = hform σ J x _; rw [hform_smul_right, hxy, mul_one]
    exact isUnit_of_mul_isUnit_right (this ▸ c.isUnit)
  obtain ⟨s, rfl⟩ := hu
  have e : ∀ v, hform σ J ((Units.map σ.toMonoidHom s⁻¹).1 • x) v = (s⁻¹).1 * φ v := fun v => by
    rw [hform_smul_left]; exact congrArg (· * _) (hσ _)
  refine ⟨Units.map σ.toMonoidHom s⁻¹, hmax _ (by rw [hform_smul_left, hform_smul_right, hxx]; simp) fun v hv => ?_,
    w, hw, by rw [e, hws, Units.inv_mul]⟩
  obtain ⟨r, hr, h⟩ := hs _ ⟨v, hv, rfl⟩
  rw [e, h, mul_comm r, Units.inv_mul_cancel_left]
  exact hr

theorem iwasawa_line (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (hR : ∀ a ∈ R, σ a ∈ R)
    (hB : ∀ a b : A, ∃ u ∈ R, ∃ v ∈ R, ∃ r ∈ R, ∃ r' ∈ R, a = r * (u * a + v * b) ∧ b = r' * (u * a + v * b))
    (hQ : ∀ p ∈ R, ∀ q ∈ R, ∃ s ∈ R, ∃ t ∈ R, ∃ d ∈ R, ∃ d' ∈ R, (s + t * p) * d = 1 ∧ (s * q + t) * d' = 1)
    (hS : ∀ c ∈ R, ∃ e ∈ R, ∃ d ∈ R, e * e = e ∧ e * c * d = e ∧
      ∀ m ∈ R, ∀ m' ∈ R, m * m' = 1 → ∀ a ∈ R, ∃ d' ∈ R, (m + (1 - e) * c * a) * d' = 1)
    (hL : ∀ u ∈ L, ∀ v ∈ L, hform σ J u v ∈ R) (hE : ∀ u ∈ L, ∃ b ∈ R, hform σ J u u = b + σ b)
    (hfg : L.FG) (hfull : ∀ v, ∃ c : Aˣ, c.1 • v ∈ L)
    (hmax : ∀ x, hform σ J x x = 0 → (∀ v ∈ L, hform σ J x v ∈ R) → x ∈ L)
    {x y : Fin n → A} (hxx : hform σ J x x = 0) (hxy : hform σ J x y = 1) {g : GL (Fin n) A} (hg : g ∈ UJ σ J) :
    ∃ k ∈ UJ σ J ⊓ stabGL L, ∃ t : Aˣ, (g * k⁻¹).1 *ᵥ x = t.1 • x := by
  obtain ⟨s, hs, w, hw, e⟩ := exists_scale hσ hB hfg hfull hmax hxx hxy
  have hxx' : hform σ J ((g⁻¹).1 *ᵥ x) ((g⁻¹).1 *ᵥ x) = 0 := by rw [hform_unitary (inv_mem hg), hxx]
  obtain ⟨s', hs', w', hw', e'⟩ := exists_scale hσ hB hfg hfull hmax hxx' (by rw [hform_unitary (inv_mem hg), hxy])
  obtain ⟨k, hk, h⟩ := exists_trans hσ hJ hR hQ hS hL hE hs hs' hw hw'
    (by rw [hform_smul_left, hform_smul_right, hxx]; simp) (by rw [hform_smul_left, hform_smul_right, hxx']; simp) e e'
  refine ⟨k⁻¹, inv_mem hk, s⁻¹ * s', ?_⟩
  have : k.1 *ᵥ x = (s⁻¹ * s').1 • (g⁻¹).1 *ᵥ x := by
    rw [Units.val_mul, mul_smul, ← h, Matrix.mulVec_smul, smul_smul, Units.inv_mul, one_smul]
  rw [inv_inv, Units.val_mul, ← Matrix.mulVec_mulVec, this, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Units.mul_inv,
    Matrix.one_mulVec]

theorem isOpen_isCompact_stab [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] (hσ : Continuous σ)
    (hfg : L.FG) (hfull : ∀ v, ∃ c : Aˣ, c.1 • v ∈ L) (ho : IsOpen (L : Set (Fin n → A)))
    (hc : IsCompact (L : Set (Fin n → A))) :
    IsOpen ((stabGL L).subgroupOf (UJ σ J) : Set (UJ σ J)) ∧ IsCompact ((stabGL L).subgroupOf (UJ σ J) : Set (UJ σ J)) := by
  have hv : Continuous fun g : GL (Fin n) A => (g : Matrix (Fin n) (Fin n) A) := Units.continuous_val
  have hcl : IsClosed (UJ σ J : Set (GL (Fin n) A)) :=
    isClosed_eq (((hv.matrix_map hσ).matrix_transpose.matrix_mul continuous_const).matrix_mul hv) continuous_const
  have hopen : IsOpen ((stabGL L).subgroupOf (UJ σ J) : Set (UJ σ J)) := by
    obtain ⟨S, hS⟩ := hfg
    have hmap : ∀ M : Matrix (Fin n) (Fin n) A, (∀ v ∈ S, M *ᵥ v ∈ L) → ∀ v ∈ L, M *ᵥ v ∈ L := fun M hM v hv => by
      rw [← hS] at hv
      induction hv using Submodule.span_induction with
      | mem a ha => exact hM a ha
      | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
      | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
      | smul c a _ ha =>
        change M *ᵥ (c.1 • a) ∈ L
        rw [Matrix.mulVec_smul]; exact smul_mem' c.2 ha
    have hO : IsOpen {g : GL (Fin n) A | ∀ v ∈ S, g.1 *ᵥ v ∈ L} := by
      simp only [Set.setOf_forall]
      exact isOpen_biInter_finset fun v _ => ho.preimage (hv.matrix_mulVec continuous_const)
    convert (hO.inter (hO.preimage continuous_inv)).preimage (continuous_subtype_val (p := (· ∈ UJ σ J))) using 1
    ext g
    have hSL : ∀ v ∈ S, v ∈ L := fun v hv => hS ▸ Submodule.subset_span hv
    refine ⟨fun h => ⟨fun v hv => (h v).1 (hSL v hv), fun v hv => ((stabGL L).inv_mem h v).1 (hSL v hv)⟩,
      fun h v => ⟨hmap _ h.1 v, fun hv => ?_⟩⟩
    have : (g.1⁻¹).1 *ᵥ (g.1.1 *ᵥ v) ∈ L := hmap _ h.2 _ hv
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this
  refine ⟨hopen, ?_⟩
  choose c hcL using fun j => hfull (Pi.single j 1)
  let S : Set (Matrix (Fin n) (Fin n) A) := Set.pi Set.univ fun i => Set.pi Set.univ fun j =>
    (fun v : Fin n → A => ((c j)⁻¹).1 * v i) '' L
  have hS : IsCompact S := isCompact_univ_pi fun i => isCompact_univ_pi fun j =>
    hc.image (continuous_const.mul (continuous_apply i))
  have hmem : ∀ g ∈ stabGL L, g.1 ∈ S := fun g hg i _ j _ => ⟨_, (hg _).1 (hcL j), by
    simp [Matrix.mulVec_smul]⟩
  have hemb := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) A)).comp
    hcl.isClosedEmbedding_subtypeVal
  have hK : IsCompact (X := UJ σ J) _ := hemb.isCompact_preimage (hS.prod (hS.image MulOpposite.continuous_op))
  exact hK.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hopen) fun h hh =>
    ⟨hmem _ hh, (h.1⁻¹).1, hmem _ ((stabGL L).inv_mem hh), rfl⟩

end GlobalTheory.EvenLatIwasawa
