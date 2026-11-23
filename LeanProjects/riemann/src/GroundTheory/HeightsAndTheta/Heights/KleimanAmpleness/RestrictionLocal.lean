import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Local

variable (k : Type u) [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} (x : Fin (N + 1) → Ω) (y : Fin (N + 1) → K')

def locAt : Set Ω :=
  {a | ∃ (f s : Poly k N) (e : ℕ), f.IsHomogeneous e ∧ s.IsHomogeneous e ∧ aeval y s ≠ 0 ∧
    a = aeval x f / aeval x s}

open Classical in

def redAt (a : Ω) : K' :=
  if h : ∃ (p : Poly k N × Poly k N) (e : ℕ), p.1.IsHomogeneous e ∧ p.2.IsHomogeneous e ∧
      aeval y p.2 ≠ 0 ∧ a = aeval x p.1 / aeval x p.2
  then aeval y h.choose.1 / aeval y h.choose.2 else 0

variable {k x y}

theorem aeval_ne_zero_of_primeOf_le (hsp : primeOf (S := k) x ≤ primeOf (S := k) y)
    {s : Poly k N} {e : ℕ} (hs : s.IsHomogeneous e) (h : aeval y s ≠ 0) : aeval x s ≠ 0 := fun h0 =>
  h ((mem_primeOf_of_isHomogeneous y hs).mp (hsp ((mem_primeOf_of_isHomogeneous x hs).mpr h0)))

theorem mem_locAt {f s : Poly k N} {e : ℕ} (hf : f.IsHomogeneous e) (hs : s.IsHomogeneous e)
    (h : aeval y s ≠ 0) : aeval x f / aeval x s ∈ locAt k x y :=
  ⟨f, s, e, hf, hs, h, rfl⟩

variable (hsp : primeOf (S := k) x ≤ primeOf (S := k) y)
include hsp

theorem redAt_eq {f s : Poly k N} {e : ℕ} (hf : f.IsHomogeneous e) (hs : s.IsHomogeneous e)
    (h : aeval y s ≠ 0) : redAt k x y (aeval x f / aeval x s) = aeval y f / aeval y s := by
  have hex : ∃ (p : Poly k N × Poly k N) (e : ℕ), p.1.IsHomogeneous e ∧ p.2.IsHomogeneous e ∧
      aeval y p.2 ≠ 0 ∧ aeval x f / aeval x s = aeval x p.1 / aeval x p.2 :=
    ⟨(f, s), e, hf, hs, h, rfl⟩
  rw [redAt, dif_pos hex]
  obtain ⟨e', hf', hs', h', heq⟩ := hex.choose_spec
  have hx := aeval_ne_zero_of_primeOf_le hsp hs h
  have hx' := aeval_ne_zero_of_primeOf_le hsp hs' h'
  rw [div_eq_div_iff hx hx'] at heq
  have hhom : (f * hex.choose.2 - hex.choose.1 * s).IsHomogeneous (e + e') := by
    refine (hf.mul hs').sub ?_
    rw [add_comm e e']; exact hf'.mul hs
  have hmem : f * hex.choose.2 - hex.choose.1 * s ∈ primeOf (S := k) x := by
    rw [mem_primeOf_of_isHomogeneous x hhom]
    simp only [map_sub, map_mul, heq, sub_self]
  have hy := (mem_primeOf_of_isHomogeneous y hhom).mp (hsp hmem)
  simp only [map_sub, map_mul] at hy
  rw [div_eq_div_iff h' h]
  linear_combination -hy

theorem locAt_algebraMap (c : k) :
    algebraMap k Ω c ∈ locAt k x y ∧ redAt k x y (algebraMap k Ω c) = algebraMap k K' c := by
  have h1 : aeval y (1 : Poly k N) ≠ 0 := by simp
  have hc : algebraMap k Ω c = aeval x (C c : Poly k N) / aeval x (1 : Poly k N) := by
    simp
  rw [hc]
  refine ⟨mem_locAt (isHomogeneous_C _ c) (isHomogeneous_one _ _) h1, ?_⟩
  rw [redAt_eq hsp (isHomogeneous_C _ c) (isHomogeneous_one _ _) h1]
  simp

theorem locAt_zero : (0 : Ω) ∈ locAt k x y ∧ redAt k x y (0 : Ω) = 0 := by
  simpa using locAt_algebraMap hsp (0 : k)

theorem locAt_one : (1 : Ω) ∈ locAt k x y ∧ redAt k x y (1 : Ω) = 1 := by
  simpa using locAt_algebraMap hsp (1 : k)

theorem locAt_add {a b : Ω} (ha : a ∈ locAt k x y) (hb : b ∈ locAt k x y) :
    a + b ∈ locAt k x y ∧ redAt k x y (a + b) = redAt k x y a + redAt k x y b := by
  obtain ⟨f, s, e, hf, hs, hsy, rfl⟩ := ha
  obtain ⟨f', s', e', hf', hs', hsy', rfl⟩ := hb
  have hsx := aeval_ne_zero_of_primeOf_le hsp hs hsy
  have hsx' := aeval_ne_zero_of_primeOf_le hsp hs' hsy'
  have hhom : (f * s' + s * f').IsHomogeneous (e + e') := (hf.mul hs').add (hs.mul hf')
  have hsum : aeval x f / aeval x s + aeval x f' / aeval x s' =
      aeval x (f * s' + s * f') / aeval x (s * s') := by
    rw [div_add_div _ _ hsx hsx']; simp only [map_add, map_mul]
  have hss : aeval y (s * s') ≠ 0 := by rw [map_mul]; exact mul_ne_zero hsy hsy'
  rw [hsum]
  refine ⟨mem_locAt hhom (hs.mul hs') hss, ?_⟩
  rw [redAt_eq hsp hhom (hs.mul hs') hss, redAt_eq hsp hf hs hsy, redAt_eq hsp hf' hs' hsy',
    div_add_div _ _ hsy hsy']
  simp only [map_add, map_mul]

theorem locAt_mul {a b : Ω} (ha : a ∈ locAt k x y) (hb : b ∈ locAt k x y) :
    a * b ∈ locAt k x y ∧ redAt k x y (a * b) = redAt k x y a * redAt k x y b := by
  obtain ⟨f, s, e, hf, hs, hsy, rfl⟩ := ha
  obtain ⟨f', s', e', hf', hs', hsy', rfl⟩ := hb
  have hprod : aeval x f / aeval x s * (aeval x f' / aeval x s') =
      aeval x (f * f') / aeval x (s * s') := by
    rw [div_mul_div_comm]; simp only [map_mul]
  have hss : aeval y (s * s') ≠ 0 := by rw [map_mul]; exact mul_ne_zero hsy hsy'
  rw [hprod]
  refine ⟨mem_locAt (hf.mul hf') (hs.mul hs') hss, ?_⟩
  rw [redAt_eq hsp (hf.mul hf') (hs.mul hs') hss, redAt_eq hsp hf hs hsy, redAt_eq hsp hf' hs' hsy',
    div_mul_div_comm]
  simp only [map_mul]

theorem locAt_pow {a : Ω} (ha : a ∈ locAt k x y) (n : ℕ) :
    a ^ n ∈ locAt k x y ∧ redAt k x y (a ^ n) = redAt k x y a ^ n := by
  induction n with
  | zero => simpa using locAt_one hsp
  | succ n ih =>
    obtain ⟨h1, h2⟩ := locAt_mul hsp ih.1 ha
    rw [pow_succ, pow_succ]
    exact ⟨h1, by rw [h2, ih.2]⟩

theorem locAt_sum {ι : Type*} (s : Finset ι) (a : ι → Ω) (ha : ∀ i ∈ s, a i ∈ locAt k x y) :
    ∑ i ∈ s, a i ∈ locAt k x y ∧ redAt k x y (∑ i ∈ s, a i) = ∑ i ∈ s, redAt k x y (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using locAt_zero hsp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    obtain ⟨h1, h2⟩ := ih fun j hj => ha j (Finset.mem_insert_of_mem hj)
    obtain ⟨h3, h4⟩ := locAt_add hsp (ha i (Finset.mem_insert_self i s)) h1
    exact ⟨h3, by rw [h4, h2]⟩

theorem locAt_inv {a : Ω} (ha : a ∈ locAt k x y) (hr : redAt k x y a ≠ 0) :
    a ≠ 0 ∧ a⁻¹ ∈ locAt k x y ∧ redAt k x y a⁻¹ = (redAt k x y a)⁻¹ := by
  obtain ⟨f, s, e, hf, hs, hsy, rfl⟩ := ha
  rw [redAt_eq hsp hf hs hsy] at hr
  have hfy : aeval y f ≠ 0 := fun h => hr (by rw [h, zero_div])
  have hfx := aeval_ne_zero_of_primeOf_le hsp hf hfy
  have hsx := aeval_ne_zero_of_primeOf_le hsp hs hsy
  refine ⟨div_ne_zero hfx hsx, by rw [inv_div]; exact mem_locAt hs hf hfy, ?_⟩
  rw [inv_div, redAt_eq hsp hs hf hfy, redAt_eq hsp hf hs hsy, inv_div]

theorem locAt_div {a b : Ω} (ha : a ∈ locAt k x y) (hb : b ∈ locAt k x y) (hr : redAt k x y b ≠ 0) :
    a / b ∈ locAt k x y ∧ redAt k x y (a / b) = redAt k x y a / redAt k x y b := by
  obtain ⟨-, h1, h2⟩ := locAt_inv hsp hb hr
  obtain ⟨h3, h4⟩ := locAt_mul hsp ha h1
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact ⟨h3, by rw [h4, h2]⟩

theorem chartRing_sub_locAt (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) (I : Chart y) {a : Ω}
    (ha : a ∈ chartRing k x (liftChart hxy I)) :
    a ∈ locAt k x y ∧ redAt k x y a ∈ chartRing k y I := by
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := ha
  have hsy : aeval y s ≠ 0 := eval_ne_zero_of_mem_monos I hs
  exact ⟨mem_locAt hf hse hsy, by rw [redAt_eq hsp hf hse hsy]; exact ⟨f, s, e, hs, hf, hse, rfl⟩⟩

theorem exists_redAt_eq (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) (I : Chart y) {c : K'}
    (hc : c ∈ chartRing k y I) : ∃ a ∈ chartRing k x (liftChart hxy I), redAt k x y a = c := by
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := hc
  exact ⟨aeval x f / aeval x s, ⟨f, s, e, hs, hf, hse, rfl⟩,
    redAt_eq hsp hf hse (eval_ne_zero_of_mem_monos I hs)⟩

end Local

section Specialize

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ}

theorem primeOf_le_primeOf_of_algHom {x : Fin (N + 1) → Ω} {j : Fin (N + 1)} (hj : x j ≠ 0)
    (ψ : chartRing k x (singleChart hj) →ₐ[k] K') :
    primeOf (S := k) x ≤ primeOf (S := k) (fun i => ψ (ratio hj i)) := by
  have key : ∀ {B : Type w} [CommRing B] [Algebra k B] (φ : chartRing k x (singleChart hj) →ₐ[k] B)
      (g : Poly k N), φ (aeval (ratio (S := k) hj) g) = aeval (fun i => φ (ratio hj i)) g := by
    intro B _ _ φ g
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  intro f hf
  have hcomp : ∀ d, homogeneousComponent d f ∈ primeOf (S := k) (fun i => ψ (ratio hj i)) := by
    intro d
    have hg := homogeneousComponent_isHomogeneous d f
    have h0 : aeval x (homogeneousComponent d f) = 0 :=
      (mem_primeOf_of_isHomogeneous x hg).mp (homogeneousComponent_mem_primeOf x hf d)
    rw [mem_primeOf_of_isHomogeneous _ hg, ← key]
    have hval : aeval (ratio (S := k) hj) (homogeneousComponent d f) = 0 := by
      apply Subtype.ext
      have := key (chartRing k x (singleChart hj)).val (homogeneousComponent d f)
      simp only [Subalgebra.coe_val] at this
      rw [this, ZeroMemClass.coe_zero]
      change aeval (fun l => x l / x j) (homogeneousComponent d f) = 0
      rw [aeval_div_of_isHomogeneous hg j, h0, zero_div]
    rw [hval, map_zero]
  rw [← sum_homogeneousComponent f]
  exact Ideal.sum_mem _ fun d _ => hcomp d

theorem algHom_ratio_self {x : Fin (N + 1) → Ω} {j : Fin (N + 1)} (hj : x j ≠ 0)
    (ψ : chartRing k x (singleChart hj) →ₐ[k] K') : ψ (ratio hj j) = 1 := by
  have : ratio (S := k) hj j = 1 := Subtype.ext (div_self hj)
  rw [this, map_one]

end Specialize

end

end GroundTheory.Heights₂.Heights.Kleiman
