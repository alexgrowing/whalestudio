import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.UnitaryTransvectionZeroSecondMemClosure

namespace ReciprocityTheory.ChartRestriction.G.SA

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}

section
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ)
include hσ hJ

theorem tor_conj_e {e f : ι → K} (he : hf σ J e e = 0) (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
    {l m c : K} {u : ι → K} (hml : m * σ l = 1) (hue : hf σ J u e = 0) (huf : hf σ J u f = 0) :
    tor σ J e f l m * eich σ J e u c = eich σ J e (σ l • u) (l * σ l * c) * tor σ J e f l m := by
  have hfe := hf_fe hσ hJ he hff hef
  have heu : hf σ J e u = 0 := by rw [← hf_symm hσ hJ, hue, map_zero]
  have hfu : hf σ J f u = 0 := by rw [← hf_symm hσ hJ, huf, map_zero]
  rw [ext_iff_mulVec]
  intro x
  rw [← mulVec_mulVec, ← mulVec_mulVec, eich_mulVec, tor_mulVec, tor_mulVec, eich_mulVec]
  simp only [hf_add_left, hf_sub_left, hf_smul_left, hf_smul_right, hσ, he, hff, hef, hfe, hue, huf,
    heu, hfu, mul_zero, mul_one, add_zero, sub_zero, zero_add]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-(hf σ J x e * u i) - l * c * hf σ J x e * e i) * hml

theorem conj_mem_along {e f : ι → K} (he : hf σ J e e = 0) (hff : hf σ J f f = 0)
    (hef : hf σ J e f = 1) {l m : K} (hml : m * σ l = 1) {M : Matrix ι ι K}
    (hM : M ∈ eichAlong σ J e f) :
    ∃ M' ∈ eichAlong σ J e f, tor σ J e f l m * M = M' * tor σ J e f l m := by
  obtain ⟨u, c, hue, huf, hc, rfl⟩ := hM
  refine ⟨_, ⟨σ l • u, l * σ l * c, ?_, ?_, ?_, rfl⟩, tor_conj_e hσ hJ he hff hef hml hue huf⟩
  · rw [hf_smul_left, hue, mul_zero]
  · rw [hf_smul_left, huf, mul_zero]
  · rw [hf_smul_left, hf_smul_right, map_mul, map_mul, hσ]
    linear_combination (l * σ l) * hc

variable {e f : ι → K} (he : hf σ J e e = 0) (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
include he hff hef

theorem conj_mem_eichSet {l m : K} (hml : m * σ l = 1) {M : Matrix ι ι K}
    (hM : M ∈ eichSet σ J e f) :
    ∃ M' ∈ eichSet σ J e f, tor σ J e f l m * M = M' * tor σ J e f l m := by
  rcases hM with hM | hM
  · obtain ⟨M', h1, h2⟩ := conj_mem_along hσ hJ he hff hef hml hM
    exact ⟨M', Or.inl h1, h2⟩
  · have hfe := hf_fe hσ hJ he hff hef
    have hlm : l * σ m = 1 := by rw [← hσ l, ← map_mul, mul_comm, hml, map_one]
    obtain ⟨M', h1, h2⟩ := conj_mem_along hσ hJ hff he hfe hlm hM
    rw [← tor_swap] at h2
    exact ⟨M', Or.inr h1, h2⟩

theorem conj_closure {l m : K} (hml : m * σ l = 1) {n : Matrix ι ι K}
    (hn : n ∈ Submonoid.closure (eichSet σ J e f)) :
    ∃ n' ∈ Submonoid.closure (eichSet σ J e f), tor σ J e f l m * n = n' * tor σ J e f l m := by
  induction hn using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨M', h1, h2⟩ := conj_mem_eichSet hσ hJ he hff hef hml hx
    exact ⟨M', Submonoid.subset_closure h1, h2⟩
  | one => exact ⟨1, Submonoid.one_mem _, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', hx', hx2⟩ := hx
    obtain ⟨y', hy', hy2⟩ := hy
    refine ⟨x' * y', Submonoid.mul_mem _ hx' hy', ?_⟩
    rw [← Matrix.mul_assoc, hx2, Matrix.mul_assoc, hy2, Matrix.mul_assoc]

theorem tor_mul (l m l' m' : K) :
    tor σ J e f l m * tor σ J e f l' m' = tor σ J e f (l * l') (m * m') := by
  rw [tor_hm, tor_hm, tor_hm, hm_mul hσ hJ he hff hef]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem tor_one : tor σ J e f 1 1 = 1 := by
  simp [tor]

end

variable (σ J) in

def Good (e f : ι → K) : Set (Matrix ι ι K) :=
  {g | ∃ n ∈ Submonoid.closure (eichSet σ J e f), ∃ l m : K, m * σ l = 1 ∧ g = n * tor σ J e f l m}

section
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) {e f : ι → K} (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
include hσ hJ he hff hef

theorem good_of_closure {n : Matrix ι ι K} (hn : n ∈ Submonoid.closure (eichSet σ J e f)) :
    n ∈ Good σ J e f :=
  ⟨n, hn, 1, 1, by rw [map_one, one_mul], by rw [tor_one hσ hJ he hff hef, Matrix.mul_one]⟩

theorem good_tor {l m : K} (hml : m * σ l = 1) : tor σ J e f l m ∈ Good σ J e f :=
  ⟨1, Submonoid.one_mem _, l, m, hml, by rw [Matrix.one_mul]⟩

theorem good_mul {g g' : Matrix ι ι K} (hg : g ∈ Good σ J e f) (hg' : g' ∈ Good σ J e f) :
    g * g' ∈ Good σ J e f := by
  obtain ⟨n, hn, l, m, hml, rfl⟩ := hg
  obtain ⟨n', hn', l', m', hml', rfl⟩ := hg'
  obtain ⟨n'', hn'', h⟩ := conj_closure hσ hJ he hff hef hml hn'
  refine ⟨n * n'', Submonoid.mul_mem _ hn hn'', l * l', m * m', ?_, ?_⟩
  · rw [map_mul]; linear_combination (m' * σ l') * hml + hml'
  · rw [← tor_mul hσ hJ he hff hef, Matrix.mul_assoc n, ← Matrix.mul_assoc (tor σ J e f l m), h]
    simp only [Matrix.mul_assoc]

theorem good_inv {g : Matrix ι ι K} (hg : g ∈ Good σ J e f) :
    ∃ g' ∈ Good σ J e f, g' * g = 1 ∧ g * g' = 1 := by
  obtain ⟨n, hn, l, m, hml, rfl⟩ := hg
  obtain ⟨ni, hni, h1, h2⟩ := closure_inv hσ hJ he hff hn
  have hlm : l * σ m = 1 := by rw [← hσ l, ← map_mul, mul_comm, hml, map_one]
  have hml' : σ l * σ (σ m) = 1 := by rw [hσ, mul_comm, hml]
  refine ⟨tor σ J e f (σ m) (σ l) * ni, good_mul hσ hJ he hff hef (good_tor hσ hJ he hff hef hml')
    (good_of_closure hσ hJ he hff hef hni), ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc ni, h1, Matrix.one_mul, tor_mul hσ hJ he hff hef,
      mul_comm (σ m), hlm, mul_comm (σ l) m, hml, tor_one hσ hJ he hff hef]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (tor σ J e f l m), tor_mul hσ hJ he hff hef, hlm,
      hml, tor_one hσ hJ he hff hef, Matrix.one_mul, h2]

theorem good_SU {δ : K} (hδ : IsUnit δ) (hσδ : σ δ = -δ) {g : Matrix ι ι K}
    (hg : g ∈ Good σ J e f) (hdet : g.det = 1) : g ∈ Submonoid.closure (eichSet σ J e f) := by
  obtain ⟨n, hn, l, m, hml, rfl⟩ := hg
  have hn1 : n.det = 1 := (closure_sub hσ hJ he hff hn).1
  rw [det_mul, hn1, one_mul, tor_det hσ hJ he hff hef] at hdet
  have hl : σ l = l := by
    calc σ l = (l * m) * σ l := by rw [hdet, one_mul]
      _ = l * (m * σ l) := by ring
      _ = l := by rw [hml, mul_one]
  obtain ⟨di, hdi⟩ := hδ.exists_right_inv
  exact Submonoid.mul_mem _ hn (tor_mem_closure hσ hJ he hff hef hσδ hdi hl hdet)

end

end ReciprocityTheory.ChartRestriction.G.SA
