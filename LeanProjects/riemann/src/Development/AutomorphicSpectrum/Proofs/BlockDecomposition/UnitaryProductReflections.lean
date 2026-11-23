import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology Matrix

namespace GlobalTheory.CompanionTheory.SaGen.ReflList

open Formalism.UG (hform UJ cT)

variable {R : Type} [CommRing R] {M : ℕ} (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R)

theorem hform_add_left (x y z : Fin M → R) : hform c Jm (x + y) z = hform c Jm x z + hform c Jm y z := by
  simp [hform, add_mul, Finset.sum_add_distrib]

theorem hform_add_right (x y z : Fin M → R) : hform c Jm z (x + y) = hform c Jm z x + hform c Jm z y := by
  simp [hform, mul_add, Finset.sum_add_distrib]

theorem hform_smul_left (s : R) (x z : Fin M → R) : hform c Jm (s • x) z = c s * hform c Jm x z := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_smul_right (s : R) (x z : Fin M → R) : hform c Jm z (s • x) = s * hform c Jm z x := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_sub_smul_left (s : R) (x y z : Fin M → R) :
    hform c Jm (x - s • y) z = hform c Jm x z - c s * hform c Jm y z := by
  rw [sub_eq_add_neg, ← neg_smul, hform_add_left, hform_smul_left, map_neg]
  ring

theorem hform_sub_smul_right (s : R) (x y z : Fin M → R) :
    hform c Jm z (x - s • y) = hform c Jm z x - s * hform c Jm z y := by
  rw [sub_eq_add_neg, ← neg_smul, hform_add_right, hform_smul_right]
  ring

theorem hform_conj (hc : ∀ x, c (c x) = x) (hJ : ∀ i j, c (Jm j i) = Jm i j) (x y : Fin M → R) :
    c (hform c Jm x y) = hform c Jm y x := by
  simp only [hform, map_sum, map_mul, hc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]
  ring

theorem hform_eq_dot (x y : Fin M → R) : hform c Jm x y = (c ∘ x) ⬝ᵥ (Jm *ᵥ y) := by
  simp [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec (g : Matrix (Fin M) (Fin M) R) (x y : Fin M → R) :
    hform c Jm (g *ᵥ x) (g *ᵥ y) = hform c (cT c g * Jm * g) x y := by
  have h1 : c ∘ (g *ᵥ x) = (g.map c) *ᵥ (c ∘ x) := by
    ext i
    simp [RingHom.map_mulVec]
  rw [hform_eq_dot, hform_eq_dot, h1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, cT,
    Matrix.dotProduct_mulVec (c ∘ x), Matrix.vecMul_transpose]

theorem hform_single (i j : Fin M) : hform c Jm (Pi.single i 1) (Pi.single j 1) = Jm i j := by
  have h1 : c ∘ (Pi.single i 1 : Fin M → R) = Pi.single i 1 := by
    ext l
    by_cases h : l = i <;> simp [Pi.single_apply, h]
  rw [hform_eq_dot, h1]
  simp

theorem hform_isom {x : GL (Fin M) R} (hx : x ∈ UJ c Jm) (u v : Fin M → R) :
    hform c Jm ((x : Matrix (Fin M) (Fin M) R) *ᵥ u) ((x : Matrix (Fin M) (Fin M) R) *ᵥ v) = hform c Jm u v := by
  have h : cT c (x : Matrix (Fin M) (Fin M) R) * Jm * (x : Matrix (Fin M) (Fin M) R) = Jm := hx
  rw [hform_mulVec, h]

def rowV (a : Fin M → R) : Fin M → R := fun j => ∑ i, c (a i) * Jm i j

theorem rowV_dot (a z : Fin M → R) : rowV c Jm a ⬝ᵥ z = hform c Jm a z := by
  simp only [dotProduct, rowV, hform, Finset.sum_mul]
  exact Finset.sum_comm

theorem qr_eq (a : Fin M → R) (k : R) : qr c Jm a k = 1 + k • Matrix.vecMulVec a (rowV c Jm a) := rfl

theorem qr_mulVec (a z : Fin M → R) (k : R) :
    qr c Jm a k *ᵥ z = z + (k * hform c Jm a z) • a := by
  rw [qr_eq, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, ← rowV_dot]
  ext i
  simp [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]

theorem qr_mul (a : Fin M → R) (k k' : R) :
    qr c Jm a k * qr c Jm a k' = qr c Jm a (k + k' + k * k' * hform c Jm a a) := by
  have h : Matrix.vecMulVec a (rowV c Jm a) * Matrix.vecMulVec a (rowV c Jm a) =
      hform c Jm a a • Matrix.vecMulVec a (rowV c Jm a) := by
    ext i j
    rw [← rowV_dot]
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, dotProduct,
      Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp only [qr_eq, add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, h, smul_smul, add_smul]
  abel_nf
  rw [show k' * (k * hform c Jm a a) = k * k' * hform c Jm a a by ring]

theorem qr_zero (a : Fin M → R) : qr c Jm a 0 = 1 := by
  simp [qr_eq]

theorem mat_ext_hform {G G' : Matrix (Fin M) (Fin M) R}
    (H : ∀ x y, hform c G x y = hform c G' x y) : G = G' := by
  ext i j
  rw [← hform_single c G i j, ← hform_single c G' i j, H]

theorem qr_unitary (hc : ∀ x, c (c x) = x) (hJ : ∀ i j, c (Jm j i) = Jm i j) (a : Fin M → R) (k : R)
    (hk : k + c k + k * c k * hform c Jm a a = 0) :
    cT c (qr c Jm a k) * Jm * qr c Jm a k = Jm := by
  refine mat_ext_hform c fun x y => ?_
  rw [← hform_mulVec, qr_mulVec, qr_mulVec, hform_add_left, hform_add_right, hform_add_right,
    hform_smul_left, hform_smul_left, hform_smul_right, hform_smul_right, map_mul,
    hform_conj c Jm hc hJ a x]
  linear_combination (hform c Jm x a * hform c Jm a y) * hk

theorem qr_rel (hc : ∀ x, c (c x) = x) (hJ : ∀ i j, c (Jm j i) = Jm i j) {a : Fin M → R} {l k : R}
    (hu : IsUnit (hform c Jm a a)) (hl : l * c l = 1) (hk : k * hform c Jm a a = l - 1) :
    k + c k + k * c k * hform c Jm a a = 0 := by
  have hH : c (hform c Jm a a) = hform c Jm a a := hform_conj c Jm hc hJ a a
  have hk' : c k * hform c Jm a a = c l - 1 := by
    have := congrArg c hk
    rwa [map_mul, hH, map_sub, map_one] at this
  apply hu.mul_left_injective
  simp only [zero_mul]
  linear_combination (1 + c k * hform c Jm a a) * hk + l * hk' + hl

theorem exists_qrGL (hc : ∀ x, c (c x) = x) (hJ : ∀ i j, c (Jm j i) = Jm i j) {a : Fin M → R} {l k : R}
    (hu : IsUnit (hform c Jm a a)) (hl : l * c l = 1) (hk : k * hform c Jm a a = l - 1) :
    ∃ T : GL (Fin M) R, (T : Matrix (Fin M) (Fin M) R) = qr c Jm a k ∧ T ∈ UJ c Jm ∧
      IsQR c Jm (T : Matrix (Fin M) (Fin M) R) := by
  have hr := qr_rel c Jm hc hJ hu hl hk
  refine ⟨⟨qr c Jm a k, qr c Jm a (c k), ?_, ?_⟩, rfl, ?_, a, l, k, hu, hl, hk, rfl⟩
  · rw [qr_mul, hr, qr_zero]
  · rw [qr_mul, add_comm (c k), mul_comm (c k), hr, qr_zero]
  · exact qr_unitary c Jm hc hJ a k hr

theorem exists_step (hc : ∀ x, c (c x) = x) (hN : NormOneGen c) (hJ : ∀ i j, c (Jm j i) = Jm i j)
    (e : Fin M → Fin M → R) (ho : ∀ i j, i ≠ j → hform c Jm (e i) (e j) = 0)
    (hu : ∀ i, IsUnit (hform c Jm (e i) (e i))) (x : GL (Fin M) R) (hx : x ∈ UJ c Jm) (k : Fin M)
    (hfix : ∀ i : Fin M, i < k → (x : Matrix (Fin M) (Fin M) R) *ᵥ e i = e i) :
    ∃ T₂ T₁ : GL (Fin M) R, (T₂ ∈ UJ c Jm ∧ IsQR c Jm (T₂ : Matrix (Fin M) (Fin M) R)) ∧
      (T₁ ∈ UJ c Jm ∧ IsQR c Jm (T₁ : Matrix (Fin M) (Fin M) R)) ∧
      ∀ i : Fin M, i ≤ k → ((T₂ * T₁ : GL (Fin M) R) : Matrix (Fin M) (Fin M) R) *ᵥ e i =
        (x : Matrix (Fin M) (Fin M) R) *ᵥ e i := by
  obtain ⟨u, hudef⟩ : ∃ u, u = e k := ⟨_, rfl⟩
  obtain ⟨f, hfdef⟩ : ∃ f, f = (x : Matrix (Fin M) (Fin M) R) *ᵥ u := ⟨_, rfl⟩
  obtain ⟨α, hαdef⟩ : ∃ α, α = hform c Jm u u := ⟨_, rfl⟩
  obtain ⟨p, hpdef⟩ : ∃ p, p = hform c Jm u f := ⟨_, rfl⟩
  have hff : hform c Jm f f = α := by rw [hfdef, hform_isom c Jm hx, hαdef]
  have hαu : IsUnit α := by rw [hαdef, hudef]; exact hu k
  have hcα : c α = α := by rw [hαdef]; exact hform_conj c Jm hc hJ u u
  have hfu : hform c Jm f u = c p := by rw [hpdef]; exact (hform_conj c Jm hc hJ u f).symm
  obtain ⟨μ, hμ, h1, h2⟩ := hN α p hαu hcα
  have hμ' : c μ * μ = 1 := by rw [mul_comm]; exact hμ
  obtain ⟨w, hwdef⟩ : ∃ w, w = u - μ • f := ⟨_, rfl⟩
  obtain ⟨d, hddef⟩ : ∃ d, d = hform c Jm w u := ⟨_, rfl⟩
  have hd : d = α - c μ * c p := by
    rw [hddef, hwdef, hform_sub_smul_left, hfu, hαdef]
  have hdu : IsUnit d := by
    have := h1.map c
    rwa [map_sub, map_mul, hcα, ← hd] at this
  have hcd : c d = α - μ * p := by
    rw [hd, map_sub, map_mul, hc, hc, hcα]
  have hww : hform c Jm w w = d + c d := by
    have e1 : hform c Jm w w = hform c Jm u w - c μ * hform c Jm f w := by
      conv_lhs => rw [hwdef]
      rw [hform_sub_smul_left]
      rw [hwdef]
    rw [e1, hwdef, hform_sub_smul_right, hform_sub_smul_right, hff, hfu, ← hαdef, ← hpdef, hcd, hd]
    linear_combination α * hμ'
  have hwwu : IsUnit (hform c Jm w w) := by
    have : hform c Jm w w = 2 * α - μ * p - c (μ * p) := by
      rw [hww, hcd, hd, map_mul]
      ring
    rw [this]
    exact h2
  obtain ⟨di, hdi⟩ := hdu.exists_right_inv
  obtain ⟨αi, hαi⟩ := hαu.exists_right_inv
  have hcdi : c d * c di = 1 := by rw [← map_mul, hdi, map_one]
  obtain ⟨T₁, hT₁, hT₁U, hT₁Q⟩ := exists_qrGL c Jm hc hJ (a := w) (l := -c d * di) (k := -di) hwwu
    (by
      rw [map_mul, map_neg, hc]
      linear_combination (c d * c di) * hdi + hcdi)
    (by
      rw [hww]
      linear_combination (-1 : R) * hdi)
  obtain ⟨T₂, hT₂, hT₂U, hT₂Q⟩ := exists_qrGL c Jm hc hJ (a := f) (l := c μ) (k := (c μ - 1) * αi)
    (by rw [hff]; exact hαu) (by rw [hc]; exact hμ')
    (by
      rw [hff]
      linear_combination (c μ - 1) * hαi)
  have hT₁u : qr c Jm w (-di) *ᵥ u = μ • f := by
    rw [qr_mulVec, ← hddef]
    have e1 : -di * d = -1 := by linear_combination (-1 : R) * hdi
    rw [e1, hwdef]
    simp
  have hT₂μ : qr c Jm f ((c μ - 1) * αi) *ᵥ (μ • f) = f := by
    rw [qr_mulVec, hform_smul_right, hff, ← add_smul]
    have e1 : μ + (c μ - 1) * αi * (μ * α) = 1 := by
      linear_combination ((c μ - 1) * μ) * hαi + hμ'
    rw [e1, one_smul]
  refine ⟨T₂, T₁, ⟨hT₂U, hT₂Q⟩, ⟨hT₁U, hT₁Q⟩, fun i hi => ?_⟩
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, hT₁, hT₂]
  rcases hi.lt_or_eq with hlt | rfl
  · have huo : hform c Jm u (e i) = 0 := by rw [hudef]; exact ho _ _ hlt.ne'
    have hfo : hform c Jm f (e i) = 0 := by
      rw [hfdef, ← hfix i hlt, hform_isom c Jm hx]
      exact huo
    have hwo : hform c Jm w (e i) = 0 := by
      rw [hwdef, hform_sub_smul_left, huo, hfo]
      simp
    have a1 : qr c Jm w (-di) *ᵥ e i = e i := by
      rw [qr_mulVec, hwo, mul_zero, zero_smul, add_zero]
    rw [a1, qr_mulVec, hfo, mul_zero, zero_smul, add_zero, hfix i hlt]
  · rw [← hudef, hT₁u, hT₂μ, hfdef]

theorem eq_one_of_fix (e : Fin M → Fin M → R) (hdet : IsUnit (Matrix.of e).det) (x : GL (Fin M) R)
    (hfix : ∀ i, (x : Matrix (Fin M) (Fin M) R) *ᵥ e i = e i) : x = 1 := by
  have h1 : Matrix.of e * (x : Matrix (Fin M) (Fin M) R)ᵀ = Matrix.of e * 1 := by
    ext i j
    have := congrFun (hfix i) j
    rw [Matrix.mul_one, Matrix.of_apply, ← this]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  have hU : IsUnit (Matrix.of e) := (Matrix.isUnit_iff_isUnit_det _).2 hdet
  have h2 : (x : Matrix (Fin M) (Fin M) R)ᵀ = 1 := hU.mul_right_injective h1
  apply Units.ext
  rw [Units.val_one, ← Matrix.transpose_transpose (x : Matrix (Fin M) (Fin M) R), h2, Matrix.transpose_one]

theorem reflection_list_exists (hc : ∀ x, c (c x) = x) (hN : NormOneGen c) (hJ : ∀ i j, c (Jm j i) = Jm i j)
    (e : Fin M → Fin M → R) (ho : ∀ i j, i ≠ j → hform c Jm (e i) (e j) = 0)
    (hu : ∀ i, IsUnit (hform c Jm (e i) (e i))) (hdet : IsUnit (Matrix.of e).det) :
    ∀ (n k : ℕ), k + n = M → ∀ x : GL (Fin M) R, x ∈ UJ c Jm →
      (∀ i : Fin M, i.val < k → (x : Matrix (Fin M) (Fin M) R) *ᵥ e i = e i) →
      ∃ l : List (GL (Fin M) R), (∀ y ∈ l, y ∈ UJ c Jm ∧ IsQR c Jm (y : Matrix (Fin M) (Fin M) R)) ∧
        l.prod = x := by
  intro n
  induction n with
  | zero =>
    intro k hk x _ hfix
    have h1 := eq_one_of_fix e hdet x fun i => hfix i (by have := i.isLt; omega)
    exact ⟨[], by simp, by simp [h1]⟩
  | succ n ih =>
    intro k hk x hx hfix
    obtain ⟨T₂, T₁, ⟨h2U, h2Q⟩, ⟨h1U, h1Q⟩, hT⟩ := exists_step c Jm hc hN hJ e ho hu x hx
      ⟨k, by omega⟩ (fun i hi => hfix i hi)
    have hy : (T₂ * T₁)⁻¹ * x ∈ UJ c Jm :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ h2U h1U)) hx
    obtain ⟨l, hl, hp⟩ := ih (k + 1) (by omega) _ hy (fun i hi => by
      have h1 := hT i (Nat.lt_succ_iff.1 hi)
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← h1, Matrix.mulVec_mulVec, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, Matrix.one_mulVec])
    refine ⟨T₂ :: T₁ :: l, ?_, ?_⟩
    · intro y hy'
      simp only [List.mem_cons] at hy'
      rcases hy' with rfl | rfl | hy'
      · exact ⟨h2U, h2Q⟩
      · exact ⟨h1U, h1Q⟩
      · exact hl y hy'
    · rw [List.prod_cons, List.prod_cons, hp, ← mul_assoc, mul_inv_cancel_left]

theorem exists_qr_list {R : Type} [CommRing R] (c : R →+* R) (hc : ∀ x, c (c x) = x) (hN : NormOneGen c) {M : ℕ}
    (Jm : Matrix (Fin M) (Fin M) R) (hJ : ∀ i j, c (Jm j i) = Jm i j) (e : Fin M → Fin M → R)
    (ho : ∀ i j, i ≠ j → Formalism.UG.hform c Jm (e i) (e j) = 0)
    (hu : ∀ i, IsUnit (Formalism.UG.hform c Jm (e i) (e i))) (hdet : IsUnit (Matrix.of e).det)
    (x : GL (Fin M) R) (hx : x ∈ Formalism.UG.UJ c Jm) :
    ∃ l : List (GL (Fin M) R), (∀ y ∈ l, y ∈ Formalism.UG.UJ c Jm ∧ IsQR c Jm (y : Matrix (Fin M) (Fin M) R)) ∧
      l.prod = x :=
  reflection_list_exists c Jm hc hN hJ e ho hu hdet M 0 (by omega) x hx (fun i hi => absurd hi (by omega))

end GlobalTheory.CompanionTheory.SaGen.ReflList
