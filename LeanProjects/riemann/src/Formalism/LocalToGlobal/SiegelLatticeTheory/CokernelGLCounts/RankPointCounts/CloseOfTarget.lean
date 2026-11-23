import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxMono
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount

noncomputable section

namespace Formalism.L2.SG.Pf.TupGlobApprox

open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.ProdEApprox Formalism.L2.SG.Pf.PCount

section Lat

variable {K : Type*} [CommRing K] (I : Subring K)

def lat (c : K) : AddSubgroup K where
  carrier := {x | ∃ y ∈ I, x = c * y}
  zero_mem' := ⟨0, I.zero_mem, by simp⟩
  add_mem' := by
    rintro x x' ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
    exact ⟨y + y', I.add_mem hy hy', by ring⟩
  neg_mem' := by
    rintro x ⟨y, hy, rfl⟩
    exact ⟨-y, I.neg_mem hy, by ring⟩

theorem mem_lat {c x : K} : x ∈ lat I c ↔ ∃ y ∈ I, x = c * y := Iff.rfl

variable {I}

theorem lat_mul {c c' x x' : K} (hx : x ∈ lat I c) (hx' : x' ∈ lat I c') : x * x' ∈ lat I (c * c') := by
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hx'
  exact ⟨y * y', I.mul_mem hy hy', by ring⟩

theorem lat_bmul {t c b x : K} (hb : t * b ∈ I) (hx : x ∈ lat I (t * c)) : b * x ∈ lat I c := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨t * b * y, I.mul_mem hb hy, by ring⟩

theorem lat_mulb {t c b x : K} (hb : t * b ∈ I) (hx : x ∈ lat I (t * c)) : x * b ∈ lat I c := by
  rw [mul_comm]; exact lat_bmul hb hx

theorem lat_mono {t c x : K} (ht : t ∈ I) (hx : x ∈ lat I (t * c)) : x ∈ lat I c := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨t * y, I.mul_mem ht hy, by ring⟩

theorem mem_of_lat {c x : K} (hc : c ∈ I) (hx : x ∈ lat I c) : x ∈ I := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact I.mul_mem hc hy

theorem lat_one {x : K} (hx : x ∈ lat I 1) : x ∈ I := mem_of_lat I.one_mem hx

theorem lat_sq {c : K} (hc : c ∈ I) : ∀ x ∈ lat I c, ∀ y ∈ lat I c, x * y ∈ lat I c :=
  fun _ hx _ hy => lat_mono hc (lat_mul hx hy)

variable {n : ℕ}

theorem ent_bmul {t c : K} {B X : Matrix (Fin n) (Fin n) K} (hB : ∀ i j, t * B i j ∈ I)
    (hX : EntIn (lat I (t * c)) X) : EntIn (lat I c) (B * X) := by
  intro i j
  rw [Matrix.mul_apply]
  exact (lat I c).sum_mem fun k _ => lat_bmul (hB i k) (hX k j)

theorem ent_mulb {t c : K} {B X : Matrix (Fin n) (Fin n) K} (hB : ∀ i j, t * B i j ∈ I)
    (hX : EntIn (lat I (t * c)) X) : EntIn (lat I c) (X * B) := by
  intro i j
  rw [Matrix.mul_apply]
  exact (lat I c).sum_mem fun k _ => lat_mulb (hB k j) (hX i k)

theorem ent_mono {t c : K} (ht : t ∈ I) {X : Matrix (Fin n) (Fin n) K} (hX : EntIn (lat I (t * c)) X) :
    EntIn (lat I c) X := fun i j => lat_mono ht (hX i j)

end Lat

section Bnd

variable {Fp : Type*} [Field Fp] {K : Type*} [CommRing K] [Algebra Fp K] {I : Subring K}

theorem bnd_fin (O : Subring Fp) (hI : ∀ s ∈ O, algebraMap Fp K s ∈ I) {ι : Type*} [Fintype ι] (f : ι → K)
    (h : ∀ i, ∃ s : Fp, s ≠ 0 ∧ s ∈ O ∧ algebraMap Fp K s * f i ∈ I) :
    ∃ s : Fp, s ≠ 0 ∧ s ∈ O ∧ ∀ i, algebraMap Fp K s * f i ∈ I := by
  classical
  choose s hs0 hsO hs using h
  refine ⟨∏ i, s i, Finset.prod_ne_zero_iff.2 fun i _ => hs0 i, O.prod_mem fun i _ => hsO i, fun i => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ i), map_mul,
    mul_comm (algebraMap Fp K (s i)), mul_assoc]
  exact I.mul_mem (hI _ (O.prod_mem fun j _ => hsO j)) (hs i)

end Bnd

section Stab

variable {K : Type*} [CommRing K]

theorem stab_core {r : ℕ} {P P' Q Q' N kL kR : Matrix (Fin (r + 1)) (Fin (r + 1)) K} {s e : K} (hs : IsUnit s)
    (hP : P' * P = 1) (hQ : Q * Q' = 1) (hkL : IsLo kL) (hkR : IsUp kR)
    (hk : kL * (s • (P * N * Q) - e • Ecorner r) * kR = s • (P * N * Q) - e • Ecorner r) :
    (P' * kL * P) * N * (Q * kR * Q') = N := by
  have h1 : kL * (s • (P * N * Q) - e • Ecorner r) * kR = s • (kL * (P * N * Q) * kR) - e • Ecorner r := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, lo_corner_up hkL hkR]
  rw [h1] at hk
  have h2 : s • (kL * (P * N * Q) * kR) = s • (P * N * Q) := sub_left_injective hk
  have h3 : kL * (P * N * Q) * kR = P * N * Q := hs.smul_left_cancel.mp h2
  calc (P' * kL * P) * N * (Q * kR * Q') = P' * (kL * (P * N * Q) * kR) * Q' := by
        simp only [Matrix.mul_assoc]
    _ = N := by
        rw [h3]
        simp only [Matrix.mul_assoc]
        rw [hQ, Matrix.mul_one, ← Matrix.mul_assoc, hP, Matrix.one_mul]

variable {n : ℕ}

theorem fix_of {σ : Fin n → Fin n} (hσ : ∀ a, σ (σ a) = a) {ν : Fin n → K} (hν : ∀ a, IsUnit (ν a))
    {z w : Matrix (Fin n) (Fin n) K} (hw : IsUp w) (h : z * mono σ ν * w = mono σ ν) :
    (∀ i j, σ j < σ i → z i j = 0) ∧ cOf σ ν z * w = 1 ∧ w * cOf σ ν z = 1 := by
  have hdw : IsUnit w.det := by rw [det_up' hw]; exact isUnit_one
  have e1 : z * mono σ ν = mono σ ν * w⁻¹ := by
    calc z * mono σ ν = z * mono σ ν * (w * w⁻¹) := by rw [Matrix.mul_nonsing_inv _ hdw, Matrix.mul_one]
      _ = mono σ ν * w⁻¹ := by rw [← Matrix.mul_assoc, h]
  have hwi := isUp_inv hw
  have hpat := fix_pat hσ ν hν (fun i j hij => hwi.2 j i hij) e1
  have e2 : cOf σ ν z = w⁻¹ := by
    have e3 : mono σ ν * cOf σ ν z = mono σ ν * w⁻¹ := by rw [← fix_cOf hσ ν hν z, e1]
    ext a b
    have := congrFun (congrFun e3 (σ a)) b
    rw [mono_mul, mono_mul, hσ] at this
    exact (hν (σ a)).mul_left_cancel this
  refine ⟨hpat, ?_, ?_⟩
  · rw [e2, Matrix.nonsing_inv_mul _ hdw]
  · rw [e2, Matrix.mul_nonsing_inv _ hdw]

theorem fix_inv {σ : Fin n → Fin n} (hσ : ∀ a, σ (σ a) = a) {ν : Fin n → K} (hν : ∀ a, IsUnit (ν a))
    {x w : Matrix (Fin n) (Fin n) K} (hx : IsLo x) (hw : IsUp w) (h : x * mono σ ν * w = mono σ ν) :
    IsLo x⁻¹ ∧ (∀ i j, σ j < σ i → x⁻¹ i j = 0) ∧ x * x⁻¹ = 1 := by
  have hdx : IsUnit x.det := by rw [det_lo' hx]; exact isUnit_one
  have e1 : x⁻¹ * mono σ ν = mono σ ν * w := by
    calc x⁻¹ * mono σ ν = x⁻¹ * (x * mono σ ν * w) := by rw [h]
      _ = mono σ ν * w := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdx, Matrix.one_mul]
  exact ⟨isLo_inv hx, fix_pat hσ ν hν (fun i j hij => hw.2 j i hij) e1, Matrix.mul_nonsing_inv _ hdx⟩

end Stab

section Close

variable {K : Type*} [CommRing K] {I : Subring K} {n : ℕ}

theorem cOf_sub_one {σ : Fin n → Fin n} (hσ : ∀ a, σ (σ a) = a) {ν : Fin n → K} (hν : ∀ a, IsUnit (ν a))
    {t c : K} (hb : ∀ a, t * ν a ∈ I) (hb' : ∀ a, t * Ring.inverse (ν a) ∈ I) {z : Matrix (Fin n) (Fin n) K}
    (hz : EntIn (lat I (t * (t * c))) (z - 1)) : EntIn (lat I c) (cOf σ ν z - 1) := by
  intro a b
  have e : (cOf σ ν z - 1) a b = Ring.inverse (ν (σ a)) * (z - 1) (σ a) (σ b) * ν (σ b) := by
    rw [Matrix.sub_apply, Matrix.sub_apply]
    by_cases hab : a = b
    · subst hab
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
      simp only [cOf, Matrix.of_apply]
      rw [mul_sub, sub_mul, mul_one, Ring.inverse_mul_cancel _ (hν _)]
    · have : σ a ≠ σ b := fun h => hab (by rw [← hσ a, h, hσ])
      rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne this]
      simp only [cOf, Matrix.of_apply, sub_zero]
  rw [e]
  exact lat_mulb (hb _) (lat_bmul (hb' _) (hz _ _))

theorem close_of_target {t c : K} {x T G : Matrix (Fin n) (Fin n) K} (hxT : x * T = 1) (bx : ∀ i j, t * x i j ∈ I)
    (hG : EntIn (lat I (t * c)) (G - T)) : EntIn (lat I c) (x * G - 1) := by
  have e : x * G - 1 = x * (G - T) := by rw [Matrix.mul_sub, hxT]
  rw [e]
  exact ent_bmul bx hG

theorem conj_eq {P P' X : Matrix (Fin n) (Fin n) K} (hPP : P * P' = 1) : P * (P' * X * P) * P' = X := by
  simp only [← Matrix.mul_assoc, hPP, Matrix.one_mul]
  rw [Matrix.mul_assoc, hPP, Matrix.mul_one]

theorem conj_sub_one {P P' X : Matrix (Fin n) (Fin n) K} (hPP : P * P' = 1) : P * (P' * X * P - 1) * P' = X - 1 := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPP, conj_eq hPP]

theorem close_pair {r : ℕ} {σ : Fin (r + 1) → Fin (r + 1)} (hσ : ∀ a, σ (σ a) = a) {ν : Fin (r + 1) → K}
    (hν : ∀ a, IsUnit (ν a)) {t c : K} (ht : t ∈ I) (hc : c ∈ I) (hbν : ∀ a, t * ν a ∈ I)
    (hbν' : ∀ a, t * Ring.inverse (ν a) ∈ I) {P P' Q Q' : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (hPP : P * P' = 1) (hP'P : P' * P = 1) (hQQ : Q * Q' = 1) (hQ'Q : Q' * Q = 1) (bP : ∀ i j, t * P i j ∈ I)
    (bP' : ∀ i j, t * P' i j ∈ I) (bQ : ∀ i j, t * Q i j ∈ I) (bQ' : ∀ i j, t * Q' i j ∈ I) {s e : K}
    (hs : IsUnit s) {a b : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (ha : IsLo a) (hb : IsUp b)
    (hab : a * (s • (P * mono σ ν * Q) - e • Ecorner r) * b = s • (P * mono σ ν * Q) - e • Ecorner r)
    (hz : IsLo (P' * a * P)) (hw : IsUp (Q * b * Q'))
    (hcl : EntIn (lat I (t * (t * (t * (t * c))))) (P' * a * P - 1)) :
    EntIn (lat I c) (a - 1) ∧ EntIn (lat I c) (b - 1) := by
  have hzw := stab_core hs hP'P hQQ ha hb hab
  obtain ⟨hpat, h1, h2⟩ := fix_of hσ hν hw hzw
  have hz2 : EntIn (lat I (t * (t * c))) (P' * a * P - 1) := ent_mono ht (ent_mono ht hcl)
  refine ⟨?_, ?_⟩
  · rw [← conj_sub_one hPP]
    exact ent_mulb bP' (ent_bmul bP hz2)
  · have hcO := cOf_sub_one hσ hν hbν hbν' hcl
    let x : GL (Fin (r + 1)) K := ⟨cOf σ ν (P' * a * P), Q * b * Q', h1, h2⟩
    have hup := cOf_up hσ ν (P' * a * P) hz.1 hpat hν
    have hJ : ∀ u ∈ lat I (t * (t * c)), ∀ v ∈ lat I (t * (t * c)), u * v ∈ lat I (t * (t * c)) :=
      lat_sq (I.mul_mem ht (I.mul_mem ht hc))
    have hlow : ∀ i j : Fin (r + 1), (fun k : Fin (r + 1) => r - k.val) i ≤ (fun k : Fin (r + 1) => r - k.val) j →
        ((x : Matrix (Fin (r + 1)) (Fin (r + 1)) K) - 1) i j = 0 := by
      intro i j hij
      have hij' : r - i.val ≤ r - j.val := hij
      have hji : j ≤ i := by
        rw [Fin.le_iff_val_le_val]
        have := i.isLt; have := j.isLt
        omega
      rw [Matrix.sub_apply]
      rcases hji.eq_or_lt with hji | hji
      · subst hji
        rw [Matrix.one_apply_eq]
        show cOf σ ν (P' * a * P) j j - 1 = 0
        rw [hup.1 j, sub_self]
      · rw [Matrix.one_apply_ne (Fin.ne_of_gt hji)]
        show cOf σ ν (P' * a * P) i j - 0 = 0
        rw [hup.2 i j hji, sub_self]
    have hinv := (inv_sub_one (fun k : Fin (r + 1) => r - k.val) (fun i => Nat.lt_succ_of_le (Nat.sub_le r i.val)) hJ x hlow hcO).1
    have hw1 : EntIn (lat I (t * (t * c))) (Q * b * Q' - 1) := hinv
    rw [← conj_sub_one hQ'Q]
    exact ent_mulb bQ (ent_bmul bQ' hw1)

end Close

end Formalism.L2.SG.Pf.TupGlobApprox
