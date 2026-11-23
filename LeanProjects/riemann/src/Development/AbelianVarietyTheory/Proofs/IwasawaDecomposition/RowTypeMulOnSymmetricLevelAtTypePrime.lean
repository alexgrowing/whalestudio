import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAdmissibleIntegralBasisChangeOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaCharSymMulInvEqOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

noncomputable section

namespace GlobalTheory.SymLevelMul

open Loc LocE GlobalTheory.SymLevelInv

section Comb

variable {κ : Type} [CommRing κ]

theorem superdiag {n k₀ rS r : ℕ} (hr : k₀ + rS < r) (hn : r ≤ n) (A B : ℕ → ℕ → κ)
    (hA : ∀ l p', l < n → p' < r → bd5 k₀ rS (symIdx k₀ rS p') ≤ symIdx k₀ rS l →
      A l p' = if l = p' then 1 else 0)
    (hB : ∀ l p', l < n → p' < r → bd5 k₀ rS (symIdx k₀ rS p') ≤ symIdx k₀ rS l →
      B l p' = if l = p' then 1 else 0)
    (p : ℕ) (hp : p + 1 < r) (hp' : p + 1 ≠ k₀) :
    ∑ l ∈ Finset.range n, A p l * B l (p + 1) = A p (p + 1) + B p (p + 1) := by
  have hle : ∀ s, bd5 k₀ rS (symIdx k₀ rS s) ≤ symIdx k₀ rS s := by
    intro s; unfold bd5; split_ifs <;> omega
  rw [Finset.sum_eq_add_of_mem p (p + 1) (by simp; omega) (by simp; omega) (by omega)]
  · rw [hA p p (by omega) (by omega) (hle p), hB (p + 1) (p + 1) (by omega) hp (hle _)]
    simp [add_comm]
  · rintro l hl ⟨h1, h2⟩
    rw [Finset.mem_range] at hl
    by_cases h : bd5 k₀ rS (symIdx k₀ rS (p + 1)) ≤ symIdx k₀ rS l
    · rw [hB l (p + 1) hl hp h, if_neg h2, mul_zero]
    · have h3 : l < r ∧ bd5 k₀ rS (symIdx k₀ rS l) ≤ symIdx k₀ rS p := by
        have e1 := symIdx_cases k₀ rS l
        have e2 := symIdx_cases k₀ rS p
        have e3 := symIdx_cases k₀ rS (p + 1)
        have e4 := symmetricBlockBoundary_cases k₀ rS (symIdx k₀ rS l)
        have e5 := symmetricBlockBoundary_cases k₀ rS (symIdx k₀ rS (p + 1))
        constructor <;> omega
      rw [hA p l (by omega) h3.1 h3.2, if_neg (Ne.symm h1), zero_mul]

theorem block {n a t : ℕ} (hn : a + t ≤ n) (A B C : ℕ → ℕ → κ)
    (hA : ∀ l l', l < n → l' < a → a ≤ l → A l l' = 0)
    (hB : ∀ l l', l < n → l' < a + t → a + t ≤ l → B l l' = 0)
    (hAB : ∀ p p', C p p' = ∑ l ∈ Finset.range n, A p l * B l p') :
    (Matrix.of fun s s' : Fin t => C (a + s.1) (a + s'.1)).det =
      (Matrix.of fun s s' : Fin t => A (a + s.1) (a + s'.1)).det *
      (Matrix.of fun s s' : Fin t => B (a + s.1) (a + s'.1)).det := by
  rw [← Matrix.det_mul]
  congr 1
  ext s s'
  have hs := s.2
  have hs' := s'.2
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range (fun l => A (a + s.1) (a + l) * B (a + l) (a + s'.1)) t, hAB]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Finset.sum_range_add, Finset.sum_range_add, Finset.sum_eq_zero (s := Finset.range a),
    Finset.sum_eq_zero (s := Finset.range m), zero_add, add_zero]
  · intro l hl
    rw [Finset.mem_range] at hl
    rw [hB _ _ (by omega) (by omega) (by omega), mul_zero]
  · intro l hl
    rw [Finset.mem_range] at hl
    rw [hA _ _ (by omega) (by omega) (by omega), zero_mul]

theorem fPos_fIdx {k₀ c n p : ℕ} (hk : k₀ ≤ n) (hp : p < n + c) :
    fIdx k₀ c n p < n + c ∧ fPos k₀ c n (fIdx k₀ c n p) = p := by
  unfold fIdx fPos
  split_ifs <;> omega

theorem fIdx_inj {k₀ c n p p' : ℕ} (hk : k₀ ≤ n) (hp : p < n + c) (hp' : p' < n + c) :
    fIdx k₀ c n p = fIdx k₀ c n p' ↔ p = p' :=
  ⟨fun h => by rw [← (fPos_fIdx hk hp).2, h, (fPos_fIdx hk hp').2], fun h => by rw [h]⟩

end Comb

section Main

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

omit [StarRing E] in
theorem unitV_mul {K : Type} [Field K] (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a b c : E}
    (h : redP P c = redP P a * redP P b) : unitV χ c = unitV χ a * unitV χ b := by
  unfold unitV
  by_cases hc : IsUnit (redP P c)
  · have hab := IsUnit.mul_iff.1 (h ▸ hc)
    rw [dif_pos hc, dif_pos hab.1, dif_pos hab.2, ← Units.val_mul, ← map_mul]
    congr 2
    exact Units.ext (by simpa using h)
  · rw [dif_neg hc]
    by_cases ha : IsUnit (redP P a)
    · rw [dif_neg (fun hb => hc (h ▸ ha.mul hb)), mul_zero]
    · rw [dif_neg ha, zero_mul]

def co (q k₀ n c : ℕ) (v : Sp E (n + c)) (p : ℕ) : E :=
  ((q : E) ^ scE n (fun i => i + 1) (fIdx k₀ c n p))⁻¹ * atN v (fIdx k₀ c n p)

omit [StarRing E] in
theorem entB_eq (hq : q ≠ 0) (k₀ n c : ℕ) (g : HomE E (n + c) (n + c)) (p p' : ℕ) :
    entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) g p p' = co q k₀ n c (g (bvecG E q k₀ n c p')) p := by
  have hq' : (q : E) ≠ 0 := Nat.cast_ne_zero.2 hq
  unfold entB co bvecG atN
  rw [map_smul, zpow_sub₀ hq']
  split_ifs
  · simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · simp

omit [StarRing E] in
theorem co_bvec (hq : q ≠ 0) {k₀ n c p p' : ℕ} (hk : k₀ ≤ n) (hp : p < n + c) (hp' : p' < n + c) :
    co q k₀ n c (bvecG E q k₀ n c p') p = if p = p' then 1 else 0 := by
  have hq' : (q : E) ≠ 0 := Nat.cast_ne_zero.2 hq
  unfold co bvecG atN eN
  rw [dif_pos (fPos_fIdx hk hp).1]
  simp only [Pi.smul_apply, smul_eq_mul, fIdx_inj hk hp hp']
  split_ifs with h
  · subst h
    rw [mul_one, inv_mul_cancel₀ (zpow_ne_zero _ hq')]
  · simp

omit [NumberField E] [StarRing E] in
theorem co_sub (k₀ n c : ℕ) (v w : Sp E (n + c)) (p : ℕ) :
    co q k₀ n c (v - w) p = co q k₀ n c v p - co q k₀ n c w p := by
  unfold co atN
  split_ifs
  · rw [Pi.sub_apply, mul_sub]
  · simp

omit [NumberField E] [StarRing E] in
theorem co_sum (k₀ n c : ℕ) (s : Finset ℕ) (a : ℕ → E) (v : ℕ → Sp E (n + c)) (p : ℕ) :
    co q k₀ n c (∑ l ∈ s, a l • v l) p = ∑ l ∈ s, co q k₀ n c (v l) p * a l := by
  unfold co atN
  split_ifs
  · rw [Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    ring
  · simp

omit [StarRing E] in
theorem eq_sum_co (hq : q ≠ 0) {k₀ n c : ℕ} (hk : k₀ ≤ n) (v : Sp E (n + c)) :
    v = ∑ l ∈ Finset.range (n + c), co q k₀ n c v l • bvecG E q k₀ n c l := by
  have hq' : (q : E) ≠ 0 := Nat.cast_ne_zero.2 hq
  funext i
  obtain ⟨h1, h2⟩ := GlobalTheory.LastSteps.fIdx_fPos hk i.2
  rw [Finset.sum_apply, Finset.sum_eq_single (fPos k₀ c n i.1)]
  · unfold co bvecG atN eN
    simp only [h2, dif_pos i.2, Pi.smul_apply, smul_eq_mul, if_true, Fin.eta]
    have := zpow_ne_zero (scE n (fun i => i + 1) i.1) hq'
    field_simp
  · intro l hl hne
    rw [Finset.mem_range] at hl
    unfold bvecG eN
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [if_neg, mul_zero, mul_zero]
    intro h
    exact hne (by rw [h, (fPos_fIdx hk hl).2])
  · intro h
    exact absurd (Finset.mem_range.2 h1) h

omit [StarRing E] in
theorem entB_mul (hq : q ≠ 0) {k₀ n c : ℕ} (hk : k₀ ≤ n) (g g' : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (p p' : ℕ) :
    entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) (g * g').toLinearMap p p' =
      ∑ l ∈ Finset.range (n + c), entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) g.toLinearMap p l *
        entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) g'.toLinearMap l p' := by
  simp only [entB_eq hq]
  show co q k₀ n c (g.toLinearMap (g'.toLinearMap _)) p = _
  conv_lhs => rw [eq_sum_co hq hk (g'.toLinearMap _), map_sum]
  simp only [map_smul]
  rw [co_sum]

theorem co_of_mem_flagS (hq : q ≠ 0) (hP : (q : 𝓞 E) ∈ P.asIdeal) {k₀ rS n c s p : ℕ} (hk : k₀ ≤ n)
    {v : Sp E (n + c)} (hv : v ∈ flagS P q k₀ rS n c s) (hp : p < n + c) (h : bd5 k₀ rS s ≤ symIdx k₀ rS p) :
    IntAt P (co q k₀ n c v p) ∧ redP P (co q k₀ n c v p) = 0 := by
  have hq' : (q : E) ≠ 0 := Nat.cast_ne_zero.2 hq
  obtain ⟨h1, h2⟩ := fPos_fIdx hk hp
  unfold flagS at hv
  rw [SymLevelInv.mem_sclLat] at hv
  have h3 := hv ⟨_, h1⟩
  simp only [] at h3
  rw [h2, if_pos h, zpow_add_one₀ hq', mul_inv] at h3
  refine of_inv_mul P hq hP ?_
  unfold co atN
  rw [dif_pos h1]
  convert h3 using 1
  ring

theorem bvec_mem_flagS (hq : q ≠ 0) {k₀ rS n c s p : ℕ} (hk : k₀ ≤ n) (hp : p < n + c)
    (h : ¬ bd5 k₀ rS s ≤ symIdx k₀ rS p) : bvecG E q k₀ n c p ∈ flagS P q k₀ rS n c s := by
  have hq' : (q : E) ≠ 0 := Nat.cast_ne_zero.2 hq
  unfold flagS
  rw [SymLevelInv.mem_sclLat]
  intro x
  unfold bvecG eN
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hx : x.1 = fIdx k₀ c n p
  · rw [if_pos hx, hx, (fPos_fIdx hk hp).2, if_neg h, add_zero, mul_one, inv_mul_cancel₀ (zpow_ne_zero _ hq')]
    exact SymLevelInv.intAt_one P
  · rw [if_neg hx, mul_zero, mul_zero]
    exact SymLevelInv.intAt_zero P

theorem entB_col (hq : q ≠ 0) (hP : (q : 𝓞 E) ∈ P.asIdeal) {k₀ rS r t n c : ℕ} (hk : k₀ ≤ n) (hr : k₀ + rS < r)
    (hn : r ≤ n + c) {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hg : g ∈ JGsym P q k₀ rS r t n c)
    (l p' : ℕ) (hl : l < n + c) (hp' : p' < r) (h : bd5 k₀ rS (symIdx k₀ rS p') ≤ symIdx k₀ rS l) :
    redP P (entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) g.toLinearMap l p') = if l = p' then 1 else 0 := by
  have h1 := (hg.2.2 (symIdx k₀ rS p') (symIdx_lt hr.le hp')).2
  unfold bvecS at h1
  rw [symIdxInv_symIdx] at h1
  obtain ⟨h3, h4⟩ := co_of_mem_flagS hq hP hk h1 hl h
  have e2 : entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) g.toLinearMap l p' =
      co q k₀ n c (g (bvecG E q k₀ n c p') - bvecG E q k₀ n c p') l + if l = p' then 1 else 0 := by
    rw [entB_eq hq, co_sub, co_bvec hq hk hl (by omega)]
    exact (sub_add_cancel _ _).symm
  rw [e2, reduction_add h3 (intAt_ite _), h4, zero_add]
  split_ifs
  · exact reduction_one' P
  · exact redP_zero' P

theorem entB_blk (hq : q ≠ 0) (hP : (q : 𝓞 E) ∈ P.asIdeal) {k₀ rS r t n c : ℕ} (hk : k₀ ≤ n) (hr : k₀ + rS < r)
    {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hg : g ∈ JGsym P q k₀ rS r t n c) (i : ℕ)
    (l l' : ℕ) (hl : l < n + c) (hl' : l' < r + i * t) (h : r + i * t ≤ l) :
    redP P (entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) g.toLinearMap l l') = 0 := by
  have key : ∀ x, bd5 k₀ rS (r + i * t) ≤ symIdx k₀ rS x ↔ r + i * t ≤ x := by
    intro x
    have e1 := symIdx_cases k₀ rS x
    have e2 := symmetricBlockBoundary_cases k₀ rS (r + i * t)
    generalize i * t = m at *
    omega
  have h0 : bvecG E q k₀ n c l' ∈ flagS P q k₀ rS n c (r + i * t) :=
    bvec_mem_flagS hq hk (by omega) (by rw [key]; omega)
  have h1 := (hg.2.1 (r + i * t) ⟨i, rfl⟩ _).2 h0
  rw [entB_eq hq]
  exact (co_of_mem_flagS hq hP hk h1 hl ((key l).2 h)).2

theorem lamGBS_mul {K : Type} [Field K] (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    {k₀ rS r t j n c : ℕ} (hk : k₀ ≤ n) (hr : k₀ + rS < r) (hn : r + j * t ≤ n + c)
    {g g' : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hg : g ∈ JGsym P (qOf P) k₀ rS r t n c)
    (hg' : g' ∈ JGsym P (qOf P) k₀ rS r t n c) :
    lamGBS (qOf P) ψ₀ χ k₀ r t j n c (g * g').toLinearMap =
      lamGBS (qOf P) ψ₀ χ k₀ r t j n c g.toLinearMap * lamGBS (qOf P) ψ₀ χ k₀ r t j n c g'.toLinearMap := by
  have hq : qOf P ≠ 0 := fun h => GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P (by rw [h, Nat.cast_zero])
  have hP : ((qOf P : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem _
  have hrn : r ≤ n + c := le_trans (Nat.le_add_right _ _) hn
  have hint : ∀ g ∈ JGsym P (qOf P) k₀ rS r t n c, ∀ p p',
      IntAt P (entB (qOf P) k₀ c n c n (fun i => i + 1) (fun i => i + 1) g.toLinearMap p p') :=
    fun g hg => GlobalTheory.LastSteps.entB_int k₀ fun y hy => (hg.1 y).2 hy
  have iA := hint g hg
  have iB := hint g' hg'
  have iC := hint _ (mul_mem hg hg')
  have cA := entB_col hq hP hk hr hrn hg
  have cB := entB_col hq hP hk hr hrn hg'
  have bA := entB_blk hq hP hk hr hg
  have bB := entB_blk hq hP hk hr hg'
  have hm := entB_mul hq hk g g'
  unfold lamGBS
  generalize entB (qOf P) k₀ c n c n (fun i => i + 1) (fun i => i + 1) (g * g').toLinearMap = C at *
  generalize entB (qOf P) k₀ c n c n (fun i => i + 1) (fun i => i + 1) g.toLinearMap = A at *
  generalize entB (qOf P) k₀ c n c n (fun i => i + 1) (fun i => i + 1) g'.toLinearMap = B at *
  have hred : ∀ p p', redP P (C p p') = ∑ l ∈ Finset.range (n + c), redP P (A p l) * redP P (B l p') := by
    intro p p'
    rw [hm, SymLevelInv.reduction_sum₂ P _ _ fun l _ => (iA p l).mul (iB l p')]
    exact Finset.sum_congr rfl fun l _ => reduction_mul (iA p l) (iB l p')
  have hsd : ∀ p, p + 1 < r → p + 1 ≠ k₀ →
      redP P (C p (p + 1)) = redP P (A p (p + 1)) + redP P (B p (p + 1)) := fun p hp hp' =>
    (hred _ _).trans (superdiag hr hrn (fun a b => redP P (A a b)) (fun a b => redP P (B a b)) cA cB p hp hp')
  have hs : ∀ M : ℕ → ℕ → E, (∀ p p', IntAt P (M p p')) →
      redP P (∑ i ∈ Finset.range (k₀ - 1), M i (i + 1) + ∑ i ∈ Finset.range (r - k₀ - 1), M (k₀ + i) (k₀ + i + 1)) =
      ∑ i ∈ Finset.range (k₀ - 1), redP P (M i (i + 1)) +
        ∑ i ∈ Finset.range (r - k₀ - 1), redP P (M (k₀ + i) (k₀ + i + 1)) := fun M hM => by
    rw [reduction_add (SymLevelInv.intAt_sum P _ _ fun _ _ => hM _ _) (SymLevelInv.intAt_sum P _ _ fun _ _ => hM _ _),
      SymLevelInv.reduction_sum₂ P _ _ fun _ _ => hM _ _, SymLevelInv.reduction_sum₂ P _ _ fun _ _ => hM _ _]
  have hd : ∀ M : ℕ → ℕ → E, (∀ p p', IntAt P (M p p')) → ∀ a,
      redP P (Matrix.det (Matrix.of fun s s' : Fin t => M (a + s.1) (a + s'.1))) =
      Matrix.det (Matrix.of fun s s' : Fin t => redP P (M (a + s.1) (a + s'.1))) := fun M hM a =>
    SymLevelInv.reduction_det P _ fun _ _ => hM _ _
  unfold lamGvS
  rw [mul_mul_mul_comm, ← AddChar.map_add_eq_mul, ← Finset.prod_mul_distrib, hs A iA, hs B iB, hs C iC,
    add_add_add_comm, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1
  · congr 2
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      exact hsd _ (by omega) (by omega)
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      exact hsd _ (by omega) (by omega)
  · refine Finset.prod_congr rfl fun i hi => unitV_mul _ ?_
    rw [Finset.mem_range] at hi
    have hi' : r + i * t + t ≤ n + c := by
      have : (i + 1) * t ≤ j * t := Nat.mul_le_mul_right t hi
      rw [add_mul, one_mul] at this
      omega
    rw [hd A iA, hd B iB, hd C iC]
    refine block hi' (fun a b => redP P (A a b)) (fun a b => redP P (B a b)) (fun a b => redP P (C a b))
      (bA i) ?_ hred
    have h := bB (i + 1)
    rwa [add_mul, one_mul, ← add_assoc] at h

end Main

theorem lamRow_mul : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), j < R.m → P ∈ Pr.vGs → ∀ g ∈ Jat (Pr := Pr) (R := R) true j P, ∀ g' ∈ Jat (Pr := Pr) (R := R) true j P, lamRow Ch mu true j P (g * g').toLinearMap = lamRow Ch mu true j P g.toLinearMap * lamRow Ch mu true j P g'.toLinearMap := by
  intro X Pr R Ch S mu j P hj hP g hg g' hg'
  unfold Jat at hg hg'
  rw [if_pos hP, if_pos rfl] at hg hg'
  unfold lamRow
  simp only [if_pos hP, if_true]
  have h2 := R.two_le_m
  refine lamGBS_mul _ _ ?_ ?_ ?_ hg hg'
  · exact Nat.le_add_right _ _
  · unfold Ranks.rS Ranks.r
    omega
  · unfold Ranks.r Ranks.N cOf
    rw [mul_add, mul_one]
    omega

end GlobalTheory.SymLevelMul

end
