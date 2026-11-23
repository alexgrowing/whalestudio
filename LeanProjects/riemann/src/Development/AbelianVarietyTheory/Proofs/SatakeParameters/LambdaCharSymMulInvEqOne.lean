import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.SymLevelInv

open Loc LocE

section Red

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

theorem intAt_zero : IntAt P (0 : E) := by simpa using IntAt.coe P 0
theorem intAt_one : IntAt P (1 : E) := by simpa using IntAt.coe P 1
theorem redP_zero' : redP P (0 : E) = 0 := by simpa using reduction_coe P 0
theorem reduction_one' : redP P (1 : E) = 1 := by simpa using reduction_coe P 1

def intRing : Subring E where
  carrier := {a | IntAt P a}
  mul_mem' := IntAt.mul
  one_mem' := intAt_one P
  add_mem' := IntAt.add
  zero_mem' := intAt_zero P
  neg_mem' := fun {a} ha => by
    have h := IntAt.mul (IntAt.coe P (-1)) ha
    simpa using h

def redHom : intRing P →+* 𝓞 E ⧸ P.asIdeal where
  toFun a := redP P a.1
  map_one' := reduction_one' P
  map_mul' a b := reduction_mul a.2 b.2
  map_zero' := redP_zero' P
  map_add' a b := reduction_add a.2 b.2

theorem intAt_sum {ι : Type} (s : Finset ι) (f : ι → E) (h : ∀ i ∈ s, IntAt P (f i)) :
    IntAt P (∑ i ∈ s, f i) := (intRing P).sum_mem h

theorem reduction_sum₂ {ι : Type} (s : Finset ι) (f : ι → E) (h : ∀ i ∈ s, IntAt P (f i)) :
    redP P (∑ i ∈ s, f i) = ∑ i ∈ s, redP P (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using redP_zero' P
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      reduction_add (h a (Finset.mem_insert_self _ _))
        (intAt_sum P s f fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

theorem reduction_det {t : ℕ} (A : Matrix (Fin t) (Fin t) E) (h : ∀ i j, IntAt P (A i j)) :
    redP P A.det = (Matrix.of fun i j => redP P (A i j)).det := by
  let B : Matrix (Fin t) (Fin t) (intRing P) := Matrix.of fun i j => ⟨A i j, h i j⟩
  have h1 : A.det = (intRing P).subtype B.det := by
    rw [RingHom.map_det]; rfl
  have h2 : (Matrix.of fun i j => redP P (A i j)).det = redHom P B.det := by
    rw [RingHom.map_det]; rfl
  rw [h1, h2]; rfl

theorem of_inv_mul {q : ℕ} (hq : q ≠ 0) (hP : (q : 𝓞 E) ∈ P.asIdeal) {a : E}
    (h : IntAt P ((q : E)⁻¹ * a)) : IntAt P a ∧ redP P a = 0 := by
  have hq' : (q : E) ≠ 0 := Nat.cast_ne_zero.2 hq
  have e : a = algebraMap (𝓞 E) E (q : 𝓞 E) * ((q : E)⁻¹ * a) := by
    rw [map_natCast, mul_inv_cancel_left₀ hq']
  constructor
  · rw [e]; exact (IntAt.coe P _).mul h
  · rw [e, reduction_mul (IntAt.coe P _) h, reduction_coe, Ideal.Quotient.eq_zero_iff_mem.2 hP, zero_mul]

theorem unitV_mul_eq_one {K : Type} [Field K] (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a b : E}
    (h : redP P a * redP P b = 1) : unitV χ a * unitV χ b = 1 := by
  have ha : IsUnit (redP P a) := IsUnit.of_mul_eq_one _ h
  have hb : IsUnit (redP P b) := IsUnit.of_mul_eq_one_right _ h
  unfold unitV
  rw [dif_pos ha, dif_pos hb, ← Units.val_mul, ← map_mul]
  have : ha.unit * hb.unit = 1 := Units.ext (by simpa using h)
  rw [this, map_one, Units.val_one]

end Red

section Comb

variable {κ : Type} [CommRing κ]

theorem symIdx_cases (k rS i : ℕ) : (i < k ∧ symIdx k rS i = i + rS) ∨
    (k ≤ i ∧ i < k + rS ∧ symIdx k rS i = i - k) ∨ (k + rS ≤ i ∧ symIdx k rS i = i) := by
  unfold symIdx; split_ifs <;> omega

theorem symmetricBlockBoundary_cases (k rS s : ℕ) : (s = rS + k ∧ bd5 k rS s = rS) ∨ (s ≠ rS + k ∧ bd5 k rS s = s) := by
  unfold bd5; split_ifs <;> omega

theorem superdiag {n k₀ rS r : ℕ} (hr : k₀ + rS < r) (hn : r ≤ n) (A B : ℕ → ℕ → κ)
    (hA : ∀ l p', l < n → p' < r → bd5 k₀ rS (symIdx k₀ rS p') ≤ symIdx k₀ rS l →
      A l p' = if l = p' then 1 else 0)
    (hB : ∀ l p', l < n → p' < r → bd5 k₀ rS (symIdx k₀ rS p') ≤ symIdx k₀ rS l →
      B l p' = if l = p' then 1 else 0)
    (p : ℕ) (hp : p + 1 < r) (hp' : p + 1 ≠ k₀)
    (hAB : ∑ l ∈ Finset.range n, A p l * B l (p + 1) = 0) :
    A p (p + 1) + B p (p + 1) = 0 := by
  have hle : ∀ s, bd5 k₀ rS (symIdx k₀ rS s) ≤ symIdx k₀ rS s := by
    intro s; unfold bd5; split_ifs <;> omega
  rw [Finset.sum_eq_add_of_mem p (p + 1) (by simp; omega) (by simp; omega) (by omega)] at hAB
  · rw [hA p p (by omega) (by omega) (hle p), hB (p + 1) (p + 1) (by omega) hp (hle _)] at hAB
    simpa [add_comm] using hAB
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

theorem block {n a t : ℕ} (hn : a + t ≤ n) (A B : ℕ → ℕ → κ)
    (hA : ∀ l l', l < n → l' < a → a ≤ l → A l l' = 0)
    (hB : ∀ l l', l < n → l' < a + t → a + t ≤ l → B l l' = 0)
    (hAB : ∀ p p', p < n → p' < n →
      ∑ l ∈ Finset.range n, A p l * B l p' = if p = p' then 1 else 0) :
    (Matrix.of fun s s' : Fin t => A (a + s.1) (a + s'.1)).det *
      (Matrix.of fun s s' : Fin t => B (a + s.1) (a + s'.1)).det = 1 := by
  rw [← Matrix.det_mul]
  convert Matrix.det_one (n := Fin t) (R := κ)
  ext s s'
  have hs := s.2
  have hs' := s'.2
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range (fun l => A (a + s.1) (a + l) * B (a + l) (a + s'.1)) t]
  have h := hAB (a + s.1) (a + s'.1) (by omega) (by omega)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Finset.sum_range_add, Finset.sum_range_add, Finset.sum_eq_zero (s := Finset.range a),
    Finset.sum_eq_zero (s := Finset.range m), zero_add, add_zero] at h
  · rw [h, Matrix.one_apply]
    simp [Fin.ext_iff]
  · intro l hl
    rw [Finset.mem_range] at hl
    rw [hB _ _ (by omega) (by omega) (by omega), mul_zero]
  · intro l hl
    rw [Finset.mem_range] at hl
    rw [hA _ _ (by omega) (by omega) (by omega), zero_mul]

end Comb

section Main

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ)

def mat {N : ℕ} (g : Sp E N → Sp E N) (p p' : ℕ) : E := atN (g (eN E N p')) p

theorem mem_sclLat {N : ℕ} (e : ℕ → ℤ) (v : Sp E N) :
    v ∈ sclLat P q N e ↔ ∀ l : Fin N, IntAt P (((q : E) ^ e l.1)⁻¹ * v l) := by
  unfold sclLat stdAt
  rw [Submodule.mem_comap, mem_localization_standardLattice]
  rfl

omit [NumberField E] [StarRing E] in
theorem fIdx_zero (k₀ n s : ℕ) : fIdx k₀ 0 n s = s := by
  unfold fIdx; split_ifs <;> omega

theorem fPos_zero {k₀ n l : ℕ} (h : l < n) : fPos k₀ 0 n l = l := by
  unfold fPos; split_ifs <;> omega

theorem scE_lt {n l : ℕ} (ex : ℕ → ℕ) (h : l < n) : scE n ex l = 0 := if_pos h

omit [NumberField E] [StarRing E] in
theorem entB_zero (k₀ n : ℕ) (ex : ℕ → ℕ) (g : HomE E (n + 0) (n + 0)) {p p' : ℕ} (hp : p < n) (hp' : p' < n) :
    entB q k₀ 0 n 0 n ex ex g p p' = mat g p p' := by
  unfold entB mat
  rw [fIdx_zero, fIdx_zero, scE_lt _ hp, scE_lt _ hp']
  simp

omit [NumberField E] [StarRing E] in
theorem mat_mul_inv {N : ℕ} (g : Sp E N ≃ₗ[E] Sp E N) {p p' : ℕ} (hp : p < N) :
    ∑ l ∈ Finset.range N, mat g p l * mat (g⁻¹ : Sp E N ≃ₗ[E] Sp E N) l p' = if p = p' then 1 else 0 := by
  rw [← Fin.sum_univ_eq_sum_range (fun l => mat g p l * mat (g⁻¹ : Sp E N ≃ₗ[E] Sp E N) l p') N]
  set v := (g⁻¹ : Sp E N ≃ₗ[E] Sp E N) (eN E N p') with hv
  have h1 : g v = eN E N p' := LinearEquiv.apply_symm_apply g _
  have h2 : v = ∑ l : Fin N, v l • eN E N l.1 := by
    funext i
    simp [Finset.sum_apply, eN, Fin.val_inj]
  have h3 := congrFun h1 ⟨p, hp⟩
  rw [h2, map_sum, Finset.sum_apply] at h3
  refine Eq.trans ?_ (h3.trans rfl)
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [mat, atN, dif_pos hp, dif_pos l.2, map_smul, Pi.smul_apply, smul_eq_mul, ← hv]
  rw [mul_comm]

variable {P q}

theorem intAt_ite (c : Prop) [Decidable c] : IntAt P (if c then (1 : E) else 0) := by
  split_ifs
  · exact intAt_one P
  · exact intAt_zero P

theorem mat_intAt {k₀ rS r t n : ℕ} {g : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0)} (hg : g ∈ JGsym P q k₀ rS r t n 0)
    (p p' : ℕ) (hp : p < n) : IntAt P (mat g p p') := by
  have h : eN E (n + 0) p' ∈ lamY P q n 0 fun i => i + 1 := by
    unfold lamY
    rw [mem_sclLat]
    intro l
    rw [scE_lt _ (show l.1 < n from l.2), zpow_zero, inv_one, one_mul]
    exact intAt_ite _
  have h2 := (hg.1 _).2 h
  unfold lamY at h2
  rw [mem_sclLat] at h2
  have h3 := h2 ⟨p, hp⟩
  rw [scE_lt _ hp, zpow_zero, inv_one, one_mul] at h3
  unfold mat atN
  rw [dif_pos (show p < n + 0 from hp)]
  exact h3

theorem mat_col (hq : q ≠ 0) (hP : (q : 𝓞 E) ∈ P.asIdeal) {k₀ rS r t n : ℕ} (hr : k₀ + rS < r) (hn : r ≤ n)
    {g : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0)} (hg : g ∈ JGsym P q k₀ rS r t n 0)
    (l p' : ℕ) (hl : l < n) (hp' : p' < r) (h : bd5 k₀ rS (symIdx k₀ rS p') ≤ symIdx k₀ rS l) :
    redP P (mat g l p') = if l = p' then 1 else 0 := by
  have h1 := (hg.2.2 (symIdx k₀ rS p') (symIdx_lt hr.le hp')).2
  have e : bvecS E q k₀ rS n 0 (symIdx k₀ rS p') = eN E (n + 0) p' := by
    unfold bvecS bvecG
    rw [symIdxInv_symIdx, fIdx_zero, scE_lt _ (show p' < n by omega), zpow_zero, one_smul]
  rw [e] at h1
  unfold flagS at h1
  rw [mem_sclLat] at h1
  have h2 := h1 ⟨l, hl⟩
  simp only [] at h2
  rw [scE_lt _ hl, fPos_zero hl, if_pos h, zero_add, zpow_one] at h2
  obtain ⟨h3, h4⟩ := of_inv_mul P hq hP h2
  have e2 : mat g l p' = (g (eN E (n + 0) p') - eN E (n + 0) p') ⟨l, hl⟩ + if l = p' then 1 else 0 := by
    unfold mat atN
    rw [dif_pos (show l < n + 0 from hl), Pi.sub_apply]
    exact (sub_add_cancel _ _).symm
  rw [e2, reduction_add h3 (intAt_ite _), h4, zero_add]
  split_ifs
  · exact reduction_one' P
  · exact redP_zero' P

theorem mat_blk (hq : q ≠ 0) (hP : (q : 𝓞 E) ∈ P.asIdeal) {k₀ rS r t n : ℕ} (hr : k₀ + rS < r)
    {g : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0)} (hg : g ∈ JGsym P q k₀ rS r t n 0) (i : ℕ)
    (l l' : ℕ) (hl : l < n) (hl' : l' < r + i * t) (h : r + i * t ≤ l) :
    redP P (mat g l l') = 0 := by
  have key : ∀ x, bd5 k₀ rS (r + i * t) ≤ symIdx k₀ rS x ↔ r + i * t ≤ x := by
    intro x
    have e1 := symIdx_cases k₀ rS x
    have e2 := symmetricBlockBoundary_cases k₀ rS (r + i * t)
    generalize i * t = m at *
    omega
  have h0 : eN E (n + 0) l' ∈ flagS P q k₀ rS n 0 (r + i * t) := by
    unfold flagS
    rw [mem_sclLat]
    intro x
    have hx : x.1 < n := x.2
    by_cases hxl : x.1 = l'
    · rw [scE_lt _ hx, fPos_zero hx, if_neg (by rw [key]; omega), zero_add, zpow_zero, inv_one, one_mul]
      exact intAt_ite _
    · unfold eN
      rw [if_neg hxl, mul_zero]
      exact intAt_zero P
  have h1 := (hg.2.1 (r + i * t) ⟨i, rfl⟩ _).2 h0
  unfold flagS at h1
  rw [mem_sclLat] at h1
  have h2 := h1 ⟨l, hl⟩
  simp only [] at h2
  rw [scE_lt _ hl, fPos_zero hl, if_pos ((key l).2 h), zero_add, zpow_one] at h2
  unfold mat atN
  rw [dif_pos (show l < n + 0 from hl)]
  exact (of_inv_mul P hq hP h2).2

theorem red_mul_inv {k₀ rS r t n : ℕ}
    {g : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0)} (hg : g ∈ JGsym P q k₀ rS r t n 0) (p p' : ℕ) (hp : p < n) :
    ∑ l ∈ Finset.range n, redP P (mat g p l) *
      redP P (mat (g⁻¹ : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0)) l p') = if p = p' then 1 else 0 := by
  have hg' := inv_mem hg
  have h := congrArg (redP P) (mat_mul_inv g (p' := p') (show p < n + 0 from hp))
  rw [reduction_sum₂ P (Finset.range (n + 0)) _ fun l hl => (mat_intAt hg p l hp).mul (mat_intAt hg' l p' (Finset.mem_range.1 hl))] at h
  refine Eq.trans (Finset.sum_congr rfl fun l hl => ?_) (h.trans ?_)
  · exact (reduction_mul (mat_intAt hg p l hp) (mat_intAt hg' l p' (Finset.mem_range.1 hl))).symm
  · split_ifs
    · exact reduction_one' P
    · exact redP_zero' P

theorem redP_superdiag {k₀ rS r t n : ℕ} (hr : k₀ + rS < r) (hn : r ≤ n)
    {g : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0)} (hg : g ∈ JGsym P q k₀ rS r t n 0) (ex : ℕ → ℕ) :
    redP P (∑ i ∈ Finset.range (k₀ - 1), entB q k₀ 0 n 0 n ex ex g.toLinearMap i (i + 1) +
      ∑ i ∈ Finset.range (r - k₀ - 1), entB q k₀ 0 n 0 n ex ex g.toLinearMap (k₀ + i) (k₀ + i + 1)) =
    ∑ i ∈ Finset.range (k₀ - 1), redP P (mat g i (i + 1)) +
      ∑ i ∈ Finset.range (r - k₀ - 1), redP P (mat g (k₀ + i) (k₀ + i + 1)) := by
  have e1 : ∑ i ∈ Finset.range (k₀ - 1), entB q k₀ 0 n 0 n ex ex g.toLinearMap i (i + 1) =
      ∑ i ∈ Finset.range (k₀ - 1), mat g i (i + 1) :=
    Finset.sum_congr rfl fun i hi => by
      rw [Finset.mem_range] at hi
      exact entB_zero q k₀ n ex _ (by omega) (by omega)
  have e2 : ∑ i ∈ Finset.range (r - k₀ - 1), entB q k₀ 0 n 0 n ex ex g.toLinearMap (k₀ + i) (k₀ + i + 1) =
      ∑ i ∈ Finset.range (r - k₀ - 1), mat g (k₀ + i) (k₀ + i + 1) :=
    Finset.sum_congr rfl fun i hi => by
      rw [Finset.mem_range] at hi
      exact entB_zero q k₀ n ex _ (by omega) (by omega)
  have i1 : ∀ i ∈ Finset.range (k₀ - 1), IntAt P (mat g i (i + 1)) := fun i hi => by
    rw [Finset.mem_range] at hi
    exact mat_intAt hg _ _ (by omega)
  have i2 : ∀ i ∈ Finset.range (r - k₀ - 1), IntAt P (mat g (k₀ + i) (k₀ + i + 1)) := fun i hi => by
    rw [Finset.mem_range] at hi
    exact mat_intAt hg _ _ (by omega)
  rw [e1, e2, reduction_add (intAt_sum P _ _ i1) (intAt_sum P _ _ i2), reduction_sum₂ P _ _ i1, reduction_sum₂ P _ _ i2]

theorem redP_det_blk {k₀ rS r t n a : ℕ} (hn : a + t ≤ n)
    {g : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0)} (hg : g ∈ JGsym P q k₀ rS r t n 0) (ex : ℕ → ℕ) :
    redP P (Matrix.det (Matrix.of fun s s' : Fin t =>
      entB q k₀ 0 n 0 n ex ex g.toLinearMap (a + s.1) (a + s'.1))) =
    Matrix.det (Matrix.of fun s s' : Fin t => redP P (mat g (a + s.1) (a + s'.1))) := by
  have e : (Matrix.of fun s s' : Fin t => entB q k₀ 0 n 0 n ex ex g.toLinearMap (a + s.1) (a + s'.1)) =
      Matrix.of fun s s' : Fin t => mat g (a + s.1) (a + s'.1) := by
    ext s s'
    have := s.2
    have := s'.2
    exact entB_zero q k₀ n ex _ (by omega) (by omega)
  rw [e]
  exact reduction_det P (Matrix.of fun s s' : Fin t => mat g (a + s.1) (a + s'.1))
    fun s s' => mat_intAt hg (a + s.1) (a + s'.1) (by have := s.2; omega)

end Main

theorem lamGBS_mul_inv : ∀ (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ), q ≠ 0 → (q : 𝓞 E) ∈ P.asIdeal → ∀ (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ rS r t j n : ℕ), k₀ + rS < r → r + j * t ≤ n → ∀ g ∈ LocE.JGsym P q k₀ rS r t n 0, LocE.lamGBS q ψ₀ χ k₀ r t j n 0 g.toLinearMap * LocE.lamGBS q ψ₀ χ k₀ r t j n 0 (g⁻¹).toLinearMap = 1 := by
  intro E K _ _ _ _ P q hq hP ψ₀ χ k₀ rS r t j n hr hn g hg
  have hg' := inv_mem hg
  have hrn : r ≤ n := le_trans (Nat.le_add_right _ _) hn
  have hsd : ∀ p, p + 1 < r → p + 1 ≠ k₀ → redP P (mat g p (p + 1)) +
      redP P (mat (g⁻¹ : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0)) p (p + 1)) = 0 := fun p hp hp' =>
    superdiag hr hrn (fun a b => redP P (mat g a b))
      (fun a b => redP P (mat (g⁻¹ : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0)) a b))
      (mat_col hq hP hr hrn hg) (mat_col hq hP hr hrn hg') p hp hp'
      ((red_mul_inv hg p (p + 1) (by omega)).trans (if_neg (by omega)))
  unfold lamGBS lamGvS
  rw [mul_mul_mul_comm, ← AddChar.map_add_eq_mul, ← Finset.prod_mul_distrib,
    redP_superdiag hr hrn hg, redP_superdiag hr hrn hg', add_add_add_comm,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_eq_zero, Finset.sum_eq_zero,
    add_zero, AddChar.map_zero_eq_one, one_mul]
  · refine Finset.prod_eq_one fun i hi => unitV_mul_eq_one P _ ?_
    rw [Finset.mem_range] at hi
    have hi' : r + i * t + t ≤ n := by
      have : (i + 1) * t ≤ j * t := Nat.mul_le_mul_right t hi
      rw [add_mul, one_mul] at this
      omega
    rw [redP_det_blk hi' hg, redP_det_blk hi' hg']
    refine block hi' (fun a b => redP P (mat g a b))
      (fun a b => redP P (mat (g⁻¹ : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0)) a b))
      (mat_blk hq hP hr hg i) ?_ fun p p' hp _ => red_mul_inv hg p p' hp
    have h := mat_blk hq hP hr hg' (i + 1)
    rwa [add_mul, one_mul, ← add_assoc] at h
  · intro i hi
    rw [Finset.mem_range] at hi
    exact hsd _ (by omega) (by omega)
  · intro i hi
    rw [Finset.mem_range] at hi
    exact hsd _ (by omega) (by omega)

end GlobalTheory.SymLevelInv
