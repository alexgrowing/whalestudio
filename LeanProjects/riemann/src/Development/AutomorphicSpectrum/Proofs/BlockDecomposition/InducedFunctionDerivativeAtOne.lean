import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.ModelS
namespace FDer

variable {n : ℕ}

theorem sum_dif (v : Fin n → ℤ) (a : Fin n) : ∑ j, (if a ≤ j then dif v j else 0) = v a := by
  set w : ℕ → ℤ := fun k => if h : k < n then v ⟨k, h⟩ else 0 with hw
  have hd : ∀ j : Fin n, (if a ≤ j then dif v j else 0) =
      (fun k : ℕ => if (a : ℕ) ≤ k then w k - w (k + 1) else 0) j := by
    intro j
    have hiff : a ≤ j ↔ (a : ℕ) ≤ j := Iff.rfl
    simp only [hiff]
    split_ifs with h
    · simp [dif, hw, j.isLt]
    · rfl
  rw [Finset.sum_congr rfl (fun j _ => hd j),
    Fin.sum_univ_eq_sum_range (fun k : ℕ => if (a : ℕ) ≤ k then w k - w (k + 1) else 0) n]
  have key : ∀ m, (a : ℕ) ≤ m →
      ∑ k ∈ range m, (if (a : ℕ) ≤ k then w k - w (k + 1) else 0) = w a - w m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      rw [Finset.sum_eq_zero]
      · simp
      · intro k hk
        simp [not_le.2 (mem_range.1 hk)]
    | succ m hm ih =>
      rw [sum_range_succ, ih, if_pos hm]
      ring
  rw [key n a.isLt.le]
  simp [hw]

theorem ini_injective (j : Fin n) : Function.Injective (ini j) := Fin.castLE_injective _

theorem ini_le (j : Fin n) (r : Fin (j + 1)) : ini j r ≤ j := by
  have := r.isLt
  show (r : ℕ) ≤ j
  omega

theorem exists_ini {j a : Fin n} (h : a ≤ j) : ∃ a' : Fin (j + 1), ini j a' = a :=
  ⟨⟨a, Nat.lt_succ_of_le h⟩, Fin.ext rfl⟩

theorem sub_in (j a b : Fin n) (z : ℂ) (a' b' : Fin (j + 1)) (ha : ini j a' = a) (hb : ini j b' = b) :
    (1 + single a b z : Mat n).submatrix (ini j) (ini j) = 1 + single a' b' z := by
  subst ha hb
  ext r s
  simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, (ini_injective j).eq_iff]

theorem sub_out (j a b : Fin n) (z : ℂ) (h : ¬ (a ≤ j ∧ b ≤ j)) :
    (1 + single a b z : Mat n).submatrix (ini j) (ini j) = 1 := by
  ext r s
  have h0 : (single a b z : Mat n) (ini j r) (ini j s) = 0 := by
    rw [Matrix.single_apply, if_neg]
    rintro ⟨h1, h2⟩
    exact h ⟨h1 ▸ ini_le j r, h2 ▸ ini_le j s⟩
  simp [Matrix.add_apply, h0, Matrix.one_apply, (ini_injective j).eq_iff]

theorem gm_eq (j : Fin n) (g : Mat n) (h : ∀ r s : Fin n, r ≤ j → j < s → g r s = 0) :
    gm j g = lm j g * conj (lm j g) := by
  have hi := ini_injective j
  set L := g.submatrix (ini j) (ini j) with hL
  set Q : Matrix (Fin (j + 1)) (Fin n) ℂ := (1 : Mat n).submatrix (ini j) id with hQd
  have hG : g.submatrix (ini j) id = L * Q := by
    ext r s
    simp only [Matrix.mul_apply, hL, hQd, submatrix_apply, id, Matrix.one_apply]
    by_cases hs : s ≤ j
    · obtain ⟨k, rfl⟩ := exists_ini hs
      rw [Finset.sum_eq_single k]
      · simp
      · intro k' _ hk
        simp [(ini_injective j).eq_iff, hk]
      · simp
    · rw [h _ _ (ini_le j r) (not_le.1 hs), Finset.sum_eq_zero]
      intro k _
      have : ini j k ≠ s := fun e => hs (e ▸ ini_le j k)
      simp [this]
  have hQ : Q * Qᴴ = 1 := by
    rw [hQd, conjTranspose_submatrix, ← submatrix_mul _ _ _ _ _ Function.bijective_id]
    simp [submatrix_one _ hi]
  unfold gm lm
  rw [← hL, hG, conjTranspose_mul, Matrix.mul_assoc L, ← Matrix.mul_assoc Q, hQ, Matrix.one_mul, det_mul, det_conjTranspose]
  rfl

theorem det_one_add_single_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) (z : ℂ) :
    (1 + single a a z : Matrix ι ι ℂ).det = 1 + z := by
  have : (1 + single a a z : Matrix ι ι ℂ) = diagonal fun i => if i = a then 1 + z else 1 := by
    ext r s
    by_cases hrs : r = s
    · subst hrs
      by_cases hra : r = a
      · subst hra
        simp [Matrix.add_apply]
      · simp [Matrix.add_apply, Matrix.single_apply, hra, Ne.symm hra]
    · have : ¬ (a = r ∧ a = s) := fun e => hrs (e.1.symm.trans e.2)
      simp [Matrix.add_apply, Matrix.single_apply, Matrix.one_apply, hrs, this, diagonal_apply]
  rw [this, det_diagonal, Finset.prod_ite_eq' univ a]
  simp

theorem dif_eq_zero {lam : Fin n → ℤ} {lev : Fin n → ℕ} (hl : IsLev lam lev) (j : Fin n) (h : (j : ℕ) + 1 < n)
    (he : lev j = lev ⟨j + 1, h⟩) : dif (muZ lam lev) j = 0 ∧ dif (yZ lam lev) j = 0 := by
  have hlam := hl.2 _ _ he
  have hmu : muZ lam lev j = muZ lam lev ⟨j + 1, h⟩ := by
    simp only [muZ, hlam, he]
  have hy : yZ lam lev j = yZ lam lev ⟨j + 1, h⟩ := by
    simp only [yZ, hlam, hmu]
  simp [dif, h, hmu, hy]

theorem fRaw_off {lam : Fin n → ℤ} {lev : Fin n → ℕ} (hl : IsLev lam lev) {a b : Fin n} (hab : a ≠ b)
    (hle : lev b ≤ lev a) (z : ℂ) : fRaw lam lev (1 + single a b z) = 1 := by
  have hdet : (1 + single a b z : Mat n) ∈ GLs n := by
    show (1 + single a b z : Mat n).det ≠ 0
    have := det_transvection_of_ne a b hab z
    rw [transvection] at this
    rw [this]
    exact one_ne_zero
  rw [fRaw, Set.indicator_of_mem hdet]
  apply Finset.prod_eq_one
  intro j _
  by_cases hc : a ≤ j ∧ j < b
  · have hj : (j : ℕ) + 1 < n := by
      have h1 : (j : ℕ) < b := hc.2
      have := b.isLt
      omega
    have h1 : lev a ≤ lev j := hl.1 hc.1
    have h2 : lev j ≤ lev ⟨j + 1, hj⟩ := hl.1 (by show (j : ℕ) ≤ j + 1; omega)
    have h3 : lev ⟨j + 1, hj⟩ ≤ lev b := hl.1 (by show (j : ℕ) + 1 ≤ b; exact hc.2)
    obtain ⟨e1', e2'⟩ := dif_eq_zero hl j hj (by omega)
    simp [e1', e2']
  · have hlm : lm j (1 + single a b z) = 1 := by
      by_cases hin : a ≤ j ∧ b ≤ j
      · obtain ⟨a', ha⟩ := exists_ini hin.1
        obtain ⟨b', hb⟩ := exists_ini hin.2
        rw [lm, sub_in j a b z a' b' ha hb]
        have hne : a' ≠ b' := fun e => hab (by rw [← ha, ← hb, e])
        have := det_transvection_of_ne a' b' hne z
        rwa [transvection] at this
      · rw [lm, sub_out j a b z hin, det_one]
    have hgm : gm j (1 + single a b z) = 1 := by
      rw [gm_eq, hlm]
      · simp
      · intro r s hr hs
        have hrs : r ≠ s := fun e => absurd hr (not_le.2 (e ▸ hs))
        have : ¬ (a = r ∧ b = s) := by
          rintro ⟨rfl, rfl⟩
          exact hc ⟨hr, hs⟩
        simp [Matrix.add_apply, Matrix.single_apply, Matrix.one_apply, hrs, this]
    simp [hlm, hgm]

theorem prod_zpow_eq {ι : Type*} (s : Finset ι) {u : ℂ} (hu : u ≠ 0) (e : ι → ℤ) :
    ∏ j ∈ s, u ^ e j = u ^ ∑ j ∈ s, e j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [prod_insert hi, sum_insert hi, ih, zpow_add₀ hu]

theorem fRaw_diag (lam : Fin n → ℤ) (lev : Fin n → ℕ) (a : Fin n) {z : ℂ} (hz : 1 + z ≠ 0) :
    fRaw lam lev (1 + single a a z) = (1 + z) ^ lam a * (1 + conj z) ^ yZ lam lev a := by
  have hdet : (1 + single a a z : Mat n) ∈ GLs n := by
    show (1 + single a a z : Mat n).det ≠ 0
    rw [det_one_add_single_diag]
    exact hz
  have hw : 1 + conj z ≠ 0 := by
    intro h
    apply hz
    have := congrArg conj h
    simpa using this
  have hlm : ∀ j : Fin n, lm j (1 + single a a z) = if a ≤ j then 1 + z else 1 := by
    intro j
    by_cases h : a ≤ j
    · obtain ⟨a', ha⟩ := exists_ini h
      rw [lm, sub_in j a a z a' a' ha ha, det_one_add_single_diag, if_pos h]
    · rw [lm, sub_out j a a z (fun e => h e.1), det_one, if_neg h]
  have hgm : ∀ j : Fin n, gm j (1 + single a a z) = if a ≤ j then (1 + z) * (1 + conj z) else 1 := by
    intro j
    rw [gm_eq, hlm]
    · split_ifs <;> simp
    · intro r s hr hs
      have hrs : r ≠ s := fun e => absurd hr (not_le.2 (e ▸ hs))
      have : ¬ (a = r ∧ a = s) := fun e => hrs (e.1.symm.trans e.2)
      simp [Matrix.add_apply, Matrix.single_apply, Matrix.one_apply, hrs, this]
  rw [fRaw, Set.indicator_of_mem hdet]
  have hfac : ∀ j : Fin n, lm j (1 + single a a z) ^ dif (muZ lam lev) j *
      gm j (1 + single a a z) ^ dif (yZ lam lev) j =
      (1 + z) ^ ((if a ≤ j then dif (muZ lam lev) j else 0) + (if a ≤ j then dif (yZ lam lev) j else 0)) *
        (1 + conj z) ^ (if a ≤ j then dif (yZ lam lev) j else 0) := by
    intro j
    rw [hlm, hgm]
    by_cases h : a ≤ j
    · simp only [if_pos h, mul_zpow, zpow_add₀ hz]
      ring
    · simp [if_neg h]
  rw [Finset.prod_congr rfl (fun j _ => hfac j), Finset.prod_mul_distrib, prod_zpow_eq _ hz, prod_zpow_eq _ hw,
    Finset.sum_add_distrib, sum_dif, sum_dif]
  simp [yZ]

theorem Rd_one (F : SmF n) (X : Mat n) {D : ℂ} (h : HasDerivAt (fun t : ℝ => F.1 (1 + t • X)) D 0) :
    Rd X F.1 1 = D := by
  have h1 : (1 : Mat n) ∈ GLs n := by
    show (1 : Mat n).det ≠ 0
    simp
  have hf := (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth F.2.1 h1).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => (1 : Mat n) + t • X) X 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (1 : Mat n)
    simp only [id, one_smul] at this
    exact this
  have hf' : HasFDerivAt F.1 (fderiv ℝ F.1 1) ((fun t : ℝ => (1 : Mat n) + t • X) 0) := by
    simpa using hf
  have hc := hf'.comp_hasDerivAt (0 : ℝ) hline
  have := hc.unique h
  show fderiv ℝ F.1 1 (1 * X) = D
  rw [one_mul]
  exact this

theorem hasDerivAt_line (L Y : ℤ) (c : ℂ) :
    HasDerivAt (fun t : ℝ => (1 + (t : ℂ) * c) ^ L * (1 + (t : ℂ) * conj c) ^ Y) (L * c + Y * conj c) 0 := by
  have hline : ∀ c : ℂ, HasDerivAt (fun t : ℝ => 1 + (t : ℂ) * c) c 0 := by
    intro c
    have := (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const c).const_add 1
    simpa using this
  have zp : ∀ (m : ℤ) (c : ℂ), HasDerivAt (fun t : ℝ => (1 + (t : ℂ) * c) ^ m) (m * c) 0 := by
    intro m c
    have := (hasDerivAt_zpow m (1 + ((0 : ℝ) : ℂ) * c) (Or.inl (by simp))).comp (0 : ℝ) (hline c)
    simpa [Function.comp_def] using this
  have := (zp L c).mul (zp Y (conj c))
  simp only [Complex.ofReal_zero, zero_mul, add_zero, _root_.one_zpow, mul_one, one_mul] at this
  exact this

theorem Rd_diag {lam : Fin n → ℤ} {lev : Fin n → ℕ} (F : SmF n) (hF : F.1 = fRaw lam lev) (a : Fin n) (c : ℂ) :
    Rd (single a a c) F.1 1 = lam a * c + yZ lam lev a * conj c := by
  apply Rd_one
  refine (hasDerivAt_line (lam a) (yZ lam lev a) c).congr_of_eventuallyEq ?_
  have hc : ContinuousAt (fun t : ℝ => 1 + (t : ℂ) * c) 0 := by fun_prop
  have ev : ∀ᶠ t : ℝ in nhds 0, 1 + (t : ℂ) * c ≠ 0 := hc.eventually_ne (by simp)
  filter_upwards [ev] with t ht
  have hs : t • (single a a c : Mat n) = single a a ((t : ℂ) * c) := by
    rw [Matrix.smul_single, Complex.real_smul]
  rw [hF, hs, fRaw_diag lam lev a ht]
  simp

theorem Rd_off {lam : Fin n → ℤ} {lev : Fin n → ℕ} (hl : IsLev lam lev) (F : SmF n) (hF : F.1 = fRaw lam lev)
    {a b : Fin n} (hab : a ≠ b) (hle : lev b ≤ lev a) (c : ℂ) : Rd (single a b c) F.1 1 = 0 := by
  apply Rd_one
  have : (fun t : ℝ => F.1 (1 + t • (single a b c : Mat n))) = fun _ => 1 := by
    funext t
    rw [hF, Matrix.smul_single, fRaw_off hl hab hle]
  rw [this]
  exact hasDerivAt_const _ _

theorem fder (n : ℕ) (lam : Fin n → ℤ) (_ : Antitone lam) (lev : Fin n → ℕ) (hl : IsLev lam lev) (F : SmF n)
    (hF : F.1 = fRaw lam lev) (a b : Fin n) (hle : lev b ≤ lev a) :
    (e1 DR a b F).1 1 = (if a = b then (lam a : ℂ) else 0) ∧
      (f1 DR a b F).1 1 = (if a = b then (yZ lam lev a : ℂ) else 0) := by
  have h1 : (1 : Mat n) ∈ GLs n := by
    show (1 : Mat n).det ≠ 0
    simp
  rw [orderedCechToCatCochainsOne_apply_valueAtSubset a b F h1, liftOneFormsToCompatible_apply a b F h1]
  by_cases hab : a = b
  · subst hab
    simp only [Eu, Pi.smul_apply, Pi.add_apply, if_true, Bool.false_eq_true, if_false, Rd_diag F hF a]
    simp
    constructor <;> (ring_nf; simp; try ring)
  · simp [Eu, hab, Rd_off hl F hF hab hle]

end FDer
end GlobalTheory.CompanionTheory.ModelS
