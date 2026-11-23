import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPosGramFormIntegralLatticeProperties
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.DualLatticeIndexEqDiscrPowMulDetPow

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem sum_isReps_add_shift {V : Type} [AddCommGroup V] (A B : AddSubgroup V) (T : Finset V)
    (hT : IsReps A B T) (f : V → ℂ) (hf : ∀ x ∈ B, ∀ m ∈ A, f (x + m) = f x) (s : V) (hs : s ∈ B) :
    ∑ x ∈ T, f (x + s) = ∑ x ∈ T, f x := by
  classical
  obtain ⟨hTB, huniq⟩ := hT
  have key : ∀ x ∈ B, ∃ y ∈ T, x - y ∈ A := fun x hx => by
    obtain ⟨y, ⟨hy, hxy⟩, _⟩ := huniq x hx
    exact ⟨y, hy, hxy⟩
  choose! g hgT hgA using key
  have hfx : ∀ x ∈ T, f (x + s) = f (g (x + s)) := by
    intro x hx
    have hxs : x + s ∈ B := B.add_mem (hTB x hx) hs
    have h := hf (g (x + s)) (hTB _ (hgT _ hxs)) _ (hgA _ hxs)
    rw [← h]
    congr 1
    abel
  rw [Finset.sum_congr rfl hfx]
  apply Finset.sum_nbij (fun x => g (x + s))
  · intro x hx
    exact hgT _ (B.add_mem (hTB x hx) hs)
  · intro x hx x' hx' h
    simp only [Finset.mem_coe] at hx hx'
    have h1 := hgA _ (B.add_mem (hTB x hx) hs)
    have h2 := hgA _ (B.add_mem (hTB x' hx') hs)
    simp only at h
    rw [h] at h1
    have hd : x - x' ∈ A := by
      have h3 := A.sub_mem h1 h2
      convert h3 using 1
      abel
    obtain ⟨y, _, hy⟩ := huniq x (hTB x hx)
    have e1 := hy x ⟨hx, by rw [sub_self]; exact A.zero_mem⟩
    have e2 := hy x' ⟨hx', hd⟩
    rw [e1, e2]
  · intro y hy
    simp only [Finset.mem_coe] at hy
    have hys : y - s ∈ B := B.sub_mem (hTB y hy) hs
    refine ⟨g (y - s), hgT _ hys, ?_⟩
    have hxs : g (y - s) + s ∈ B := B.add_mem (hTB _ (hgT _ hys)) hs
    apply (huniq _ hxs).unique ⟨hgT _ hxs, hgA _ hxs⟩ ⟨hy, ?_⟩
    have h4 := A.neg_mem (hgA _ hys)
    convert h4 using 1
    abel
  · intro x hx
    rfl

theorem gaussSum_dual_shift : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ (N : ℕ) (a b c d : F) (T : Finset (κ → F)), 0 < N → (∀ y ∈ dualL F G, (N : F) • y ∈ LL F κ ∧ IsIntegral ℤ ((N : F) * QF G y)) → IsIntegral ℤ a → IsIntegral ℤ b → IsIntegral ℤ (c / N) → IsIntegral ℤ d → a * d - b * c = 1 → c ≠ 0 → IsReps (aL κ c) (aL κ (1 : F)) T → ∀ y ∈ dualL F G, (∑ x ∈ T, et (a / c * QF G x) * et (BF G y x / c)) * et (d / c * QF G y) = oneL y * ∑ x ∈ T, et (a / c * QF G x) := by
  intro F _ _ κ _ _ G hG N a b c d T hN hNy ha hb hcN hd hdet hc hT y hy
  obtain ⟨hBsymm, hsmul, hBadd, hint, hLLiff, haL, het, hLLdual⟩ := GlobalTheory.T.evenPos_gramForm_integral_lattice_properties F κ G hG
  obtain ⟨-, -, hdd, -, -⟩ := GlobalTheory.T.dualLattice_index_eq_discr_pow_mul_det_pow F κ G hG
  have etadd : ∀ u v : F, et (u + v) = et u * et v := fun u v => (het u v).1
  have etint : ∀ u : F, IsIntegral ℤ u → et u = 1 := fun u hu => (het u 0).2.2.2 hu
  have etiff : ∀ u : F, et u = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ F u = n := fun u => (het u 0).2.2.1
  have hLLsmul : ∀ r : F, IsIntegral ℤ r → ∀ x ∈ LL F κ, r • x ∈ LL F κ := by
    intro r hr x hx
    rw [hLLiff] at hx ⊢
    intro i
    simpa [Pi.smul_apply, smul_eq_mul] using hr.mul (hx i)
  have hB1 : ∀ x, x ∈ aL κ (1 : F) ↔ x ∈ LL F κ := by
    intro x
    rw [haL]
    constructor
    · rintro ⟨l, hl, rfl⟩
      simpa using hl
    · intro hx
      exact ⟨x, hx, by simp⟩
  have hdualet : ∀ w ∈ dualL F G, ∀ l ∈ LL F κ, et (BF G w l) = 1 := by
    intro w hw l hl
    exact (etiff _).2 (hw l hl)
  have hexp : ∀ (x : κ → F) (r : F) (z : κ → F),
      QF G (x + r • z) = QF G x + r * BF G x z + r ^ 2 * QF G z := by
    intro x r z
    rw [(hBsymm x (r • z)).2, (hBsymm x (r • z)).1, (hsmul r z x).1, (hsmul r z x).2.1,
      (hBsymm z x).1]
  have hBlin : ∀ (y x : κ → F) (r : F) (z : κ → F),
      BF G y (x + r • z) = BF G y x + r * BF G y z := by
    intro y x r z
    rw [(hBsymm y (x + r • z)).1, hBadd, (hsmul r z y).1, (hBsymm x y).1, (hBsymm z y).1]
  have hNF : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hcw : ∀ w ∈ dualL F G, c • w ∈ LL F κ := by
    intro w hw
    have e : c • w = (c / N) • ((N : F) • w) := by
      rw [smul_smul]
      congr 1
      field_simp
    rw [e]
    exact hLLsmul _ hcN _ (hNy w hw).1
  have hcQ : ∀ w ∈ dualL F G, IsIntegral ℤ (a * c * QF G w) := by
    intro w hw
    have e : a * c * QF G w = a * (c / N) * ((N : F) * QF G w) := by
      field_simp
    rw [e]
    exact (ha.mul hcN).mul (hNy w hw).2
  have haB : ∀ x ∈ LL F κ, ∀ w ∈ dualL F G, et (a * BF G x w) = 1 := by
    intro x hx w hw
    rw [← (hsmul a x w).1, (hBsymm _ w).1]
    exact hdualet w hw _ (hLLsmul a ha x hx)
  have hg : ∀ x ∈ aL κ (1 : F), ∀ m ∈ aL κ c,
      et (a / c * QF G (x + m)) = et (a / c * QF G x) := by
    intro x hx m hm
    rw [hB1] at hx
    obtain ⟨l, hl, rfl⟩ := (haL c m).1 hm
    rw [hexp]
    have e : a / c * (QF G x + c * BF G x l + c ^ 2 * QF G l)
        = a / c * QF G x + (a * BF G x l + a * c * QF G l) := by
      field_simp
      ring
    rw [e, etadd, etint _ ((ha.mul ((hint x hx).2 l hl)).add (hcQ l (hLLdual hl))), mul_one]
  by_cases hyL : y ∈ LL F κ
  · have h1 : oneL y = 1 := by simp [oneL, hyL]
    rw [h1, one_mul, Finset.sum_mul]
    have hs : d • y ∈ aL κ (1 : F) := (hB1 _).2 (hLLsmul d hd y hyL)
    refine Eq.trans ?_ (sum_isReps_add_shift (aL κ c) (aL κ 1) T hT
      (fun x => et (a / c * QF G x)) hg (d • y) hs)
    apply Finset.sum_congr rfl
    intro x hxT
    have hx : x ∈ LL F κ := (hB1 x).1 (hT.1 x hxT)
    rw [hexp]
    have key : a / c * (QF G x + d * BF G x y + d ^ 2 * QF G y)
        = a / c * QF G x + BF G y x / c + d / c * QF G y
          + (b * BF G x y + b * d * QF G y) := by
      rw [(hBsymm x y).1]
      field_simp
      linear_combination (BF G y x + d * QF G y) * hdet
    rw [key, etadd, etint _ ((hb.mul ((hint x hx).2 y hyL)).add ((hb.mul hd).mul (hint y hyL).1)),
      mul_one, etadd, etadd]
  · have h0 : oneL y = 0 := by simp [oneL, hyL]
    rw [h0, zero_mul]
    obtain ⟨w, hw, hnot⟩ : ∃ w ∈ dualL F G, et (BF G y w) ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact hyL (hdd y (fun ν hν => (etiff _).1 (hcon ν hν)))
    have hs : c • w ∈ aL κ (1 : F) := (hB1 _).2 (hcw w hw)
    have hf : ∀ x ∈ aL κ (1 : F), ∀ m ∈ aL κ c,
        et (a / c * QF G (x + m)) * et (BF G y (x + m) / c)
          = et (a / c * QF G x) * et (BF G y x / c) := by
      intro x hx m hm
      rw [hg x hx m hm]
      congr 1
      obtain ⟨l, hl, rfl⟩ := (haL c m).1 hm
      rw [hBlin y x c l]
      have e : (BF G y x + c * BF G y l) / c = BF G y x / c + BF G y l := by
        field_simp
      rw [e, etadd, hdualet y hy l hl, mul_one]
    have h := sum_isReps_add_shift (aL κ c) (aL κ 1) T hT
      (fun x => et (a / c * QF G x) * et (BF G y x / c)) hf (c • w) hs
    have hmul : ∑ x ∈ T, et (a / c * QF G (x + c • w)) * et (BF G y (x + c • w) / c)
        = et (BF G y w) * ∑ x ∈ T, et (a / c * QF G x) * et (BF G y x / c) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hxT
      have hx : x ∈ LL F κ := (hB1 x).1 (hT.1 x hxT)
      rw [hexp, hBlin]
      have e1 : a / c * (QF G x + c * BF G x w + c ^ 2 * QF G w)
          = a / c * QF G x + (a * BF G x w + a * c * QF G w) := by
        field_simp
        ring
      have e2 : (BF G y x + c * BF G y w) / c = BF G y x / c + BF G y w := by
        field_simp
      rw [e1, e2, etadd, etadd, etadd, haB x hx w hw, etint _ (hcQ w hw)]
      ring
    have hsum : ∑ x ∈ T, et (a / c * QF G x) * et (BF G y x / c) = 0 := by
      rw [hmul] at h
      have h5 : (et (BF G y w) - 1) * ∑ x ∈ T, et (a / c * QF G x) * et (BF G y x / c) = 0 := by
        rw [sub_mul, h, one_mul, sub_self]
      exact (mul_eq_zero.1 h5).resolve_left (sub_ne_zero.2 hnot)
    rw [hsum, zero_mul]

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_gaussSum_twist_dual_eq_indicator : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ (N : ℕ) (a b c d : F) (T : Finset (κ → F)), 0 < N → (∀ y ∈ dualL F G, (N : F) • y ∈ LL F κ ∧ IsIntegral ℤ ((N : F) * QF G y)) → IsIntegral ℤ a → IsIntegral ℤ b → IsIntegral ℤ (c / N) → IsIntegral ℤ d → a * d - b * c = 1 → c ≠ 0 → IsReps (aL κ c) (aL κ (1 : F)) T → ∀ y ∈ dualL F G, (∑ x ∈ T, et (a / c * QF G x) * et (BF G y x / c)) * et (d / c * QF G y) = oneL y * ∑ x ∈ T, et (a / c * QF G x) := by
  first | exact @GlobalTheory.HilbertThetaSeries.gaussSum_dual_shift | exact GlobalTheory.HilbertThetaSeries.gaussSum_dual_shift | (intros; apply GlobalTheory.HilbertThetaSeries.gaussSum_dual_shift <;> assumption)
