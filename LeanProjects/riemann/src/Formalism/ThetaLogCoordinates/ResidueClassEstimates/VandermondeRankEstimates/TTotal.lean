import Formalism.ThetaLogCoordinates.ResidueClassEstimates.StatementT

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.BranchingDimensions

open Letters

namespace extendedWeightWeylDimension

theorem extW_val {n : ℕ} (la : Fin n → ℤ) (m : Fin n) : extW la m.val = la m := by
  simp [extW]

theorem extW_mk {n : ℕ} (f : ℕ → ℤ) (m : ℕ) :
    extW (fun l : Fin n => f l.val) m = if m < n then f m else 0 := by
  unfold extW
  by_cases h : m < n <;> simp [h]

theorem extW_ge {n : ℕ} (la : Fin n → ℤ) {m : ℕ} (h : n ≤ m) : extW la m = 0 := by
  unfold extW
  rw [dif_neg (by omega)]

theorem extW_inj {n : ℕ} {a b : Fin n → ℤ} (h : ∀ m, m < n → extW a m = extW b m) : a = b := by
  funext m
  rw [← extW_val a m, ← extW_val b m]
  exact h _ m.2

theorem finsum_prop_congr {α : Type*} {p q : α → Prop} {f g : α → ℝ} (h : ∀ y, p y ↔ q y)
    (hf : ∀ y, q y → f y = g y) : ∑ᶠ (y : α) (_ : p y), f y = ∑ᶠ (y : α) (_ : q y), g y := by
  classical
  refine finsum_congr fun y => ?_
  rw [finsum_eq_if, finsum_eq_if]
  by_cases hq : q y
  · rw [if_pos ((h y).2 hq), if_pos hq, hf y hq]
  · rw [if_neg (fun hp => hq ((h y).1 hp)), if_neg hq]

theorem term_le {n : ℕ} {a b : ℕ → ℤ} (h : ∀ m, m < n → a m ≤ b m) {m : ℕ} (hm : m < n) :
    b m - a m ≤ wsize n b - wsize n a := by
  unfold wsize
  rw [← Finset.sum_sub_distrib]
  exact Finset.single_le_sum (f := fun m => b m - a m)
    (fun i hi => sub_nonneg.2 (h i (mem_range.1 hi))) (mem_range.2 hm)

theorem dom_le {n : ℕ} {la : ℕ → ℤ} (h : Dom n la) : ∀ m, m < n → la m ≤ la 0
  | 0, _ => le_rfl
  | m + 1, hm => le_trans (h m hm) (dom_le h m (by omega))

def star {n : ℕ} (la : Fin n → ℤ) : Fin n → ℤ := fun m => -(extW la (n - 1 - m.val))

theorem extW_star {n : ℕ} (la : Fin n → ℤ) {m : ℕ} (hm : m < n) :
    extW (star la) m = -(extW la (n - 1 - m)) := by
  unfold star
  rw [extW_mk (fun m => -(extW la (n - 1 - m))), if_pos hm]

theorem star_star {n : ℕ} (la : Fin n → ℤ) : star (star la) = la := by
  refine extW_inj fun m hm => ?_
  rw [extW_star _ hm, extW_star _ (by omega), neg_neg]
  congr 1; omega

theorem hstrip_star {n : ℕ} {a b : Fin n → ℤ} (h : HStrip n (extW a) (extW b)) :
    HStrip n (extW (star b)) (extW (star a)) := by
  constructor
  · intro m hm
    rw [extW_star _ hm, extW_star _ hm]
    have := h.1 (n - 1 - m) (by omega)
    omega
  · intro m hm
    rw [extW_star _ hm, extW_star _ (by omega : m < n)]
    have := h.2 (n - 1 - (m + 1)) (by omega)
    have e : n - 1 - (m + 1) + 1 = n - 1 - m := by omega
    rw [e] at this
    omega

theorem dom_star {n : ℕ} {a : Fin n → ℤ} (h : Dom n (extW a)) : Dom n (extW (star a)) := by
  intro m hm
  rw [extW_star _ hm, extW_star _ (by omega : m < n)]
  have := h (n - 1 - (m + 1)) (by omega)
  have e : n - 1 - (m + 1) + 1 = n - 1 - m := by omega
  rw [e] at this
  omega

theorem wsize_star {n : ℕ} (a : Fin n → ℤ) : wsize n (extW (star a)) = -(wsize n (extW a)) := by
  unfold wsize
  rw [← Finset.sum_range_reflect (fun m => extW a m) n, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun m hm => extW_star a (mem_range.1 hm)

theorem weylDim_star {n : ℕ} (a : Fin n → ℤ) : weylDim n (extW (star a)) = weylDim n (extW a) := by
  unfold weylDim
  rw [Finset.prod_sigma', Finset.prod_sigma']
  refine Finset.prod_nbij' (fun s => ⟨n - 1 - s.2, n - 1 - s.1⟩) (fun s => ⟨n - 1 - s.2, n - 1 - s.1⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨j, i⟩ hs
    simp only [Finset.mem_sigma, mem_range] at hs ⊢
    omega
  · rintro ⟨j, i⟩ hs
    simp only [Finset.mem_sigma, mem_range] at hs ⊢
    omega
  · rintro ⟨j, i⟩ hs
    simp only [Finset.mem_sigma, mem_range] at hs
    have h1 : n - 1 - (n - 1 - j) = j := by omega
    have h2 : n - 1 - (n - 1 - i) = i := by omega
    simp only [h1, h2]
  · rintro ⟨j, i⟩ hs
    simp only [Finset.mem_sigma, mem_range] at hs
    have h1 : n - 1 - (n - 1 - j) = j := by omega
    have h2 : n - 1 - (n - 1 - i) = i := by omega
    simp only [h1, h2]
  · rintro ⟨j, i⟩ hs
    simp only [Finset.mem_sigma, mem_range] at hs
    have h1 : (((n - 1 - i : ℕ) : ℝ)) + i + 1 = n := by
      have : (n - 1 - i) + i + 1 = n := by omega
      exact_mod_cast this
    have h2 : (((n - 1 - j : ℕ) : ℝ)) + j + 1 = n := by
      have : (n - 1 - j) + j + 1 = n := by omega
      exact_mod_cast this
    have hd : (((n - 1 - i : ℕ) : ℝ)) - ((n - 1 - j : ℕ) : ℝ) = (j : ℝ) - i := by linarith
    simp only
    rw [hd, extW_star _ (by omega : i < n), extW_star _ hs.1]
    congr 2
    push_cast
    ring

theorem pieriDual (hP : PieriDim) (n : ℕ) (mu : Fin n → ℤ) (B : ℕ) (hn : 1 ≤ n) (hd : Dom n (extW mu)) :
    ∑ᶠ (mu' : Fin n → ℤ) (_ : HStrip n (extW mu') (extW mu) ∧ wsize n (extW mu) - wsize n (extW mu') = B),
      weylDim n (extW mu') = weylDim n (extW mu) * ((B + n - 1).choose (n - 1) : ℝ) := by
  have h := hP n (star mu) B hn (dom_star hd)
  rw [weylDim_star] at h
  rw [← h]
  let e : (Fin n → ℤ) ≃ (Fin n → ℤ) := Function.Involutive.toPerm star star_star
  have h2 := finsum_comp_equiv e (f := fun z : Fin n → ℤ =>
    ∑ᶠ (_ : HStrip n (extW (star mu)) (extW z) ∧ wsize n (extW z) - wsize n (extW (star mu)) = B),
      weylDim n (extW z))
  rw [← h2]
  refine (finsum_prop_congr (fun y => ?_) (fun y _ => ?_)).symm
  · show HStrip n (extW (star mu)) (extW (star y)) ∧ _ ↔ _
    have e1 : e y = star y := rfl
    rw [e1, wsize_star, wsize_star]
    constructor
    · rintro ⟨h1, h3⟩
      have := hstrip_star h1
      rw [star_star, star_star] at this
      exact ⟨this, by omega⟩
    · rintro ⟨h1, h3⟩
      exact ⟨hstrip_star h1, by omega⟩
  · show weylDim n (extW (star y)) = _
    exact weylDim_star y

theorem frame_sum (hBr : BranchDim) (k n c : ℕ) (hk : k = n + (c + 1)) (be : ℤ) (x : Fin k → ℤ)
    (hd : Dom k (extW x)) (h0 : extW x 0 ≤ be) (hh : ∀ m, m < c → extW x m = be) :
    ∑ᶠ (y : Fin k → ℤ) (_ : Dom k (extW y) ∧ HStrip k (extW x) (extW y) ∧ ∀ m, m < c + 1 → extW y m = be),
      weylDim n (fun l => extW y (l + (c + 1))) = weylDim (n + 1) (fun l => extW x (l + c)) := by
  let mu : Fin (n + 1) → ℤ := fun l => extW x (l.val + c)
  have hmu : extW mu = fun l => extW x (l + c) := by
    funext l
    show extW (fun l : Fin (n + 1) => extW x (l.val + c)) l = _
    rw [extW_mk (fun l => extW x (l + c))]
    split_ifs with h
    · rfl
    · exact (extW_ge x (by omega)).symm
  have hdmu : Dom (n + 1) (extW mu) := by
    rw [hmu]; intro m hm
    have := hd (m + c) (by omega)
    have e : m + c + 1 = m + 1 + c := by omega
    rw [e] at this; exact this
  have hB := hBr n mu hdmu
  rw [hmu] at hB
  rw [← hB]
  let e : (Fin k → ℤ) → (Fin n → ℤ) := fun y l => extW y (l.val + (c + 1))
  have he : ∀ y, extW (e y) = fun l => extW y (l + (c + 1)) := by
    intro y; funext l
    show extW (fun l : Fin n => extW y (l.val + (c + 1))) l = _
    rw [extW_mk (fun l => extW y (l + (c + 1)))]
    split_ifs with h
    · rfl
    · exact (extW_ge y (by omega)).symm
  have hxbe : ∀ m, m < k → extW x m ≤ be := fun m hm => le_trans (dom_le hd m hm) h0
  refine finsum_mem_eq_of_bijOn e
    (s := {y | Dom k (extW y) ∧ HStrip k (extW x) (extW y) ∧ ∀ m, m < c + 1 → extW y m = be})
    (t := {la | Interl n (extW la) (fun l => extW x (l + c))}) ⟨?_, ?_, ?_⟩ ?_
  · rintro y ⟨_, hys, _⟩
    show Interl n (extW (e y)) _
    rw [he]
    intro l hl
    constructor
    · exact hys.2 (l + c) (by omega)
    · have := hys.1 (l + (c + 1)) (by omega)
      have e1 : l + 1 + c = l + (c + 1) := by omega
      show extW x (l + 1 + c) ≤ _
      rw [e1]; exact this
  · rintro y ⟨_, _, hyh⟩ y' ⟨_, _, hyh'⟩ heq
    refine extW_inj fun m hm => ?_
    by_cases hmc : m < c + 1
    · rw [hyh m hmc, hyh' m hmc]
    · have h1 := congrFun ((he y).symm.trans ((congrArg extW heq).trans (he y'))) (m - (c + 1))
      have e1 : m - (c + 1) + (c + 1) = m := by omega
      simp only [e1] at h1
      exact h1
  · intro la hla
    have hla' : ∀ l, l < n → extW la l ≤ extW x (l + c) ∧ extW x (l + 1 + c) ≤ extW la l := hla
    let y : Fin k → ℤ := fun m => if m.val < c + 1 then be else extW la (m.val - (c + 1))
    have hyd : ∀ m, extW y m = if m < k then (if m < c + 1 then be else extW la (m - (c + 1))) else 0 :=
      fun m => extW_mk (fun m => if m < c + 1 then be else extW la (m - (c + 1))) m
    have hy1 : ∀ m, m < c + 1 → extW y m = be := by
      intro m hm
      rw [hyd, if_pos (by omega), if_pos hm]
    have hy2 : ∀ l, extW y (l + (c + 1)) = extW la l := by
      intro l
      rw [hyd]
      by_cases hl : l < n
      · rw [if_pos (by omega), if_neg (by omega), Nat.add_sub_cancel]
      · rw [if_neg (by omega)]
        exact (extW_ge la (by omega)).symm
    refine ⟨y, ⟨?_, ⟨?_, ?_⟩, hy1⟩, ?_⟩
    · intro m hm
      by_cases hmc : m + 1 < c + 1
      · rw [hy1 _ hmc, hy1 m (by omega)]
      · obtain ⟨l, hl⟩ : ∃ l, m + 1 = l + (c + 1) := ⟨m - c, by omega⟩
        rw [hl, hy2]
        rcases Nat.eq_zero_or_pos l with h0l | h0l
        · rw [hy1 m (by omega)]
          exact le_trans (hla' l (by omega)).1 (hxbe _ (by omega))
        · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
          have e1 : m = l' + (c + 1) := by omega
          rw [e1, hy2]
          exact le_trans (hla' (l' + 1) (by omega)).1 (hla' l' (by omega)).2
    · intro m hm
      by_cases hmc : m < c + 1
      · rw [hy1 m hmc]; exact hxbe m hm
      · obtain ⟨l, rfl⟩ : ∃ l, m = l + (c + 1) := ⟨m - (c + 1), by omega⟩
        rw [hy2]
        have := (hla' l (by omega)).2
        have e1 : l + 1 + c = l + (c + 1) := by omega
        rw [e1] at this; exact this
    · intro m hm
      by_cases hmc : m + 1 < c + 1
      · rw [hy1 _ hmc, hh m (by omega)]
      · obtain ⟨l, hl⟩ : ∃ l, m = l + c := ⟨m - c, by omega⟩
        subst hl
        have e1 : l + c + 1 = l + (c + 1) := by omega
        rw [e1, hy2]
        exact (hla' l (by omega)).1
    · refine extW_inj fun m _ => ?_
      rw [he]
      exact hy2 m
  · intro y _
    rw [he]

def _root_.Formalism.InvariantFactorPaths.BranchingDimensions.Letters.twStep (D : Letters) (i : ℕ) (x y : Fin D.k → ℤ) : Prop :=
  Dom D.k (extW y) ∧
  (D.vec i = true → HStrip D.k (extW x) (extW y)) ∧
  (D.vec i = false → HStrip D.k (extW y) (extW x)) ∧
  (i ≤ D.n0 → D.vec i = true → wsize D.k (extW y) - wsize D.k (extW x) = D.B i) ∧
  (i ≤ D.n0 → D.vec i = false → wsize D.k (extW x) - wsize D.k (extW y) = D.B i) ∧
  (∀ m, m < i - D.n0 → extW y m = D.be)

def _root_.Formalism.InvariantFactorPaths.BranchingDimensions.Letters.twGood (D : Letters) (j : ℕ) (x : Fin D.k → ℤ) : Prop :=
  Dom D.k (extW x) ∧ extW x 0 ≤ ((∑ l ∈ Icc 1 (min j D.n0), D.B l : ℕ) : ℤ) ∧
    ∀ m, m < j - D.n0 → extW x m = D.be

def _root_.Formalism.InvariantFactorPaths.BranchingDimensions.Letters.twG (D : Letters) (j : ℕ) (x : Fin D.k → ℤ) : ℝ :=
  weylDim (D.k - (j - D.n0)) (fun l => extW x (l + (j - D.n0)))

def _root_.Formalism.InvariantFactorPaths.BranchingDimensions.Letters.twC (D : Letters) (i : ℕ) : ℝ :=
  if i ≤ D.n0 then ((D.B i + D.k - 1).choose (D.k - 1) : ℝ) else 1

theorem twG_early (D : Letters) {j : ℕ} (hj : j ≤ D.n0) (x : Fin D.k → ℤ) :
    D.twG j x = weylDim D.k (extW x) := by
  unfold Letters.twG
  have : j - D.n0 = 0 := by omega
  simp [this]

theorem sum_step (hP : PieriDim) (hBr : BranchDim) (D : Letters) (hW : D.Wf) (j : ℕ) (x : Fin D.k → ℤ)
    (hj : j < D.Ns) (hg : D.twGood j x) :
    ∑ᶠ (y : Fin D.k → ℤ) (_ : D.twStep (j + 1) x y), D.twG (j + 1) y = D.twG j x * D.twC (j + 1) := by
  obtain ⟨hr1, hK1, h3r, hvec1, hvec2⟩ := hW
  have hk : D.k = D.r + D.K := rfl
  have hn0 : D.n0 = D.Ns - D.r := rfl
  by_cases hn : j + 1 ≤ D.n0
  · have hc : D.twC (j + 1) = ((D.B (j + 1) + D.k - 1).choose (D.k - 1) : ℝ) := by
      unfold Letters.twC; rw [if_pos hn]
    rw [twG_early D (by omega : j ≤ D.n0), hc]
    by_cases hv : D.vec (j + 1) = true
    · rw [← hP D.k x (D.B (j + 1)) (by omega) hg.1]
      refine finsum_prop_congr (fun y => ?_) (fun y _ => twG_early D hn y)
      constructor
      · intro h; exact ⟨h.2.1 hv, h.2.2.2.1 hn hv⟩
      · rintro ⟨s, sz⟩
        refine ⟨fun m hm => le_trans (s.2 m hm) (s.1 m (by omega)), fun _ => s,
          fun hf => by rw [hv] at hf; exact absurd hf (by simp), fun _ _ => sz,
          fun _ hf => by rw [hv] at hf; exact absurd hf (by simp), fun m hm => by omega⟩
    · have hv' : D.vec (j + 1) = false := by simpa using hv
      rw [← pieriDual hP D.k x (D.B (j + 1)) (by omega) hg.1]
      refine finsum_prop_congr (fun y => ?_) (fun y _ => twG_early D hn y)
      constructor
      · intro h; exact ⟨h.2.2.1 hv', h.2.2.2.2.1 hn hv'⟩
      · rintro ⟨s, sz⟩
        refine ⟨fun m hm => le_trans (s.1 (m + 1) hm) (s.2 m hm),
          fun hf => absurd hf hv, fun _ => s,
          fun _ hf => absurd hf hv, fun _ _ => sz, fun m hm => by omega⟩
  · have hv : D.vec (j + 1) = true := hvec2 (j + 1) (by omega) (by omega)
    have hc : D.twC (j + 1) = 1 := by
      unfold Letters.twC; rw [if_neg hn]
    have e1 : j + 1 - D.n0 = (j - D.n0) + 1 := by omega
    have e2 : D.k - (j - D.n0) = D.k - ((j - D.n0) + 1) + 1 := by omega
    have h0 : extW x 0 ≤ (D.be : ℤ) := by
      have := hg.2.1
      have e3 : min j D.n0 = D.n0 := by omega
      rw [e3] at this
      exact this
    have hfr := frame_sum hBr D.k (D.k - ((j - D.n0) + 1)) (j - D.n0) (by omega) (D.be : ℤ) x hg.1 h0 hg.2.2
    rw [hc, mul_one]
    have hgx : D.twG j x = weylDim (D.k - ((j - D.n0) + 1) + 1) (fun l => extW x (l + (j - D.n0))) := by
      unfold Letters.twG; rw [← e2]
    rw [hgx, ← hfr]
    refine finsum_prop_congr (fun y => ?_) (fun y _ => ?_)
    · constructor
      · intro h
        refine ⟨h.1, h.2.1 hv, ?_⟩
        have := h.2.2.2.2.2
        rw [e1] at this
        exact this
      · rintro ⟨hd, s, hh⟩
        refine ⟨hd, fun _ => s, fun hf => by rw [hv] at hf; exact absurd hf (by simp),
          fun h => absurd h hn, fun h => absurd h hn, ?_⟩
        rw [e1]; exact hh
    · unfold Letters.twG; rw [e1]

def rho (D : Letters) (nu : ℕ → Fin D.k → ℤ) : D.Stages := fun i => nu i.val

end extendedWeightWeylDimension

open extendedWeightWeylDimension

end Formalism.InvariantFactorPaths.BranchingDimensions
