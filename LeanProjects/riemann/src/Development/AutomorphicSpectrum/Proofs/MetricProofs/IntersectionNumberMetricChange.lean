import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PositionPot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDerived
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Tele

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem ptsIntegral_congr_on {e : ℕ} (P : Ideal (MRing J)) (φ : Fin e → ((Σ k, J k) → ℂ) → ℝ)
    {g g' : ((Σ k, J k) → ℂ) → ℝ} (h : ∀ z ∈ mcPts P, g z = g' z) :
    ptsIntegral P φ g = ptsIntegral P φ g' := by
  have hs : ∀ (Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) y w,
      sheetDensity P Ψ φ g y w = sheetDensity P Ψ φ g' y w := by
    intro Ψ y w
    unfold sheetDensity
    by_cases hs : ∃ c, IsSheet P Ψ y w c
    · rw [dif_pos hs, dif_pos hs, h _ hs.choose_spec.2.self_of_nhds.2.1]
    · rw [dif_neg hs, dif_neg hs]
  unfold ptsIntegral ptsIntegralAt
  simp only [hs]

def logDiff (A B : HermLine J) (z : (Σ k, J k) → ℂ) : ℝ := by
  classical
  exact if ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 then Real.log (A.h z) - Real.log (B.h z) else 0

theorem cone_smul_iff (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (z : (Σ k, J k) → ℂ) :
    (∀ k, ∃ i, (fun p : (Σ k, J k) => c p.1 * z p) ⟨k, i⟩ ≠ 0) ↔ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := by
  simp only [ne_eq, mul_eq_zero, hc, false_or]

theorem logDiff_smul {A B : HermLine J} (hab : B.a = A.a) (c : K → ℂ) (z : (Σ k, J k) → ℂ)
    (hc : ∀ k, c k ≠ 0) : logDiff A B (fun p => c p.1 * z p) = logDiff A B z := by
  unfold logDiff
  by_cases hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0
  · rw [if_pos hz, if_pos ((cone_smul_iff c hc z).2 hz), A.smul c z hc, B.smul c z hc, hab]
    have hp : (∏ k, ‖c k‖ ^ A.a k) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
    rw [Real.log_mul hp (A.pos z hz).ne', Real.log_mul hp (B.pos z hz).ne']
    ring
  · rw [if_neg hz, if_neg fun h => hz ((cone_smul_iff c hc z).1 h)]

theorem logDiff_smooth {A B : HermLine J} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    ReciprocityTheory.ChartRestriction.G.AI.I2.SmoothFn (logDiff A B) := by
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => Real.log (A.h z) - Real.log (B.h z))
      {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    (ContDiffOn.log hA fun z hz => (A.pos z hz).ne').sub
      (ContDiffOn.log hB fun z hz => (B.pos z hz).ne')
  refine h1.congr fun z hz => ?_
  unfold logDiff
  exact if_pos hz

theorem step (hLoc : ReciprocityTheory.ChartRestriction.G.AI.I2.MetricLocalStatement)
    (I : Ideal (MRing J) → (n : ℕ) → (Fin n → HermLine J) → ℝ) (hI : IsIntersectionFamily I)
    (P : Ideal (MRing J)) (n : ℕ) (L : Fin n → HermLine J) (A B : HermLine J)
    (hP : IsArithVar P (n + 1)) (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A)
    (hB : IsSmoothHerm B) (hab : B.a = A.a) :
    I P (n + 1) (Fin.snoc L B) = I P (n + 1) (Fin.snoc L A) -
      ptsIntegral P (pot L) (fun z => Real.log (A.h z) - Real.log (B.h z)) := by
  have hu := fun (c : K → ℂ) z (hc : ∀ k, c k ≠ 0) => logDiff_smul (A := A) (B := B) hab c z hc
  have hus := logDiff_smooth hA hB
  have hch := metricChange K J I hI P n L A (logDiff A B) hu hP hL hA hus
  set T := A.tensor (HermLine.ofWeight (logDiff A B) hu) with hT
  have hTh : ∀ z, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → T.h z = B.h z := by
    intro z hz
    have e : T.h z = A.h z * Real.exp (-logDiff A B z) := rfl
    rw [e]
    unfold logDiff
    rw [if_pos hz, neg_sub, Real.exp_sub, Real.exp_log (B.pos z hz), Real.exp_log (A.pos z hz)]
    have := (A.pos z hz).ne'
    field_simp
  have hTs : IsSmoothHerm T := by
    unfold IsSmoothHerm
    exact (ContDiffOn.congr hB fun z hz => hTh z hz)
  have hTa : T.a = B.a := by
    rw [hab]
    show A.a + 0 = A.a
    simp
  have hSn : ∀ X : HermLine J, IsSmoothHerm X → ∀ j, IsSmoothHerm ((Fin.snoc L X : Fin (n + 1) → HermLine J) j) := by
    intro X hX j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa using hX
    · simpa using hL j
  have hloc : I P (n + 1) (Fin.snoc L T) = I P (n + 1) (Fin.snoc L B) := by
    refine hLoc K J I hI P (n + 1) _ _ hP (hSn T hTs) (hSn B hB) (fun j => ?_) (fun j z hz => ?_)
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using hTa
      · simp
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using hTh z hz.1
      · simp
  rw [← hloc, hch]
  congr 1
  refine ptsIntegral_congr_on P _ fun z hz => ?_
  unfold logDiff
  rw [if_pos hz.1]

def toLast {n : ℕ} (p : Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) :=
  (finSuccEquiv' p).trans finSuccEquivLast.symm

theorem toLast_self {n : ℕ} (p : Fin (n + 1)) : toLast p p = Fin.last n := by
  simp [toLast]

theorem toLast_succAbove {n : ℕ} (p : Fin (n + 1)) (j : Fin n) :
    toLast p (p.succAbove j) = j.castSucc := by
  simp [toLast]

def word (A B : HermLine J) (m i : ℕ) : Fin m → HermLine J := fun j => if (j : ℕ) < i then B else A

theorem word_snoc (A B X : HermLine J) (n : ℕ) (p : Fin (n + 1)) (q : Fin (n + 1)) :
    (Fin.snoc (word A B n p) X : Fin (n + 1) → HermLine J) (toLast p q) =
      if (q : ℕ) < p then B else if q = p then X else A := by
  rcases Fin.eq_self_or_eq_succAbove p q with rfl | ⟨j, rfl⟩
  · simp [toLast_self]
  · rw [toLast_succAbove, Fin.snoc_castSucc]
    have hne := Fin.succAbove_ne p j
    rw [if_neg hne]
    unfold word
    by_cases h : (j : ℕ) < p
    · have : p.succAbove j = j.castSucc := Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)
      simp [this, h]
    · have : p.succAbove j = j.succ := Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using h)
      have h' : ¬ ((j : ℕ) + 1 < p) := by omega
      simp [this, h, h']

theorem smooth_snoc {n : ℕ} {L : Fin n → HermLine J} {X : HermLine J} (hL : ∀ j, IsSmoothHerm (L j))
    (hX : IsSmoothHerm X) (j : Fin (n + 1)) :
    IsSmoothHerm ((Fin.snoc L X : Fin (n + 1) → HermLine J) j) := by
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simpa using hX
  · simpa using hL j

theorem word_smooth {A B : HermLine J} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) (m i : ℕ)
    (j : Fin m) : IsSmoothHerm (word A B m i j) := by
  unfold word
  split_ifs
  · exact hB
  · exact hA

theorem word_step (hLoc : ReciprocityTheory.ChartRestriction.G.AI.I2.MetricLocalStatement)
    (I : Ideal (MRing J) → (n : ℕ) → (Fin n → HermLine J) → ℝ) (hI : IsIntersectionFamily I)
    (P : Ideal (MRing J)) (n : ℕ) (A B : HermLine J)
    (hP : IsArithVar P (n + 1)) (hA : IsSmoothHerm A)
    (hB : IsSmoothHerm B) (hab : B.a = A.a) (i : ℕ) (hi : i < n + 1) :
    I P (n + 1) (word A B (n + 1) (i + 1)) = I P (n + 1) (word A B (n + 1) i) -
      ptsIntegral P (pot (word A B n i)) (fun z => Real.log (A.h z) - Real.log (B.h z)) := by
  let p : Fin (n + 1) := ⟨i, hi⟩
  have hL := word_smooth (J := J) hA hB n i
  have sB : word A B (n + 1) (i + 1) = (Fin.snoc (word A B n i) B : Fin (n + 1) → HermLine J) ∘ toLast p := by
    funext q
    have h := word_snoc A B B n p q
    simp only [Function.comp_apply]
    refine Eq.trans ?_ h.symm
    unfold word
    have hq : q = p ↔ (q : ℕ) = i := by simp [p, Fin.ext_iff]
    by_cases h1 : (q : ℕ) < i
    · have h2 : (q : ℕ) < i + 1 := by omega
      simp only [p, h1, h2, if_true]
    · by_cases h3 : (q : ℕ) = i
      · have h2 : (q : ℕ) < i + 1 := by omega
        simp [p, h1, h2, hq.2 h3]
      · have h2 : ¬ (q : ℕ) < i + 1 := by omega
        have h4 : q ≠ p := fun e => h3 (hq.1 e)
        simp [p, h1, h2, h4]
  have sA : word A B (n + 1) i = (Fin.snoc (word A B n i) A : Fin (n + 1) → HermLine J) ∘ toLast p := by
    funext q
    have h := word_snoc A B A n p q
    simp only [Function.comp_apply]
    refine Eq.trans ?_ h.symm
    unfold word
    by_cases h1 : (q : ℕ) < i
    · simp [p, h1]
    · simp [p, h1]
  rw [sB, sA, hI.1 P (n + 1) _ (toLast p) hP (smooth_snoc hL hB),
    hI.1 P (n + 1) _ (toLast p) hP (smooth_snoc hL hA)]
  exact step hLoc I hI P n _ A B hP hL hA hB hab

theorem telescope : ReciprocityTheory.ChartRestriction.G.AI.I2.MetricLocalStatement → ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing J)) (n : ℕ) (A B : HermLine J), IsFullIntersectionSystem II → IsArithVar P (n + 1) → IsSmoothHerm A → IsSmoothHerm B → B.a = A.a → II K J P (n + 1) (fun _ => B) = II K J P (n + 1) (fun _ => A) - ∑ i ∈ Finset.range (n + 1), ptsIntegral P (pot fun j : Fin n => if (j : ℕ) < i then B else A) (fun z => Real.log (A.h z) - Real.log (B.h z)) := by
  intro hLoc K _ J _ II P n A B hII hP hA hB hab
  have hI : IsIntersectionFamily (II K J) := hII.1 K J
  have key : ∀ i, i ≤ n + 1 → II K J P (n + 1) (word A B (n + 1) i) =
      II K J P (n + 1) (word A B (n + 1) 0) - ∑ k ∈ Finset.range i,
        ptsIntegral P (pot (word A B n k)) (fun z => Real.log (A.h z) - Real.log (B.h z)) := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      rw [word_step hLoc _ hI P n A B hP hA hB hab i (by omega), ih (by omega),
        Finset.sum_range_succ]
      ring
  have e1 : word A B (n + 1) (n + 1) = fun _ => B := by
    funext j
    simp [word, j.isLt]
  have e0 : word A B (n + 1) 0 = fun _ => A := by
    funext j
    simp [word]
  have h := key (n + 1) le_rfl
  rw [e1, e0] at h
  exact h

end GlobalTheory.CompanionTheory.Ar.Tele
