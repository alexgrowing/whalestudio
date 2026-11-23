import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseVectorProperties
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFifth
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

section Minors

variable {N : ℕ}

theorem minor_self_of_lowerUni {L : Matrix (Fin N) (Fin N) ℂ} (hL : IsLowerUni L) (C : Finset (Fin N)) :
    minorIJ L C C = 1 := by
  unfold minorIJ
  rw [dif_pos rfl, Matrix.det_of_lowerTriangular]
  · exact Finset.prod_eq_one fun i _ => hL.1 _
  · intro a b hab
    exact hL.2 _ _ ((C.orderEmbOfFin rfl).strictMono hab)

theorem minor_insert_of_lowerUni {L : Matrix (Fin N) (Fin N) ℂ} (hL : IsLowerUni L) {C : Finset (Fin N)} {s r : Fin N}
    (hs : s ∈ C) (hmax : ∀ a ∈ C, a ≤ s) (hr : s < r) : minorIJ L (insert r (C.erase s)) C = L r s := by
  have hrn : r ∉ C.erase s := fun h => absurd (hmax r (Finset.mem_of_mem_erase h)) (not_le.2 hr)
  have hcard : (insert r (C.erase s)).card = C.card := by
    rw [Finset.card_insert_of_notMem hrn, Finset.card_erase_of_mem hs]
    have := Finset.card_pos.2 ⟨s, hs⟩
    omega
  unfold minorIJ
  rw [dif_pos hcard]
  set e := C.orderEmbOfFin rfl with he
  have hmem : ∀ i, e i ∈ C := fun i => Finset.orderEmbOfFin_mem C rfl i
  obtain ⟨m, hm⟩ : ∃ m, e m = s := by
    have : s ∈ Set.range e := by
      rw [he, Finset.range_orderEmbOfFin]
      exact hs
    exact this
  have hle : ∀ i, i ≤ m := fun i => e.le_iff_le.1 (by rw [hm]; exact hmax _ (hmem i))
  let f : Fin C.card → Fin N := fun i => if i = m then r else e i
  have hf_ne : ∀ i, i ≠ m → f i = e i := fun i h => if_neg h
  have hf_m : f m = r := if_pos rfl
  have hmono : StrictMono f := by
    intro a b hab
    have ham : a ≠ m := fun h => absurd (hle b) (by rw [← h]; exact not_le.2 hab)
    rw [hf_ne a ham]
    by_cases hb : b = m
    · rw [hb, hf_m]
      exact lt_of_le_of_lt (hmax _ (hmem a)) hr
    · rw [hf_ne b hb]
      exact e.strictMono hab
  have hin : ∀ i, f i ∈ insert r (C.erase s) := by
    intro i
    by_cases hi : i = m
    · rw [hi, hf_m]
      exact Finset.mem_insert_self _ _
    · rw [hf_ne i hi]
      refine Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨fun h => hi ?_, hmem i⟩)
      exact e.injective (h.trans hm.symm)
  have hfe : f = (insert r (C.erase s)).orderEmbOfFin hcard := Finset.orderEmbOfFin_unique hcard hin hmono
  rw [← hfe, Matrix.det_of_lowerTriangular]
  · rw [Finset.prod_eq_single m]
    · rw [Matrix.submatrix_apply, hf_m, hm]
    · intro i _ hi
      rw [Matrix.submatrix_apply, hf_ne i hi]
      exact hL.1 _
    · intro h
      exact absurd (Finset.mem_univ m) h
  · intro a b hab
    have hab' : a < b := hab
    have ham : a ≠ m := fun h => absurd (hle b) (by rw [← h]; exact not_le.2 hab')
    rw [Matrix.submatrix_apply, hf_ne a ham]
    exact hL.2 _ _ (e.strictMono hab')

end Minors

theorem flag_uniq : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (l : Fin BM.q), ∀ b ∈ BM.O l, ∀ L L' : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (L τ') ∧ IsLowerUni (L τ')) → (∀ τ', IsBlockDiag j (L' τ') ∧ IsLowerUni (L' τ')) → SameOrbit (FC.flagPt M (BM.F l) (FC.bvec BM l b) L) (FC.flagPt M (BM.F l) (FC.bvec BM l b) L') → L = L' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM l b hb L L' hL hL' ho
  obtain ⟨hβ, hg, -, -⟩ := bvec_good K ι Φ y Ψ N j M n BM l b hb
  obtain ⟨c, -, ez⟩ := ho
  have hjN := M.j_le
  have key : ∀ (τ' : Ψ) (i : Fin N), IsProperStep N j i → ∃ a : ℂ, ∀ I,
      minorIJ (L τ') I (stepCols N j i) = a * minorIJ (L' τ') I (stepCols N j i) := by
    intro τ' i hi
    obtain ⟨k, hk⟩ : ∃ k, M.blk (τ', i) = some k :=
      Option.ne_none_iff_exists'.1 fun e => (M.blk_none _).1 e hi
    refine ⟨c k, fun I => ?_⟩
    have h0 := FibreCount.plucker_inj M (BM.isFrame l) hβ hg hk
      (fun I => minorIJ (L τ') I (stepCols N j i) - c k * minorIJ (L' τ') I (stepCols N j i))
      (fun I hI => by
        show minorIJ (L τ') I (stepCols N j i) - c k * minorIJ (L' τ') I (stepCols N j i) = 0
        rw [FibreCount.minor_off_step hjN hi (hL τ').1 hI, FibreCount.minor_off_step hjN hi (hL' τ').1 hI]
        ring)
      (fun m => by
        have x := congrFun ez ⟨k, m⟩
        simp only at x
        rw [flagPt_step M (BM.F l) _ L hk m, flagPt_step M (BM.F l) _ L' hk m] at x
        simp only [mul_sub, Finset.sum_sub_distrib]
        rw [x, Finset.mul_sum, sub_eq_zero]
        exact Finset.sum_congr rfl fun _ _ => by ring) I
    exact sub_eq_zero.1 h0
  have ent : ∀ (τ' : Ψ) (i : Fin N) (s r : Fin N), IsProperStep N j i → s ∈ stepCols N j i →
      (∀ a ∈ stepCols N j i, a ≤ s) → s < r → L τ' r s = L' τ' r s := by
    intro τ' i s r hi hs hmax hr
    obtain ⟨a, ha⟩ := key τ' i hi
    have h1 := ha (stepCols N j i)
    rw [minor_self_of_lowerUni (hL τ').2, minor_self_of_lowerUni (hL' τ').2, mul_one] at h1
    have h2 := ha (insert r ((stepCols N j i).erase s))
    rw [minor_insert_of_lowerUni (hL τ').2 hs hmax hr, minor_insert_of_lowerUni (hL' τ').2 hs hmax hr, ← h1,
      one_mul] at h2
    exact h2
  funext τ'
  ext r s
  rcases lt_trichotomy s r with hsr | hsr | hsr
  · have hsr' : (s : ℕ) < r := hsr
    by_cases hblk : ((r : ℕ) < N - j ↔ (s : ℕ) < N - j)
    · by_cases hs : (s : ℕ) < N - j
      · have hr : (r : ℕ) < N - j := hblk.2 hs
        refine ent τ' ⟨s + j, by omega⟩ s r ⟨by simp only; omega, by simp only; omega⟩ ?_ ?_ hsr
        · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [if_neg (by omega)]
          omega
        · intro a ha
          simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at ha
          rw [if_neg (by omega)] at ha
          exact Fin.le_def.2 (by omega)
      · have hr : ¬ (r : ℕ) < N - j := fun h => hs (hblk.1 h)
        have hrN := r.2
        refine ent τ' ⟨s - (N - j), by omega⟩ s r ⟨by simp only; omega, by simp only; omega⟩ ?_ ?_ hsr
        · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [if_pos (by omega)]
          omega
        · intro a ha
          simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at ha
          rw [if_pos (by omega)] at ha
          exact Fin.le_def.2 (by omega)
    · rw [(hL τ').1 r s hblk, (hL' τ').1 r s hblk]
  · rw [hsr, (hL τ').2.1, (hL' τ').2.1]
  · rw [(hL τ').2.2 r s hsr, (hL' τ').2.2 r s hsr]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
