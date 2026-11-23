import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import GroundTheory.HeightsAndTheta.Heights.Intersections.UniquenessDegreeFormOfIntersectionForm
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

open Classical in

def killBlocks (S : Set K) : MRing ι →ₐ[ℤ] MRing ι :=
  aeval fun p => if p.1 ∈ S then 0 else X p

omit [Fintype K] [∀ k, Fintype (ι k)] in
open Classical in

theorem killBlocks_X (S : Set K) (p : Σ k, ι k) :
    killBlocks S (X p : MRing ι) = if p.1 ∈ S then 0 else X p := by
  rw [killBlocks, aeval_X]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem killBlocks_monomial_of_forall (S : Set K) (m : (Σ k, ι k) →₀ ℕ) (c : ℤ)
    (h : ∀ p ∈ m.support, p.1 ∉ S) : killBlocks S (monomial m c : MRing ι) = monomial m c := by
  rw [killBlocks, aeval_monomial, monomial_eq, algebraMap_eq]
  congr 1
  refine Finsupp.prod_congr fun p hp => ?_
  rw [if_neg (h p hp)]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem killBlocks_monomial_of_mem (S : Set K) (m : (Σ k, ι k) →₀ ℕ) (c : ℤ) (p : Σ k, ι k)
    (hp : p ∈ m.support) (hS : p.1 ∈ S) : killBlocks S (monomial m c : MRing ι) = 0 := by
  rw [killBlocks, aeval_monomial, Finsupp.prod]
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero hp ?_)
  rw [if_pos hS, zero_pow (Finsupp.mem_support_iff.mp hp)]

theorem killBlocks_of_isMultiHomog (S : Set K) {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) :
    killBlocks S f = f ∨ killBlocks S f = 0 := by
  by_cases ha : ∀ k ∈ S, a k = 0
  · left
    rw [f.as_sum, map_sum]
    refine Finset.sum_congr rfl fun m hm => killBlocks_monomial_of_forall S m _ ?_
    rintro ⟨k, i⟩ hp hkS
    have h1 := hf m hm k
    rw [ha k hkS] at h1
    have h2 : m ⟨k, i⟩ ≤ ∑ j, m ⟨k, j⟩ :=
      Finset.single_le_sum (f := fun j => m ⟨k, j⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    exact Finsupp.mem_support_iff.mp hp (by omega)
  · right
    push Not at ha
    obtain ⟨k, hkS, hak⟩ := ha
    rw [f.as_sum, map_sum]
    refine Finset.sum_eq_zero fun m hm => ?_
    have h1 := hf m hm k
    obtain ⟨i, hi⟩ : ∃ i, m ⟨k, i⟩ ≠ 0 := by
      by_contra h0
      push Not at h0
      have : ∑ j, m ⟨k, j⟩ = 0 := Finset.sum_eq_zero fun j _ => h0 j
      omega
    exact killBlocks_monomial_of_mem S m _ ⟨k, i⟩ (Finsupp.mem_support_iff.mpr hi) hkS

theorem le_comap_killBlocks {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) (S : Set K) :
    P ≤ P.comap (killBlocks S) := by
  obtain ⟨T, hT, rfl⟩ := hP
  refine Ideal.span_le.mpr fun f hf => ?_
  obtain ⟨a, ha⟩ := hT f hf
  rw [SetLike.mem_coe, Ideal.mem_comap]
  rcases killBlocks_of_isMultiHomog S ha with h | h <;> rw [h]
  · exact Ideal.subset_span hf
  · exact Ideal.zero_mem _

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem killBlocks_comp {S S' : Set K} (h : S ⊆ S') :
    (killBlocks S').comp (killBlocks S) = (killBlocks S' : MRing ι →ₐ[ℤ] MRing ι) := by
  refine MvPolynomial.algHom_ext fun p => ?_
  rw [AlgHom.comp_apply, killBlocks_X, killBlocks_X]
  by_cases hp : p.1 ∈ S
  · rw [if_pos hp, map_zero, if_pos (h hp)]
  · rw [if_neg hp, killBlocks_X]

theorem comap_killBlocks_mono {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) {S S' : Set K}
    (h : S ⊆ S') : P.comap (killBlocks S) ≤ P.comap (killBlocks S') := by
  intro f hf
  rw [Ideal.mem_comap] at hf ⊢
  have e : killBlocks S' f = killBlocks S' (killBlocks S f) := by
    rw [← AlgHom.comp_apply, killBlocks_comp h]
  rw [e]
  exact le_comap_killBlocks hP S' hf

theorem arithVarZero : ReciprocityTheory.ChartRestriction.G.AI.I2.ArithVarZeroStatement := by
  intro K _ ι _ P hP
  obtain ⟨_, ⟨hPp, hPh, hPr⟩, hhor, hdim⟩ := hP
  have := hPp
  set m := Fintype.card K with hm
  let e : K ≃ Fin m := Fintype.equivFin K
  let S : ℕ → Set K := fun n => {k | (e k : ℕ) < n}
  let Q : ℕ → Ideal (MRing ι) := fun n => P.comap (killBlocks (S n))
  let Q2 : Ideal (MRing ι) :=
    RingHom.ker ((Int.castRingHom (ZMod 2)).comp (constantCoeff : MRing ι →+* ℤ))
  have hQp : ∀ n, (Q n).IsPrime := fun n => Ideal.IsPrime.comap _
  have hQ2p : Q2.IsPrime := RingHom.ker_isPrime _
  have hstep : ∀ n, n < m → Q n < Q (n + 1) := by
    intro n hn
    obtain ⟨i, hi⟩ := hPr (e.symm ⟨n, hn⟩)
    refine SetLike.lt_iff_le_and_exists.mpr
      ⟨comap_killBlocks_mono hPh fun k hk => Nat.lt_succ_of_lt hk, X ⟨e.symm ⟨n, hn⟩, i⟩, ?_, ?_⟩
    · show killBlocks _ _ ∈ P
      rw [killBlocks_X, if_pos (by simp [S])]
      exact P.zero_mem
    · intro h2
      change killBlocks _ _ ∈ P at h2
      rw [killBlocks_X, if_neg (by simp [S])] at h2
      exact hi h2
  have hall : ∀ f : MRing ι, killBlocks (S m) f = C (constantCoeff f) := by
    intro f
    have : killBlocks (S m) = aeval (0 : (Σ k, ι k) → MRing ι) := by
      refine MvPolynomial.algHom_ext fun p => ?_
      rw [killBlocks_X, if_pos (by simp [S]), aeval_X]
      rfl
    rw [this, aeval_zero, algebraMap_eq]
  have hQm : ∀ f, f ∈ Q m ↔ constantCoeff f = 0 := by
    intro f
    change killBlocks (S m) f ∈ P ↔ _
    rw [hall]
    change constantCoeff f ∈ P.comap (C : ℤ →+* MRing ι) ↔ _
    rw [hhor, Ideal.mem_bot]
  have hstep2 : Q m < Q2 := by
    refine SetLike.lt_iff_le_and_exists.mpr ⟨fun f hf => ?_, C 2, ?_, fun h2 => ?_⟩
    · rw [RingHom.mem_ker, RingHom.comp_apply, (hQm f).mp hf, map_zero]
    · rw [RingHom.mem_ker, RingHom.comp_apply, constantCoeff_C]
      rfl
    · have := (hQm _).mp h2
      rw [constantCoeff_C] at this
      norm_num at this
  let T : ℕ → Ideal (MRing ι) := fun n => if n ≤ m then Q n else Q2
  have hTp : ∀ n, (T n).IsPrime := by
    intro n
    dsimp only [T]
    split_ifs
    exacts [hQp n, hQ2p]
  have hPT : ∀ n, P ≤ T n := by
    intro n
    dsimp only [T]
    split_ifs
    · exact le_comap_killBlocks hPh _
    · exact (le_comap_killBlocks hPh _).trans hstep2.le
  have hTlt : ∀ n, n ≤ m → T n < T (n + 1) := by
    intro n hn
    dsimp only [T]
    rw [if_pos hn]
    rcases hn.lt_or_eq with h | h
    · rw [if_pos (Nat.succ_le_of_lt h)]
      exact hstep n h
    · rw [if_neg (by omega), h]
      exact hstep2
  let g : Fin (m + 2) → PrimeSpectrum.zeroLocus (R := MRing ι) (P : Set (MRing ι)) :=
    fun j => ⟨⟨T j, hTp j⟩, hPT j⟩
  have hg : StrictMono g := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    exact hTlt i (Nat.lt_succ_iff.mp i.isLt)
  have hlen := Order.LTSeries.length_le_krullDim (LTSeries.mk (m + 1) g hg)
  rw [← ringKrullDim_quotient, hdim] at hlen
  have h3 : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ ((0 + m : ℕ) : WithBot ℕ∞) := hlen
  have h4 : m + 1 ≤ 0 + m := by exact_mod_cast h3
  omega

end GroundTheory.Heights₂.Heights.Inter

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
