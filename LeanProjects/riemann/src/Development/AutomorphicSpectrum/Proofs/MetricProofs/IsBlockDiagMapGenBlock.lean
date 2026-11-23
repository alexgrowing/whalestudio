import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenericBlockMatrixIsBlockDiag
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CauchyBinet

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

section Homog

variable {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isMultiHomog_mul_alt {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp [Finset.sum_add_distrib, hf m₁ h₁ k, hg m₂ h₂ k]

theorem isMultiHomog_add_alt {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem isMultiHomog_zero_alt (a : K → ℕ) : IsMultiHomog (0 : MRing ι) a := by
  intro m hm
  simp at hm

theorem isMultiHomog_one_alt : IsMultiHomog (1 : MRing ι) 0 := by
  classical
  intro m hm k
  have : m = 0 := by
    have h := MvPolynomial.support_monomial_subset (s := (0 : (Σ k, ι k) →₀ ℕ)) (a := (1 : ℤ)) hm
    simpa using h
  simp [this]

theorem isMultiHomog_rename_base {σ : Type} (blk : σ → Option K) {d' : NonPluckerBlocks blk → ℕ}
    {g : MRing (baseIdx ι blk)} (hg : IsMultiHomog g d') :
    open Classical in
    IsMultiHomog (rename (fun q : Σ k, baseIdx ι blk k => (⟨q.1.1, q.2⟩ : Σ k, ι k)) g)
      (fun k => if h : ∀ p, blk p ≠ some k then d' ⟨k, h⟩ else 0) := by
  classical
  have hinj : Function.Injective (fun q : Σ k, baseIdx ι blk k => (⟨q.1.1, q.2⟩ : Σ k, ι k)) := by
    rintro ⟨⟨k, hk⟩, a⟩ ⟨⟨k', hk'⟩, b⟩ h
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
    cases h
    rfl
  intro m hm k
  rw [support_rename_of_injective hinj, Finset.mem_image] at hm
  obtain ⟨m', hm', rfl⟩ := hm
  beta_reduce
  by_cases h : ∀ p, blk p ≠ some k
  · rw [dif_pos h, ← hg m' hm' ⟨k, h⟩]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finsupp.mapDomain_apply hinj m' ⟨⟨k, h⟩, i⟩
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun i _ => Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨⟨⟨k', hk'⟩, b⟩, e⟩
    obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.mp e
    exact h hk'

def IsFormQuot {Φ : Type} [Field Φ] (y : (Σ k, ι k) → Φ) (s : Φ) : Prop :=
  ∃ (d : K → ℕ) (g h : MRing ι), IsMultiHomog g d ∧ IsMultiHomog h d ∧ aeval y h ≠ 0 ∧ aeval y g = s * aeval y h

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}

theorem IsFormQuot.zero : IsFormQuot y 0 :=
  ⟨0, 0, 1, isMultiHomog_zero_alt _, isMultiHomog_one_alt, by simp, by simp⟩

theorem IsFormQuot.add {s t : Φ} (hs : IsFormQuot y s) (ht : IsFormQuot y t) : IsFormQuot y (s + t) := by
  obtain ⟨d₁, g₁, h₁, hg₁, hh₁, hy₁, e₁⟩ := hs
  obtain ⟨d₂, g₂, h₂, hg₂, hh₂, hy₂, e₂⟩ := ht
  refine ⟨d₁ + d₂, g₁ * h₂ + g₂ * h₁, h₁ * h₂,
    isMultiHomog_add_alt (isMultiHomog_mul_alt hg₁ hh₂) (by rw [add_comm d₁]; exact isMultiHomog_mul_alt hg₂ hh₁),
    isMultiHomog_mul_alt hh₁ hh₂, by rw [map_mul]; exact mul_ne_zero hy₁ hy₂, ?_⟩
  rw [map_add, map_mul, map_mul, map_mul, e₁, e₂]
  ring

theorem IsFormQuot.mul {s t : Φ} (hs : IsFormQuot y s) (ht : IsFormQuot y t) : IsFormQuot y (s * t) := by
  obtain ⟨d₁, g₁, h₁, hg₁, hh₁, hy₁, e₁⟩ := hs
  obtain ⟨d₂, g₂, h₂, hg₂, hh₂, hy₂, e₂⟩ := ht
  refine ⟨d₁ + d₂, g₁ * g₂, h₁ * h₂, isMultiHomog_mul_alt hg₁ hg₂, isMultiHomog_mul_alt hh₁ hh₂,
    by rw [map_mul]; exact mul_ne_zero hy₁ hy₂, ?_⟩
  rw [map_mul, map_mul, e₁, e₂]
  ring

theorem IsFormQuot.inv {s : Φ} (hs : IsFormQuot y s) : IsFormQuot y s⁻¹ := by
  by_cases h0 : s = 0
  · rw [h0, inv_zero]
    exact IsFormQuot.zero
  · obtain ⟨d, g, h, hg, hh, hy, e⟩ := hs
    refine ⟨d, h, g, hh, hg, by rw [e]; exact mul_ne_zero h0 hy, ?_⟩
    rw [e]
    field_simp

theorem IsFormQuot.sum {α : Type} (A : Finset α) {f : α → Φ} (hf : ∀ a ∈ A, IsFormQuot y (f a)) :
    IsFormQuot y (∑ a ∈ A, f a) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using IsFormQuot.zero
  | insert a A ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self _ _)).add
      (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))

end Homog

section Minors

variable {N : ℕ}

theorem minorIJ_eq_det_of_card {R : Type} [CommRing R] (h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) {r : ℕ}
    (hI : I.card = r) (hJ : J.card = r) :
    minorIJ h I J = (h.submatrix (I.orderEmbOfFin hI) (J.orderEmbOfFin hJ)).det := by
  subst hJ
  unfold minorIJ
  rw [dif_pos hI]

theorem minorIJ_mul_sum {R : Type} [CommRing R] (T h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) :
    minorIJ (T * h) I J = ∑ I', minorIJ T I I' * minorIJ h I' J := by
  classical
  by_cases e : I.card = J.card
  · have hm : (T * h).submatrix (I.orderEmbOfFin e) (J.orderEmbOfFin rfl) =
        T.submatrix (I.orderEmbOfFin e) id * h.submatrix id (J.orderEmbOfFin rfl) := by
      ext a b
      simp [Matrix.mul_apply]
    have hsum : ∑ I', minorIJ T I I' * minorIJ h I' J =
        ∑ S : {S : Finset (Fin N) // S.card = J.card}, minorIJ T I S.1 * minorIJ h S.1 J := by
      rw [← Finset.sum_filter_of_ne (s := Finset.univ) (p := fun S : Finset (Fin N) => S.card = J.card)]
      · exact Finset.sum_subtype _ (by simp) _
      · intro S _ hS
        by_contra hc
        apply hS
        rw [show minorIJ h S J = 0 by unfold minorIJ; rw [dif_neg hc], mul_zero]
    rw [minorIJ_eq_det_of_card _ I J e rfl, hm, ReciprocityTheory.ChartRestriction.DS.cauchyBinet, hsum]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [minorIJ_eq_det_of_card T I S.1 e S.2, minorIJ_eq_det_of_card h S.1 J S.2 rfl]
    rfl
  · have h0 : minorIJ (T * h) I J = 0 := by
      unfold minorIJ
      rw [dif_neg e]
    rw [h0]
    symm
    refine Finset.sum_eq_zero fun I' _ => ?_
    by_cases e' : I.card = I'.card
    · rw [show minorIJ h I' J = 0 by
        unfold minorIJ
        rw [dif_neg fun c => e (e'.trans c)], mul_zero]
    · rw [show minorIJ T I I' = 0 by unfold minorIJ; rw [dif_neg e'], zero_mul]

theorem minorIJ_block_zero {R : Type} [CommRing R] {j : ℕ} {i : Fin N} {h : Matrix (Fin N) (Fin N) R}
    (hh : IsBlockDiag j h) {I : Finset (Fin N)} (hnot : ¬ IsStepRows N j i I) :
    minorIJ h I (stepCols N j i) = 0 := by
  have hiN := i.isLt
  by_cases e : I.card = (stepCols N j i).card
  · have hsub : ¬ I ⊆ if (i : ℕ) + 1 ≤ j then wIdx N j else omIdx N j := fun hs => hnot ⟨e, hs⟩
    obtain ⟨a, haI, haB⟩ := Finset.not_subset.mp hsub
    have hr : a ∈ Set.range (I.orderEmbOfFin e) := by
      rw [Finset.range_orderEmbOfFin]
      exact haI
    obtain ⟨r, rfl⟩ := hr
    unfold minorIJ
    rw [dif_pos e]
    refine Matrix.det_eq_zero_of_row_eq_zero r fun c => ?_
    have hb := Finset.orderEmbOfFin_mem (stepCols N j i) rfl c
    refine hh _ _ ?_
    generalize (stepCols N j i).orderEmbOfFin rfl c = b at hb
    generalize I.orderEmbOfFin e r = a at haB
    by_cases hc : (i : ℕ) + 1 ≤ j
    · simp only [stepCols, wIdx, Finset.mem_filter, Finset.mem_univ, true_and, if_pos hc] at hb haB
      omega
    · simp only [stepCols, omIdx, Finset.mem_filter, Finset.mem_univ, true_and, if_neg hc] at hb haB
      omega
  · unfold minorIJ
    rw [dif_neg e]

def genBlock (Ω : Type) [Field Ω] (N j : ℕ) : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N × Fin N) Ω) :=
  fun a b => if ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) then X (a, b) else 0

theorem isBlockDiag_inv {F : Type} [Field F] {j : ℕ} {T : Matrix (Fin N) (Fin N) F} (hT : IsBlockDiag j T)
    (hd : T.det ≠ 0) : IsBlockDiag j T⁻¹ := by
  classical
  haveI : Invertible T := Matrix.invertibleOfIsUnitDet T (isUnit_iff_ne_zero.mpr hd)
  have h1 : T.BlockTriangular (fun a : Fin N => if (a : ℕ) < N - j then 0 else 1) := by
    intro a b hab
    refine hT a b fun hiff => ?_
    simp only [hiff] at hab
    exact lt_irrefl _ hab
  have h2 : T.BlockTriangular (fun a : Fin N => if (a : ℕ) < N - j then 1 else 0) := by
    intro a b hab
    refine hT a b fun hiff => ?_
    simp only [hiff] at hab
    exact lt_irrefl _ hab
  have i1 := Matrix.blockTriangular_inv_of_blockTriangular h1
  have i2 := Matrix.blockTriangular_inv_of_blockTriangular h2
  intro a b hab
  by_cases ha : (a : ℕ) < N - j
  · have hb : ¬ (b : ℕ) < N - j := fun hb => hab (iff_of_true ha hb)
    refine i2 ?_
    simp [ha, hb]
  · have hb : (b : ℕ) < N - j := by
      by_contra hb
      exact hab (iff_of_false ha hb)
    refine i1 ?_
    simp [ha, hb]

end Minors

section Model

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ}

end Model

end GlobalTheory.CompanionTheory.Ar.PB
