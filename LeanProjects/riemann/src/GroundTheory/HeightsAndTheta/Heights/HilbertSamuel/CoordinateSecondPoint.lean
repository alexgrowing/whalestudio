import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.MdifferentiableAtChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ExistsNatMulMemConeRingIntFin
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial Filter

noncomputable section

theorem geoNum_nonneg {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] :
    ∀ (n : ℕ) (V : Ideal (MRing ι)) (a : Fin n → K → ℤ), (∀ j k, 0 ≤ a j k) → 0 ≤ geoNum n V a
  | 0, V, a, _ => by
    unfold geoNum
    split_ifs <;> simp
  | n + 1, V, a, ha => by
    unfold geoNum
    split_ifs with h
    · refine Finset.sum_nonneg fun k _ ↦ mul_nonneg (ha _ _) (finsum_nonneg fun W ↦ finsum_nonneg fun _ ↦ ?_)
      exact mul_nonneg (Nat.cast_nonneg _) (geoNum_nonneg n W _ fun j k ↦ ha _ _)
    · exact le_rfl

theorem nefOnFibres_of_nonneg {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) {a : K → ℤ} (ha : ∀ k, 0 ≤ a k) : NefOnFibres P a :=
  fun W _ _ _ _ ↦ geoNum_nonneg 1 W _ fun _ k ↦ ha k

namespace P1

theorem sum_blk (m : J2 →₀ ℕ) : ∑ i : Fin 2, m ⟨(), i⟩ = ∑ q, m q := by
  rw [sum_twoPoint, Fin.sum_univ_two]; rfl

theorem isMultiHomog_iff (f : MvPolynomial J2 ℤ) (d : ℕ) :
    IsMultiHomog (ι := GlobalTheory (Fin 2)) f (fun _ ↦ d) ↔ f.IsHomogeneous d := by
  constructor
  · intro h m hm
    have := h m (mem_support_iff.mpr hm) ()
    rw [sum_blk] at this
    simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one]
    rw [Finsupp.sum_fintype _ _ (by simp)]
    exact this
  · intro h m hm k
    have := h (mem_support_iff.mp hm)
    simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one] at this
    rw [Finsupp.sum_fintype _ _ (by simp)] at this
    rw [sum_blk]
    exact this

theorem isMultiHomog_X (q : J2) : IsMultiHomog (ι := GlobalTheory (Fin 2)) (X q : MvPolynomial J2 ℤ) fun _ ↦ 1 :=
  (isMultiHomog_iff _ 1).mpr (isHomogeneous_X ℤ q)

theorem isMultiHomog_one : IsMultiHomog (ι := GlobalTheory (Fin 2)) (1 : MvPolynomial J2 ℤ) fun _ ↦ 0 :=
  (isMultiHomog_iff _ 0).mpr (isHomogeneous_one _ _)

abbrev Afs : HermLine (GlobalTheory (Fin 2)) := HermLine.ofCone fs

theorem ratio_mem (c : ∀ k, GlobalTheory (Fin 2) k) (q : J2) :
    x q / x ⟨(), c ()⟩ ∈ chartRingZ (ι := GlobalTheory (Fin 2)) x c :=
  Algebra.subset_adjoin ⟨q, rfl⟩

def e2 : Fin 2 → J2 := fun i ↦ ⟨(), i⟩

end P1

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
