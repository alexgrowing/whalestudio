import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LinFormOneZero
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)

namespace GenericFibreIdeal

variable {n : ℕ}

def blkEquiv (n : ℕ) : Fin n ≃ (Σ _ : Unit, PBlk n ()) where
  toFun i := ⟨(), i⟩
  invFun p := p.2
  left_inv _ := rfl
  right_inv p := by rcases p with ⟨⟨⟩, i⟩; rfl

def blkRingEquiv (n : ℕ) : MvPolynomial (Fin n) ℤ ≃+* MRing (PBlk n) :=
  (renameEquiv ℤ (blkEquiv n)).toRingEquiv

theorem finIdeal_eq_map (P : Ideal (MRing (PBlk n))) :
    IndefiniteRowSideFullHecke.ArithBezout.finIdeal P = P.map (blkRingEquiv n).symm := by
  rw [Ideal.map_symm]
  exact Ideal.ext fun _ => Iff.rfl

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem algebraMap_eq :
    algebraMap (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℚ) =
      MvPolynomial.map (Int.castRingHom ℚ) := by
  show MvPolynomial.map (algebraMap ℤ ℚ) = _
  rw [RingHom.ext_int (algebraMap ℤ ℚ) (Int.castRingHom ℚ)]

abbrev intUnits (n : ℕ) : Submonoid (MvPolynomial (Fin n) ℤ) :=
  (nonZeroDivisors ℤ).map (C : ℤ →+* MvPolynomial (Fin n) ℤ)

instance : IsLocalization (intUnits n) (MvPolynomial (Fin n) ℚ) :=
  MvPolynomial.isLocalization (nonZeroDivisors ℤ) ℚ

theorem finIdeal_isPrime_disjoint (n d : ℕ) (P : Ideal (MRing (PBlk n))) (hP : IsArithVar P d) :
    (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P).IsPrime ∧
      Disjoint ((intUnits n : Set (MvPolynomial (Fin n) ℤ))) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) := by
  obtain ⟨-, ⟨hprime, -, -⟩, hhor, -⟩ := hP
  refine ⟨?_, ?_⟩
  · have := hprime
    exact Ideal.comap_isPrime _ _
  · refine Set.disjoint_left.mpr ?_
    rintro _ ⟨a, ha, rfl⟩ hx
    have h1 : (C a : MRing (PBlk n)) ∈ P := by
      simpa [IndefiniteRowSideFullHecke.ArithBezout.finIdeal, Ideal.mem_comap] using hx
    have h2 : a ∈ P.comap (C : ℤ →+* MRing (PBlk n)) := h1
    rw [hhor, Ideal.mem_bot] at h2
    exact nonZeroDivisors.ne_zero ha h2

section Homog

attribute [local instance] MvPolynomial.gradedAlgebra

theorem genericIdeal_isHomogIdeal (P : Ideal (MRing (PBlk n)))
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal P) : IsHomogIdeal (genericIdeal P) := by
  obtain ⟨S, hS, hPS⟩ := hP
  have hH : (genericIdeal P).IsHomogeneous (homogeneousSubmodule (Fin n) ℚ) := by
    rw [genericIdeal, finIdeal_eq_map, hPS, Ideal.map_span, Ideal.map_span]
    refine Ideal.homogeneous_span _ _ ?_
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    obtain ⟨a, ha⟩ := hS s hs
    refine ⟨a (), (mem_homogeneousSubmodule _ _).mpr ?_⟩
    have hs' : s.IsHomogeneous (a ()) := by
      intro m hm
      change Finsupp.weight (fun _ => 1) m = a ()
      rw [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum, Fintype.sum_sigma]
      simpa using ha m (mem_support_iff.mpr hm) ()
    exact (IsHomogeneous.rename_isHomogeneous hs').map _
  intro f hf k
  exact homogeneousComponent_mem_of_mem hH hf k

end Homog

theorem proof : GenericFibreIdeal.Statement := by
  intro n d P hP
  obtain ⟨hQprime, hdisj⟩ := finIdeal_isPrime_disjoint n d P hP
  have hgen : genericIdeal P =
      (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P).map
        (algebraMap (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℚ)) := by
    rw [algebraMap_eq]; rfl
  have hsat : (genericIdeal P).comap (MvPolynomial.map (Int.castRingHom ℚ)) =
      IndefiniteRowSideFullHecke.ArithBezout.finIdeal P := by
    rw [hgen, ← algebraMap_eq]
    exact IsLocalization.under_map_of_isPrime_disjoint (intUnits n) _ hQprime hdisj
  obtain ⟨-, ⟨-, ⟨S, hS, hPS⟩, hrel⟩, -, -⟩ := hP
  refine ⟨⟨?_, ?_, ?_⟩, hsat⟩
  · rw [hgen]
    exact IsLocalization.isPrime_of_isPrime_disjoint (intUnits n) _ _ hQprime hdisj
  · exact genericIdeal_isHomogIdeal P ⟨S, hS, hPS⟩
  ·
    obtain ⟨i, hi⟩ := hrel ()
    refine ⟨i, fun hX => hi ?_⟩
    have hmem : (X i : MvPolynomial (Fin n) ℤ) ∈ IndefiniteRowSideFullHecke.ArithBezout.finIdeal P := by
      rw [← hsat, Ideal.mem_comap, map_X]
      exact hX
    simpa [IndefiniteRowSideFullHecke.ArithBezout.finIdeal, Ideal.mem_comap] using hmem

end GenericFibreIdeal

end ObjectsChow

end GroundTheory.Heights₂.Heights
