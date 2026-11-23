import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ImportsAlt
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.AevalGenericIdealIff
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace VerticalPartGauss

open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal coeffGaussNorm)
open ObjectsChow (genericIdeal)

section Places

variable {K : Type*} [Field K] [NumberField K] {σ : Type*}

end Places

section Generic

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {n : ℕ}

abbrev constUnits (n : ℕ) : Submonoid (MvPolynomial (Fin n) ℤ) :=
  (nonZeroDivisors ℤ).map (C : ℤ →+* MvPolynomial (Fin n) ℤ)

theorem algebraMap_eq : algebraMap (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℚ) =
    map (Int.castRingHom ℚ) := by
  rw [MvPolynomial.algebraMap_def, algebraMap_int_eq]

theorem genericIdeal_eq (P : Ideal (MRing (PBlk n))) :
    genericIdeal P = (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P).map
      (algebraMap (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℚ)) := by
  rw [algebraMap_eq]
  rfl

theorem finIdeal_isPrime {P : Ideal (MRing (PBlk n))} {d : ℕ} (hP : IsArithVar P d) :
    (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P).IsPrime := by
  have := hP.2.1.1
  unfold IndefiniteRowSideFullHecke.ArithBezout.finIdeal
  infer_instance

theorem disjoint_constUnits {P : Ideal (MRing (PBlk n))} {d : ℕ} (hP : IsArithVar P d) :
    Disjoint (constUnits n : Set (MvPolynomial (Fin n) ℤ)) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) := by
  rw [Set.disjoint_left]
  rintro _ ⟨k, hk, rfl⟩ hmem
  have hk0 : k ≠ 0 := nonZeroDivisors.ne_zero hk
  have h1 : (C k : MRing (PBlk n)) ∈ P := by
    simpa [IndefiniteRowSideFullHecke.ArithBezout.finIdeal, Ideal.mem_comap, rename_C] using hmem
  have h2 : k ∈ P.comap (C : ℤ →+* MRing (PBlk n)) := h1
  rw [hP.2.2.1] at h2
  exact hk0 ((Submodule.mem_bot ℤ).mp h2)

theorem map_mem_genericIdeal_iff {P : Ideal (MRing (PBlk n))} {d : ℕ} (hP : IsArithVar P d)
    (x : MvPolynomial (Fin n) ℤ) :
    map (Int.castRingHom ℚ) x ∈ genericIdeal P ↔ x ∈ IndefiniteRowSideFullHecke.ArithBezout.finIdeal P := by
  have h := IsLocalization.under_map_of_isPrime_disjoint (constUnits n) (MvPolynomial (Fin n) ℚ)
    (finIdeal_isPrime hP) (disjoint_constUnits hP)
  rw [genericIdeal_eq, ← algebraMap_eq]
  constructor
  · intro hx
    rw [← h]
    exact hx
  · exact Ideal.mem_map_of_mem _

theorem genericIdeal_isPrime {P : Ideal (MRing (PBlk n))} {d : ℕ} (hP : IsArithVar P d) :
    (genericIdeal P).IsPrime := by
  rw [genericIdeal_eq]
  exact IsLocalization.isPrime_of_isPrime_disjoint (constUnits n) _ _ (finIdeal_isPrime hP)
    (disjoint_constUnits hP)

def blkEquiv (n : ℕ) : Fin n ≃ (Σ _ : Unit, PBlk n ()) where
  toFun i := ⟨(), i⟩
  invFun p := p.2
  left_inv _ := rfl
  right_inv := fun ⟨(), _⟩ => rfl

theorem isHomogeneous_of_isMultiHomog {s : MRing (PBlk n)} {a : Unit → ℕ}
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) :
    (map (Int.castRingHom ℚ) (rename (blkEquiv n).symm s)).IsHomogeneous (a ()) := by
  refine IsHomogeneous.map ?_ _
  refine IsHomogeneous.rename_isHomogeneous ?_
  intro m hm
  have h := hs m (mem_support_iff.mpr hm) ()
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma, Fintype.sum_unique]
  simpa using h

theorem finIdeal_eq_span {P : Ideal (MRing (PBlk n))} {S : Set (MRing (PBlk n))}
    (hS : P = Ideal.span S) :
    IndefiniteRowSideFullHecke.ArithBezout.finIdeal P = Ideal.span (rename (blkEquiv n).symm '' S) := by
  have hre : ∀ x : MvPolynomial (Fin n) ℤ, rename (blkEquiv n).symm (rename (fun i : Fin n =>
      (⟨(), i⟩ : Σ _ : Unit, PBlk n ())) x) = x := fun x => by
    rw [rename_rename]
    exact rename_id_apply x
  have hre' : ∀ s : MRing (PBlk n), rename (fun i : Fin n => (⟨(), i⟩ : Σ _ : Unit, PBlk n ()))
      (rename (blkEquiv n).symm s) = s := fun s => by
    rw [rename_rename]
    convert rename_id_apply s
    funext p
    rcases p with ⟨⟨⟩, i⟩
    rfl
  apply le_antisymm
  · intro x hx
    have hx' : rename (fun i : Fin n => (⟨(), i⟩ : Σ _ : Unit, PBlk n ())) x ∈ Ideal.span S := by
      rw [← hS]; exact hx
    have := Ideal.mem_map_of_mem (rename (blkEquiv n).symm : MRing (PBlk n) →ₐ[ℤ] _).toRingHom hx'
    rw [Ideal.map_span] at this
    simpa [hre] using this
  · rw [Ideal.span_le]
    rintro _ ⟨s, hs, rfl⟩
    change rename _ (rename (blkEquiv n).symm s) ∈ P
    rw [hre', hS]
    exact Ideal.subset_span hs

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem genericIdeal_isHomog {P : Ideal (MRing (PBlk n))} {d : ℕ} (hP : IsArithVar P d) :
    IsHomogIdeal (genericIdeal P) := by
  obtain ⟨S, hSh, hS⟩ := hP.2.1.2.1
  have hspan : genericIdeal P = Ideal.span ((fun s => map (Int.castRingHom ℚ)
      (rename (blkEquiv n).symm s)) '' S) := by
    rw [ObjectsChow.genericIdeal, finIdeal_eq_span hS, Ideal.map_span, ← Set.image_comp]
    rfl
  have hhom : (genericIdeal P).IsHomogeneous (homogeneousSubmodule (Fin n) ℚ) := by
    rw [hspan]
    refine Ideal.homogeneous_span _ _ ?_
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨a, ha⟩ := hSh s hs
    exact ⟨a (), (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_of_isMultiHomog ha)⟩
  intro f hf i
  have := hhom i hf
  rwa [← decomposition.decompose'_apply]

theorem genericIdeal_isRelevant {P : Ideal (MRing (PBlk n))} {d : ℕ} (hP : IsArithVar P d) :
    IsRelevant (genericIdeal P) := by
  obtain ⟨j, hj⟩ := (ObjectsChow.isRelevant_finIdeal_iff P).mpr hP.2.1.2.2
  refine ⟨j, fun h => hj ((map_mem_genericIdeal_iff hP (X j)).mp ?_)⟩
  rwa [map_X]

theorem isProjPrime_genericIdeal {P : Ideal (MRing (PBlk n))} {d : ℕ} (hP : IsArithVar P d) :
    IsProjPrime (genericIdeal P) :=
  ⟨genericIdeal_isPrime hP, genericIdeal_isHomog hP, genericIdeal_isRelevant hP⟩

theorem linForm_not_mem_genericIdeal {P : Ideal (MRing (PBlk n))} {d : ℕ} (hP : IsArithVar P d)
    {u : Fin n → ℤ} (hu : IndefiniteRowSideFullHecke.ArithBezout.linForm u ∉ P) :
    linForm (fun j => (u j : ℚ)) ∉ genericIdeal P := by
  intro h
  have hmap : linForm (fun j => (u j : ℚ)) = map (Int.castRingHom ℚ) (linForm u) := by
    simp [linForm, map_sum]
  rw [hmap, map_mem_genericIdeal_iff hP, ObjectsChow.linForm_mem_finIdeal] at h
  exact hu h

end Generic

theorem isChowForm_genericIdeal {n e δ : ℕ} {P : Ideal (MRing (PBlk n))} (hP : IsArithVar P (e + 1))
    {f : MvPolynomial (Fin (e + 1) × Fin n) ℚ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) e δ
      (map (Rat.castHom ℂ) f)) :
    IsChowForm (genericIdeal P) (e + 1) f := by
  obtain ⟨c, hc, g, hcg, hg⟩ := ObjectsChow.ComplexChowFormToChowForm.proof n e δ P _ hP hf
  obtain ⟨m, hm⟩ := ne_zero_iff.mp hg.1
  have hcoef := congrArg (coeff m) hcg
  rw [coeff_map, coeff_C_mul, coeff_map] at hcoef
  have hm' : ((g.coeff m : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hm
  have hcq : c = ((f.coeff m / g.coeff m : ℚ) : ℂ) := by
    rw [Rat.cast_div, eq_div_iff hm']
    simpa using hcoef.symm
  have hfq : f = C (f.coeff m / g.coeff m) * g := by
    apply map_injective (Rat.castHom ℂ) (Rat.castHom ℂ).injective
    rw [hcg, map_mul, map_C, hcq]
    rfl
  have hq : f.coeff m / g.coeff m ≠ 0 := by
    intro h
    apply hc
    rw [hcq, h, Rat.cast_zero]
  rw [hfq]
  exact ObjectsChow.isChowForm_C_mul hg hq

end VerticalPartGauss

end GroundTheory.Heights₂.Heights
