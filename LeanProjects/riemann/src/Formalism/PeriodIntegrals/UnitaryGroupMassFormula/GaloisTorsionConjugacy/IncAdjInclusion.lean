import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.MulDefs

noncomputable section

namespace PI.GalTorsConj.W

open Polynomial

def incAdj (M M₁ : IntermediateField ℚ ℂ) : M₁ →+* IntermediateField.adjoin M (M₁ : Set ℂ) where
  toFun x := ⟨x, IntermediateField.subset_adjoin M _ x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem incAdj_inclusion (M M₁ : IntermediateField ℚ ℂ) (h : M ≤ M₁) (x : M) :
    incAdj M M₁ (IntermediateField.inclusion h x) = algebraMap M _ x := Subtype.ext rfl

theorem extRho : ExtRho := by
  intro M M₁ h halg ρ
  letI iA : Algebra M M₁ := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI hA : Algebra.IsAlgebraic M M₁ := by
    refine ⟨fun x => ?_⟩
    let f : M₁ →ₐ[M] ℂ :=
      { toRingHom := (M₁.val : M₁ →+* ℂ)
        commutes' := fun _ => rfl }
    exact (isAlgebraic_algHom_iff f M₁.val.injective).mp (halg x x.2)
  letI iC : Algebra M ℂ := ρ.toRingHom.toAlgebra
  let φ : M₁ →ₐ[M] ℂ := IsAlgClosed.lift
  refine ⟨{ toRingHom := φ.toRingHom, commutes' := φ.toRingHom.map_rat_algebraMap }, fun x => ?_⟩
  exact φ.commutes x

theorem descent : Descent := by
  classical
  intro M M₁ h halg x hx
  by_contra hxM
  have hint : IsIntegral M (x : ℂ) := (halg x x.2).isIntegral
  have hsep : (minpoly M (x : ℂ)).Separable := (minpoly.irreducible hint).separable
  have hdeg : 2 ≤ (minpoly M (x : ℂ)).natDegree := by
    have h1 : (minpoly M (x : ℂ)).natDegree ≠ 1 := by
      intro h1
      apply hxM
      obtain ⟨m, hm⟩ := minpoly.natDegree_eq_one_iff.mp h1
      rw [← hm]
      exact m.2
    have h0 : 0 < (minpoly M (x : ℂ)).natDegree := minpoly.natDegree_pos hint
    omega
  have hc : Fintype.card ((minpoly M (x : ℂ)).rootSet ℂ) = (minpoly M (x : ℂ)).natDegree :=
    Polynomial.card_rootSet_eq_natDegree hsep (IsAlgClosed.splits _)
  have hxr : (x : ℂ) ∈ (minpoly M (x : ℂ)).rootSet ℂ :=
    Polynomial.mem_rootSet.mpr ⟨minpoly.ne_zero hint, minpoly.aeval M (x : ℂ)⟩
  have h2 : 1 < Fintype.card ((minpoly M (x : ℂ)).rootSet ℂ) := by omega
  obtain ⟨⟨y, hyr⟩, hyx'⟩ := Fintype.exists_ne_of_one_lt_card h2 (⟨(x : ℂ), hxr⟩ :
    (minpoly M (x : ℂ)).rootSet ℂ)
  have hyx : y ≠ (x : ℂ) := fun e => hyx' (Subtype.ext e)
  have hy : y ∈ (minpoly M (x : ℂ)).aroots ℂ :=
    Polynomial.mem_aroots.mpr ⟨minpoly.ne_zero hint, (Polynomial.mem_rootSet.mp hyr).2⟩
  let K : IntermediateField M ℂ := IntermediateField.adjoin M {(x : ℂ)}
  let τ : K →ₐ[M] ℂ := (IntermediateField.algHomAdjoinIntegralEquiv M hint).symm ⟨y, hy⟩
  have hτ : τ (IntermediateField.AdjoinSimple.gen M (x : ℂ)) = y :=
    IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen M hint ⟨y, hy⟩
  let M' : IntermediateField ℚ ℂ := K.restrictScalars ℚ
  have hMM' : M ≤ M' := fun m hm => (IntermediateField.mem_restrictScalars ℚ).mpr (K.algebraMap_mem ⟨m, hm⟩)
  have hM'1 : M' ≤ M₁ := by
    intro z hz
    have hz' : z ∈ K := (IntermediateField.mem_restrictScalars ℚ).mp hz
    have hle : K ≤ IntermediateField.extendScalars h :=
      IntermediateField.adjoin_simple_le_iff.mpr ((IntermediateField.mem_extendScalars h).mpr x.2)
    exact (IntermediateField.mem_extendScalars h).mp (hle hz')
  have halg' : ∀ z ∈ M₁, IsAlgebraic M' z := by
    intro z hz
    letI : Algebra M M' := (IntermediateField.inclusion hMM').toRingHom.toAlgebra
    haveI : IsScalarTower M M' ℂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    exact (halg z hz).tower_top M'
  let f : M' →+* ℂ := τ.toRingHom
  let ρ : M' →ₐ[ℚ] ℂ := { toRingHom := f, commutes' := f.map_rat_algebraMap }
  obtain ⟨ρ₁, hρ₁⟩ := extRho M' M₁ hM'1 halg' ρ
  have hfix : ∀ m : M, ρ₁ (IntermediateField.inclusion h m) = (m : ℂ) := by
    intro m
    have e : IntermediateField.inclusion h m =
        IntermediateField.inclusion hM'1 (IntermediateField.inclusion hMM' m) := rfl
    rw [e, hρ₁]
    exact τ.commutes m
  have memx : (x : ℂ) ∈ M' :=
    (IntermediateField.mem_restrictScalars ℚ).mpr (IntermediateField.mem_adjoin_simple_self M (x : ℂ))
  apply hyx
  calc y = τ (IntermediateField.AdjoinSimple.gen M (x : ℂ)) := hτ.symm
    _ = ρ ⟨(x : ℂ), memx⟩ := rfl
    _ = ρ₁ (IntermediateField.inclusion hM'1 ⟨(x : ℂ), memx⟩) := (hρ₁ _).symm
    _ = ρ₁ x := rfl
    _ = x := hx ρ₁ hfix

end PI.GalTorsConj.W

end
