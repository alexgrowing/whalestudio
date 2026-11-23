import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.BkCoeff

open GlobalTheory.PstCoeff

theorem isModuleTopology_of_tower (R LL V : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Field LL] [Algebra R LL] [TopologicalSpace LL] [IsTopologicalRing LL] [IsModuleTopology R LL]
    [AddCommGroup V] [Module LL V] [Module R V] [IsScalarTower R LL V] [FiniteDimensional LL V]
    [TopologicalSpace V] [IsModuleTopology LL V] : IsModuleTopology R V := by
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd LL V
  let e : V ≃ₗ[LL] (Fin (finrank LL V) → LL) := (Module.finBasis LL V).equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let e' : (Fin (finrank LL V) → LL) ≃L[R] V :=
    { e.symm.restrictScalars R with continuous_toFun := h2, continuous_invFun := h1 }
  exact IsModuleTopology.iso e'

section Coeff

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l}
  {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
  (ρ : Representation LL ↥(GK K) V)

theorem actVB_resQ (g : ↥(GK K)) (x : V ⊗[ℚ_[l]] P.R.B) :
    actVB (P.PD K) (resQ ρ) g x = actVB (P.PD K) ρ g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem galoisInvariants_restrictScalarsToQl : H0V (resQ ρ) = (H0V ρ).restrictScalars ℚ_[l] := by
  ext x
  simp [H0V, Submodule.mem_iInf, sub_eq_zero]

theorem FilV_resQ (a : ℤ) :
    FilV (P.PD K) (LL := ℚ_[l]) (V := V) a = (FilV (P.PD K) (LL := LL) (V := V) a).restrictScalars ℚ_[l] := by
  have h : ∀ y, AlgebraTensorModule.map (LinearMap.id : V →ₗ[ℚ_[l]] V)
      (((P.PD K).Fil a).restrictScalars ℚ_[l]).subtype y =
      AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (((P.PD K).Fil a).restrictScalars ℚ_[l]).subtype y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  ext x
  simp only [FilV, Submodule.restrictScalars_mem, LinearMap.mem_range, h]

variable [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] [ContinuousConstSMul ℚ_[l] V]

theorem mem_finiteCocycles_restrictScalars_Ql (c : ↥(GK K) → V) : c ∈ finiteCocycles (P.PD K) (resQ ρ) ↔ c ∈ finiteCocycles (P.PD K) ρ := by
  show (c ∈ continuousCocycles (resQ ρ) ∧ ∃ x, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) (resQ ρ) g x - x) ↔
    (c ∈ continuousCocycles ρ ∧ ∃ x, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) ρ g x - x)
  simp only [actVB_resQ]
  exact Iff.rfl

def finiteCocyclesResEquiv : ↥(finiteCocycles (P.PD K) (resQ ρ)) ≃ₗ[ℚ_[l]] ↥(finiteCocycles (P.PD K) ρ) where
  toFun x := ⟨x.1, (mem_finiteCocycles_restrictScalars_Ql P ρ x.1).mp x.2⟩
  invFun x := ⟨x.1, (mem_finiteCocycles_restrictScalars_Ql P ρ x.1).mpr x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def h1fEquiv : FiniteCohomology (P.PD K) (resQ ρ) ≃ₗ[ℚ_[l]] FiniteCohomology (P.PD K) ρ :=
  (Submodule.Quotient.equiv _ (((B1 ρ).comap (finiteCocycles (P.PD K) ρ).subtype).restrictScalars ℚ_[l]) (finiteCocyclesResEquiv P ρ) (by
    rw [Submodule.map_equiv_eq_comap_symm]
    ext x
    exact Iff.rfl)).trans (Submodule.Quotient.restrictScalarsEquiv ℚ_[l] _)

end Coeff

end GlobalTheory.BkCoeff

namespace GlobalTheory

open GlobalTheory.PstCoeff GlobalTheory.BkCoeff

theorem bkADim_of_dimFormula : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l),
    GlobalTheory.Published.BlochKato.DimFormula (P.PD K) → Formalism.MainNotions.LocalSituation.bkADim (P.PD K) := by
  intro l _ P K hD LL _ _ _ O _ _ hO A hdR
  obtain ⟨-, hfin, hmt, htr, -⟩ := hO
  haveI := hfin
  haveI := hmt
  haveI := htr
  haveI : FiniteDimensional ℚ_[l] A.V := Module.Finite.trans LL A.V
  haveI : IsModuleTopology ℚ_[l] A.V := isModuleTopology_of_tower ℚ_[l] LL A.V
  obtain ⟨-, he⟩ := hD A.V (resQ (LL := LL) A.ρ) A.cont ((isDR_resQ_iff P A.ρ).mpr hdR)
  have hH1 : finrank ℚ_[l] (FiniteCohomology (P.PD K) (resQ A.ρ)) = finrank ℚ_[l] LL * finrank LL (FiniteCohomology (P.PD K) A.ρ) := by
    rw [(h1fEquiv P A.ρ).finrank_eq, finrank_mul_finrank]
  have hH0 : finrank ℚ_[l] ↥(H0V (resQ A.ρ)) = finrank ℚ_[l] LL * finrank LL ↥(H0V A.ρ) := by
    rw [galoisInvariants_restrictScalarsToQl, finrank_mul_finrank]
    rfl
  have hdR' : finrank ℚ_[l] ↥(DdR (P.PD K) (resQ A.ρ)) = finrank ℚ_[l] LL * finrank LL ↥(DdR (P.PD K) A.ρ) := by
    rw [DdR_resQ, finrank_mul_finrank]
    rfl
  have hF : finrank ℚ_[l] ↥(DdR (P.PD K) (resQ A.ρ) ⊓ FilV (P.PD K) (LL := ℚ_[l]) (V := A.V) 0) =
      finrank ℚ_[l] LL * finrank LL ↥(DdR (P.PD K) A.ρ ⊓ FilV (P.PD K) (LL := LL) (V := A.V) 0) := by
    rw [DdR_resQ, FilV_resQ P (LL := LL), ← Submodule.restrictScalars_inf, finrank_mul_finrank]
    rfl
  rw [hH1, hH0, hdR', hF] at he
  push_cast at he
  have hd : (finrank ℚ_[l] LL : ℤ) ≠ 0 := by exact_mod_cast (Module.finrank_pos (R := ℚ_[l]) (M := LL)).ne'
  refine mul_left_cancel₀ hd ?_
  rw [he]
  ring

end GlobalTheory
