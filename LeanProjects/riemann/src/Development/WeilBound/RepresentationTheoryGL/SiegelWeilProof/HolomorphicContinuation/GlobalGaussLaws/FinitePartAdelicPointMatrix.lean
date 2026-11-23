import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawA
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRealPointUnitaryWithComponents

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Matrix
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocLawH

variable {D : D7} {n : ℕ}

def cf (θ : InfFam D) (τ : D.what₂.Tau) : AE D →+* ℂ := RingHom.comp (θ τ) (infPart D)

theorem compAt_eq_map {m k : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (X : Mx D m k) :
    compAt θ τ X = X.map (cf θ τ) := rfl

theorem compAt_mulM {m k l : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (X : Mx D m k) (Y : Mx D k l) :
    compAt θ τ (X * Y) = compAt θ τ X * compAt θ τ Y := by
  rw [compAt_eq_map, compAt_eq_map, compAt_eq_map]
  exact Matrix.map_mul

theorem compAt_one (θ : InfFam D) (τ : D.what₂.Tau) : compAt θ τ (1 : Mx D n n) = 1 := by
  rw [compAt_eq_map]
  exact Matrix.map_one (cf θ τ) (map_zero _) (map_one _)

theorem compAt_add {m k : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (X Y : Mx D m k) :
    compAt θ τ (X + Y) = compAt θ τ X + compAt θ τ Y := by
  rw [compAt_eq_map, compAt_eq_map, compAt_eq_map]
  exact Matrix.map_add (cf θ τ) (map_add (cf θ τ)) X Y

theorem ext_mx {m k : ℕ} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ) {X Y : Mx D m k}
    (hf : X.map (finPart D) = Y.map (finPart D)) (hc : ∀ τ, compAt θ τ X = compAt θ τ Y) : X = Y := by
  obtain ⟨-, -, -, -, hext⟩ := h
  refine Matrix.ext fun i j => ?_
  refine sub_eq_zero.mp (hext _ ?_ fun τ => ?_)
  · rw [map_sub, sub_eq_zero]
    exact congrFun (congrFun hf i) j
  · rw [map_sub, map_sub, sub_eq_zero]
    exact congrFun (congrFun (hc τ) i) j

def baseColumnsAt (σ : (D.what₂.Tau → ℂ) →+ AE D) (τ : D.what₂.Tau) (M : Matrix (Fin n) (Fin n) ℂ) : Mx D n n :=
  1 + atT σ τ (M - 1)

theorem component_adelic_point_matrix {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ) (τ : D.what₂.Tau)
    (M : Matrix (Fin n) (Fin n) ℂ) : compAt θ τ (baseColumnsAt σ τ M) = M := by
  show compAt θ τ (1 + atT σ τ (M - 1)) = M
  rw [compAt_add, compAt_one, compAt_atT h]
  abel

theorem component_adelic_point_ne {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ) {τ τ' : D.what₂.Tau}
    (hne : τ' ≠ τ) (M : Matrix (Fin n) (Fin n) ℂ) : compAt θ τ' (baseColumnsAt σ τ M) = 1 := by
  show compAt θ τ' (1 + atT σ τ (M - 1)) = 1
  rw [compAt_add, compAt_one, compAt_atT_ne h hne, add_zero]

theorem finite_part_adelic_point_matrix {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ) (τ : D.what₂.Tau)
    (M : Matrix (Fin n) (Fin n) ℂ) : (baseColumnsAt σ τ M).map (finPart D) = 1 := by
  show (1 + atT σ τ (M - 1)).map (finPart D) = 1
  rw [Matrix.map_add (finPart D) (map_add (finPart D)), Matrix.map_one (finPart D) (map_zero _) (map_one _),
    show (atT σ τ (M - 1)).map (finPart D) = 0 from Matrix.ext fun i j => finPart_atT h τ (M - 1) i j, add_zero]

theorem finPart_atT_map {m k : ℕ} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ)
    (τ : D.what₂.Tau) (M : Matrix (Fin m) (Fin k) ℂ) : (atT σ τ M).map (finPart D) = 0 := by
  exact Matrix.ext fun i j => finPart_atT h τ M i j

def unitAt {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ) (τ : D.what₂.Tau)
    (a : GL (Fin n) ℂ) : GL (Fin n) (AE D) where
  val := baseColumnsAt σ τ a.1
  inv := baseColumnsAt σ τ a⁻¹.1
  val_inv := ext_mx h (by rw [Matrix.map_mul, finite_part_adelic_point_matrix h, finite_part_adelic_point_matrix h, Matrix.one_mul, Matrix.map_one _ (map_zero _) (map_one _)])
    fun τ' => by
      by_cases e : τ' = τ
      · subst e; rw [compAt_mulM, component_adelic_point_matrix h, component_adelic_point_matrix h, compAt_one]; simp
      · rw [compAt_mulM, component_adelic_point_ne h e, component_adelic_point_ne h e, compAt_one, Matrix.one_mul]
  inv_val := ext_mx h (by rw [Matrix.map_mul, finite_part_adelic_point_matrix h, finite_part_adelic_point_matrix h, Matrix.one_mul, Matrix.map_one _ (map_zero _) (map_one _)])
    fun τ' => by
      by_cases e : τ' = τ
      · subst e; rw [compAt_mulM, component_adelic_point_matrix h, component_adelic_point_matrix h, compAt_one]; simp
      · rw [compAt_mulM, component_adelic_point_ne h e, component_adelic_point_ne h e, compAt_one, Matrix.one_mul]

theorem unitAt_val {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ) (τ : D.what₂.Tau)
    (a : GL (Fin n) ℂ) : (unitAt h τ a).1 = baseColumnsAt σ τ a.1 := rfl

end PositivityTheory.Rg.Sw.Glob.LocLawH
