import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetInd
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.WS.Comp

theorem rowAct_rowAct {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    (h k : GL (Fin 2) F) (v : F × F) :
    GlobalTheory.CompanionTheory.WS.rowAct h (GlobalTheory.CompanionTheory.WS.rowAct k v) = GlobalTheory.CompanionTheory.WS.rowAct (k * h) v := by
  ext <;>
    simp only [GlobalTheory.CompanionTheory.WS.rowAct, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem rowAct_one {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (v : F × F) :
    GlobalTheory.CompanionTheory.WS.rowAct (1 : GL (Fin 2) F) v = v := by
  ext <;> simp [GlobalTheory.CompanionTheory.WS.rowAct]

theorem continuous_rowAct {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (g : GL (Fin 2) F) :
    Continuous (GlobalTheory.CompanionTheory.WS.rowAct g) := by
  unfold GlobalTheory.CompanionTheory.WS.rowAct
  fun_prop

def rowActHomeo {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (g : GL (Fin 2) F) :
    (F × F) ≃ₜ (F × F) where
  toFun := GlobalTheory.CompanionTheory.WS.rowAct g
  invFun := GlobalTheory.CompanionTheory.WS.rowAct g⁻¹
  left_inv v := by rw [rowAct_rowAct, mul_inv_cancel, rowAct_one]
  right_inv v := by rw [rowAct_rowAct, inv_mul_cancel, rowAct_one]
  continuous_toFun := continuous_rowAct g
  continuous_invFun := continuous_rowAct g⁻¹

theorem isSB_comp_rowAct : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (Ψ : F × F → ℂ),
    GlobalTheory.CompanionTheory.WS.IsSB Ψ → ∀ g : GL (Fin 2) F, GlobalTheory.CompanionTheory.WS.IsSB (Ψ ∘ GlobalTheory.CompanionTheory.WS.rowAct g) := by
  intro F _ _ _ _ _ _ Ψ hΨ g
  exact ⟨hΨ.1.comp_continuous (continuous_rowAct g),
    hΨ.2.comp_homeomorph (rowActHomeo g)⟩

end GlobalTheory.CompanionTheory.WS.Comp
