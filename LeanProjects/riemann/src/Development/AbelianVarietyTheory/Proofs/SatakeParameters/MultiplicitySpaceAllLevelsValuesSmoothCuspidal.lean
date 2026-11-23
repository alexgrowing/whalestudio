import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacteristicFunctionIntegralApply
import Formalism.LocalToGlobal.IndefiniteReal.CompZeroOfOrth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct ComplexOrder
open Formalism.IndefR Formalism.IndefR.Mult Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.MinfCusp

theorem minf_val_autCusp : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : Formalism.BasicNotions.TH.HSp D}
    {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} {n : ℕ} (P : principalLevelFrame.RowPsi V n) (M : DSModel V S),
    ∀ T ∈ principalLevelFrame.Minf θ P M, ∀ v : M.Vec, IsAutFunSm θ V (T v) ∧ IsCuspFun V (T v) := by
  intro D θ V S n P M T hT v
  obtain ⟨N, hN⟩ := (principalLevelFrame.mem_Minf (θ := θ) (P := P) (M := M)).1 hT
  have h := (GlobalTheory.MultMem.mem_mult_iff D θ V S M _ _ T).1 hN
  exact ⟨h.aut v, h.cusp v⟩

end GlobalTheory.MinfCusp
