import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelPlacesNotIsConjPlaceRealDat
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section
namespace GlobalTheory.SeeConjGroup

open Classical Formalism.L2.SG.HidaSetting

abbrev II (D : D7) : AutInst := Formalism.L2.SG.InstExistsPf.instOf D

section Red
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def redV (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Pl E) (v : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) : Fin n → kP PP :=
  fun i => if h : ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _).mulVec v i ∈
      Formalism.L2.Herm.intAf F E then resS F PP ⟨_, h⟩ else 0

end Red

def basisOrRevDual {M : Type} {k : ℕ} (w : Bool) (b bd : Fin k → M) : Fin k → M := if w then b else fun i => bd (Fin.rev i)

def dualOrRevBasis {M : Type} {k : ℕ} (w : Bool) (b bd : Fin k → M) : Fin k → M := if w then bd else fun i => b (Fin.rev i)

def LocAt {D : D7} (g : ℕ) (e0 f0 : Fin D.R.rS → VA (II D)) (z0 : VA (II D)) (bw bwd : Fin D.R.k → VA (II D))
    (ew : EAf D) (β : GL (Fin (Yc D 0).rank) (EAf D)) (PP : Pl D.host.E) (w : Bool) : Prop :=
  ((g : 𝓞 D.host.E) ∈ PP.asIdeal) ∧
    (∀ h1 : ew ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, resS D.host.F PP ⟨ew, h1⟩ = if w then 1 else 0) ∧
    (∀ h1 : sigA (II D) ew ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      resS D.host.F PP ⟨sigA (II D) ew, h1⟩ = if w then 0 else 1) ∧
    RedIs β PP (flagV D.R.rS D.R.k (Yc D 0).rank e0 f0 (basisOrRevDual w bw bwd) z0)

end GlobalTheory.SeeConjGroup
