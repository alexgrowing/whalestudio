import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjChar

open Classical GlobalTheory.SeeConjRead

variable {D : D7}

def resT (PP : Pl D.host.E) (x : EAf D) : kP PP :=
  if hx : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E then Formalism.L2.DIV.resS D.host.F PP ⟨x, hx⟩ else 0

def hT (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (x y : Fin (Yc D 0).rank → EAf D) : EAf D :=
  cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) h)
    (Formalism.L2.SG.HidaSetting.hA X.B.I (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) h.symm) x)
      (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) h.symm) y))

def argT (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (M : GL (Fin (Yc D 0).rank) (EAf D)) : EAf D :=
  (∑ a, hT X h (f0T X h a) (Matrix.mulVec M.val (Formalism.L2.SG.HidaSetting.nxt (e0T X h) (z0T X h) a))) +
    ∑ i : Fin D.R.k, if hi : i.1 + 1 < D.R.k then
      hT X h (bwdT X h i) (Matrix.mulVec M.val (bwT X h ⟨i.1 + 1, hi⟩)) else 0

def sideAt (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E) : Bool :=
  decide (GlobalTheory.StdFrames.cpt PP (ewT X h) = 1)

def wA (ρ k : ℕ) (s : Bool) {r : ℕ} (i _j : Fin r) : ℤ :=
  if i.1 < ρ then 1 else if i.1 + 1 < ρ + k then (if s then 1 else 0) else 0

def wB (ρ k : ℕ) (s : Bool) {r : ℕ} (i _j : Fin r) : ℤ :=
  if i.1 < ρ then 0 else if i.1 + 1 < ρ + k then (if s then 0 else -1) else if i.1 = ρ + k then 1 else -1

theorem conjPrime_asIdeal (PP : Pl D.host.E) :
    (GlobalTheory.IdemSupport.cP PP).asIdeal = PP.asIdeal.map (GlobalTheory.IdemSupport.cO D) := by
  ext x
  rw [GlobalTheory.IdemSupport.mem_cP, Ideal.mem_map_of_equiv]
  constructor
  · intro hx
    exact ⟨GlobalTheory.IdemSupport.cO D x, hx, GlobalTheory.IdemSupport.cO_cO x⟩
  · rintro ⟨y, hy, rfl⟩
    rw [GlobalTheory.IdemSupport.cO_cO]
    exact hy

def conjRes (PP : Pl D.host.E) : kP PP ≃+* kP (GlobalTheory.IdemSupport.cP PP) :=
  Ideal.quotientEquiv _ _ (GlobalTheory.IdemSupport.cO D) (conjPrime_asIdeal PP)

end GlobalTheory.SeeConjChar
