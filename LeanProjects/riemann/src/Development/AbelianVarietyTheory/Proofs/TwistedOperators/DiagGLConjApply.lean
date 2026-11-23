import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.SeeConjRead

open Classical

variable {D : D7}

def diagGL {κ : Type} [CommRing κ] {r : ℕ} (d : Fin r → κˣ) : GL (Fin r) κ :=
  Units.map (Matrix.diagonalRingHom (Fin r) κ).toMonoidHom (MulEquiv.piUnits.symm d)

theorem diagGL_val {κ : Type} [CommRing κ] {r : ℕ} (d : Fin r → κˣ) :
    ((diagGL d : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) = Matrix.diagonal fun i => (d i : κ) := rfl

def flagV {M : Type} [Zero M] (ρ k n : ℕ) (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin n) : M :=
  if h1 : i.1 < ρ then e ⟨i.1, h1⟩
  else if h2 : i.1 < ρ + k then b ⟨i.1 - ρ, by omega⟩
  else if h4 : i.1 = ρ + k then z
  else if h3 : i.1 < 2 * ρ + k + 1 then f ⟨2 * ρ + k - i.1, by omega⟩
  else 0

def e0T (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) :
    Fin D.R.rS → Fin (Yc D 0).rank → EAf D :=
  cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Fin D.R.rS → Formalism.L2.SG.HidaSetting.VA I) h) X.e0

def f0T (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) :
    Fin D.R.rS → Fin (Yc D 0).rank → EAf D :=
  cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Fin D.R.rS → Formalism.L2.SG.HidaSetting.VA I) h) X.f0

def z0T (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) :
    Fin (Yc D 0).rank → EAf D :=
  cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) h) X.z0

def bwT (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) :
    Fin D.R.k → Fin (Yc D 0).rank → EAf D :=
  cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Fin D.R.k → Formalism.L2.SG.HidaSetting.VA I) h) X.bw

def bwdT (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) :
    Fin D.R.k → Fin (Yc D 0).rank → EAf D :=
  cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Fin D.R.k → Formalism.L2.SG.HidaSetting.VA I) h) X.bwd

def ewT (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) : EAf D :=
  cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) h) X.ew

def flagAt (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E) :
    Fin (Yc D 0).rank → Fin (Yc D 0).rank → EAf D :=
  if GlobalTheory.StdFrames.cpt PP (ewT X h) = 1 then
    flagV D.R.rS D.R.k (Yc D 0).rank (e0T X h) (f0T X h) (bwT X h) (z0T X h)
  else flagV D.R.rS D.R.k (Yc D 0).rank (e0T X h) (f0T X h) (fun i => bwdT X h (Fin.rev i)) (z0T X h)

def RedIs {n : ℕ} (β : GL (Fin n) (EAf D)) (PP : Pl D.host.E) (w : Fin n → Fin n → EAf D) : Prop :=
  ∀ i j, ∃ hm : Matrix.mulVec (β⁻¹).val (w j) i ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E,
    Formalism.L2.DIV.resS D.host.F PP ⟨_, hm⟩ = if i = j then 1 else 0

end GlobalTheory.SeeConjRead

namespace GlobalTheory.SeeConjRead

theorem diagGL_inv {κ : Type} [CommRing κ] {r : ℕ} (d : Fin r → κˣ) : (diagGL d)⁻¹ = diagGL (fun i => (d i)⁻¹) := by
  unfold diagGL
  rw [← map_inv, ← map_inv]
  rfl

theorem diagGL_conj_apply {κ : Type} [CommRing κ] {r : ℕ} (d : Fin r → κˣ) (u : GL (Fin r) κ) (i j : Fin r) :
    (((diagGL d)⁻¹ * u * diagGL d : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) i j =
      (((d i)⁻¹ : κˣ) : κ) * (u : Matrix (Fin r) (Fin r) κ) i j * (d j : κ) := by
  rw [diagGL_inv, Units.val_mul, Units.val_mul, diagGL_val, diagGL_val, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem unipSym_conj_of {κ : Type} [CommRing κ] {r : ℕ} (ρ k : ℕ) (d : Fin r → κˣ) {u : GL (Fin r) κ}
    (hu : u ∈ unipSym κ r ρ k) : (diagGL d)⁻¹ * u * diagGL d ∈ unipSym κ r ρ k := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hu
  refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j a b c => ?_⟩
  · show (((diagGL d)⁻¹ * u * diagGL d : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) i j = 0
    rw [diagGL_conj_apply, h1 hij, mul_zero, zero_mul]
  · rw [diagGL_conj_apply, h2, mul_one, Units.inv_mul]
  · rw [diagGL_conj_apply, h3 i j a b c, mul_zero, zero_mul]

theorem unipSym_conj_iff {κ : Type} [CommRing κ] {r : ℕ} (ρ k : ℕ) (d : Fin r → κˣ) (u : GL (Fin r) κ) :
    u ∈ unipSym κ r ρ k ↔ (diagGL d)⁻¹ * u * diagGL d ∈ unipSym κ r ρ k := by
  refine ⟨unipSym_conj_of ρ k d, fun h => ?_⟩
  have h' := unipSym_conj_of ρ k (fun i => (d i)⁻¹) h
  rw [← diagGL_inv, inv_inv] at h'
  simpa [mul_assoc] using h'

end GlobalTheory.SeeConjRead
