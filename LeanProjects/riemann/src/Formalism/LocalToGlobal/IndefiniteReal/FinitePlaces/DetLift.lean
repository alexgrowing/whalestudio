import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.DetLiftA
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.InjectiveDecompositionAction Formalism.IndefR.Fin.U1
  MeasureTheory IsDedekindDomain NumberField Topology

namespace Formalism.IndefR.Fin.DL

set_option synthInstance.maxHeartbeats 80000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def cUD (D : D7) : (AE D)ˣ →* (AE D)ˣ := Units.map (cA D).toMonoidHom

@[simp] theorem cUD_val (x : (AE D)ˣ) : ((cUD D x : (AE D)ˣ) : AE D) = cA D (x : AE D) := rfl

def hq (D : D7) : (AE D)ˣ →* (AE D)ˣ := MonoidHom.id _ / cUD D

theorem hq_apply (x : (AE D)ˣ) : hq D x = x / cUD D x := rfl

section Inv

variable (δ : D.host.E) (hδ : D.sp.cm.sig δ = -δ) (hδ0 : δ ≠ 0)

include hδ hδ0 in
theorem cA_cA (y : AE D) : cA D (cA D y) = y := by
  rw [← pt_co δ hδ hδ0 y, cA_pt δ hδ, cA_pt δ hδ, neg_neg]

end Inv

theorem cA_cA' (y : AE D) : cA D (cA D y) = y := by
  obtain ⟨δ, hδ, hδ0⟩ := exists_delta_D D
  exact cA_cA δ hδ hδ0 y

theorem cUD_cUD' (x : (AE D)ˣ) : cUD D (cUD D x) = x := Units.ext (cA_cA' _)

theorem hq_mem (x : (AE D)ˣ) : hq D x ∈ FirstPropositionFrame D := by
  have h : hq D x * cUD D (hq D x) = 1 := by
    rw [hq_apply, map_div, cUD_cUD', div_mul_div_cancel, div_self']
  show ((hq D x : (AE D)ˣ) : AE D) * cA D ((hq D x : (AE D)ˣ) : AE D) = 1
  have := congrArg (fun z : (AE D)ˣ => (z : AE D)) h
  simpa using this

def phiU (D : D7) : (AE D)ˣ →* FirstPropositionFrame D := (hq D).codRestrict (FirstPropositionFrame D) hq_mem

section Coord

variable (δ : D.host.E) (hδ : D.sp.cm.sig δ = -δ) (hδ0 : δ ≠ 0) (Δ : D.host.F)
  (hΔ : algebraMap D.host.F D.host.E Δ = δ * δ)

end Coord

theorem detU_mem (V : HSp D) (g : GA D V) : Matrix.GeneralLinearGroup.det (matHom V g) ∈ FirstPropositionFrame D := by
  show ((Matrix.GeneralLinearGroup.det (matHom V g) : (AE D)ˣ) : AE D) *
    cA D ((Matrix.GeneralLinearGroup.det (matHom V g) : (AE D)ˣ) : AE D) = 1
  rw [Matrix.GeneralLinearGroup.val_det_apply, mul_comm]
  exact det_conj_mul V g

def detU (V : HSp D) : GA D V →* FirstPropositionFrame D :=
  (Matrix.GeneralLinearGroup.det.comp (matHom V)).codRestrict (FirstPropositionFrame D) (detU_mem V)

end Formalism.IndefR.Fin.DL

namespace Formalism.IndefR.Fin

open Formalism.IndefR.Fin.DL

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

end Formalism.IndefR.Fin

end
