import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatMMemOfLeHalf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaDataLevelForms
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwistResidue

open Formalism.IndefR.Datum

variable {D : D7}

set_option maxHeartbeats 800000 in

theorem isRes_of_chrEq : ∀ (D : D7) (δ : GlobalTheory.ExportSeries.Twist D Circle), δ.Good → ∀ (χ : Formalism.L2.Host.HChar D.host.E),
    ChrEq δ.chi χ → ∀ P ∈ δ.Q, IsRes χ P (δ.resC P) := by
  intro D δ hδ χ hχ P hP a k u hka hu
  have h := hδ.split.isIdemAt hP
  have he : GlobalTheory.ExportSeries.idemAt P * GlobalTheory.ExportSeries.idemAt P = GlobalTheory.ExportSeries.idemAt P := h.1.1
  have e1 := hχ.2 P _ (by obtain ⟨⟨g1, g2, v, ε, hv, hs⟩, g3⟩ := h; exact ⟨g1, ⟨v, ε, hv, Or.inl ⟨g2, hs⟩⟩, g3⟩) k (locU he k) (locU_val he k)
  obtain ⟨hi, h1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D _ P h
  have hb : toEAf D (incA D (k : D.host.E)) = ((oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
    rw [hka]; rfl
  have hx0 : ((locU he k : (AE D)ˣ) : AE D) = 1 + GlobalTheory.ExportSeries.idemAt P * (incA D (k : D.host.E) - 1) := rfl
  have hv : toEAf D ((locU he k : (AE D)ˣ) : AE D) =
      ((1 + ⟨_, hi⟩ * (oToS D.host.F D.host.E a - 1) : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
    rw [hx0, GlobalTheory.ConjTwist.map_loc, hb]
    rfl
  have hx : toEAf D ((locU he k : (AE D)ˣ) : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [hv]
    exact Subtype.property _
  have hoff : (1 - GlobalTheory.ExportSeries.idemAt P) * ((locU he k : (AE D)ˣ) : AE D) = 1 - GlobalTheory.ExportSeries.idemAt P := by
    rw [hx0]
    linear_combination (1 - incA D (k : D.host.E)) * he
  have hres : resS D.host.F P ⟨_, hx⟩ = u := by
    have e2 : (⟨_, hx⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = 1 + ⟨_, hi⟩ * (oToS D.host.F D.host.E a - 1) :=
      Subtype.ext hv
    refine (congrArg (resS D.host.F P) e2).trans ?_
    rw [GlobalTheory.ConjTwist.map_loc, h1, resS_oToS, hu]
    ring
  have e3 := hδ.res P hP _ hoff hx u hres
  refine Units.ext ?_
  rw [← e1, e3]
  rfl

end GlobalTheory.TwistResidue
