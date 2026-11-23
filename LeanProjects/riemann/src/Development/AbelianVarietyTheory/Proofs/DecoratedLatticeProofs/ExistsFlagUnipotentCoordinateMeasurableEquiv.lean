import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomeomorphWittFlagCoordinatesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.Unf

def coordFlip (D : D7) (ρ m : ℕ) : skewA D ρ × (Mx D ρ m × UX D ρ) ≃ₜ UX D ρ × (Mx D ρ m × skewA D ρ) :=
  haveI : IsTopologicalAddGroup (Mx D ρ m) := (lattice_Mx D ρ m).1
  haveI : IsTopologicalAddGroup (Mx D ρ ρ) := (lattice_Mx D ρ ρ).1
  { toFun := fun p => (p.2.2⁻¹, (-p.2.1, -p.1))
    invFun := fun q => (-q.2.2, (-q.2.1, q.1⁻¹))
    left_inv := fun p => Prod.ext (neg_neg _) (Prod.ext (neg_neg _) (inv_inv _))
    right_inv := fun q => Prod.ext (inv_inv _) (Prod.ext (neg_neg _) (neg_neg _))
    continuous_toFun := continuous_snd.snd.inv.prodMk (continuous_snd.fst.neg.prodMk continuous_fst.neg)
    continuous_invFun := continuous_snd.snd.neg.prodMk (continuous_snd.fst.neg.prodMk continuous_fst.inv) }

theorem coordFlip_apply (D : D7) (ρ m : ℕ) (p : skewA D ρ × (Mx D ρ m × UX D ρ)) :
    coordFlip D ρ m p = (p.2.2⁻¹, (-p.2.1, -p.1)) := rfl

end GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem flagCoord_measEquiv : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ),
    ∃ e : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ) ≃ᵐ flagN d,
      ∀ p, (e p : GA D V) = d.nC p.1 * (d.nB p.2.1 * d.levi p.2.2.1) := by
  intro D V V₀ ρ d
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_homeomorph_wittFlagCoordinates D V V₀ ρ d
  haveI : SecondCountableTopology (Mx D ρ V₀.rank) := (lattice_Mx D ρ V₀.rank).2.2.1
  haveI : SecondCountableTopology (Mx D ρ ρ) := (lattice_Mx D ρ ρ).2.2.1
  haveI : SecondCountableTopology (UX D ρ) := (GlobalTheory.UnitU.topology D ρ).2.1
  haveI : BorelSpace (Mx D ρ V₀.rank) := ⟨rfl⟩
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  haveI : BorelSpace (skewA D ρ) := Subtype.borelSpace _
  haveI : SecondCountableTopology (skewA D ρ) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  refine ⟨((coordFlip D ρ V₀.rank).trans (Φ.trans (Homeomorph.inv (flagN d)))).toMeasurableEquiv, fun p => ?_⟩
  change (((Φ (coordFlip D ρ V₀.rank p))⁻¹ : flagN d) : GA D V) = _
  rw [Subgroup.coe_inv, hΦ, coordFlip_apply]
  change (d.levi ((p.2.2⁻¹ : UX D ρ) : GL (Fin ρ) (AE D)) * (d.nB (-p.2.1) * d.nC (-p.1)))⁻¹ = _
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, d.nB_inv, d.nC_inv, neg_neg, neg_neg, Subgroup.coe_inv, map_inv, inv_inv,
    mul_assoc]

end GlobalTheory.Unf

end
