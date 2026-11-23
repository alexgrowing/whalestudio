import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteThetaLiftLocalVector
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameHeckeIntegralUnitsEqResidueCharProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SuppInd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory.AdjRedOff

theorem resS_idemSum_eq_zero {D : D7} {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (hI : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) {PP : Pl D.host.E} (hPP : PP ∉ P) :
    Formalism.L2.DIV.resS D.host.F PP ⟨toEAf D e, hI⟩ = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  choose hi _ using fun Q : P => GlobalTheory.IdemRes.resS_idem_eq_one D (es Q) Q (hes Q Q.2)
  let t : P → Formalism.L2.Herm.intAf D.host.F D.host.E := fun Q => ⟨toEAf D (es Q), hi Q⟩
  have e1 : (⟨toEAf D (∑ Q ∈ P, es Q), hI⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ∑ Q, t Q := by
    apply Subtype.ext
    change toEAf D (∑ Q ∈ P, es Q) = _
    rw [← Finset.sum_coe_sort P]
    refine (GlobalTheory.TameProd.map_sum_ringHom (toEAf D) _ _).trans ?_
    exact (map_sum (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype t Finset.univ).symm
  rw [e1, map_sum]
  refine Finset.sum_eq_zero fun Q _ => ?_
  exact GlobalTheory.TameProd.resS_idem_eq_zero (hes Q Q.2) (fun h => hPP (by rw [← h]; exact Q.2)) _

end GlobalTheory.AdjRedOff

theorem GlobalTheory.AdjRedOff.redM_frMapAdj_off : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → ∀ i t σ s P cμ cη m ω BW f₀ f c io, GlobalTheory.LiftRows.IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ e : AE D, IsIdemSum e (R.Pg ∪ R.Q t) → ∀ x : WO (Vc D i) (Wc D i), IsHalf (cA D e) x → IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) →
  ∀ PP : Pl D.host.E, PP ∉ R.Pg ∪ R.Q t → redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) = 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _ i t σ s P cμ cη m ω BW f₀ f c io _ e he x hx hint PP hPP
  obtain ⟨hI, -⟩ := GlobalTheory.TameProd.resS_idemSum he
  ext a b
  have hm := hint a b
  simp only [redM, dif_pos hm, Matrix.zero_apply]
  have e1 : (⟨frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x a b, hm⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
      ⟨toEAf D e, hI⟩ * ⟨frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x a b, hm⟩ :=
    Subtype.ext (GlobalTheory.AdjVecLocal.frMapAdj_half _ _ _ _ hx a b).symm
  rw [e1, map_mul, GlobalTheory.AdjRedOff.resS_idemSum_eq_zero he hI hPP, zero_mul]
