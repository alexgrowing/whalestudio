import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.HaarFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMulRight

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwMatch

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.SiegelND

variable {D : D7} {n : ℕ}

theorem trPair_eq_halfTr (S T : Mx D n n) :
    PositivityTheory.PfSWUS.Loc.trPair (AF D.host.F) S T = halfTr (Matrix.trace (HMul.hMul S T : Mx D n n)) := rfl

theorem gramR_tupInv (V : HSp D) (y : Mx D V.rank n) :
    HeckeCharacterZeroLocus.SiegelWeilU.gramR (AF D.host.F) D.sp.cm.sig (HSpace.gram V) (tupInv y) = GlobalTheory.StdUnn.inner V y y := by
  ext a c
  exact hR_tup V y y a c

theorem inner_mul_right (V : HSp D) (y : Mx D V.rank n) (a : Mx D n n) :
    GlobalTheory.StdUnn.inner V (HMul.hMul y a : Mx D V.rank n) (HMul.hMul y a : Mx D V.rank n) =
      adj a * GlobalTheory.StdUnn.inner V y y * a := by
  unfold GlobalTheory.StdUnn.inner
  rw [adj_mul]
  simp only [Matrix.mul_assoc]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem jt_conj (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n))
    (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕) (a : GL (Fin n) (AE D)) (φ : Mx D V.rank n → ℂ) (c : hermA D n) :
    PositivityTheory.PfSWUS.Loc.jtR (AF D.host.F) D.sp.cm.sig (HSpace.gram V) ψ (μ.map tupInv)
        (fun X => φ (HMul.hMul (tupOf X) a.1)) (hermTo (conjH a c)) =
      npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(V.rank : ℂ)) * Jt ψ V μ φ c := by
  obtain ⟨k1, -, -, -, -, -⟩ := lattice_Mx D V.rank n
  have : IsTopologicalAddGroup (Mx D V.rank n) := k1
  have : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  have : BorelSpace (Fin n → Fin V.rank → AE D) := borel_tup
  obtain ⟨j1, -⟩ := Formalism.IndefR.Eqv.ae_facts D
  unfold Jt
  rw [← GlobalTheory.RightMulJac.integral_mul_right D V.rank n μ 𝓕 hμ a]
  refine (integral_map_of tupInv tupOf tupOf_tupInv tupInv_tupOf tupInv_add continuous_tupInv continuous_tupOf μ
    (fun Y => φ (HMul.hMul (tupOf Y) a.1) * ψ (PositivityTheory.PfSWUS.Loc.trPair (AF D.host.F) (conjH a c).1
      (HeckeCharacterZeroLocus.SiegelWeilU.gramR (AF D.host.F) D.sp.cm.sig (HSpace.gram V) Y)))).trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change φ (HMul.hMul y a.1) * ψ (PositivityTheory.PfSWUS.Loc.trPair (AF D.host.F) (conjH a c).1
      (HeckeCharacterZeroLocus.SiegelWeilU.gramR (AF D.host.F) D.sp.cm.sig (HSpace.gram V) (tupInv y))) =
    φ (HMul.hMul y a.1) * ψ (halfTr (Matrix.trace (HMul.hMul c.1
      (GlobalTheory.StdUnn.inner V (HMul.hMul y a.1 : Mx D V.rank n) (HMul.hMul y a.1 : Mx D V.rank n)) : Mx D n n)))
  rw [gramR_tupInv, trPair_eq_halfTr, inner_mul_right]
  have e : Matrix.trace (a.1 * c.1 * adj a.1 * GlobalTheory.StdUnn.inner V y y) =
      Matrix.trace (c.1 * (adj a.1 * GlobalTheory.StdUnn.inner V y y * a.1)) := by
    rw [← Matrix.mul_assoc c.1, Matrix.trace_mul_comm _ a.1]
    simp only [Matrix.mul_assoc]
  exact congrArg (fun z => φ (HMul.hMul y a.1) * ψ (halfTr z)) e

theorem char_conj (ψ : AddChar (AF D.host.F) ℂ) (β : HermE D n) (a : GL (Fin n) (AE D)) (c : hermA D n) :
    ψ (-PositivityTheory.PfSWUS.Loc.trPair (AF D.host.F) (β.1.map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF D.host.F))) (hermTo (conjH a c)).1) =
      ψ (-halfTr (Matrix.trace (HMul.hMul (adj a.1 * β.1.map (incA D) * a.1) c.1 : Mx D n n))) := by
  have e : Matrix.trace (β.1.map (incA D) * (a.1 * c.1 * adj a.1)) =
      Matrix.trace (adj a.1 * β.1.map (incA D) * a.1 * c.1) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm _ (adj a.1)]
    simp only [Matrix.mul_assoc]
  exact congrArg (fun z => ψ (-z))
    ((trPair_eq_halfTr (D := D) (β.1.map (incA D)) (a.1 * c.1 * adj a.1)).trans (congrArg halfTr e))

end PositivityTheory.PfSWUS.SwMatch

end
