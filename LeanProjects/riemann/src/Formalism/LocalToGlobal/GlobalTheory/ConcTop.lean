import Formalism.LocalToGlobal.GlobalTheory.GlobalReductionOfCompatibleFamily
import Formalism.LocalToGlobal.GlobalTheory.GL1.AdelicLatticeLinkFamily
import Formalism.SharpRestriction.SmoothDesignExistence.LinkGLOBALPk
import Formalism.LocalToGlobal.GlobalTheory.FamCol
import Formalism.LocalToGlobal.GlobalTheory.AnalyticConclusionOfProp25

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.ConcTop

section Part1

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions.Lnk Formalism.MainNotions.Pk Formalism.L2.GlobalTheoryTheory NumberField

def ObjSel (𝒞 : FamClass) := ∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → GlobalObjF Fm

def RowReal (𝒞 : FamClass) : Prop :=
  Closed 𝒞 fun Fm _ => ∀ x (i : Fm.Ix x), Formalism.L2.Theta.RealTied (Fm.D x i)

def RowCurveTies (𝒞 : FamClass) (O : ObjSel 𝒞) : Prop :=
  Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm, ∀ x (i : Fm.Ix x), CurveTies (Fm.D x i) ((O Fm hc).K x i)

def RowExtra (𝒞 : FamClass) (O : ObjSel 𝒞) : Prop :=
  Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm, ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
    Formalism.L2.Herm.ExtraTied ((O Fm hc).T x i).herm (Fm.ex x hx i)

def RowDataIn (𝒞 : FamClass) (O : ObjSel 𝒞) : Prop :=
  Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm, ∀ x (i : Fm.Ix x),
    TaylorLogMetric.DataIn (Fm.D x i) (TaylorLogMetric.tor0 (Fm.D x i) (Fm.D x i).host.ccK ((O Fm hc).K x i).δ) ((O Fm hc).K x i).M

def RowKRat (𝒞 : FamClass) : Prop :=
  Closed 𝒞 fun Fm _ => ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, flipTwoThree.adm7 (Fm.D x i)

def ThetaObjectClauses (𝒞 : FamClass) (O : ObjSel 𝒞) (C : ℝ) : Prop :=
  Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm, ∀ x (i : Fm.Ix x),
    Cl22 (Fm.D x i) C (Fm.D x i).host.ccK ((O Fm hc).K x i).δ ((O Fm hc).K x i).χ ((O Fm hc).K x i).e

def RowThPow (𝒞 : FamClass) (O : ObjSel 𝒞) : Prop :=
  Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm, ∀ x (i : Fm.Ix x),
    GL3Theta.thPow (Fm.D x i) (Fm.D x i).host.ccK ((O Fm hc).K x i).δ ((O Fm hc).K x i).e

def RowColVal (𝒞 : FamClass) : Prop :=
  Closed 𝒞 fun Fm _ => ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, flipTwoThree.adm3 (Fm.D x i) → ∀ u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u)

def RowAdm0 (𝒞 : FamClass) : Prop :=
  Closed 𝒞 fun Fm _ => ∀ x, Fm.x1 < x → ∀ (i : Fm.Ix x) u, product_first_zeroth_parts.UpDownIncidenceInverse (Fm.D x i) u

def RowAdmT (𝒞 : FamClass) : Prop :=
  Closed 𝒞 fun Fm _ => ∀ x, Fm.x1 < x → ∀ (i : Fm.Ix x) u, product_first_zeroth_parts.admT (Fm.D x i) u

def RowBr (𝒞 : FamClass) : Prop :=
  Closed 𝒞 fun Fm _ => ∀ x, Fm.x1 < x → ∀ (i : Fm.Ix x) u, ∃ P : product_first_zeroth_parts.Pend (Fm.D x i) u, product_first_zeroth_parts.ArchimedeanSignatureMatching P

def ClosedStandardLatticeFamilyAssumption (𝒞 : FamClass) : Prop := Closed 𝒞 fun Fm _ => StandardLattice.FamilyTheoremThreeAdmitted Fm

def ClosedThetaFamilyConstant (𝒞 : FamClass) (C22 : ℝ) : Prop := Closed 𝒞 fun Fm _ => TaylorLogMetric.StatementFamilyConstant Fm C22
def ClosedKudlaFamilyConstantFree (𝒞 : FamClass) : Prop := Closed 𝒞 fun Fm _ => flipTwoThree.KudlaFamilyStatement Fm
def ClosedKudlaFamilyStandardLattice (𝒞 : FamClass) (C3 : ℝ) : Prop := Closed 𝒞 fun Fm _ => StandardLattice.KudlaFamilyStatement Fm C3
def ClosedPacketCrystallineStatement (𝒞 : FamClass) (crystallineComparison : ℝ) : Prop := Closed 𝒞 fun Fm _ => product_first_zeroth_parts.KudlaFamilyStatement Fm crystallineComparison

def LinkClosed (𝒞 : FamClass) (Cabs C0 eL : ℝ) : Prop :=
  Closed 𝒞 fun Fm CH => Fm.CoverAll → TuSize Fm → DGamSize Fm → LinkGLOBAL Fm Cabs CH C0 Cabs eL

def ClosedCompatible (𝒞 : FamClass) (C22 : ℝ) : Prop := Closed 𝒞 fun Fm _ => GlobalTiedF Fm C22

def WithCompatibility (𝒞 : FamClass) (C22 : ℝ) : FamClass := fun Fm => 𝒞 Fm ∧ GlobalTiedF Fm C22

def objOfCompatible (𝒞 : FamClass) (C22 : ℝ) : ObjSel (WithCompatibility 𝒞 C22) := fun _ hc => Classical.choose hc.2

end Part1

section Part2

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LBr2 Formalism.LFunctionChainParameters.LBrDiv Formalism.LFunctionChainParameters.SectionsFourToSixTransfer Formalism.LFunctionChainParameters.LChain6
  Formalism.L2.GlobalTheoryTheory.MergeGL2

def ConcCoreAt (q d : ℕ) [Fact q.Prime] [Fact d.Prime] (A c' Cord eD eL K cHH eK eW KW ε x : ℝ) : Prop :=
  ∃ (e : ℕ) (Ω : Type) (_ : Fintype Ω)
    (W : Ω → HA e → Type) (_ : ∀ o u0, Fintype (W o u0)) (_ : ∀ o u0, Nonempty (W o u0)) (m : ℕ)
    (G : Glob) (C : Consts) (N : ℕ)
    (TT T2 : Finset (HA e)) (a : Ω → HA e → ℝ) (w : Ω → HA e → Fin m → E0 × HA e → ℝ)
    (Q : ∀ o u0, FamCol.Pt (W o u0)) (Rw : ∀ o u0, Formalism.LFunctionChainParameters.LChain6.Rows ((Q o u0).fam m))
    (O : ∀ o, Formalism.LFunctionChainParameters.LChain6.SizeCountLevelObjects (HA e) (W o) m TT)
    (Lp : HA e → Ω → LossP (HA e) m)
    (P : Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.Par) (π : Ω → ℝ) (s sB : Finset ℕ) (BAD : ℕ → HA e → Prop) (Sig : ℕ → Ω → ℝ) (η : ℝ)
    (g₁ g₂ : ℕ) (logOm C0 cZ cL cE5 c5 : ℝ),
    G.x = x ∧ G.ε = ε ∧ C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ C.cHH ≤ cHH ∧ P.e₂ = e ∧
    ((2 ^ e : ℕ) : ℝ) ≤ x ^ A ∧
    G.v = hostV e q d ∧ g₁.Prime ∧ g₂.Prime ∧ G.lg = Real.log ((g₁ : ℝ) * (g₂ : ℝ)) ∧
    PerHost e q d logOm ∧
    LossHyp (hostData e q d) G C N TT a w (fun o u0 => (Q o u0).fam m) Lp P π s sB BAD Sig Cord eW KW ∧
    ∀ o, 0 < π o →
      (∀ u0, (Q o u0).OkIn m (PhiSet (H := HA e)).card g₁ g₂ (XppH (HA e) G)) ∧
      FamCol.RemainingInputsAfter (hostData e q d) (hostEll e q d) G C N TT T2 (a o) (w o) (Q o) (Rw o) (O o) η
        (Real.exp (-c' * x ^ (ε / 8))) eK K logOm C0 cZ cL cE5 c5 g₁ g₂

def ConcreteMainReduction : Prop :=
  ∃ Cord c' : ℝ, 0 ≤ Cord ∧ 0 < c' ∧ ∀ eD eL ε₁ : ℝ, 0 < ε₁ →
    (∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ∃ A K cHH eK eW KW x₀ : ℝ, 0 < A ∧ ∀ x : ℝ, x₀ ≤ x →
        ∀ (_ : Fact (q1At ε x).Prime) (_ : Fact (dAt ε x).Prime),
          ConcCoreAt (q1At ε x) (dAt ε x) A c' Cord eD eL K cHH eK eW KW ε x) →
    RiemannHypothesis

end Part2

end Formalism.L2.GlobalTheoryTheory.ConcTop

end
