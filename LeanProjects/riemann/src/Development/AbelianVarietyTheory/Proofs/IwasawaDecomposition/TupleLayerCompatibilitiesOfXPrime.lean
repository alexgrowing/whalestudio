import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormLastCoordinateUniformizerVectorSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CevInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtMMulVecFix
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TuplePrimedSpaceClassesLevelAndComparisonStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsXTupleChainOfLevelReadingStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.Mem.Col2.TC.tupleLayer_compatibility : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (inQ : I.ι → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (T : Formalism.L2.Herm.TwChTied (I.rec7 l Z) inQ) (J : Formalism.L2.Herm.TwChJointS T H) (W : TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) T J F) (Lv : SymmetricTwistedLevelData W), (∀ a v, inQ a v ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → I.StdW l Z l0 W → I.StdLv l Z l0 Lv → (∀ u a (ha : a ≠ I.mu0) (h1 : 1 ≤ B.R.m), ∃ k, I.Reads u a B.R.m (T.chOf u a B.R.m) (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.Lb)
      (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.U) (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.chi)
      (fun c => ((W.ch u a ha B.R.m h1 le_rfl (T.chOf u a B.R.m c)).y ⟨c, rfl⟩).1)
      (fun c s => ((W.ch u a ha B.R.m h1 le_rfl (T.chOf u a B.R.m c)).stabI ⟨c, rfl⟩ s).1) k ∧
      ∀ β (d : XPt (B.primes X) B.R I.sel (I.tup a)) (g' : GA B (B.R.N B.R.m - 1)) (g : GA B (B.R.N B.R.m)), PtOf g' d →
        IsExt (I.rec7 l Z) (z0 X u) (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) g'.1 g.1 →
        PtOf (g * k β) (tilF I.sel (I.tup a) u d)) → ∃ (Pt : TwPTiedS Lv) (E : TwPEvzS Pt), TwPAtGS Pt ∧ I.StdP l Z l0 Pt E := by
  intro B X I hI hP l Z l0 inQ H F T J W Lv hQ hF hW hLv hTop
  have hQ' : ∀ a v, v ∈ T.Q a ↔ I.UnderQ a v := fun a v => (T.Q_iff a v).trans (hQ a v)
  have hC := fun u a => GlobalTheory.T.tuplePrimedSpaceClasses_level_and_comparison I hI hP l Z u a (T.Q a) (F u).clsP (hQ' a) (J.Q_off u a) (hF u).1.what₂
  choose K hLb hfin hrd hU hchi using hC
  have hV := fun u a => GlobalTheory.T.formsX_tupleChain_of_levelReading I hI hP l Z u a (T.Q a) (K u a) (hQ' a) (J.Q_off u a) (hrd u a)
  choose V hN hE using hV
  choose k hk hkT using hTop
  have hTil := fun u a ha h1 => GlobalTheory.Mem.Col2.TwP.til_tw I hI hP l Z hF hW hLv u a ha h1 (K u a) (hrd u a) (hk u a ha h1) (hkT u a ha h1)
  choose Tl hz hev using hTil
  choose jM hj0 hj1 hj2 hj3 hj4 using fun u a => GlobalTheory.Mem.Col2.PerConj.period_conj I hI hP l Z u a
  let Pt : TwPTiedS Lv :=
    { cls := fun u a _ => K u a
      Lb := fun u a _ => hLb u a
      chi_fin := fun u a _ => hfin u a
      val := fun u a _ => V u a
      norm := fun u a _ => hN u a
      til := fun u a ha h1 => Tl u a ha h1 }
  let E : TwPEvzS Pt :=
    { eWz := fun u a => LinearEquiv.refl ℂ _
      evz := fun u a ha h1 φ c s s' hs => hev u a ha h1 φ c s s' hs
      jM := jM
      per := fun u a _ => ⟨hj1 u a, hj2 u a, hj3 u a⟩ }
  refine ⟨Pt, E, ⟨fun u a _ v hv => hU u a v hv, fun u a _ κ κ' h h' => hchi u a κ κ' h h'⟩, ⟨fun u a _ => hrd u a, fun u a _ z c s s' h => hE u a z c s s' h, fun u a ha h1 => hz u a ha h1, fun u a z => rfl⟩⟩

end
