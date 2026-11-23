import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.TiedTwJSym
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStandardFormComparisonSymmetricLevelMemberStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianColumnChoicesOfFormsLevelsClassesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianDataAtLevelPrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianColumnsGeneratorsBaseLatticesFunctionalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdditiveCharacterTypePrimesValuesCoefficientFielStatement
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.ChiMemSubfield
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroHermitianLevelUniformiserKillsValuesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

set_option maxHeartbeats 4000000 in

theorem colsTiedSym_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)),
    ∃ C : ColsTiedSym (I.rec7 l Z), I.StdC l Z C ∧ ∀ u, I.StdLvC l Z u (C.forms u) := by
  intro B X I hOk hP l Z
  obtain ⟨Ch, chOf, F, hF, hfin, hm, hgl, hchi⟩ := GlobalTheory.T.exists_standardFormComparison_symmetricLevel_members I hOk hP l Z
  obtain ⟨lev00, lev, cls, vT, Fv, hH0⟩ := GlobalTheory.T.hermitianColumnChoices_of_formsLevelsClasses I hOk hP l Z Ch chOf F hfin hm (fun u => (hF u).1)
  choose lev0 hLb hUl hU hy hst hsp hfrG hpi using fun u => GlobalTheory.T.stepZeroHermitianLevel_uniformiser_kills_values_alt I hOk hP l Z u (F u) (hF u).1 (lev00 u) (hH0.car0 u)
  let H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z) :=
    { lev0 := lev0, Ch := Ch, ChFin := hfin, Ch_m := hm, chOf := chOf, lev := lev, cls := cls, vT := vT, Fv := Fv }
  have hH : CarH H F :=
    { eV := hH0.eV, fv := hH0.fv
      car0 := fun u => by
        show SameCar _ (lev0 u).Lb _ (lev0 u).Uloc _ (lev0 u).U _ (fun c => ((lev0 u).y c).1) _ (fun c s => ((lev0 u).stabI c s).1) _
        rw [hLb u, hUl u, hU u, hy u, hst u]; exact hH0.car0 u
      carC := hH0.carC, carM := hH0.carM
      sp := fun u => by show _ = (lev0 u).splitG; rw [hsp u]; exact hH0.sp u
      fr0 := fun u => by show ∀ i v h, _ = reGL _ _ ((lev0 u).frG i v h); rw [hfrG u]; exact hH0.fr0 u }
  obtain ⟨A, hT, hAd, hSt⟩ := GlobalTheory.T.exists_hermitian_data_carT_of_std I hOk hP l Z H F hF hH
  obtain ⟨hCof, hBase, ⟨hFv⟩, X0, hX0⟩ := GlobalTheory.T.hermitianColumns_generators_baseLattices_functionals I hOk hP l Z H F A hF hH hT
    (fun u w h a ha m => hpi u w h a (by rw [ha, hT.piU u]) m)
  have hStd := (GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hP l Z).1
  have hpiG : ∀ u u', (X0 u).piG = (X0 u').piG := fun u u' => by rw [hX0 u, hX0 u']
  have hpiG' : ∀ u, (F u).gl.piG = (X0 u).piG := fun u => by rw [hX0 u]; exact ((hF u).1.gl).piG
  have hfr0 : ∀ u u', (F u).glev0.fr = (F u').glev0.fr := fun u u' => by
    funext j v h
    rw [(hF u).1.fr0, (hF u').1.fr0]
  have hfrP : ∀ u u', (F u).glevP.fr = (F u').glevP.fr := fun u u' => by
    funext j v h
    rw [(hF u).1.frP, (hF u').1.frP]
  refine ⟨
    { herm :=
        { base := H, atT := A, levelZeroCompatibility := X0, ad := hAd, cof := hCof, piG := hpiG,
          stabMap := hSt, fvI := hFv, std := hStd, baseL := hBase }
      forms := F
      eV := hH.eV
      piU := hT.piU
      res := hT.res
      car0 := hH.car0
      carC := hH.carC
      carM := hH.carM
      carP := hT.carP
      lattice₂ := hT.lattice₂
      pr := hT.pr
      prk := hT.prk
      prC := hT.prC
      z0 := hT.z0
      ga := hT.ga
      sp := hH.sp
      piG := hpiG'
      fr0 := hH.fr0
      gl_const := hgl
      chi := hchi
      frame_level_zero_const := hfr0
      frP_const := hfrP }, fun u => (hF u).1, fun u => (hF u).2⟩

end GlobalTheory.Mem.Col2.TC
