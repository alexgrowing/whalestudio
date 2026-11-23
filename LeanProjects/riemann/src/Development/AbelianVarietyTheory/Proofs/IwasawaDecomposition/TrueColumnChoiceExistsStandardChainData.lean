import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChoiceExistsChainDataWithBasePointsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleChainsLevelStructureCompatibleAtLevelPrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleLayerCompatibilitiesOfXPrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SubOneMemMapOfEq

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem underQ_iff {B : Base} {X : PreX B.toPre} {I : TC B X} (hI : I.Ok) (a : I.ι) (v : HeightOneSpectrum (𝓞 B.host.F)) :
    I.UnderQ a v ↔ ∃ w ∈ Formalism.L2.Host.aboveF (L := B.host.E) B.host.F v, ¬ (I.xi a).UnrAt w := by
  have hq := GlobalTheory.Mem.ReadTwist.mem_qprime_iff (hI.xi_reads a) v
  have hab : ∀ w : HeightOneSpectrum (𝓞 B.host.E), w ∈ Formalism.L2.Host.aboveF (L := B.host.E) B.host.F v ↔ w.under (𝓞 B.host.F) = v := fun w => by
    unfold Formalism.L2.Host.aboveF
    rw [Set.Finite.mem_toFinset]
    rfl
  constructor
  · rintro ⟨P, hP, rfl⟩
    obtain ⟨w, hw, hu⟩ := hq.1 ((GlobalTheory.TwistPlaces.mem_QE_iff hI.sel_ok (I.tup a)).1 hP).1
    exact ⟨w, (hab w).2 hw, hu⟩
  · rintro ⟨w, hw, hu⟩
    have hv := hq.2 ⟨w, (hab w).1 hw, hu⟩
    exact ⟨I.sel v, (Formalism.L2.Col.mem_QE I.sel (I.tup a) _).2 ⟨v, hv, rfl⟩, GlobalTheory.TwistPlaces.under_eq_iff.2 (hI.sel_ok v)⟩

theorem carH_of_cols {D : D7} (C : ColsTiedSym D) : CarH C.herm.base C.forms where
  eV := C.eV
  fv u v a := by
    rw [C.res u]
    exact (C.herm.atT u).res_F v a
  car0 := C.car0
  carC := C.carC
  carM := C.carM
  sp := C.sp
  fr0 := C.fr0

theorem colsTwPTiedS_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (nch : NChoice (I.rec7 l Z)) (tp : Formalism.L2.Host.TupTied (I.rec7 l Z) (I.cf l Z) nch) (C : ColsTiedSym (I.rec7 l Z)), tp.xi = I.xi → I.StdC l Z C → (∀ u, I.StdLvC l Z u (C.forms u)) → ∃ t : SymmetricTwistedColumnsAtPrimes tp C (I.tw l l0 Z), I.StdTw l Z l0 t := by
  intro B X I hI hP l Z l0 nch tp C hxi hC hLv
  have hQ : ∀ a v, tp.InQ' a v ↔ I.UnderQ a v := fun a v => by
    rw [underQ_iff hI a v]
    unfold Formalism.L2.Host.TupTied.InQ'
    rw [hxi]
    exact Iff.rfl
  have hF : ∀ u, I.StdF l Z u (C.forms u) ∧ I.StdLvC l Z u (C.forms u) := fun u => ⟨hC u, hLv u⟩
  obtain ⟨T, J, W, hM, hW, ⟨lvJ⟩, hPt⟩ := GlobalTheory.T.trueColumnChoice_exists_chainData_with_basePoints I hI hP l Z l0 (fun a v => tp.InQ' a v) C.herm.base C.forms hQ hF (carH_of_cols C)
  obtain ⟨⟨Lv, hL⟩, ⟨same⟩⟩ := GlobalTheory.T.tupleChains_levelStructure_compatible_at_levelPrime I hI hP l Z l0 (fun a v => tp.InQ' a v) C.herm.base C.forms T J W hF hW
  obtain ⟨Pt, E, hG, hS⟩ := GlobalTheory.T.tupleLayerCompatibilities_of_X_prime I hI hP l Z l0 (fun a v => tp.InQ' a v) C.herm.base C.forms T J W Lv hQ hF hW hL hPt
  exact ⟨{ ch := T, chJ := J, chM := hM, forms := W, lv := Lv, same := same, lvJ := lvJ, pt := Pt, ptG := hG, ptE := E }, hW, hL, hS⟩

end GlobalTheory.Mem.Col2.TC

end
