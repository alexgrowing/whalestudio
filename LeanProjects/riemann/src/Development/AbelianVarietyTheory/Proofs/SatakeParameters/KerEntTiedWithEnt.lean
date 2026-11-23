import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetIdStdBot
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

theorem kerEntTied_withEnt {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
    {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX}
    (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (E : KerEnt (I.rec7 l Z) Y ex.tw)
    (hE : EntOk E O) (hS : ∀ u w h, ThAtServed (ex.ker u w h) E)
    (t : KerEntTied ex) (ht : I.StdKerTie l Z t) (hO : t.O = O) (hTop : t.TopPinned) :
    ∃ t' : KerEntTied ex, I.StdKerTie l Z t' ∧ t'.O = O ∧ t'.ent = E ∧ t'.Adapted ∧ t'.TopPinned := by
  obtain ⟨⟨kf, kf_un⟩, hAd⟩ := hE
  subst hO
  refine ⟨{ t with ent := E, ent_lam := fun u w h => (hS u w h).1, kf := kf, kf_un := kf_un, served := hS },
    ?_, rfl, rfl, hAd, hTop⟩
  exact { X_eq := ht.X_eq, seam := ht.seam, Pr := ht.Pr, Ch := ht.Ch, sel := ht.sel, S := ht.S, word := ht.word, tup := ht.tup,
          cst := ht.cst, idx := ht.idx, m2 := ht.m2, glob := ht.glob, amb := ht.amb, δ := ht.δ, O := ht.O }

end GlobalTheory.Mem.Col2.TC

end
