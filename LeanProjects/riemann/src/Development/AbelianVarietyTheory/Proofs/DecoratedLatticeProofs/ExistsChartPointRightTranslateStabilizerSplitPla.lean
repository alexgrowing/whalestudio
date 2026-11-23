import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoStabTrivial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfLastCoordinateDilationOnePrime
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAdeleIdempotentOfFMulSelf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryClassRepresentativesBijective
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReduction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResidueEqZeroIffValLt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameGlInt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameImageTrivialOffLevelPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastRowInvFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.DiaChart

theorem decoratedLattice_unitScale_functional_keeps_frames {X : Formalism.L2.Col.Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y}
    (p : PtY (X := X) (n := n) ST SG Q y) (P : ST) (c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) (P' : HeightOneSpectrum (𝓞 X.E)) :
    ptFr (p.mv (Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco)).1.1 P' = ptFr p.1.1 P' := by
  by_cases h : (∀ (P₁ : Q) (x : Formalism.L2.Col.Sp X.E n), p.1.1.1.2 P₁ x ∈ (Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco).1.at P₁.1 ↔
      x ∈ Formalism.L2.Col.stdAt X.E n P₁.1) ∧ p.1.2 ∈ y.ys (Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco).1.N
  · have e : p.mv (Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco) =
        ⟨(⟨(Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco, p.1.1.1.2), h.1⟩, p.1.2), h.2⟩ := dif_pos h
    rw [e]
    unfold ptFr
    rfl
  · have e : p.mv (Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco) = p := dif_neg h
    rw [e]

theorem finM_mul' {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (g h : GA D V) :
    finM V hn (g * h) = finM V hn g * finM V hn h := by
  subst hn
  exact GlobalTheory.AdForm.RdLaw.finM_mul V g h

theorem ptOf_gl_dia : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 →
    ∀ g : 𝓀[k]ˣ → GL (Fin ((I.rec7 l Z).sp.X j).rank) k, (∀ s, g s • Q j i = s • Q j i) →
      ∀ b (c : {c // A.chOf j c = b}), ∃ e : 𝓀[k]ˣ ≃ ((I.atT l u a).Fv v)ˣ, ∀ s,
        ∃ z : TC.GA B (B.R.N j),
          z.1 = finM _ (rankN (I.rec7 l Z) j hj) (A.h j b c * (β j i).gl (g s)) ∧
          TC.PtOf (z * A.kb j b) (extTo I.SQ (((I.atIn u a).A j).diaPt v (e s) c.1).1.1) := by
  intro B X I hOk hPins l Z u a Ch A hA k _ _ _ _ ι p β Q L hStd j hj i v hv g hg b c
  obtain ⟨c, rfl⟩ := c
  obtain ⟨-, ρ, hρ⟩ := GlobalTheory.FinPl.SplitPt.resField_equiv (I.rec7 l Z) k (p i) v.1 hv
  refine ⟨(Units.mapEquiv ρ.toMulEquiv).toEquiv, fun s => ?_⟩
  obtain ⟨δ, hδ, huni, hint, hint'⟩ := GlobalTheory.AdForm.frameGl_int I hOk hPins l Z u a k ι p β Q L hStd j hj i v hv (g s) s (hg s)
  have htriv := GlobalTheory.T.frameImage_trivial_off_levelPrime I hOk hPins l Z u a k ι p β Q L hStd j hj i v hv (g s) δ hδ
  have hrow := GlobalTheory.AdForm.lastRow_inv_frame I hOk hPins l Z u a k ι p β Q L hStd j hj i v hv ρ hρ (g s) s (hg s) δ hδ hint'
  have hR := hA.reads j hj
  let y : TC.GA B (B.R.N j) := ((A.K j hj (A.chOf j c)).y ⟨c, rfl⟩).1
  refine ⟨y * δ, ?_, ?_⟩
  · rw [Units.val_mul, hδ, finM_mul', (hA.h j hj _ ⟨c, rfl⟩).2]
    rfl
  · obtain ⟨p0, hk0, hN0⟩ := hR.k_std (A.chOf j c)
    have hkc := hk0.lat
    rw [hN0] at hkc
    refine GlobalTheory.Mem.Col2.DilPt.isPointOf_last_coordinate_dilation_one_prime_alt _ _ _ _ _ _ _ y δ (A.kb j (A.chOf j c)) (extTo I.SQ ((I.stp u a j).rep c).1.1) _
      ⟨v.1, v.2⟩ ((Units.mapEquiv ρ.toMulEquiv) s) _ (hR.pt c) hk0.uni huni hkc hint hint' htriv
      (fun r r' hr => hR.k_T (A.chOf j c) ⟨v.1, v.2⟩ r r' hr) (fun r r' hr => hrow r r' hr) ?_ ?_
    · rw [extTo_deco, extTo_deco]
      exact GlobalTheory.Mem.Col2.TwAtStd.diaPt_deco B X I u a j ⟨v.1, v.2⟩ _ c
    · funext P'
      rw [extTo_fr, extTo_fr]
      exact decoratedLattice_unitScale_functional_keeps_frames ((I.stp u a j).rep c) ⟨v.1, v.2⟩ _ P'.1

end GlobalTheory.AdForm.DiaChart

end
