import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowPairValue
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam.TopFrame
set_option maxHeartbeats 1600000 in
theorem baseFr_top_eq_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ i (hm : (J.G i).s + 1 + 1 ≤ B.R.m) (γ : J.Ch₀ ((J.G i).s + 1 + 1)) (e : GlobalTheory.StepData.Ix (Fin B.R.k ⊕ Fin ((J.G i).s + 1)) (Fin B.R.t) ((J.G i).s + 2) ⊕ Unit ≃ Fin (B.R.N ((J.G i).s + 1 + 1))), GlobalTheory.SymBridge.IsOrd (Sum.elim GlobalTheory.SymBridge.zPos fun _ => B.R.N B.R.m - 1) e → ∀ r b, (ofSplit (J.G i).q).pr (baseFr J.A (J.P i) ((J.G i).s + 1 + 1) hm γ r (e b)) = (J.G i).FM.β r b := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat hiA t J hJ i hm γ e he r b
  have hs : (J.G i).s + 1 + 1 = B.R.m := (J.G i).hs
  have key : ∀ j (h : j = (I.rec7 l Z).R.m), (∀ r s, (a.g.oT j h).iA r s = if r.val = s.val then 1 else 0) ∧
      ∀ r, vecB (a.g.oT j h) (@TDat.ζ₀ _ _ _ a.fld a.val a.top a.loc _ a.o) r = if r.val + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 0 := by
    intro j h
    subst h
    exact ⟨hiA, fun r => hat.z0 r⟩
  obtain ⟨hA, hz⟩ := key _ (J.G i).hs
  obtain ⟨-, ⟨e', he', hT'⟩, hz0⟩ := ha.stdQ (J.pl i) ⟨t, J.mem i⟩
  let ι : (I.rec7 l Z).host.E →+* (J.G i).k := (J.G i).q.pr.comp (incA (I.rec7 l Z))
  have hL := frsF_top J.A hJ.is hW.tr.ok (J.P i) (hJ.tw i).nmem _ hs γ (finCongr (rankN (I.rec7 l Z) _ hm) r) (e b)
  have hL' : baseFr J.A (J.P i) ((J.G i).s + 1 + 1) hm γ r (e b) =
      if r.val = (e b).val then (if r.val + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 1) else 0 := hL
  have hN : B.R.N ((J.G i).s + 1 + 1) = B.R.N B.R.m := congrArg _ hs
  refine (congrArg _ hL').trans (Eq.trans ?_ (congrFun (congrFun (J.G i).last r) b).symm)
  rcases b with b | b
  · have hb : (e (Sum.inl b)).val = (e' b).val := (he _).trans (he' b).symm
    have hb2 : (e (Sum.inl b)).val + 1 ≠ B.R.N B.R.m := by
      intro h
      have h2 : (e (Sum.inr ())).val = B.R.N B.R.m - 1 := he _
      have h3 : e (Sum.inl b) = e (Sum.inr ()) := Fin.ext (by omega)
      exact Sum.inl_ne_inr (e.injective h3)
    have h5 : (if r.val = (e (Sum.inl b)).val then (if r.val + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 1) else 0) =
        (a.g.oT _ (J.G i).hs).iA r (e' b) := by
      refine Eq.trans ?_ (hA r (e' b)).symm
      rw [← hb]
      split_ifs with h1 h2
      · exact absurd (h1 ▸ h2) hb2
      · rfl
      · rfl
    refine (congrArg _ h5).trans ?_
    show _ = ∑ c, ι ((a.g.oT _ (J.G i).hs).iA r c) * (J.G i).FT.β c b
    have h6 : ∀ c, (J.G i).FT.β c b = if c = e' b then 1 else 0 := fun c => (congrFun (congrFun hT' c) b).trans Matrix.one_apply
    refine Eq.symm ((Finset.sum_congr rfl fun c _ => congrArg _ (h6 c)).trans ?_)
    refine (Finset.sum_eq_single (e' b) (fun c _ hc => ?_) (fun h => absurd (Finset.mem_univ _) h)).trans ?_
    · exact (congrArg _ (if_neg hc)).trans (mul_zero _)
    · exact (congrArg _ (if_pos rfl)).trans (mul_one _)
  · have h2 : (e (Sum.inr b)).val = B.R.N B.R.m - 1 := he _
    have h3 := (e (Sum.inr b)).2
    have h4 : (if r.val = (e (Sum.inr b)).val then (if r.val + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 1) else 0) =
        vecB (a.g.oT _ (J.G i).hs) (@TDat.ζ₀ _ _ _ a.fld a.val a.top a.loc _ a.o) r := by
      rw [hz]
      split_ifs with h5 h6 h7
      · rfl
      · omega
      · omega
      · rfl
    refine (congrArg _ h4).trans ?_
    show ι (∑ c, (a.g.oT _ (J.G i).hs).iB r c * (@TDat.ζ₀ _ _ _ a.fld a.val a.top a.loc _ a.o) c) = ∑ c, ι ((a.g.oT _ (J.G i).hs).iB r c) * (J.G i).z₀ c
    exact (map_sum ι _ _).trans (Finset.sum_congr rfl fun c _ => (map_mul ι _ _).trans (congrArg _ (congrFun hz0 c).symm))
end GlobalTheory.Fam.TopFrame
end
