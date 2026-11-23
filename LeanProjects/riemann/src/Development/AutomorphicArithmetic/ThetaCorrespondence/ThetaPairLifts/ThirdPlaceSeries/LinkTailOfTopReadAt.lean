import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReferenceTupleFamilyPeriodEqPeriod
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NotMemQBase
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEqAlt

set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
noncomputable section
namespace GlobalTheory.MiTop.TailColumnRecursion
open Classical
open Formalism.L2.Forms GlobalTheory.Core.Rk.Top
variable {D : D7}
variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word}
theorem tcol_alt (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (t : W.P.T) (i : ℕ) (ψ : (f.t t).Col 0) :
    (f.t t).col i ψ = Formalism.ThetaLiftIndependence.chainOpM (D.chTw u (W.P.I.tup t)).wt (D.chTw u (W.P.I.tup t)).Kmap i ψ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show (f.t t).K i ((f.t t).col i ψ) = _
    rw [ih]; rfl
end GlobalTheory.MiTop.TailColumnRecursion
namespace GlobalTheory.MiTop.TailColumnRecursion
open Classical
open Formalism.L2.Forms GlobalTheory.Core.Rk.Top Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev
variable {D : D7}
end GlobalTheory.MiTop.TailColumnRecursion
namespace GlobalTheory.MiTop.TailColumnRecursion
open Classical
open Formalism.L2.Forms GlobalTheory.Core.Rk.Top Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev
variable {D : D7}
end GlobalTheory.MiTop.TailColumnRecursion
namespace GlobalTheory.MiTop.TailColumnRecursion
open Classical
open Formalism.L2.Forms GlobalTheory.Core.Rk.Top Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev
variable {D : D7}
section G
variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {Pm : PeriodMap D.R C}
    {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm}
    {bad : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F))} {K : ClassesAtPrimes M bad} {okW : D.what₂.places.Pl → Prop}
end G
end GlobalTheory.MiTop.TailColumnRecursion
namespace GlobalTheory.MiTop.TailColumnRecursion
open Classical
open Formalism.L2.Forms GlobalTheory.Core.Rk.Top Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev
variable {D : D7}
end GlobalTheory.MiTop.TailColumnRecursion
namespace GlobalTheory.MiTop
open Classical
open GlobalTheory.MiTop.TailColumnRecursion Formalism.L2.Forms
theorem linkTail_of_topReadAt_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.LeadingReadAt W u f.j f.g.bT → (∀ t, W.P.I.tup t = D.what₂.mu0 → ∀ φ : D.what₂.Mu u, HEq (_root_.GlobalTheory.MiTop.col0_alt f t φ) (D.eMu u φ).1) → _root_.GlobalTheory.MiTop.LinkTailCondition f := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hTR h0 n h t φ F F' hFF G hG
  obtain ⟨hJ, -, hall⟩ := hTR
  have hR := (hall t).2 F F' hFF
  have hex : ∃ G0, _root_.GlobalTheory.Fam.ReadsCoefficients W u f.j f.g.bT (W.P.I.tup t) G0 (_root_.GlobalTheory.Fam.leadingLinearMap W t F') := ⟨_, hR⟩
  have hspec := hex.choose_spec
  show _root_.GlobalTheory.Fam.tailCoefficient W u f.j f.g.bT (W.P.I.tup t)
    (Eq.rec (motive := fun n _ => (D.chTw u (W.P.I.tup t)).cls n → (D.chTw u (W.P.I.tup t)).Y n → ℂ)
      ((f.t t).col (2 * n) (_root_.GlobalTheory.MiTop.col0_alt f t φ)) h) G.1 = _
  rw [hG, _root_.GlobalTheory.MiTop.TailColumnRecursion.tcol_alt, rec_chain]
  unfold _root_.GlobalTheory.Fam.tailCoefficient
  rw [dif_pos hex]
  by_cases hμ : W.P.I.tup t = D.what₂.mu0
  · rw [dif_pos hμ]
    refine referenceTuple_familyPeriod_eq_period u _ hμ _ φ (h0 t hμ φ) _ _ ?_
    have hv : ∀ z ∈ (D.fm u).ptC, ∀ c, (W.R.T.cols.forms u).valP.eW z c ∈ LinearMap.range f.j := by
      intro z hz c
      rw [hJ.range]
      exact fic_val _ _ _ _ (((W.R.T.cols.forms u).valP.ptC z).1 hz) c
    exact reads_uniq _ _ _ _ (W.R.T.cols.forms u).jM hv (W.R.T.cols.forms u).per.2.1 (W.R.T.cols.forms u).per.2.2
      (pos_0 (W.R.T.cols.forms u)) (hspec.1 hμ) (hR.1 hμ)
  · rw [dif_neg hμ, D.perCol_tie u _ hμ, PeriodMap.PtilCol, PeriodMap.Ptil, PeriodMap.Ptil]
    have hv : ∀ z ∈ (ex.tw.fm u (W.P.I.tup t)).ptC, ∀ c, (W.R.T.tw.pt.val u _ hμ).eW z c ∈ LinearMap.range f.j := by
      intro z hz c
      rw [hJ.range, ← sg_eq (W.R.T.tw.pt.val u _ hμ) (W.R.T.cols.forms u).valP]
      exact fic_val _ _ _ _ (((W.R.T.tw.pt.val u _ hμ).ptC z).1 hz) c
    rw [reads_uniq _ _ _ _ (W.R.T.tw.ptE.jM u _) hv (W.R.T.tw.ptE.per u _ hμ).2.1 (W.R.T.tw.ptE.per u _ hμ).2.2
      (pos_G (W.R.T.tw.pt.val u _ hμ)) (hspec.2 hμ) (hR.2 hμ)]
    rfl
end GlobalTheory.MiTop
end
end
