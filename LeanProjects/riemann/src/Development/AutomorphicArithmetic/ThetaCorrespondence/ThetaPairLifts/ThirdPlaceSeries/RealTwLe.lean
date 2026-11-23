import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff ser)
open GlobalTheory.FlatVecSum (princ)
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
namespace GlobalTheory.BigOn.Exp.TupLe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
def AllPtsAlt (Q : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}, PtAt ex Csz → Fin D.R.m → Prop) : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts)
    (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz) (j : Fin D.R.m), p.PointConditions' → More p → Q p j
open Classical in
def PlacesCondition : Prop := _root_.GlobalTheory.BigOn.Exp.TupLe.AllPtsAlt fun {D _ _ _ _ _ _ _ ex _} p j => ∀ w : D.what₂.places.Pl, D.plEq w ∈ p.R.twPl →
  IntegralHeckeForms.TwOK (ex.nch.twI w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w) →
  ∀ ρ : Setup D.ntw, ρ.Good → RealPin p.R p.cG ρ →
  ChrEq (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi (p.Tp.psi w) →
  p.R.xi (p.R.mu (D.plEq w)) = (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.chi *
    (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi →
  SplitSet (p.R.Q (p.R.mu (D.plEq w))) ∧
    (∀ P ∈ p.R.Q (p.R.mu (D.plEq w)), ((D.ntw.l (ex.nch.twI w) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) ∧
    idem (p.R.Q (p.R.mu (D.plEq w))) + cA D (idem (p.R.Q (p.R.mu (D.plEq w)))) =
      idem ((ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.Q ∪
          (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).Q) +
        cA D (idem ((ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.Q ∪
          (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).Q))
open Classical in
def FlatCondition : Prop := _root_.GlobalTheory.BigOn.Exp.TupLe.AllPtsAlt fun {D _ _ _ _ _ _ _ _ _} p j => ∀ (B : Base (Vc D j) (Wc D j)) (ψ : Twist D Circle) (t : p.P.T),
  B.Good → BaseOf (R2 p) j B → ψ.Good → B.admitted ψ.Q → (R2 p).xi t = B.de.chi * ψ.chi →
  idem ((R2 p).Q t) + cA D (idem ((R2 p).Q t)) = idem (B.de.Q ∪ ψ.Q) + cA D (idem (B.de.Q ∪ ψ.Q)) →
  ∃ (z : GA D (Vc D j)) (c : ℂ), SuppAt (idem ((R2 p).Q t)) (Vc D j) z ∧ UnitOff (GlobalTheory.TwistField.tupPrime (R2 p) t) c ∧
    (princ B).vecFlat ψ = c • (R2 p).ωP j t (z⁻¹, 1) ((R2 p).vP j t)
def TraceCondition : Prop := _root_.GlobalTheory.BigOn.Exp.TupLe.AllPtsAlt fun {D _ _ _ _ _ _ _ _ _} p j => ∀ (ρ : Setup D.ntw), ρ.Good → RealPin p.R p.cG ρ → ρ.LevelOf D.nexp →
  ∀ (i : D.ntw.Tw) (b : Bool) (ψ : Twist D Circle) (ω : PairRep (Vc D j) (Wc D j)), ψ.Good → (ρ.B i j b).admitted ψ.Q →
    (ρ.B i j b).IsWeil ψ.chi ω → ∀ (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank),
      levelTrace (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ (series (ρ.B i j b).F ω ((princ (ρ.B i j b)).vecFlat ψ) h P) =
        series (ρ.B i j b).F ω ((ρ.B i j b).vecFlat ψ) h P
def CoefficientCondition' : Prop := _root_.GlobalTheory.BigOn.Exp.TupLe.AllPtsAlt fun {D _ _ _ _ _ _ _ _ _} p j => ∀ (B : Base (Vc D j) (Wc D j)), B.Good → BaseOf (R2 p) j B →
  ∀ c : ℂ, c ≠ 0 → IsScale p.R p.v₀ B c → ∀ u : ∀ τ, lowT ((R2 p).MW j (sg0 D p.P.A3.A)) τ,
    (∀ τ, (u τ : ((R2 p).MW j (sg0 D p.P.A3.A)).sm τ) = p.v₀ j _ τ) → ∀ O' : Subring ℂ, IsCoefRing D.what₂.embLL (labLL D) O' →
    ∀ h ∈ GfC (Vc D j), ∀ v, InCoefLat (R2 p) j h v →
      ∃ P ∈ B.coefLat D.what₂.embLL (labLL D) O' (finPt (Vc D j) h), (R2 p).ioP j (PiTensorProduct.tprod ℂ u) v = c • P
def SmallnessCondition : Prop := _root_.GlobalTheory.BigOn.Exp.TupLe.AllPtsAlt fun {D _ _ _ _ _ _ _ _ _} p j => ∀ (B : Base (Vc D j) (Wc D j)), B.Good → BaseOf (R2 p) j B →
  ∀ O O' : Subring ℂ, IsCoefRing (embLL0 D) (labLL0 D) O → IsCoefRing D.what₂.embLL (labLL D) O' →
    ∀ (h : GA D (Vc D j)), ∀ P ∈ B.coefLat D.what₂.embLL (labLL D) O' (finPt (Vc D j) h),
      P ∈ Submodule.span O' (B.coefLat (embLL0 D) (labLL0 D) O (finPt (Vc D j) h) : Set (PolF D (Wc D j).rank (Vc D j).rank))
section Units
variable {O K : Type} [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Field K] [Algebra O K] [IsFractionRing O K]
end Units
section Read
variable {D : D7} {ρ : Setup D.ntw} {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} (rd : Rd ρ D.nexp i j b)
  {L : Type} [Field L] [Algebra (D.ntw.O i) L] (e : L →+* ℂ) (he : ∀ c : D.ntw.O i, e (algebraMap _ L c) = ρ.eO i b c)
end Read
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m)
variable {p w j}
end Point
section Move
variable {D : D7} {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
include hρ
end Move
section Assembly
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {w : D.what₂.places.Pl} {j : Fin D.R.m}
theorem realTw_le_alt (s1 : _root_.GlobalTheory.BigOn.Exp.TupLe.PlacesCondition) (s2 : _root_.GlobalTheory.BigOn.Exp.TupLe.FlatCondition) (s3 : _root_.GlobalTheory.BigOn.Exp.TupLe.TraceCondition) (s4 : _root_.GlobalTheory.BigOn.Exp.TupLe.CoefficientCondition') (s5 : _root_.GlobalTheory.BigOn.Exp.TupLe.SmallnessCondition) (hr : p.PointConditions') (hm : More p)
    (hL : Links2 p) (hw : D.plEq w ∈ p.R.twPl)
    (hok : IntegralHeckeForms.TwOK (ex.nch.twI w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w))
    {ρ : Setup D.ntw} (hρ : ρ.Good) (hpin : RealPin p.R p.cG ρ) (hlev : ρ.LevelOf D.nexp)
    (hB0 : BaseOf (R2 p) j (ρ.B (ex.nch.twI w) j (ex.nch.sd w)))
    (e : FractionRing (ex.nch.Oe w) →+* ℂ) (h1 : ∀ x, e (ex.nch.embW w x) = D.what₂.embLL x)
    (h2 : ∀ a : D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w),
      e (algebraMap (ex.nch.Oe w) _ (algebraMap _ (ex.nch.Oe w) a)) = ρ.eOk (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) a)
    (c1 : ChrEq (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi (p.Tp.psi w))
    (c2 : p.R.xi (p.R.mu (D.plEq w)) = (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.chi *
      (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi)
    {ν : ℂ} (hν : IsNorm p.R p.v₀ (ρ.B (ex.nch.twI w) j (ex.nch.sd w)) ν) (hR : RatAt p w j hρ ν) {rd : Can p w j} (hc : IsCan p rd) :
    realTw p rd ≤ twLat p w j hρ ν := by
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hK := GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.isKsForm_of_iso (p.nexp.fi j) (p.fw.ks j)
  obtain ⟨Z⟩ := hm.2.2.series
  have hF : Faithful (rdAt p w j hρ ν) := realRd_faithful _ _ _ _ _ _ _ _ _ _ p.nexp p.v₀ ρ hρ _ j _ ν hν.1 hL.2.2.1
    p.charW.base.models.HW (Z.vec j) hK
  obtain ⟨p1, p2, p3⟩ := s1 _ _ _ _ _ _ _ _ _ _ p j hr hm w hw hok ρ hρ hpin c1 c2
  obtain ⟨ht, hadm, -⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ _ j (ex.nch.sd w) _ _ _ hok
  have hB := hρ.base (ex.nch.twI w) j (ex.nch.sd w)
  obtain ⟨z, cz, hz, hcz, hfl⟩ := s2 _ _ _ _ _ _ _ _ _ _ p j hr hm _ _ ((R2 p).mu (D.plEq w)) hB hB0 ht hadm c2 p3
  have hzf : z ∈ GfC (Vc D j) := GlobalTheory.TwTraceCx.mem_GfC_of_suppAt p1 hz
  have hω : (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).IsWeil
      (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi
      ((R2 p).ωP j ((R2 p).mu (D.plEq w))) := by
    have e0 : (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).mu *
        (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi =
        (R2 p).toLevCh.mu ((R2 p).mu (D.plEq w)) ((j : ℕ) + 1) := by
      rw [Base.mu, hB0.mu0, mul_assoc, ← c2]
      rfl
    rw [Base.IsWeil, e0, hB0.ψ, hB0.eta]
    exact hC.thP.ωP j _
  have hN : IsUnit ((GlobalTheory.TwistField.tupPrime (R2 p) ((R2 p).mu (D.plEq w)) : ℕ) : ex.nch.Oe w) := by
    have hcop : Nat.Coprime (D.ntw.l (ex.nch.twI w)) (GlobalTheory.TwistField.tupPrime (R2 p) ((R2 p).mu (D.plEq w))) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hq
      have := GlobalTheory.NormUnit.coprime_absNorm _ (D.ntw.lPrime _).out P (p2 P hP)
      rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this
    simpa using (GlobalTheory.NormUnit.isUnit_natCast_of_coprime (D.ntw.O_l _) hcop).map (algebraMap _ (ex.nch.Oe w))
  have hO' : IsCoefRing D.what₂.embLL (labLL D) (imO ex.nch w e) := by
    refine ⟨fun τ => FWT.embV_spec (RingHom.id _) D.what₂.embLL (RingHom.comp_id _) τ, fun a => ?_⟩
    obtain ⟨b, hb⟩ := mem_of_ringOfIntegers (O := ex.nch.Oe w) (ex.nch.embW w) a
    exact ⟨b, by rw [RingHom.comp_apply, hb, h1]⟩
  obtain ⟨ν0, c, hs, n, hn, hνc⟩ := hν
  rw [p.phsOne j, map_one, one_mul] at hνc
  have c0 : c ≠ 0 := fun h => ν0 (by rw [h, zero_pow hn] at hνc; exact pow_eq_zero_iff hn |>.1 hνc)
  obtain ⟨-, -, -, -, u, hu, -⟩ := id hs
  refine le_of_comb hρ hc hR hF hK e h1 h2 hN ?_
  rintro x ⟨h, hh, v, hv, hx⟩
  obtain ⟨P, hP, hio⟩ := s4 _ _ _ _ _ _ _ _ _ _ p j hr hm _ hB hB0 c c0 hs u hu _ hO' h hh v hv
  have hP' := s5 _ _ _ _ _ _ _ _ _ _ p j hr hm _ hB hB0 _ _ (hρ.isCoefRing (ex.nch.twI w) (ex.nch.sd w)) hO' h P hP
  have hhz : h * z ∈ GfC (Vc D j) := mul_mem hh hzf
  refine ⟨ν⁻¹ * c * cz⁻¹, unitOff_mul (unitOff_root hn ?_) (unitOff_inv hcz),
    series (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).F ((R2 p).ωP j ((R2 p).mu (D.plEq w)))
      ((ρ.B (ex.nch.twI w) j (ex.nch.sd w)).vecFlat
        (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w))) (h * z) P, ?_, ?_⟩
  · rw [mul_pow, inv_pow, hνc, inv_mul_cancel₀ (pow_ne_zero _ c0)]
  · clear hP hio
    induction hP' using Submodule.span_induction with
    | mem Q hQ =>
      obtain ⟨s, h', P', hd, g, hg, a, ea⟩ := series_eq_gen hρ _ j _ hok hω hhz (lat_translate_of_prime hρ _ j _ p1 p2 hz hQ)
      rw [ea]
      exact Submodule.smul_mem _ (⟨_, ⟨algebraMap _ _ a, h2 a⟩⟩ : imO ex.nch w e) (Submodule.subset_span ⟨s, h', P', hd, hg⟩)
    | zero => rw [map_zero]; exact zero_mem _
    | add _ _ _ _ a b => rw [map_add]; exact add_mem a b
    | smul a y _ hy =>
      rw [show a • y = (a : ℂ) • y from rfl, map_smul]
      exact Submodule.smul_mem _ a hy
  · have e1 : adForm (R2 p) j x (p.v₀ j _) = levelTrace (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹
        (ser (R2 p) j ((R2 p).mu (D.plEq w)) ((R2 p).vP j ((R2 p).mu (D.plEq w))) u h v) :=
      ((congrArg (adForm (R2 p) j x) (funext hu)).symm.trans (hx u)).trans (one_smul _ _)
    have e2 : ser (R2 p) j ((R2 p).mu (D.plEq w)) ((R2 p).vP j ((R2 p).mu (D.plEq w))) u h v = (c * cz⁻¹) •
        series (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).F ((R2 p).ωP j ((R2 p).mu (D.plEq w)))
          ((princ (ρ.B (ex.nch.twI w) j (ex.nch.sd w))).vecFlat
            (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w))) (h * z) P := by
      rw [mul_comm, mul_smul, ← map_smul, ← hio]
      refine Eq.trans ?_ (congrArg (cz⁻¹ • ·) (hB0.series_eq_ser _ _ u (h * z) v)).symm
      rw [hfl]
      funext g
      have e3 := GlobalTheory.Adopt.thetaSeries_translated_datum_at_translated_class _ _ _ _ _ _ (R2 p) _ hC j ((R2 p).mu (D.plEq w)) z⁻¹ cz (inv_mem hzf) u (h * z) v g
      rw [mul_inv_cancel_right] at e3
      refine Eq.trans ?_ (congrArg (cz⁻¹ * ·) e3).symm
      exact (inv_mul_cancel_left₀ hcz.1 _).symm
    rw [e1, e2, map_smul, s3 _ _ _ _ _ _ _ _ _ _ p j hr hm ρ hρ hpin hlev _ _ _ _ ht hadm hω, smul_smul, mul_assoc]
end Assembly
end GlobalTheory.BigOn.Exp.TupLe
end
end
