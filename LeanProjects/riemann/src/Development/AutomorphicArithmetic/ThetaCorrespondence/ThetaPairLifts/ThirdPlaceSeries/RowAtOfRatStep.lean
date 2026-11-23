import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
namespace GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Sets
variable {D : D7} {ρ : Setup D.ntw} (hρ : ρ.Good) {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} (rd : Rd ρ D.nexp i j b)
end Sets
section Hyp
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
end Hyp
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m)
variable {p w j}
namespace Fit
variable {ρ : Setup D.ntw} {hρ : ρ.Good} {ν : ℂ} (h : Fit p w j hρ ν)
include h
end Fit
end Point
def TwistConditions (Q : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i →
    (Fm.D x i).what₂.places.Pl → Fin (Fm.D x i).R.m → Prop) : Prop :=
  _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x hx i p => ∀ w, (Fm.D x i).plEq w ∈ p.R.twPl → ∀ j, Q Fm x hx i p w j
section AtTw
variable {Q Q' : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i →
  (Fm.D x i).what₂.places.Pl → Fin (Fm.D x i).R.m → Prop}
theorem TwistConditions.and (h : _root_.GlobalTheory.BigOn.Exp.TwistConditions Q) (h' : _root_.GlobalTheory.BigOn.Exp.TwistConditions Q') : _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => Q Fm x hx i p w j ∧ Q' Fm x hx i p w j :=
  Closed.imp (Closed.and h h') fun _ _ _ H =>
    let ⟨x0, K⟩ := _root_.GlobalTheory.BigTop.EventuallyAtPoints.and H.1 H.2
    ⟨x0, fun x hx h0 i p r m w hw j => ⟨(K x hx h0 i p r).1 m w hw j, (K x hx h0 i p r).2 m w hw j⟩⟩
theorem TwistConditions.imp (h : _root_.GlobalTheory.BigOn.Exp.TwistConditions Q) (f : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i), p.PointConditions' →
    More p → ∀ w, (Fm.D x i).plEq w ∈ p.R.twPl → ∀ j, Q Fm x hx i p w j → Q' Fm x hx i p w j) : _root_.GlobalTheory.BigOn.Exp.TwistConditions Q' :=
  Closed.imp h fun Fm _ _ ⟨x0, K⟩ => ⟨x0, fun x hx h0 i p r m w hw j => f Fm x hx i p r m w hw j (K x hx h0 i p r m w hw j)⟩
theorem TwistConditions.of_forall (f : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i), p.PointConditions' →
    More p → ∀ w, (Fm.D x i).plEq w ∈ p.R.twPl → ∀ j, Q Fm x hx i p w j) : _root_.GlobalTheory.BigOn.Exp.TwistConditions Q :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ⟨0, fun x hx _ i p => f Fm x hx i p⟩⟩⟩
end AtTw
def CanonicalExists : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∃ rd : Can p w j, IsCan p rd ∧
  ∃ (n : ℕ) (β : Module.Basis (Fin n) (Fm.D x i).what₂.LL (Fin ((R2 p).nW j) → (Fm.D x i).what₂.LL)),
    LinearIndependent (FractionRing ((Fm.ex x hx i).nch.Oe w)) fun a => rd (β a)
def CanonicalProjection₂ : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x _ i p w j => ∀ rd : Can p w j, IsCan p rd → ∀ y,
  rd ((((R2 p).FW j).eOp fun g => (idemOf p.P.A3.A.X).coeff g) y) = eExt (Fm.D x i).nexp _ _ _ _ (rd y)
def TwAdmAlt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i _ w _ =>
  IntegralHeckeForms.TwOK ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w) ((Fm.ex x hx i).nch.Q w)
                     (GlobalTheory.TwistIndex.chosenChar (Fm.ex x hx i).nch w) ∧
    IntegralHeckeForms.ClsQ (D := Fm.D x i) ((Fm.ex x hx i).nch.Q w) ∧ (Fm.D x i).ntw.NonzeroIndexPlace ((Fm.ex x hx i).nch.twI w)
def LowerBoundAtPlace : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i _ w _ => ∀ P : Pl (Fm.D x i).host.E,
  (((Fm.D x i).host.QS * (Fm.D x i).host.q * Ideal.absNorm (Fm.D x i).host.ccK * ((Fm.D x i).host.g 0 * (Fm.D x i).host.g 1 * (Fm.D x i).host.pde *
    (Fm.D x i).host.pde') : ℕ) : 𝓞 (Fm.D x i).host.E) ∈ P.asIdeal → P ∈ (Fm.D x i).ntw.S0 ((Fm.ex x hx i).nch.twI w)
def ConditionAtPlace : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good), RealPin p.R p.cG ρ →
  ρ.LevelOf (Fm.D x i).nexp → RatRow p.nexp p.v₀ hρ ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
def RationalityHypothesis : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j =>
  ∃ (T' : CoreJ (Fm.D x i)) (_ : Algebra T'.Q.c.F (Fm.D x i).what₂.LL) (Rl' : RealDat3 (Fm.D x i) p.P.A3 T'.Q.c.F)
    (cG' : G0 Rl'.Pg (Fm.D x i).R.r ≃* G0g (Fm.D x i).nd) (S' : NX.RatDat (Fm.D x i).ntw) (YS' : NX.NExpRealS Rl' cG' S')
    (F' : Face (Fm.D x i) p.P.A3.A) (κ' : ∀ j : Fin (Fm.D x i).R.m, WeightFamilies.Wt (Fm.D x i) ((j : ℕ) + 1))
    (v₀' : ∀ (j : Fin (Fm.D x i).R.m) (σ : (Fm.D x i).what₂.LL →+* ℂ), (Rl'.MW j σ).Vec)
    (O' : ∀ j, OMDat T'.toCore Rl'.toRealDat j Unit (fun _ => p.P.A3.A.μ0)) (hV' : T'.V ((j : ℕ) + 1) T'.σ₀ = Wc (Fm.D x i) j),
    RatHyp T' Rl' F' κ' v₀' O' ((Fm.ex x hx i).nch.twI w) j hV' ∧
      (∀ ρ : Setup (Fm.D x i).ntw, RealPin p.R p.cG ρ → RealPin Rl' cG' ρ) ∧
      ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (b : Bool), RatRow YS' v₀' hρ ((Fm.ex x hx i).nch.twI w) j b →
        RatRow p.nexp p.v₀ hρ ((Fm.ex x hx i).nch.twI w) j b
theorem twist_at_statement_of_ratHypAt (h : _root_.GlobalTheory.BigOn.Exp.RationalityHypothesis) (hR : RatStep) : _root_.GlobalTheory.BigOn.Exp.ConditionAtPlace :=
  _root_.GlobalTheory.BigOn.Exp.TwistConditions.imp h fun Fm x hx i _ _ _ _ _ j ⟨T', _, Rl', cG', S', YS', F', κ', v₀', O', hV', h1, h2, h3⟩ ρ hρ hp hL =>
    h3 ρ hρ _ (hR _ _ _ _ _ _ T' Rl' cG' S' YS' F' κ' v₀' O' ρ hρ _ j _ hV' (h2 ρ hp) hL
      ⟨(Fm.params x hx i).level_split _ (Fm.D x i).host.pde_level.1, (Fm.params x hx i).level_split _ (Fm.D x i).host.pde_level.2⟩ h1)
def CompatibilityRational : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ Z : ExportTie p.nexp p.v₀,
  IsNorm p.R p.v₀ (Z.ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ∧ RatAt p w j Z.good (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w))
def RecursiveSide : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ Z : ExportTie p.nexp p.v₀, RatAt p w j Z.good (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) →
  Submodule.span ((Fm.ex x hx i).nch.Oe w) ((fun a => (1 : FractionRing ((Fm.ex x hx i).nch.Oe w)) ⊗ₜ (Fm.D x i).nexp.th _ _ _ a) ''
      IntegralHeckeForms.SgJ (Fm.D x i).nexp (twE Fm x hx i) ((Fm.ex x hx i).nch.twI w) ((j : ℕ) + 1) ((Fm.ex x hx i).nch.sd w)) = baseLat p w j Z.good (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ∧
  Submodule.span ((Fm.ex x hx i).nch.Oe w) (incl (Fm.D x i).nexp _ _ _ ((Fm.ex x hx i).nch.Oe w) ((Fm.ex x hx i).nch.k' w) ''
      ⋃ a ∈ IntegralHeckeForms.SgJ (Fm.D x i).nexp (twE Fm x hx i) ((Fm.ex x hx i).nch.twI w) ((j : ℕ) + 1) ((Fm.ex x hx i).nch.sd w),
        (Fm.D x i).nexp.thPsi _ _ _ ((Fm.ex x hx i).nch.k' w) ((Fm.ex x hx i).nch.Q w)
          (GlobalTheory.TwistIndex.chosenChar (Fm.ex x hx i).nch w) a) = twLat p w j Z.good (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w))
def AdaptedExistence₂ : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x _ i p w _ => ∀ ρ : Setup (Fm.D x i).ntw, ρ.Good → RealPin p.R p.cG ρ →
  ∃ ρ' : Setup (Fm.D x i).ntw, ρ'.Good ∧ SameBut ρ ρ' ∧ Adapted p w ρ'
def ConjugateBase : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ ρ' : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ),
  RealPin p.R p.cG ρ → SameBut ρ ρ' → IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
    RatAt p w j hρ ν → Fit p w j hρ' ν' → baseLat p w j hρ ν = baseLat p w j hρ' ν'
def ConjugateTwist : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ ρ' : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ),
  RealPin p.R p.cG ρ → SameBut ρ ρ' → IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
    RatAt p w j hρ ν → Fit p w j hρ' ν' → twLat p w j hρ ν = twLat p w j hρ' ν'
def TwistCharacter : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ ρ : Setup (Fm.D x i).ntw, ρ.Good → Adapted p w ρ →
  ChrEq (ρ.tw ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.k' w) ((Fm.ex x hx i).nch.Q w)
      (GlobalTheory.TwistIndex.chosenChar (Fm.ex x hx i).nch w)).chi (p.Tp.psi w) ∧
    p.R.xi (p.R.mu ((Fm.D x i).plEq w)) = (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).de.chi *
      (ρ.tw ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.k' w) ((Fm.ex x hx i).nch.Q w)
        (GlobalTheory.TwistIndex.chosenChar (Fm.ex x hx i).nch w)).chi
def CanonicalFits (Q : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i) (w : (Fm.D x i).what₂.places.Pl)
    (j : Fin (Fm.D x i).R.m) (ρ : Setup (Fm.D x i).ntw), ρ.Good → ℂ → Can p w j → Prop) : Prop :=
  _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ) (rd : Can p w j), Fit p w j hρ ν → IsCan p rd →
    Q Fm x hx i p w j ρ hρ ν rd
def BaseUpperBound₂ : Prop := _root_.GlobalTheory.BigOn.Exp.CanonicalFits fun _ _ _ _ p w j _ hρ ν rd => realBase p rd ≤ baseLat p w j hρ ν
def BaseLowerBound₂ : Prop := _root_.GlobalTheory.BigOn.Exp.CanonicalFits fun _ _ _ _ p w j _ hρ ν rd => baseLat p w j hρ ν ≤ realBase p rd
def TwistUpperBound₂ : Prop := _root_.GlobalTheory.BigOn.Exp.CanonicalFits fun _ _ _ _ p w j _ hρ ν rd => realTw p rd ≤ twLat p w j hρ ν
def TwistLowerBound : Prop := _root_.GlobalTheory.BigOn.Exp.CanonicalFits fun _ _ _ _ p w j _ hρ ν rd => twLat p w j hρ ν ≤ realTw p rd
def InductionConditions : Prop := _root_.GlobalTheory.BigOn.Exp.CanonicalExists ∧ _root_.GlobalTheory.BigOn.Exp.CanonicalProjection₂ ∧ _root_.GlobalTheory.BigOn.Exp.TwAdmAlt ∧ _root_.GlobalTheory.BigOn.Exp.ConditionAtPlace ∧ _root_.GlobalTheory.BigOn.Exp.CompatibilityRational ∧ _root_.GlobalTheory.BigOn.Exp.RecursiveSide ∧ _root_.GlobalTheory.BigOn.Exp.AdaptedExistence₂ ∧ _root_.GlobalTheory.BigOn.Exp.ConjugateBase ∧ _root_.GlobalTheory.BigOn.Exp.ConjugateTwist ∧ _root_.GlobalTheory.BigOn.Exp.BaseUpperBound₂ ∧ _root_.GlobalTheory.BigOn.Exp.BaseLowerBound₂ ∧ _root_.GlobalTheory.BigOn.Exp.TwistUpperBound₂ ∧ _root_.GlobalTheory.BigOn.Exp.TwistLowerBound
theorem exists_exportTie_fit_at_tw (h1 : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt) (h2 : _root_.GlobalTheory.BigOn.Exp.ConditionAtPlace) (h3 : _root_.GlobalTheory.BigOn.Exp.AdaptedExistence₂) : _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x _ i p w j => Nonempty (ExportTie p.nexp p.v₀) ∧
    ∀ Z : ExportTie p.nexp p.v₀, ∃ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ), SameBut Z.ρ ρ ∧ Fit p w j hρ ν :=
  _root_.GlobalTheory.BigOn.Exp.TwistConditions.imp (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h1 (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h2 h3)) fun _ _ _ _ _ _ hm _ _ _ ⟨a1, a2, a3⟩ => ⟨hm.2.2.series, fun Z =>
    let ⟨ρ, hρ, hs, ha⟩ := a3 Z.ρ Z.good Z.pin
    have hL := levelOf_of_sameBut hm.2.2 Z.good hρ Z.pin ha.1 hs (levelOf_exportTie Z)
    let ⟨ν, hn, hr⟩ := a2 ρ hρ ha.1 hL
    ⟨ρ, hρ, ν, hs, ha, hn, ⟨hr.1, hr.2.1 _ _ _ a1.1 a1.2.1⟩, hL⟩⟩
theorem InductionConditions.exportSt (h : _root_.GlobalTheory.BigOn.Exp.InductionConditions) : _root_.GlobalTheory.BigOn.ExportedStatement := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  refine Closed.imp (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and (_root_.GlobalTheory.BigOn.Exp.exists_exportTie_fit_at_tw h3 h4 h7) (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h1 (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h2 (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h5 (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h6 (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h8 (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h9
    (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h10 (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h11 (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h12 h13)))))))))) fun Fm _ _ ⟨x0, K⟩ => ⟨x0, fun x hx h0 i p r m v hv j => ?_⟩
  obtain ⟨⟨⟨Z⟩, a0⟩, ⟨rd, hc, hβ⟩, a2, a5, a6, a8, a9, a10, a11, a12, a13⟩ :=
    K x hx h0 i p r m ((Fm.D x i).plEq.symm v) (by rwa [Equiv.apply_symm_apply]) j
  obtain ⟨ρ, hρ, ν, hs, hf⟩ := a0 Z
  obtain ⟨hN, hR⟩ := a5 Z
  obtain ⟨r1, r2⟩ := a6 Z hR
  have b1 := le_antisymm (a10 ρ hρ ν rd hf hc) (a11 ρ hρ ν rd hf hc)
  have b2 := le_antisymm (a12 ρ hρ ν rd hf hc) (a13 ρ hρ ν rd hf hc)
  simp only [realBase, realTw, Equiv.apply_symm_apply] at b1 b2
  exact ⟨rd, hβ, a2 rd hc, (b1.trans (a8 Z.ρ ρ Z.good hρ _ ν Z.pin hs hN hR hf).symm).trans r1.symm,
    (b2.trans (a9 Z.ρ ρ Z.good hρ _ ν Z.pin hs hN hR hf).symm).trans r2.symm⟩
end GlobalTheory.BigOn.Exp
end
end
