import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SameSetup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBasisAtTransport
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

local macro:max "kc% " e:term:max : term => `((by kexactB $e))

namespace GlobalTheory.TwInputs.Move.TieUp

variable {D : D7} (r : Rest D)

theorem placeModel_up {mm nn : ℕ} {ψ B hs e Λ c f₀ T} (h : @IsPlaceModel D mm nn ψ B hs e Λ c f₀ T) :
    @IsPlaceModel (overD D r) mm nn ((ψ)) ((B)) ((hs)) ((e)) ((Λ)) c ((f₀)) ((T)) :=
  @IsPlaceModel.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (trans := (by with_unfolding_all exact (h.trans :))) (modul := (by with_unfolding_all exact (h.modul :)))
    (vac := (by with_unfolding_all exact (h.vac :)))

theorem placeModel_dn {mm nn : ℕ} {ψ B hs e Λ c f₀ T} (h : @IsPlaceModel (overD D r) mm nn ψ B hs e Λ c f₀ T) :
    @IsPlaceModel D mm nn ((ψ)) ((B)) ((hs)) ((e)) ((Λ)) c ((f₀)) ((T)) :=
  @IsPlaceModel.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (trans := (by with_unfolding_all exact (h.trans :))) (modul := (by with_unfolding_all exact (h.modul :)))
    (vac := (by with_unfolding_all exact (h.vac :)))

theorem placeMap_up {S T : HSp D} (B : Base S T) (a : AE D) :
    (baseUp r B).F.placeMap ((a)) = (B.F.placeMap a) := by
  have hP : (fun L : (WO (D := overD D r) ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))) → ℂ) →ₗ[ℂ] (WO (D := overD D r) ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))) → ℂ) =>
      IsPlaceModel (baseUp r B).F.ψ (symplO ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))))
        (heisO (baseUp r B).F.ψ ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :)))) ((by with_unfolding_all exact (a :))) (baseUp r B).F.lat 1 (baseUp r B).F.f₀ L) =
      (by with_unfolding_all exact ((fun L : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) =>
        IsPlaceModel B.F.ψ (symplO S T) (heisO B.F.ψ S T) a B.F.lat 1 B.F.f₀ L) :)) :=
    funext fun L => propext ⟨fun h => (by with_unfolding_all exact ((placeModel_dn r h) :)), fun h => (by with_unfolding_all exact ((placeModel_up r h) :))⟩
  unfold Frame.placeMap
  exact (by with_unfolding_all exact ((congrArg Classical.epsilon hP) :))

theorem vec_up {S T : HSp D} (B : Base S T) (Q ω) :
    (baseUp r B).F.vec (baseUp r B).G (kc% Q) (kc% ω) = kc% (B.F.vec B.G Q ω) := by
  have e := placeMap_up r B (halfIdem B.G.Pg Q)
  show (baseUp r B).F.placeMap (kc% (halfIdem B.G.Pg Q)) (kc% (B.F.datumFn B.G Q ω)) = _
  rw [e]
  exact kc% rfl

open Classical in

theorem vecAt_up {S T : HSp D} (B : Base S T) (Q φ) :
    (baseUp r B).vecAt (kc% Q) (kc% φ) = kc% (B.vecAt Q φ) := by
  show (baseUp r B).F.vec (baseUp r B).G (kc% (B.de.Q ∪ Q)) (kc% (B.locFn Q φ)) = _
  exact vec_up r B _ _

theorem series_up {S T : HSp D} (B : Base S T) (ω : PairRep S T) (Q φ h) :
    series (baseUp r B).F (kc% ω) ((baseUp r B).vecAt (kc% Q) (kc% φ)) (kc% h) = kc% (series B.F ω (B.vecAt Q φ) h) := by
  rw [vecAt_up r B]
  exact kc% rfl

theorem theta_up {S T : HSp D} (B : Base S T) (ω : PairRep S T) (h : GA D S) :
    (baseUp r B).theta ((ω)) ((h)) = (B.theta ω h) :=
  series_up r B ω ∅ (fun _ _ => 1) h

theorem vecFlat_up {S T : HSp D} (B : Base S T) (ψ : Twist D Circle) :
    (baseUp r B).vecFlat (twistUp r ψ) = (B.vecFlat ψ) :=
  vecAt_up r B ψ.Q _

theorem gen_up {S T : HSp D} (B : Base S T) (ω : PairRep S T) (ψ : Twist D Circle) :
    (baseUp r B).gen ((ω)) (twistUp r ψ) = (B.gen ω ψ) := by
  unfold Base.gen
  rw [vecFlat_up]
  exact (by with_unfolding_all exact (rfl :))

theorem genSet_up {S T : HSp D} (B : Base S T) (ω : PairRep S T) (ψ : Twist D Circle) (h P) :
    (baseUp r B).genSet ((by with_unfolding_all exact (ω :))) (twistUp r ψ) (kc% h) (kc% P) = kc% (B.genSet ω ψ h P) := by
  unfold Base.genSet
  rw [gen_up]
  exact kc% rfl

def univUp {C : Type} [AddCommGroup C] (u : UnivTwist D C) : UnivTwist (overD D r) C := ⟨(by with_unfolding_all exact (u.del :)), (by with_unfolding_all exact (u.kap :))⟩

theorem vecFam_up {S T : HSp D} (B : Base S T) {C : Type} (Q : Finset (Pl D.host.E))
    (Φ : ∀ PP : Pl D.host.E, C → Matrix (Fin T.rank) (Fin S.rank) (kP PP) → ℚ) :
    (baseUp r B).vecFam (C := C) ((by with_unfolding_all exact (Q :))) ((by with_unfolding_all exact (Φ :))) = (by with_unfolding_all exact ((B.vecFam (C := C) Q Φ) :)) :=
  funext fun a => vecAt_up r B Q _

theorem xiCoef_up {S T : HSp D} (B : Base S T) {C : Type} [AddCommGroup C] [Fintype C] (ω : PairRep S T) (u : UnivTwist D C)
    (Q : Finset (Pl D.host.E)) (Φ : ∀ PP : Pl D.host.E, C → Matrix (Fin T.rank) (Fin S.rank) (kP PP) → ℚ) (h : GA D S)
    (P : PolF D T.rank S.rank) :
    (baseUp r B).xiCoef ((ω)) (univUp r u) ((Q)) ((Φ)) ((h)) ((P)) = (B.xiCoef ω u Q Φ h P) := by
  unfold Base.xiCoef Base.xi
  rw [vecFam_up]
  exact (by with_unfolding_all exact (rfl :))

theorem classSum_up {S T : HSp D} (B : Base S T) (ω : PairRep S T) (ψ : Twist D Circle) {I : Type} [Fintype I] (h : I → GA D S) :
    (baseUp r B).classSum (I := I) ((by with_unfolding_all exact (ω :))) (twistUp r ψ) ((by with_unfolding_all exact (h :))) = (by with_unfolding_all exact ((B.classSum ω ψ h) :)) := by
  unfold Base.classSum
  rw [vecFlat_up]
  exact (by with_unfolding_all exact (rfl :))

theorem coefLat_of_equiv {S T : HSp D} (B : Base S T) {K : Type} [Field K] [NumberField K] (e : K ≃+* ↥D.LL0) (σ : K →+* ℂ)
    (emb : D.what₂.Tau → (D.host.E →+* K)) (hσ : ∀ x, embLL0 D (e x) = σ x) (hemb : ∀ τ, σ.comp (emb τ) = tauE D τ)
    (O : Subring ℂ) : B.coefLat σ emb O = B.coefLat (embLL0 D) (labLL0 D) O := by
  obtain rfl : (embLL0 D).comp e.toRingHom = σ := RingHom.ext hσ
  have h : (fun τ => e.toRingHom.comp (emb τ)) = labLL0 D := funext fun τ => RingHom.ext fun x => (embLL0 D).injective
    ((DFunLike.congr_fun (hemb τ) x).trans (DFunLike.congr_fun (embLL0_labLL0 τ) x).symm)
  funext x
  rw [Base.coefLat, Base.coefLat, harmLat, harmLat, GlobalTheory.CoefLatIso.coefLatFn_ringEquiv, h]

theorem mtLat_of_equiv {S T : HSp D} (B : Base S T) {K : Type} [Field K] [NumberField K] (e : K ≃+* ↥D.LL0) (σ : K →+* ℂ)
    (emb : D.what₂.Tau → (D.host.E →+* K)) (hσ : ∀ x, embLL0 D (e x) = σ x) (hemb : ∀ τ, σ.comp (emb τ) = tauE D τ)
    (O : Subring ℂ) (t : Twist D Circle) : B.mtLat σ emb O t = B.mtLat (embLL0 D) (labLL0 D) O t := by
  rw [Base.mtLat, Base.mtLat, coefLat_of_equiv B e σ emb hσ hemb]

section Setup

variable (ρ : Setup D.ntw) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)

theorem liftSetupOverExtendedData_theta_eq : (setupUp r ρ).theta ((i)) ((j)) b = (ρ.theta i j b) :=
  (by with_unfolding_all exact ((funext fun h => congrArg DFunLike.coe (theta_up r (ρ.B i j b) (ρ.om i j b 1) h)) :))

theorem liftSetupOverExtendedData_gens_eq : (setupUp r ρ).gens ((i)) ((j)) b = (ρ.gens i j b) :=
  (by with_unfolding_all exact ((funext fun k => funext fun Q => funext fun ψ => funext fun h => funext fun P =>
    genSet_up r (ρ.B i j b) (ρ.om i j b 1) (ρ.tw i b k Q ψ) h P) :))

theorem liftSetupOverExtendedData_classSum_eq : (setupUp r ρ).sum ((i)) ((j)) b = (ρ.sum i j b) :=
  (by with_unfolding_all exact ((funext fun k => funext fun Q => funext fun ψ =>
    classSum_up r (ρ.B i j b) (ρ.om i j b (ρ.tw i b k Q ψ).chi) (ρ.tw i b k Q ψ) (ρ.rep i j b (ρ.tw i b k Q ψ))) :))

theorem liftSetupOverExtendedData_xi_eq : (setupUp r ρ).xi ((i)) ((j)) b (overD D r).nexp = (ρ.xi i j b D.nexp) :=
  (by with_unfolding_all exact ((funext fun Q => funext fun M => funext fun h => funext fun P =>
    xiCoef_up r (ρ.B i j b) (ρ.om i j b 1) (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc)
      (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M)) (Base.univFam (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc) (ρ.β j)) h P) :))

variable {r} {ι : D.what₂.LL →+* (overD D r).what₂.LL} {e : ↥(overD D r).LL0 ≃+* ↥D.LL0} (hc : CopyTw D (overD D r) ι e)
include hc

theorem liftSetupOverExtendedData_lat_eq : (setupUp r ρ).lat ((i)) ((j)) b = (ρ.lat i j b) := by
  funext O x
  have := coefLat_of_equiv (ρ.B i j b) e (embLL0 (overD D r)) ((by with_unfolding_all exact ((labLL0 (overD D r)) :))) hc.embLL0_eq
    ((by with_unfolding_all exact ((embLL0_labLL0 (D := overD D r)) :))) O
  exact (by with_unfolding_all exact ((congrFun this (finPt _ x)) :))

theorem liftSetupOverExtendedData_integralForms_eq : (setupUp r ρ).mt ((i)) ((j)) b = (ρ.mt i j b) := by
  have H := mtLat_of_equiv (ρ.B i j b) e (embLL0 (overD D r)) ((by with_unfolding_all exact ((labLL0 (overD D r)) :))) hc.embLL0_eq
    ((by with_unfolding_all exact ((embLL0_labLL0 (D := overD D r)) :)))
  have H' := fun (k : ℕ) (Q : Finset (Pl D.host.E)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) =>
    H (ρ.eOk i b k).range (ρ.tw i b k Q ψ)
  funext k Q ψ
  exact (by with_unfolding_all exact ((H' k ((Q)) ((ψ))) : _))

theorem liftSetupOverExtendedData_isDatum_eq : (setupUp r ρ).IsDatum ((i)) ((j)) b = (ρ.IsDatum i j b) := by
  funext s x P
  have hl := liftSetupOverExtendedData_lat_eq ρ i j b hc
  refine propext ⟨fun d => ?_, fun d => ?_⟩
  · have m := d.mem
    rw [hl] at m
    exact (⟨(by with_unfolding_all exact (d.split :)), (by with_unfolding_all exact (d.off :)), (by with_unfolding_all exact (d.fin :)), (by with_unfolding_all exact (d.supp :)), (by with_unfolding_all exact (m :))⟩ : ρ.IsDatum i j b ((by with_unfolding_all exact (s :))) ((by with_unfolding_all exact (x :))) ((by with_unfolding_all exact (P :))))
  · have d' : ρ.IsDatum i j b ((by with_unfolding_all exact (s :))) ((by with_unfolding_all exact (x :))) ((by with_unfolding_all exact (P :))) := d
    refine ⟨(by with_unfolding_all exact (d'.split :)), (by with_unfolding_all exact (d'.off :)), (by with_unfolding_all exact (d'.fin :)), (by with_unfolding_all exact (d'.supp :)), ?_⟩
    rewrite [hl]
    exact (by with_unfolding_all exact (d'.mem :))

end Setup

section Cell

variable {ι : D.what₂.LL →+* (overD D r).what₂.LL} {e : ↥(overD D r).LL0 ≃+* ↥D.LL0} (hc : CopyTw D (overD D r) ι e)
  {ρ : Setup D.ntw} {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool}

def cellUp {hρ : ρ.Good} (hρ' : (setupUp r ρ).Good) {rd : Rd ρ D.nexp i j b} (t : CellTie hρ D.nexp rd) :
    CellTie hρ' (overD D r).nexp (i := (by with_unfolding_all exact (i :))) (j := (by with_unfolding_all exact (j :))) (b := b) ((by with_unfolding_all exact (rd :))) where
  supp := (by with_unfolding_all exact (t.supp :))
  cls := (by with_unfolding_all exact (t.cls :))
  coef := (by with_unfolding_all exact (t.coef :))
  rdV := (by with_unfolding_all exact (t.rdV :))
  U_eq := (by with_unfolding_all exact (t.U_eq :))
  psiU_eq := (by with_unfolding_all exact (t.psiU_eq :))
  dat := by rewrite [liftSetupOverExtendedData_isDatum_eq ρ i j b hc]; exact (by with_unfolding_all exact (t.dat :))
  dat_onto := by rewrite [liftSetupOverExtendedData_isDatum_eq ρ i j b hc, liftSetupOverExtendedData_theta_eq r ρ i j b]; exact (by with_unfolding_all exact (t.dat_onto :))
  lev_iff := (by with_unfolding_all exact (t.lev_iff :))
  th_eq := by rewrite [liftSetupOverExtendedData_theta_eq r ρ i j b]; exact (by with_unfolding_all exact (t.th_eq :))
  thPsi_iff := by rewrite [liftSetupOverExtendedData_gens_eq r ρ i j b]; exact (by with_unfolding_all exact (t.thPsi_iff :))
  thU_eq := by rewrite [liftSetupOverExtendedData_xi_eq r ρ i j b]; exact (by with_unfolding_all exact (t.thU_eq :))
  thU_off := by rewrite [liftSetupOverExtendedData_xi_eq r ρ i j b]; exact (by with_unfolding_all exact (t.thU_off :))
  rdV_inj := (by with_unfolding_all exact (t.rdV_inj :))
  mtLat_iff := by rewrite [liftSetupOverExtendedData_integralForms_eq ρ i j b hc]; exact (by with_unfolding_all exact (t.mtLat_iff :))
  thP_eq := by rewrite [liftSetupOverExtendedData_classSum_eq r ρ i j b]; exact (by with_unfolding_all exact (t.thP_eq :))

theorem cellUp_rdV {hρ : ρ.Good} (hρ' : (setupUp r ρ).Good) {rd : Rd ρ D.nexp i j b} (t : CellTie hρ D.nexp rd) :
    HEq t.rdV (cellUp r hc hρ' t).rdV := HEq.rfl

include hc in

theorem rat_up (hρ : ρ.Good) (hρ' : (setupUp r ρ).Good) (rd : Rd ρ D.nexp i j b) :
    SeriesTie.Rat hρ' (Y := (overD D r).nexp) (i := (by with_unfolding_all exact (i :))) (j := (by with_unfolding_all exact (j :))) (b := b) ((by with_unfolding_all exact (rd :))) ↔ SeriesTie.Rat hρ rd := by
  conv_lhs => delta SeriesTie.Rat RatBase RatTwist RatUniv
  rewrite [liftSetupOverExtendedData_isDatum_eq ρ i j b hc, liftSetupOverExtendedData_theta_eq r ρ i j b, liftSetupOverExtendedData_gens_eq r ρ i j b, liftSetupOverExtendedData_xi_eq r ρ i j b]
  exact (by with_unfolding_all exact ((Iff.refl (SeriesTie.Rat hρ rd)) :))

end Cell

end GlobalTheory.TwInputs.Move.TieUp

end
