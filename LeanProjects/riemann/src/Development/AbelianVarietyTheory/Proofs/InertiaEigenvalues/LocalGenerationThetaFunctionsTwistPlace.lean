import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasShape
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaCoefficientIsSchwartzBruhatUniformSplitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceInvariantFormsSeparateThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalTranslatesSpanPrescribedCoefficientStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanTranslatesConjugateHalfTwistPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionMemSpanOfCoefficientSpanStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaShapeRelationDropSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProductDatumThetaHasShapeAdjointPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalHeisenbergSpanPreservesTypeRelationsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionLiftPairStepVectorInvLevelChar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalVAlgebraMapMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnderEqOfConj
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPlacesThetaFunctionFixedVectorShape

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

namespace GlobalTheory.DownLift.GenTwist

section Generic

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem suppAt_conj {e : AE D} {V : HSp D} {g : GA D V} (h : SuppAt e V g) : SuppAt (cA D e) V g := by
  intro i j
  rw [GlobalTheory.DualPairCheck.cA_cA, add_comm]
  exact h i j

theorem suppAt_one (e : AE D) (V : HSp D) : SuppAt e V 1 := by
  intro i j
  have : mt V (1 : GA D V) = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [map_one]; rfl
  rw [this, sub_self, Matrix.zero_apply, mul_zero]

theorem suppAt_inv {e : AE D} {V : HSp D} {g : GA D V} (h : SuppAt e V g) : SuppAt e V g⁻¹ := by
  intro i j
  have := congrFun (congrFun (GlobalTheory.SplitScalar.off_smul_mt_inv h) i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  rw [Matrix.sub_apply]
  linear_combination -this

theorem om_form {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : IsWeilDatumO ψ S T χS χT om) {a : AE D} (ha : IsSplitIdem D a) {g : GA D S} {h : GA D T}
    (hg : SuppAt a S g) (hh : SuppAt a T h) :
    ∃ s : ℂ, s ≠ 0 ∧ ∀ ℓ, InvForm ψ S T a ℓ → ∀ f, IsThetaFunO ψ S T f → ∀ x,
      ℓ (heisO ψ S T (actO S T g h x) (om (g, h) f)) = s * ℓ (heisO ψ S T x f) := by
  obtain ⟨r, hr, H⟩ := hW.om_split a ha g h hg hh _ _ (GlobalTheory.VecInv.isDetAt_detAt a ha.1 S g)
    (GlobalTheory.VecInv.isDetAt_detAt a ha.1 T h)
  refine ⟨_, mul_ne_zero (Complex.ofReal_ne_zero.2 hr.ne') (Circle.coe_ne_zero (splitFacO χS χT
    (GlobalTheory.VecInv.detAt a ha.1 S g) (GlobalTheory.VecInv.detAt a ha.1 T h))), fun ℓ hℓ f hf x => ?_⟩
  rw [← hW.om_heis g h x f hf]
  exact H ℓ (fun u hu f hf => hℓ u hu f hf) _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hW.std hf x)

theorem cross_law {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : IsWeilDatumO ψ S T χS χT om) {a : AE D} (ha : IsSplitIdem D a) {κ : GA D S} (hκ : SuppAt a S κ)
    {f w Φ : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hw : IsThetaFunO ψ S T w) (hw0 : w ≠ 0)
    (hs : HasShape ψ S T a Φ w) {c : ℂ} (hc : c ≠ 0) (ef : om (κ, 1) f = c • f) (ew : om (κ, 1) w = c • w)
    {ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ} (hℓ : InvForm ψ S T a ℓ) {x x' : WO S T} (hx : IsHalf a x) (hx' : IsHalf a x') :
    coef ψ S T a ℓ f (actO S T κ 1 x) * Φ x' = coef ψ S T a ℓ f x * Φ (actO S T κ 1 x') := by
  obtain ⟨s, hs0, H⟩ := om_form hW ha hκ (suppAt_one a T)
  have hne : ¬ ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x w) = 0 := fun h =>
    hw0 (GlobalTheory.T.splitPlace_invariantForms_separate_thetaFunctions D ψ S T hW.std a ha w hw h)
  push Not at hne
  obtain ⟨ℓ₀, hℓ₀, x₀, hx₀, hne⟩ := hne
  obtain ⟨c₀, hc₀⟩ := hs ℓ₀ hℓ₀
  have hc0 : c₀ ≠ 0 := by
    rintro rfl
    exact hne (by rw [hc₀ x₀ hx₀, zero_mul])
  have e1 := H ℓ hℓ f hf x
  have e2 := H ℓ₀ hℓ₀ w hw x'
  rw [ef, GlobalTheory.SplitScalar.heisO_smul, map_smul, smul_eq_mul] at e1
  rw [ew, GlobalTheory.SplitScalar.heisO_smul, map_smul, smul_eq_mul, hc₀ _ (GlobalTheory.SplitHecke.isHalf_actO κ 1 hx'), hc₀ _ hx'] at e2
  unfold coef
  rw [if_pos (GlobalTheory.SplitHecke.isHalf_actO κ 1 hx), if_pos hx]
  have e3 : c * Φ (actO S T κ 1 x') = s * Φ x' := mul_left_cancel₀ hc0 (by linear_combination e2)
  apply mul_left_cancel₀ hc
  linear_combination (Φ x') * e1 - (ℓ (heisO ψ S T x f)) * e3

open Classical in
theorem omegaQ_split {a b : ℕ} (Q : Finset (Pl D.host.E)) (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ)
    {PP : Pl D.host.E} (hP : PP ∈ Q) (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) :
    omegaQ Q r ξ k y = omegaQ {PP} r ξ k y * omegaQ (Q.erase PP) r ξ k y := by
  let F : Pl D.host.E → ℂ := fun P => if h : IsUnit (topL r (y P)).det then ((ξ P h.unit : ℂˣ) : ℂ) ^ k else 0
  have key : ∀ Q' : Finset (Pl D.host.E), omegaQ Q' r ξ k y =
      if ∀ P ∈ Q', LowZero r (y P) ∧ IsUnit (topL r (y P)).det then ∏ P ∈ Q', F P else 0 := by
    intro Q'
    unfold omegaQ
    split_ifs with h
    · rw [← Finset.prod_attach Q' F]
      refine Finset.prod_congr rfl fun P _ => ?_
      simp only [F]
      rw [dif_pos (h P.1 P.2).2]
    · rfl
  rw [key, key, key]
  by_cases h : ∀ P ∈ Q, LowZero r (y P) ∧ IsUnit (topL r (y P)).det
  · rw [if_pos h, if_pos (fun P hP' => h P (by rw [Finset.mem_singleton.1 hP']; exact hP)),
      if_pos (fun P hP' => h P (Finset.mem_of_mem_erase hP')), Finset.prod_singleton, Finset.mul_prod_erase Q F hP]
  · rw [if_neg h]
    by_cases h1 : ∀ P ∈ ({PP} : Finset (Pl D.host.E)), LowZero r (y P) ∧ IsUnit (topL r (y P)).det
    · rw [if_pos h1, if_neg (fun h2 => h fun P hP' => by
        by_cases e : P = PP
        · exact h1 P (Finset.mem_singleton.2 e)
        · exact h2 P (Finset.mem_erase.2 ⟨e, hP'⟩)), mul_zero]
    · rw [if_neg h1, zero_mul]

theorem idem_over {e : AE D} {PP : Pl D.host.E} {v : HeightOneSpectrum (𝓞 D.host.F)}
    (he : Formalism.L2.NTheta.IsIdemAt e PP) (hv : Over PP v) :
    ∃ ε, IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε := by
  obtain ⟨v', hv'⟩ := (GlobalTheory.IdemModTwo.isSplitIdem_iff e).1 he.1
  obtain ⟨PP', h1, h2⟩ := GlobalTheory.IdemPrime.exists_isIdemAt D v' e hv'
  obtain rfl : PP' = PP := GlobalTheory.PlaceVec.isIdemAt_inj h1 he
  obtain rfl : v' = v := HeightOneSpectrum.ext (h2.symm.trans hv)
  exact ⟨_, ⟨_, rfl, GlobalTheory.SplitIdem.evalV_singleV_same _ v' 1,
    fun w hw => GlobalTheory.SplitIdem.evalV_singleV_ne _ v' _ hw⟩, hv'.2.2⟩

end Generic

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem step_of_shape (R : RealDat D A Ks) (hW : R.thP_ωP) (i : Fin D.R.m) (t : T)
    {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))} {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∈ Sb)
    {ε : AF D.host.F} {a : AE D} (ha : IsSplitIdem D a) (hε : IsPlaceIdem D v ε)
    (hae : a + cA D a = algebraMap (AF D.host.F) (AE D) ε)
    {ΛS : Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E)} (dS : IsSelfDualC (Vc D i) ΛS)
    (dT : IsSelfDualC (Wc D i) ΛT) (hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t))
    {Φ f : WO (Vc D i) (Wc D i) → ℂ} (hΦ : IsSBHalf a (latH (Vc D i) (Wc D i) ΛS ΛT) Φ)
    (hs : HasShape R.ψ (Vc D i) (Wc D i) a Φ (R.vP i t)) (hT : TypeIn R i t Sb f) (hC : CleanIn R i t Sb f)
    (hL : LikeOff R i t Sb f)
    (hsp : ∀ ℓ, InvForm R.ψ (Vc D i) (Wc D i) a ℓ →
      coef R.ψ (Vc D i) (Wc D i) a ℓ f ∈ Submodule.span ℂ (translT (Vc D i) (Wc D i) a Φ)) :
    f ∈ Submodule.span ℂ (StepGen R i t (dropPl Sb v)) := by
  have hψ := (hW i t).std
  refine GlobalTheory.T.thetaFunction_mem_span_of_coefficientSpan D R.ψ _ _ hψ a ha f hT.1 _ _ ?_ ?_ hsp
  · rintro _ ⟨g, f', h1, -, -, rfl⟩
    exact (hW i t).om_pres _ _ h1.1
  · rintro _ ⟨g, hg, rfl⟩ x₁ hx₁
    obtain ⟨f', hf', H⟩ := GlobalTheory.T.exists_localTranslatesSpan_prescribedCoefficient D R.ψ _ _ hψ ΛS ΛT dS dT a ha f hT.1 Φ hΦ x₁ hx₁
    obtain ⟨p1, p2, p3⟩ := GlobalTheory.T.localHeisenbergSpan_preserves_type_relations D G Pl0 T A Ks R hW i t Sb v hv ε a hε hae f hT hC hL f' hf'
    have p4 := GlobalTheory.T.thetaShapeRelation_drop_splitPlace D G Pl0 T A Ks R hψ i t Sb v ε a ha hε hae hth Φ f' hs
      (fun ℓ hℓ => ⟨_, fun x hx => (H ℓ hℓ x hx).trans (mul_comm _ _)⟩) p3
    have hg' : SuppAt a (Wc D i) g⁻¹ := suppAt_inv hg
    obtain ⟨s, hs0, E⟩ := om_form (hW i t) ha (suppAt_one a (Vc D i)) hg'
    refine ⟨s⁻¹ • R.ωP i t (1, g⁻¹) f', Submodule.smul_mem _ _ (Submodule.subset_span ⟨g⁻¹, f', p1, p2, p4, rfl⟩),
      fun ℓ hℓ x hx => ?_⟩
    have e := E ℓ hℓ f' p1.1 (actO _ _ 1 g x)
    have e' := GlobalTheory.SplitHecke.actO_inv_actO (S := Vc D i) (T := Wc D i) 1 g x
    rw [inv_one] at e'
    rw [e', H ℓ hℓ _ (GlobalTheory.SplitHecke.isHalf_actO 1 g hx)] at e
    rw [GlobalTheory.SplitScalar.heisO_smul, map_smul, smul_eq_mul, e, ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]

theorem law_vP (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) (hW : R.thP_ωP) (hv : R.thP_vP) (i : Fin D.R.m) (t : T)
    {κ : GA D (Vc D i)} (hκ : κ ∈ levG (Vc D i) (R.βV i) (R.datVt i t)) :
    R.ωP i t (κ, 1) (R.vP i t) = (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ • R.vP i t := by
  have h1 : (1 : GA D (Wc D i)) ∈ levG (Wc D i) (R.βW i) (R.datWp i R.triv) := one_mem _
  have h := GlobalTheory.VecInv.omega_lifts_vP R hL (hv i t).1.2.inf hW hv i t 1 κ 1
    ⟨hκ.1, hκ.2.1, Subgroup.mem_bot.1 hκ.2.2⟩ ⟨h1.1, h1.2.1, Subgroup.mem_bot.1 h1.2.2⟩
  have h2 := levFn_withP (V := Vc D i) (β := R.βV i) (L := R.datVt i t) (R.datVt i t).P (finE (Vc D i) κ)
  have h3 : Formalism.L2.DIV.ext1 (R.datVt i t).P.H (R.datVt i t).P.chi
      (Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) κ)) = 1 := by
    unfold Formalism.L2.DIV.ext1; split_ifs with hm
    · have : (⟨_, hm⟩ : (R.datVt i t).P.H) = 1 := Subtype.ext (Subgroup.mem_bot.1 hm)
      rw [this, map_one]
    · rfl
  rw [h3, one_mul] at h2
  rw [h]
  unfold levChi
  exact congrArg (fun z : ℂˣ => (z : ℂ)⁻¹ • R.vP i t) h2.symm

theorem suppIn_of_suppAt {V : HSp D} {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∈ Sb) {ε : AF D.host.F} {e : AE D} (he : IsSplitIdem D e)
    (hε : IsPlaceIdem D v ε) (hae : e + cA D e = algebraMap (AF D.host.F) (AE D) ε) {κ : GA D V} (hκ : SuppAt e V κ) :
    SuppIn Sb V κ := by
  refine ⟨Matrix.ext fun i j => ?_, fun w hw ε' hε' i j => ?_⟩
  · rw [Matrix.map_apply, ← hκ i j, RingHom.map_mul, RingHom.map_add, GlobalTheory.SplitScalar.infPart_splitIdem he,
      GlobalTheory.SplitScalar.infPart_splitIdem (GlobalTheory.SplitScalar.isSplitIdem_conj he), add_zero, zero_mul, Matrix.zero_apply]
  · rw [← hκ i j, hae, ← mul_assoc, ← RingHom.map_mul,
      GlobalTheory.PlaceDatum.placeIdem_mul hε' hε (fun h => hw (h ▸ hv)), RingHom.map_zero, zero_mul]

theorem step_twist : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (v : HeightOneSpectrum (𝓞 D.host.F)), v ∈ Sb → (∀ PP ∈ R.Pg, ¬ GlobalTheory.DownLift.GenFinite.Over PP v) → (∃ PP ∈ R.Q t, GlobalTheory.DownLift.GenFinite.Over PP v) → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), GlobalTheory.DownLift.GenFinite.TypeIn R i t Sb f → GlobalTheory.DownLift.GenFinite.CleanIn R i t Sb f → GlobalTheory.DownLift.GenFinite.LikeOff R i t Sb f → f ∈ Submodule.span ℂ (GlobalTheory.DownLift.GenFinite.StepGen R i t (GlobalTheory.DownLift.GenFinite.dropPl Sb v)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t Sb v hv hPg ⟨PP, hPP, hov⟩ f hT hC hL
  classical
  have hc := hG.core
  have hW := hc.thP.ωP
  have hψ := (hW i t).std
  have dS := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hc.lev.βV i)
  have dT := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hc.lev.βW i)
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hr : (Wc D i).rank ≤ (Vc D i).rank := rW.trans_le (r_le_V i)
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hc.thP.pt_theta i t 1
    unfold RealDat.ptP pureTensorO at this
    rwa [GlobalTheory.AdTh.VecFock.pureTensorL_one] at this
  have hv0 : R.vP i t ≠ 0 := GlobalTheory.AdTh.VecNe.thPVec_ne_zero dS dT hr (hc.thP.vP i t)
  obtain ⟨hvac, e, he', hΘ⟩ := hc.thP.vP i t
  obtain ⟨P, he, hP⟩ : ∃ P, IsIdemSum e P ∧ ∀ PP, PP ∈ P ↔ PP ∈ R.Pg ∨ PP ∈ R.Q t :=
    ⟨_, he', fun PP => Finset.mem_union⟩
  have hPP' : PP ∈ P := (hP PP).2 (Or.inr hPP)
  obtain ⟨es, hes, -⟩ := he.1
  have h0 := hes PP hPP'
  obtain ⟨ε, hε, hae⟩ := idem_over h0 hov
  have ha := GlobalTheory.SplitScalar.isSplitIdem_conj h0.1
  have hae' : cA D (es PP) + cA D (cA D (es PP)) = algebraMap (AF D.host.F) (AE D) ε := by
    rw [GlobalTheory.DualPairCheck.cA_cA, add_comm, hae]
  have hne : ∀ PP' ∈ R.Pg, PP' ≠ PP := fun PP' h h' => hPg PP' h (h' ▸ hov)
  have hs : HasShape R.ψ (Vc D i) (Wc D i) (cA D (es PP))
      (adjDat (Vc D i) (Wc D i) (R.βV i) (R.βW i) (es PP) (omegaQ {PP} (Wc D i).rank (R.xiR t) (-1))) (R.vP i t) := by
    refine GlobalTheory.T.productDatumTheta_hasShape_adjoint_place D R.ψ _ _ hψ _ _ dS dT (R.βV i) (R.βW i) P e (es PP) PP he hPP' h0 _
      (fun y => omegaK R.Pg y * omegaQ ((R.Q t).erase PP) (Wc D i).rank (R.xiR t) (-1) y)
      (fun y y' h => GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ fun P' hP' => by rw [Finset.mem_singleton.1 hP']; exact h)
      (fun y y' h => ?_) (R.vacP i) _ hvac.2.theta ?_
    · rw [GlobalTheory.PlaceVec.omegaK_congr R.Pg fun P' hP' => h P' ((hP P').2 (Or.inl hP')) (hne P' hP'),
        GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ fun P' hP' =>
          h P' ((hP P').2 (Or.inr (Finset.mem_of_mem_erase hP'))) (Finset.ne_of_mem_erase hP')]
    · convert hΘ using 1
      funext x
      unfold adjDat
      congr 1
      rw [omegaQ_split (R.Q t) _ _ _ hPP, mul_left_comm]
  have hΦ : IsSBHalf (cA D (es PP)) (latH (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i))
      (adjDat (Vc D i) (Wc D i) (R.βV i) (R.βW i) (es PP) (omegaQ {PP} (Wc D i).rank (R.xiR t) (-1))) :=
    GlobalTheory.PlaceVec.isSBHalf_of_red dS.1 dT.1 (GlobalTheory.SplitScalar.infPart_splitIdem ha) _
      (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _) {PP} _
      fun y y' h => GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ h
  refine step_of_shape R hW i t hv ha hε hae' dS dT hth hΦ hs hT hC hL fun ℓ hℓ => ?_
  obtain ⟨c, hB⟩ := hc.lev.βV i
  refine GlobalTheory.T.mem_span_translates_conjugateHalf_twistPlace D _ _ (R.βV i) (R.βW i) hr _ _ _ hB dS.1 dT.1 (es PP) PP h0 (R.xiR t)
    (GlobalTheory.ChainTw.RModel.xiR_ne R hc.lev t PP hPP) _
    ((GlobalTheory.T.thetaCoefficient_isSchwartzBruhat_uniform_split D R.ψ _ _ hψ _ _ dS dT _ ha f hT.1).2.1 ℓ hℓ) fun κ k1 k2 k3 k4 _ x x' hx hx' => ?_
  have k5 : ∀ P' ∈ P, P' ≠ PP → redFn (R.βV i) P' (finE (Vc D i) κ) = 1 := fun P' h h' =>
    GlobalTheory.DiagLiftFix.redFn_eq_one_of_ne he hPP' h0 k1 k3 h h'.symm
  have hκ : κ ∈ levG (Vc D i) (R.βV i) (R.datVt i t) := by
    refine ⟨k2, ⟨⟨⟨GlobalTheory.LevSplit.finE_mem_UA _ κ, k3⟩, ?_⟩, ?_⟩, ?_⟩
    · refine Subgroup.mem_iInf.2 fun P' => Subgroup.mem_iInf.2 fun h => mem_parah.2 ⟨k3, ?_⟩
      rw [k5 P' ((hP P').2 (Or.inl h)) (hne P' h)]
      exact one_mem _
    · refine Subgroup.mem_iInf.2 fun P' => Subgroup.mem_iInf.2 fun h => mem_parah.2 ⟨k3, ?_⟩
      by_cases h' : P' = PP
      · rw [h']
        rw [rW] at k4
        exact k4
      · rw [k5 P' ((hP P').2 (Or.inr h)) h']
        exact one_mem _
    · refine Subgroup.mem_bot.2 (funext fun P' => ?_)
      show upperLeftBlock _ (redFn (R.βV i) P'.1 (finE (Vc D i) κ)) = 1
      rw [k5 P'.1 ((hP P').2 (Or.inl P'.2)) (hne P'.1 P'.2)]
      exact blockDiagonalExtendByOnePrimeField_one _ _
  exact cross_law (hW i t) ha (suppAt_conj k1) hT.1 hth hv0 hs (inv_ne_zero (levChi_ne_zero _ κ))
    (hT.2 κ hκ (suppIn_of_suppAt hv h0.1 hε hae k1)) (law_vP R hc.lev hW hc.thP.vP i t hκ) hℓ hx hx'

end GlobalTheory.DownLift.GenTwist

end
