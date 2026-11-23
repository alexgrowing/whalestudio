import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRangeRestrictEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaProjectionIntertwinesLevelLifts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodProjectorUnitaryFormsModelLaws
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalOperatorsFormsOnRankSpaceNormal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvectorAdjointIntertwinerNormalOperators
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaIntertwinesMatchedOperators
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalThetaCorrespondenceInertPlaceOfHowe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwoSidedHeckePartnerInertPrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftTransferHeckePolySplitPrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightCocharacterEqOfGoodPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperspecialFixesAllChainVacuaAtInertPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Hk3 Formalism.IndefR

set_option maxHeartbeats 4000000

namespace GlobalTheory.DownLift.Sat

theorem exists_adjoint_comp {X E : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (f : X →ₗ[ℂ] E) (N : Submodule ℂ X)
    (hk : ∀ y ∈ N, LinearMap.adjoint f (f y) ∈ N) (hi : ∀ y ∈ N, f y = 0 → y = 0) :
    ∀ y ∈ N, ∃ y' ∈ N, LinearMap.adjoint f (f y') = y := by
  intro y hy
  let S : N →ₗ[ℂ] N := (LinearMap.adjoint f ∘ₗ f).restrict hk
  have hinj : Function.Injective S := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    have h1 : LinearMap.adjoint f (f u) = 0 := congrArg Subtype.val hu
    have h2 : ⟪f u, f u⟫_ℂ = 0 := by rw [← LinearMap.adjoint_inner_left, h1, inner_zero_left]
    exact Subtype.ext (hi u u.2 (inner_self_eq_zero.1 h2))
  obtain ⟨u, hu⟩ := LinearMap.injective_iff_surjective.1 hinj ⟨y, hy⟩
  exact ⟨u, u.2, congrArg Subtype.val hu⟩

theorem adjoint_eig {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    (L : Module.End ℂ X) (hn : Commute L (LinearMap.adjoint L)) (l : ℂ) (u : X) (hu : L u = l • u) :
    LinearMap.adjoint L u = star l • u := by
  have h1 : L (LinearMap.adjoint L u) = l • LinearMap.adjoint L u := by
    rw [← Module.End.mul_apply, hn.eq, Module.End.mul_apply, hu, map_smul]
  have h2 : ∀ w, L w = l • w → ⟪LinearMap.adjoint L u - star l • u, w⟫_ℂ = 0 := fun w hw => by
    rw [inner_sub_left, LinearMap.adjoint_inner_left, hw, inner_smul_right, inner_smul_left]
    simp
  rw [← sub_eq_zero]
  refine inner_self_eq_zero.1 (h2 _ ?_)
  rw [map_sub, h1, map_smul, hu, smul_sub, smul_comm]

variable {D : D7}

theorem translate_of_lift {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {g₀ : G0 L.Pg L.r} {F F' : Bridge.Gf V → W}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations.IsTranslate V β L g₀ F F') (k : GA D V) (hk : IsLevelLift V β L g₀ k) (x : Bridge.Gf V) :
    F' x = (levChi V β (flagL L) k)⁻¹ • F (x * (finHom V).rangeRestrict k) := by
  have e1 : finE V k = Formalism.UG.bc (swapAE D) ((finHom V).rangeRestrict k).1 := finE_eq V k
  have hq1 : Formalism.UG.bc (swapAE D) ((finHom V).rangeRestrict k).1 ∈ lev D.sp.cm V.gram β (flagL L) :=
    ⟨e1 ▸ hk.2.1, Subgroup.mem_top _⟩
  have hq : (finHom V).rangeRestrict k ∈ (levEnv V β L).Q := hq1
  have hl : GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations.LiftsTo V β L ⟨_, hq⟩ g₀ := (congrArg (rTup β L) e1).symm.trans hk.2.2
  have hc : levChi V β (flagL L) k = (((levEnv V β L).ch ⟨_, hq⟩ : ℂˣ) : ℂ) :=
    congrArg Units.val ((congrArg (levFn β (flagL L)) e1).trans (GlobalTheory.LiftEquivariance.ch_eq ⟨_, hq⟩).symm)
  refine (h.2 _ hl x).trans ?_
  exact congrArg (fun a : ℂ => a • F (x * (finHom V).rangeRestrict k))
    ((Units.val_inv_eq_inv_val _).trans (congrArg (·⁻¹) hc.symm))

theorem actL_comp {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} (c : CoefA V) (hc : c.Is)
    {g₀ : G0 L.Pg L.r} {F F' : Bridge.Gf V → c.W} (h : GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations.IsTranslate V β L g₀ F F') (l : c.W →ₗ[ℂ] ℂ) :
    actL V β L g₀ (fun x => l (c.ext F x)) = fun x => l (c.ext F' x) := by
  have hex : ∃ κ, IsLevelLift V β L g₀ κ := (GlobalTheory.LiftEquivariance.exists_adelic_lift h).imp fun _ h => h.1
  funext x
  have h0 : levChi V β (flagL L) hex.choose ≠ 0 := levChi_ne_zero (V := V) (β := β) (flagL L) _
  have h1 := GlobalTheory.ThetaProjEquiv.ext_shift c hc _ hex.choose_spec.1 _ h0 F F' (translate_of_lift h _ hex.choose_spec) x
  have e : actL V β L g₀ (fun x => l (c.ext F x)) = actG0 V β L g₀ (fun x => l (c.ext F x)) := rfl
  rw [e]
  unfold actG0
  rw [dif_pos hex]
  show _ * l (c.ext F _) = _
  rw [← h1, map_smul, Pi.smul_apply, map_smul, smul_eq_mul, inv_mul_cancel_left₀ h0]

theorem sum_fix {G E E' : Type} [Group G] [Fintype G] [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    (ρ : Representation ℂ G E) (ρ' : Representation ℂ G E') (f : E →ₗ[ℂ] E') (hf : GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations.Commutes ρ ρ' f)
    (c : G → ℂ) (x : E) (hx : (∑ g, c g • ρ g) x = x) : ∑ g, c g • ρ' g (f x) = f x := by
  conv_rhs => rw [← hx, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [LinearMap.smul_apply, map_smul, hf g x]

theorem gaL_fix {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} (c : CoefA V) (hc : c.Is)
    {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (M : HMod (Bridge.Gf V → c.W)) (π : Representation ℂ G M.H)
    (hπ : GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations.IsTransRep V β L eG M π) (a : G → ℂ) (u : M.H) (hu : ∑ g, a g • π g u = u) (l : c.W →ₗ[ℂ] ℂ) :
    gaL V β L eG a (fun x => l (c.ext (M.e u) x)) = fun x => l (c.ext (M.e u) x) := by
  have e1 : ∀ g, actL V β L (eG g) (fun x => l (c.ext (M.e u) x)) = fun x => l (c.ext (M.e (π g u)) x) :=
    fun g => actL_comp c hc (hπ g u) l
  have e2 : gaL V β L eG a (fun x => l (c.ext (M.e u) x)) = ∑ g, a g • actL V β L (eG g) (fun x => l (c.ext (M.e u) x)) := by
    unfold gaL
    exact LinearMap.sum_apply _ _ _
  have e3 : (fun x => l (c.ext (M.e u) x)) = ∑ g, a g • fun x => l (c.ext (M.e (π g u)) x) := by
    conv_lhs => rw [← hu]
    funext x
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [e2]
  simp only [e1]
  exact e3.symm

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem goodVt_of (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (u : (R.HV i t).H)
    (h : ∀ l : (R.cV i).W →ₗ[ℂ] ℂ, gaL (Vc D i) (R.βV i) (R.datVt i t) R.eG (RealDat.eC (A := A) (sg0 D A))
      (fun x => l ((R.cV i).ext ((R.HV i t).e u) x)) = fun x => l ((R.cV i).ext ((R.HV i t).e u) x)) : GoodVt R i t u := by
  intro l
  simp only [RealDat.extV, LinearMap.coe_comp, Function.comp_apply]
  exact h l

theorem good_adjoint (R : RealDat D A Ks) (F : Face D A) (hC : Core R F) (i : Fin D.R.m) (t : T)
    (x : (R.HW i (sg0 D A)).H) (hx : eH R i x = x) : GoodVt R i t (LinearMap.adjoint (R.thG i t) x) := by
  have hs : ∀ g, ∃ κ, GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations.LiftsTo (Vc D i) (R.βV i) (R.datVt i t) κ (R.eG g) := fun g =>
    ((R.B.L i t).act_tie.red_surj g).imp fun q hq => (hC.grp.red_L i t q).symm.trans (congrArg R.eG hq)
  have hM : (R.HV i t).Is (Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ (levEnv _ (R.βV i) (R.datVt i t)).J
      (levEnv _ (R.βV i) (R.datVt i t)).χ) (Bridge.adInner (Bridge.ratF (Vc D i)) (levEnv _ (R.βV i) (R.datVt i t)).J (R.B.L i t).pres.y) :=
    hC.models.HV i t
  obtain ⟨π, hπ⟩ := GlobalTheory.LiftEquivariance.exists_transRep (Vc D i) (R.βV i) (R.datVt i t) (R.cV i) (hC.models.cV i) (R.HV i t) (R.B.L i t).pres.y
    (R.B.L i t).pres.reps hM R.eG hs
  have hc : GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations.Commutes π (R.gW i (sg0 D A)) (R.thG i t) := fun g y =>
    (GlobalTheory.LiftEquivariance.exists_adelic_lift (hπ.2 g y)).elim fun κ hκ =>
      GlobalTheory.ThetaProjEquiv.thG_intertwines_core R F hC i t g κ hκ.1 y _ hκ.2
  have ha := GlobalTheory.LiftEquivariance.commutes_adjoint π _ hπ.1 (GlobalTheory.T.norm_liftForms_finiteGroup_action R hC.models.HW hC.models.gW hC.models.νW i _) _ hc
  have hx' : (∑ g, RealDat.eC (A := A) (sg0 D A) g • R.gW i (sg0 D A) g) x = x := hx
  have h1 := sum_fix _ _ _ ha (RealDat.eC (A := A) (sg0 D A)) x hx'
  exact goodVt_of R i t _ fun l => gaL_fix (V := Vc D i) (β := R.βV i) (L := R.datVt i t) (R.cV i) (hC.models.cV i) R.eG (R.HV i t) π hπ.2 _ _ h1 l

theorem partner_inert (hH : HoweUnram) (R : RealDat D A Ks) (F : Face D A) (hC : Core R F) (hS : SchurAll R) (hF : R.FullP)
    (i : Fin D.R.m) (t : T) (P : Pl D.host.E) (hG : Good R t P) (hP : Formalism.DivisionValues.conjPl P = P) (cV : List ℤ →₀ ℂ) :
    ∃ cW, MatchW R i t P cV cW := by
  have hU := GlobalTheory.T.splittingCharacters_unramified_offLevels R F hC.lev t P hG
  have u1 : UnrPl P (R.toLevCh.mu t ((i : ℕ) + 1)) := hU.2 ((i : ℕ) + 1) (by omega) i.2
  have hV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have hWr : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have ht : Odd D.R.t := D.R.t_odd
  have hfix : VacFix R.ψ (R.ωP i t) P := by
    refine GlobalTheory.VacFixInert.vacFix_of_inert _ _ P (hF i t).inert ?_ ?_ hP u1 (GlobalTheory.VacFixInert.unrPl_mul_inv' u1 hU.1)
    · rw [hV, hWr]; have := ht.pos; omega
    · left; rw [hV]; exact GlobalTheory.VacFixInert.r_odd.add_odd ht
  have hc : SphCorr R.ψ (R.ωP i t) P := GlobalTheory.T.sphericalThetaCorrespondence_inertPlace_of_howe hH R.ψ _ _ _ _ _ P (hC.thP.ωP i t) hP hfix
  exact (hc.2.2 (dualC cV)).imp fun cW h => GlobalTheory.T.thetaLiftGoodProjector_intertwines_matchedHecke R F hC hS i t P hG hfix cV cW h

theorem partner_split (R : RealDat D A Ks) (F : Face D A) (hC : Core R F) (hS : SchurAll R)
    (i : Fin D.R.m) (t : T) (P : Pl D.host.E) (hG : Good R t P) (hP : Formalism.DivisionValues.conjPl P ≠ P) (k : ℕ) (hk : k ≤ (Vc D i).rank) :
    ∃ cW, MatchW R i t P (Finsupp.single (splitLab (Vc D i).rank k) 1) cW := by
  have hU := GlobalTheory.T.splittingCharacters_unramified_offLevels R F hC.lev t P hG
  obtain ⟨e, he⟩ := GlobalTheory.ParahoricLift.exists_isIdemAt (GlobalTheory.ThetaPrimeHecke.not_isConjPl hP)
  obtain ⟨ϖ, hϖ1, hϖ2, hϖ3⟩ := GlobalTheory.ThetaPrimeHecke.exists_unif P
  have hϖ0 : (ϖ : D.host.E) ≠ 0 := fun h => by
    rw [h, map_zero] at hϖ3
    exact WithZero.exp_ne_zero hϖ3.symm
  have hee : e * e = e := he.1.1
  have hx' : ((Formalism.L2.JoinChr.locU hee (Units.mk0 _ hϖ0) : (AE D)ˣ) : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) := by
    show Formalism.L2.JoinChr.locE D e (Units.mk0 _ hϖ0 : D.host.Eˣ) = _
    rw [Formalism.L2.JoinChr.locE, Units.val_mk0]
    ring
  have hun1 := hU.2 ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2
  have hM := GlobalTheory.T.thetaVacuum_heckeIdentity_splitPlace R.ψ _ _ _ _ _ P (hC.thP.ωP i t) hP hun1 (GlobalTheory.ThetaPrimeHecke.unrPl_mul_inv hun1 hU.1)
  have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hV : (Vc D i).rank = (Wc D i).rank + D.R.t := by
    rw [hW]
    exact D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  exact ⟨_, GlobalTheory.T.thetaLiftGoodProjector_intertwines_matchedHecke R F hC hS i t _ hG hM.1 _ _ ((hM.2 e ϖ _ D.R.t he hϖ1 hϖ2 hx').2 hV k hk)⟩

theorem exists_isSF (R : RealDat D A Ks) : ∃ SF, IsSF R SF := by
  classical
  refine ⟨R.Pg.image fun P => P.under (𝓞 D.host.F), fun v => ?_⟩
  rw [Finset.mem_image]
  exact exists_congr fun P => and_congr_right fun _ => HeightOneSpectrum.ext_iff

theorem adj_single {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    {ok : Pl D.host.E → Prop} {h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ H} (hn : NormalFam ok h) {P : Pl D.host.E}
    (hP : ok P) (d : List ℤ) : LinearMap.adjoint (h P (Finsupp.single d 1)) = h P (Finsupp.single (dualLab d) 1) := by
  have := hn.2 P hP (Finsupp.single d 1)
  rw [Finsupp.mapRange_single, star_one, dualC, Finsupp.mapDomain_single] at this
  exact this

theorem NormalFam.normal {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    {ok : Pl D.host.E → Prop} {h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ H} (hn : NormalFam ok h) {P : Pl D.host.E}
    (hP : ok P) (c : List ℤ →₀ ℂ) : Commute (h P c) (LinearMap.adjoint (h P c)) := by
  rw [hn.2 P hP c]
  exact hn.1 P P hP hP _ _

theorem eig_of_match (R : RealDat D A Ks) (F : Face D A) (hC : Core R F) (hS : SchurAll R) (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ)
    (i : Fin D.R.m) (t : T) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV i t).H) (hh : IsOpsV R i t h)
    (hN : NormalFam (Good R t) h)
    (P : Pl D.host.E) (hG : Good R t P) (cV : List ℤ →₀ ℂ) (hM : ∃ cW, MatchW R i t P cV cW) (l : ℂ) (y : (R.HV i t).H)
    (hy : h P cV y = l • y) :
    h P cV (LinearMap.adjoint (R.thG i t) (R.thG i t y)) = l • LinearMap.adjoint (R.thG i t) (R.thG i t y) := by
  refine hM.elim fun cW hM => (exists_isSF R).elim fun SF hSF => (GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R F hC hS hX SF hSF i).elim fun hW hhW => ?_
  have hP0 : Good R A.μ0 P := ((GlobalTheory.T.theta_lift_levels_good_primes_properties R F hC.lev).2.1 t P hG).2.2
  have key := (GlobalTheory.SysW.matched_operators_theta_intertwine R F hC hS hX SF hSF i t P hG cV cW hM h hh).1 hW hhW.1
  exact GlobalTheory.T.eigenvector_adjoint_intertwiner_normal_operators (R.thG i t) (fun _ : Unit => h P cV) (fun _ : Unit => hW P cW) (fun _ u => key u)
    (fun _ => NormalFam.normal hN hG cV) (fun _ => NormalFam.normal hhW.2.1 hP0 cW) () l _
    ((key y).symm.trans ((congrArg (R.thG i t) hy).trans (map_smul _ _ _)))

theorem eig_of_split {V : HSp D} {X : Type} [AddCommGroup X] [Module ℂ X] (π : GA D V →* Module.End ℂ X)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (E : H →ₗ[ℂ] X)
    (hinj : Function.Injective E) (ok : Pl D.host.E → Prop) (P : Pl D.host.E) (hok : ok P) (hP : Formalism.DivisionValues.conjPl P ≠ P)
    (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ H) (hN : NormalFam ok h)
    (ho : ∀ c x, opOf π P c (E x) = E (h P c x)) (hfix : ∀ x, ∀ k ∈ hyp V P, π k (E x) = E x)
    (s : List ℤ → ℂ) (y u : H) (hy0 : y = 0 → u = 0) (hy : ∀ d, IsLab V P d → h P (Finsupp.single d 1) y = s d • y)
    (hu : ∀ k, k ≤ V.rank → ∀ l : ℂ, h P (Finsupp.single (splitLab V.rank k) 1) y = l • y →
      h P (Finsupp.single (splitLab V.rank k) 1) u = l • u) (d : List ℤ) (hd : IsLab V P d) :
    h P (Finsupp.single d 1) u = s d • u := by
  by_cases hy00 : y = 0
  · rw [hy0 hy00, map_zero, smul_zero]
  have h1 : ∀ d, ∃ l : ℂ, h P (Finsupp.single d 1) y = l • y := fun d => by
    by_cases hd : IsLab V P d
    · exact ⟨_, hy d hd⟩
    · refine ⟨0, hinj ?_⟩
      rw [← ho, GlobalTheory.Hk3.LabDet.opOf_single_of_not π P d hd, zero_smul, map_zero]
      rfl
  have hs : ∀ x ∈ {x : Module.End ℂ X | ∃ k, k ≤ V.rank ∧
      (x = opOf π P (Finsupp.single (splitLab V.rank k) 1) ∨ x = opOf π P (Finsupp.single (dualLab (splitLab V.rank k)) 1))},
      ∃ l : ℂ, x (E y) = l • E y ∧ x (E u) = l • E u := by
    rintro x ⟨k, hk, rfl | rfl⟩
    · obtain ⟨l, hl⟩ := h1 (splitLab V.rank k)
      exact ⟨l, by rw [ho, hl, map_smul], by rw [ho, hu k hk l hl, map_smul]⟩
    · obtain ⟨l, hl⟩ := h1 (splitLab V.rank k)
      have e := adj_single hN hok (splitLab V.rank k)
      have nn := NormalFam.normal hN hok (Finsupp.single (splitLab V.rank k) 1)
      exact ⟨star l, by rw [ho, ← e, adjoint_eig _ nn l y hl, map_smul],
        by rw [ho, ← e, adjoint_eig _ nn l u (hu k hk l hl), map_smul]⟩
  obtain ⟨a, ha1, ha2⟩ := GlobalTheory.T.exists_adjoin_splitHeckeGenerators_duals_spherical V P hP X π d
  obtain ⟨l, e1, e2⟩ := GlobalTheory.Hk3.LabDet.adjoin_common _ (E y) (E u) hs a ha1
  rw [ha2 _ (hfix y), ho, hy d hd, map_smul] at e1
  rw [ha2 _ (hfix u), ho, ← map_smul] at e2
  rw [smul_left_injective ℂ (fun h0 => hy00 (hinj (h0.trans (map_zero _).symm))) e1]
  exact hinj e2

theorem eig_keep (hH : HoweUnram) (R : RealDat D A Ks) (F : Face D A) (hC : Core R F) (hS : SchurAll R)
    (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (hF : R.FullP) (i : Fin D.R.m) (t : T)
    (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV i t).H) (hh : IsOpsV R i t h) (s : Sys D) (y : (R.HV i t).H)
    (hy : IsEigV R i t h s y) : IsEigV R i t h s (LinearMap.adjoint (R.thG i t) (R.thG i t y)) := by
  have XV := (GlobalTheory.T.realization_family_normal_operators R F hC.lev hC.fam hC.models).2 i t
  obtain ⟨h', hh', hN⟩ := XV
  have e : ∀ P, Good R t P → ∀ c x, h P c x = h' P c x := fun P hP c x =>
    (hC.models.HV i t).1 ((hh P hP c x).trans (hh' P hP c x).symm)
  have hy' : IsEigV R i t h' s y := fun P d hP hd => (e P hP _ y).symm.trans (hy P d hP hd)
  intro P d hG hd
  refine (e P hG _ _).trans ?_
  by_cases hP : Formalism.DivisionValues.conjPl P = P
  · exact eig_of_match R F hC hS hX i t h' hh' hN P hG _ (partner_inert hH R F hC hS hF i t P hG hP _) _ y (hy' P d hG hd)
  refine (hC.lev.βV i).elim fun n hn => ?_
  have hn' : IsBaseFrame (Vc D i) (R.βV i) (R.ΛV i) 1 := (one_pow n : (1 : ℕ) ^ n = 1) ▸ hn
  exact eig_of_split (GlobalTheory.DefiniteOps.rtr (GlobalTheory.SplitHeckeAdj.fin (Vc D i)) (R.cV i).W) (R.HV i t).e
    (hC.models.HV i t).1 (Good R t) P hG hP h' hN
    (fun c x => ((hh' P hG c x).trans (GlobalTheory.DefiniteOps.hkF_eq (Vc D i) P c _)).symm)
    (fun x => GlobalTheory.DefiniteOps.fixed_of_mem (Vc D i) (R.βV i) (R.ΛV i) (R.datVt i t) hn' P hG (R.cV i).coef.ρ _
      ((hC.models.HV i t).2.1.le ⟨x, rfl⟩))
    (s P) y _ (fun h0 => (congrArg (fun z => LinearMap.adjoint (R.thG i t) (R.thG i t z)) h0).trans
      ((congrArg (LinearMap.adjoint (R.thG i t)) (R.thG i t).map_zero).trans (LinearMap.adjoint (R.thG i t)).map_zero))
    (fun d hd => hy' P d hG hd)
    (fun k hk l hl => eig_of_match R F hC hS hX i t h' hh' hN P hG _ (partner_split R F hC hS i t P hG hP k hk) l y hl) d hd

theorem eig_add {H : Type} [AddCommGroup H] [Module ℂ H] (L : Module.End ℂ H) (l : ℂ) {a b : H} (ha : L a = l • a)
    (hb : L b = l • b) : L (a + b) = l • (a + b) := by rw [map_add, ha, hb, smul_add]

theorem eig_smul {H : Type} [AddCommGroup H] [Module ℂ H] (L : Module.End ℂ H) (l z : ℂ) {a : H} (ha : L a = l • a) :
    L (z • a) = l • (z • a) := by rw [map_smul, ha, smul_comm]

theorem eig_zero {H : Type} [AddCommGroup H] [Module ℂ H] (L : Module.End ℂ H) (l : ℂ) : L 0 = l • (0 : H) := by
  rw [map_zero, smul_zero]

theorem fix_add {H X W : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup W] [Module ℂ W] (T : (X → ℂ) →ₗ[ℂ] (X → ℂ))
    (E : H →ₗ[ℂ] (X → W)) (l : W →ₗ[ℂ] ℂ) {a b : H} (ha : T (fun x => l (E a x)) = fun x => l (E a x))
    (hb : T (fun x => l (E b x)) = fun x => l (E b x)) : T (fun x => l (E (a + b) x)) = fun x => l (E (a + b) x) := by
  have e : (fun x => l (E (a + b) x)) = (fun x => l (E a x)) + fun x => l (E b x) := by
    funext x; simp
  rw [e, map_add, ha, hb]

theorem fix_smul {H X W : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup W] [Module ℂ W] (T : (X → ℂ) →ₗ[ℂ] (X → ℂ))
    (E : H →ₗ[ℂ] (X → W)) (l : W →ₗ[ℂ] ℂ) (z : ℂ) {a : H} (ha : T (fun x => l (E a x)) = fun x => l (E a x)) :
    T (fun x => l (E (z • a) x)) = fun x => l (E (z • a) x) := by
  have e : (fun x => l (E (z • a) x)) = z • fun x => l (E a x) := by
    funext x; simp
  rw [e, map_smul, ha]

theorem fix_zero {H X W : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup W] [Module ℂ W] (T : (X → ℂ) →ₗ[ℂ] (X → ℂ))
    (E : H →ₗ[ℂ] (X → W)) (l : W →ₗ[ℂ] ℂ) : T (fun x => l (E 0 x)) = fun x => l (E 0 x) := by
  have e : (fun x => l (E 0 x)) = 0 := by
    funext x; simp
  rw [e, map_zero]

def goodEig (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV i t).H)
    (s : Sys D) : Submodule ℂ (R.HV i t).H where
  carrier := {y | IsEigV R i t h s y ∧ GoodVt R i t y}
  add_mem' := fun {a b} ha hb => ⟨fun P d hP hd => eig_add _ _ (ha.1 P d hP hd) (hb.1 P d hP hd),
    fun l => fix_add _ (R.extV i t) l (ha.2 l) (hb.2 l)⟩
  zero_mem' := ⟨fun P d _ _ => eig_zero _ _, fun l => fix_zero _ (R.extV i t) l⟩
  smul_mem' := fun z {a} ha => ⟨fun P d hP hd => eig_smul _ _ z (ha.1 P d hP hd), fun l => fix_smul _ (R.extV i t) l z (ha.2 l)⟩

theorem saturated : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, TypeNZ R i t → DownEig R i t → GoodMem R i t → GlobalTheory.RawLift.UpInj R i t → UnrCorr R i t (fun _ => True) → ParamsEx R i t → Saturated R i t := by
  intro hD hH D G _ _ Pl0 T A Ks _ _ _ R F hG hF i t hNZ hDE hGM _ _ _ h hh s hs
  have hS : SchurAll R := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hD R
  have hE := GlobalTheory.Hk3.eH_laws R F hG.core hG.irr i
  refine (hDE h hh s).imp fun c hc y hy1 hy2 => ?_
  refine (exists_adjoint_comp (R.thG i t) (goodEig R i t h s)
    (fun u hu => ⟨eig_keep hH R F hG.core hS hG.irr hF i t h hh s u hu.1, good_adjoint R F hG.core i t _ (hE.2.2.2 t u)⟩)
    (fun u hu => hNZ h hh s hs u hu.1 hu.2) y ⟨hy1, hy2⟩).elim fun u hu => ?_
  exact ⟨R.thG i t u, ⟨(hGM u hu.1.2).symm ▸ hc u hu.1.1, (hE.2.2.1 _).1 (hE.2.2.2 t u)⟩, hu.2⟩

end GlobalTheory.DownLift.Sat

end
