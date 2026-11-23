import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.BlockTheory.RationalLaws.RationalAdjointLaw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConstOfConstOnDictLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivAtRecordOfEquivRow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGroupActsByLiftTranslationPrincipalType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstRelIffTwistFactorAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoeffRoots
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionMemCuspForms
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCovPinNotIsXiDet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.ExistsCovPinIff
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.OfBeforeProjector

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.OneMapRefCompare

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeDeterminantCharacters
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

abbrev unitCov (d : DeltaDat Xo c n) : DeltaDat Xo c n := { d with cδ := 1 }

theorem evR_one {S : Type} [CommRing S] [IsReduced S] [Algebra c.F S] (y : FrPt Xo c S) : evR Xo c 1 y = 1 :=
  evalAt_one _ _ y (GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c S y)

theorem evR_smul {S : Type} [CommRing S] [Algebra c.F S] (a : c.F) (f : Rul Xo c) (y : FrPt Xo c S) :
    evR Xo c (a • f) y = algebraMap c.F S a * evR Xo c f y := evalAt_smul _ _ a f y

theorem covPin_unitCov {d : DeltaDat Xo c n} (h : CovPin Xo c fun _ : Unit => d) :
    CovPin Xo c fun _ : Unit => unitCov d := fun t => by
  obtain ⟨⟨l1, l2, l3, l4, l5, l6, l7, -, -⟩, h2, h3⟩ := h t
  exact ⟨⟨l1, l2, l3, l4, l5, l6, l7, GlobalTheory.LevelCover.one_mem_sec_zero _ _, fun k _ _ _ y => by
    rw [show (unitCov d).cδ = 1 from rfl, evR_one]; exact one_ne_zero⟩, h2, h3⟩

theorem trace_value {K L : Type} [Field K] [CharZero K] [Field L] [Algebra K L] [Module.Finite K L] [Algebra K ℂ] (x : L) (c0 : ℂ)
    (h : ∀ j : L →ₐ[K] ℂ, j x = c0) : ∃ u : K, algebraMap K ℂ u = c0 := by
  have h1 := trace_eq_sum_embeddings ℂ (K := K) (L := L) (x := x)
  simp only [h, Finset.sum_const, Finset.card_univ, AlgHom.card, nsmul_eq_mul] at h1
  have h2 : (Module.finrank K L : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  exact ⟨Algebra.trace K L x / Module.finrank K L, by rw [map_div₀, h1, map_natCast]; field_simp⟩

theorem eq_const_of_complex (σ : c.F →+* ℂ) {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0) (c0 : ℂ)
    (h : ∀ y : FrPt Xo c (CAt σ), toC (evR Xo c f y) = c0) (y : FrPt Xo c (CAt σ)) :
    ∃ u : c.F, σ u = c0 ∧ f = u • 1 := by
  have hB := GlobalTheory.firstFiveLaws.1.secBaseChange
  haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  haveI : Nontrivial (CAt σ) := inferInstanceAs (Nontrivial ℂ)
  obtain ⟨p, φ, y₀, -⟩ := GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c _ y
  obtain ⟨m, hm, -⟩ := Ideal.exists_le_maximal (RingHom.ker φ.toRingHom) (RingHom.ker_ne_top _)
  letI : Algebra c.F ℂ := σ.toAlgebra
  letI := Ideal.Quotient.field m
  haveI : Module.Finite c.F (p.R ⧸ m) := finite_of_finite_type_of_isJacobsonRing c.F _
  obtain ⟨u, hu⟩ := trace_value (K := c.F) (Ideal.Quotient.mk m (f p y₀)) c0 fun j => by
    let ψ : p.R →ₐ[c.F] CAt σ := (j.comp (Ideal.Quotient.mkₐ c.F m) : p.R →ₐ[c.F] ℂ)
    obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c _ _ ψ y₀
    exact (GlobalTheory.ShortSpanCompare.evR_of_frMap hf ψ hz).symm.trans (h z)
  refine ⟨u, hu, GlobalTheory.CoverPinCompare.eq_of_complex σ hf
    (Submodule.smul_mem _ u (GlobalTheory.LevelCover.one_mem_sec_zero _ _)) fun z => ?_⟩
  rw [evR_smul, evR_one, mul_one]
  exact (h z).trans hu.symm

variable {Cl : Type} [Fintype Cl] {Vs : Type} [AddCommGroup Vs] [Module c.F Vs]

theorem isThClsD_const {d : DeltaDat Xo c n} {u : c.F} (hu : u ≠ 0) (hd : d.cδ = d.eF u • 1)
    (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F)
    (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (x : Cl → Vs) (f : Rul Xo c) :
    IsThClsD Xo c d w La Nc gam vol ep io x (u • f) ↔ IsThClsD Xo c (unitCov d) w La Nc gam vol ep io x f := by
  refine forall_congr' fun k => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun hk => forall_congr' fun y => forall_congr' fun y₂ => forall_congr' fun _ => exists_congr fun vc =>
      and_congr_right fun _ => ?_
  have h1 : evR (unitCov d).Xo₂ (unitCov d).c₂ (unitCov d).cδ y₂ = 1 := evR_one y₂
  rw [h1, hd, evR_smul, evR_smul, evR_one, hk, mul_one, one_mul]
  exact mul_right_inj' ((map_ne_zero _).2 hu)

end Cover

section Core

variable {D : D7}

theorem actLev_mem_cuspA {T : Core D} (h : LawsM T) {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j) {G : Type} [Group G]
    {lev : G → ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La) × ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La)}
    (hL : ActLev (Xo := T.Q.Xo j) T.Q.c lev) (γ : G) {f : T.R j} (hf : f ∈ T.cuspA j (wtA w) w.n) :
    actLev (Xo := T.Q.Xo j) T.Q.c lev γ f ∈ T.cuspA j (wtA w) w.n := by
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    have := (GlobalTheory.Member.exists_iotaOK D T.Q h.pins _ hj).2
    omega
  obtain ⟨hs, hc⟩ := (mem_cusp _ _ _ _ _ _).1 hf
  have hg := GlobalTheory.LevelEquivCompare.actLev_mem_sec hL γ hs
  refine (mem_cusp _ _ _ _ _ _).2 ⟨hg, fun σ hσ => holCusp_mem_holSub _ _ fun k => ?_⟩
  have hU := h.unf j hj σ hσ
  refine GlobalTheory.LevelCusp.rdU_mem_SS (U := Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hσ hU (hU.1 ▸ hpq)
    (fun k k' τ => (h.xiAbs j hj σ hσ k τ).trans (h.xiAbs j hj σ hσ k' τ).symm) (dom_wtA w) hs hg
    (fun k => GlobalTheory.CuspSecFin.mem_SS_of_mem_holSub _ _ (hc σ hσ) k) (fun y => ?_) k
  obtain ⟨ρ, ν, -, -, hm⟩ := mvPt_spec hL.total γ y
  exact ⟨ρ, ν, _, hm, evalAt_actL hL (h.evalWD j hj) frMap_trans_id γ hs.1 y⟩

variable (T : CoreJ D) (i : Fin D.R.m) {c' : Coeff T.Q.l} (hle : T.Q.c.F ≤ c'.F)
  (hV : T.V ((i : ℕ) + 1) (sigB T hle) = Wc D i)

theorem adC'_leftInv (h : LawsM T.toCore) (a : (D.host.E →+* ℂ) × ℕ → ℕ) {n : ℕ} (hd : Dom a n) (cc : Cmp T i hle → ℂ)
    {f : Rul (T.Q.Xo ((i : ℕ) + 1)) c'} (hf : f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) c' a n) :
    ∀ γ ∈ GQ (Wc D i), ∀ g, adC' T i hle hV a cc f (γ * g) = adC' T i hle hV a cc f g := by
  obtain ⟨m, as, fs, hfs, hBC⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ hle).1 a n f hf
  have e : ∀ g, adC' T i hle hV a cc f g = ∑ k, c'.F.val.toRingHom (as k) * ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℂ) *
      adel (Wc D i) (castDict hV (T.dict _ _)) (muPin (Wc D i) (castDict hV (T.dict _ _)) (castDict hV (T.mu _ _)) cc)
        (rdU (T.U _ _) (fs k)) g) := fun g => by
    refine (congrArg (_ * ·) (GlobalTheory.PhaseRational.rdU_of_isBC hle _ _ hBC _ _)).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [adel_muPin]
    unfold castDict toDict
    ring
  intro γ hγ g
  rw [e, e]
  exact Finset.sum_congr rfl fun k _ => congrArg (_ * ·) (congrArg (_ * ·)
    (GlobalTheory.PhaseRational.adel_muPin_leftInv h (GlobalTheory.LevelEquivCompare.inR i) (σ := sigB T hle) T.toCore.good_σ₀ hV cc hd (hfs k)
      γ hγ g))

theorem adC'_smul (a : (D.host.E →+* ℂ) × ℕ → ℕ) (cc : Cmp T i hle → ℂ) (u : c'.F)
    (f : Rul (T.Q.Xo ((i : ℕ) + 1)) c') (g : GA D (Wc D i)) :
    adC' T i hle hV a cc (u • f) g = (u : ℂ) * adC' T i hle hV a cc f g := by
  unfold adC' adFn
  rw [map_smulₛₗ]
  change _ * ((u : ℂ) * _) = _
  ring

include hV in
set_option maxHeartbeats 1000000 in

theorem exists_cover_dict (hT : LawsJ T) {n : ℕ} (d : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' n) (hA : d.l₂.A = 1) (h1 : d.cδ = 1) :
    ∃ (U₂ : Unf d.Xo₂ d.c₂ ((inC c').comp (d.eF.symm : d.c₂.F →+* c'.F)) D.R.r)
      (dict₂ : GA D (Wc D i) → Σ k, Frame (U₂.X k).Ψ D.R.r),
      CXiVal (Wc D i) (rank_Wc i) (inC c') (fun _ : Unit => d) (fun _ => U₂) (fun _ => dict₂) (iotaW T i)
        (T.x₀ ((i : ℕ) + 1) (sigB T hle)) (fun _ => 1) ∧ ∀ k, ModelW (Wc D i) (rank_Wc i) (U₂.X k) := by
  have hj := GlobalTheory.LevelEquivCompare.inR i
  have hpos : 1 ≤ (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q := by
    have := (GlobalTheory.Member.exists_iotaOK D T.Q hT.pins _ hj).2
    omega
  obtain ⟨hio, hx₀⟩ := GlobalTheory.TupleCover.iotaOK_and_frame T hT _ hj (sigB T hle) rfl (Wc D i) hV (rank_Wc i)
  have hg₂ : GoodEmb d.c₂ ((inC c').comp (d.eF.symm : d.c₂.F →+* c'.F)) := rfl
  obtain ⟨C, hC, hCι, hCx⟩ := (GlobalTheory.Member.exists_ctx D _ _ d.l₂ d.Xo₂ d.c₂ _ _ _ (rank_Wc i) _ hio hpos hA hg₂).2.2 _ hx₀
  obtain ⟨Kf, hKf⟩ := (GlobalTheory.Member.PrincLevel.exists_levelK_and_nhds D (Wc D i) d.l₂.M).1
  obtain ⟨un, dict, mu, -, -, hP⟩ := GlobalTheory.Member.exists_pkgLaws D _ _ _ _ _ _ _ _ C hC Kf hKf 1
    ⟨continuous_const, fun _ => rfl⟩ (fun _ => rfl)
  obtain ⟨g, e, F, ik, φ, th, hth, hdu, hdl⟩ := hP.dictLaws
  refine ⟨C.unf un, dict, ⟨1, ⟨1, one_pos, one_pow 1⟩, fun _ => ⟨hP.unf, hP.modelW, g, e, F, ik, φ, th, hth, ?_,
    fun h γ _ => ?_⟩⟩, hP.modelW⟩
  · rw [hCι, hCx] at hdl
    exact hdl
  · haveI : IsReduced (CAt ((inC c').comp (d.eF.symm : d.c₂.F →+* c'.F))) := inferInstanceAs (IsReduced ℂ)
    refine (dif_pos (hdu.2.2.2.1 h)).trans ?_
    rw [h1, evR_one]
    exact (one_mul (1 : ℂ)).symm

end Core

section Clauses

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}
  (O : OMDat T.toCore R i Unit fun _ => A.μ0) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : (R.MW i (sg0 D A)).Vec)

set_option maxHeartbeats 1000000 in

theorem cover_const (hT : LawsJ T) (hL : R.toLevCh.Is A.μ0)
    (hP : O.Pins κ v₀ (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) :
    ∃ u : O.c'.F, (∃ m : ℕ, 0 < m ∧ u ^ m = 1) ∧ (O.dδ ()).cδ = (O.dδ ()).eF u • 1 := by
  have hj := GlobalTheory.LevelEquivCompare.inR i
  have hpos : 1 ≤ (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q := by
    have := (GlobalTheory.Member.exists_iotaOK D T.Q hT.pins _ hj).2
    omega
  obtain ⟨hio, hx₀⟩ := GlobalTheory.TupleCover.iotaOK_and_frame T hT _ hj O.s0 rfl (Wc D i) O.hV (rank_Wc i)
  obtain ⟨c0, ⟨m, hm, hc⟩, H⟩ := hP.cxi
  obtain ⟨hU, hW, g, e, F, ik, φ, th, hth, hdl, hval⟩ := H ()
  have hv : ∀ h, rdU (O.U₂ ()) (O.dδ ()).cδ (O.dict₂ () h).1 (O.dict₂ () h).2 = c0 := fun h => by
    obtain ⟨γ, h1, h2, h3, -⟩ := hdl.2 h
    obtain ⟨x, hx⟩ := (GlobalTheory.Member.isDetRoot_laws D (Wc D i)).1 (γ * h)
    rw [hval h γ ⟨h1, h2, h3⟩, (hP.tuple ()).xi _ x hx,
      GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi A.μ0) x, Circle.coe_one, mul_one]
  have hs := (hP.cov ()).1.2.2.2.2.2.2.2.1
  have hd : (O.dict₂ () 1).2 ∈ ((O.U₂ ()).X (O.dict₂ () 1).1).dom := by
    by_contra hd
    have h0 : c0 = 0 := (hv 1).symm.trans (dif_neg hd)
    rw [h0, zero_pow hm.ne'] at hc
    exact zero_ne_one hc
  obtain ⟨u, hu, hf⟩ := eq_const_of_complex _ hs c0 (GlobalTheory.Member.const_of_const_on_dictLat D _ _ _ _ _ _ _ _ _ (O.U₂ ()) (O.dict₂ ()) _ g e F ik φ th _
    hio hpos (hP.cov ()).2.1 rfl hx₀ hU hW hth hdl _ hs c0 hv) ((O.U₂ ()).un _ ⟨_, hd⟩)
  refine ⟨(O.dδ ()).eF.symm u, ⟨m, hm, (inC O.c').injective ?_⟩, by rw [AlgEquiv.apply_symm_apply]; exact hf⟩
  rw [map_pow, map_one]
  exact (congrArg (· ^ m) hu).trans hc

variable (cc : Cmp T i O.hle → ℂ)

theorem adC_eq_phi (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R ((i : ℕ) + 1)) (g : GA D (Wc D i)) :
    adC T i O.hle O.hV a cc f g = (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℂ) * O.phi cc f g := by
  change cc _ * _ * _ * _ = _ * (cc (O.dict g).1 * O.mu g * _)
  rw [mul_comm (cc _), mul_assoc, mul_assoc, mul_assoc]
  rfl

theorem equivAt_iff (hT : LawsM T.toCore) (hL : ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c O.lev2) :
    O.EquivAt κ cc ↔ LevelLaw T R i O.hle O.hV (wtA κ) κ.n O.lev2 cc := by
  have h0 : (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (lieFac_pos _ _ _).ne'
  refine ⟨fun H g k hk f hf x => ?_, fun H g k hk f hf =>
    ⟨actLev_mem_cuspA hT (GlobalTheory.LevelEquivCompare.inR i) κ hL g hf, fun x => mul_left_cancel₀ h0 ?_⟩⟩
  · rw [adC_eq_phi, adC_eq_phi, (H g k hk f hf).2 x, mul_left_comm]
    rfl
  · have := H g k hk f hf x
    rw [adC_eq_phi, adC_eq_phi] at this
    rw [this, mul_left_comm]
    rfl

theorem jFn_eq (a : (D.host.E →+* ℂ) × ℕ → ℕ) (ze : ℂ) (f : Rul (T.Q.Xo ((i : ℕ) + 1)) O.c') (q : AutQ (Wc D i)) :
    ze * cc (O.dict q.out).1 * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℂ) *
      jFn (Wc D i) (inC O.c') (rdU (unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c'))) O.dict O.mu f q =
        ze * adC' T i O.hle O.hV a cc f q.out := by
  change _ * (O.mu q.out * _) = ze * (cc (O.dict q.out).1 * _ * O.mu q.out * _)
  simp only [mul_assoc]
  rfl

variable (h : O.Cl' () → GA D (Vc D i))

abbrev ClassSum (n : ℕ) (ph : ℂ) (z : G) : Prop :=
  ClassSumLaw T R i O.hle O.hV (wtA κ) n v₀ O.lev2 O.c0' O.io (unitCov (O.dδ ())) h (O.La ()) (O.Nc ()) (O.gam ()) (O.vol ())
    (O.ep ()) (O.w ()) cc ph z

set_option maxHeartbeats 1000000 in

theorem identity_iff (hT : LawsM T.toCore) (hL : ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) O.c' O.lev2) (hmem : R.thP_thF_mem)
    (hn : κ.n = (Vc D i).rank) (hA : ThAdIs R i A.μ0 h O.c0' v₀ (O.thAd ()))
    (hPl : ∀ x, O.Plc () x ↔ ∃ x₀, Place R i A.μ0 h O.c0' (jVx R i A.μ0 x₀) x)
    {u : O.c'.F} (hu : u ≠ 0) (hd : (O.dδ ()).cδ = (O.dδ ()).eF u • 1) (ph : ℂ) :
    GlobalTheory.PhaseRational.IdentityAt O κ cc ph ↔ (∀ k, ‖cc k‖ = 1) ∧ ‖ph‖ = 1 ∧ ∃ z ∈ Subgroup.center G,
      ∃ ze ∈ D.what₂.embLL.toRatAlgHom.fieldRange, (∃ m : ℕ, 0 < m ∧ ze ^ m = 1) ∧
        ClassSum O κ v₀ cc h κ.n ((ze * u)⁻¹ * ph) z := by
  have hdom := dom_wtA κ
  rw [hn] at hdom ⊢
  refine and_congr_right fun _ => and_congr_right fun _ => exists_congr fun z => and_congr_right fun _ => ?_
  rw [Unique.forall_iff]
  refine exists_congr fun ze => and_congr_right fun _ => and_congr_right fun ⟨m, hm, hz⟩ => ?_
  have h0 : ze * (u : ℂ) ≠ 0 := mul_ne_zero (fun e => by rw [e, zero_pow hm.ne'] at hz; exact zero_ne_one hz)
    (fun e => hu (Subtype.ext e))
  have key := isThClsD_const hu hd (O.w ()) (O.La ()) (O.Nc ()) (O.gam ()) (O.vol ()) (O.ep ()) O.io
  have key' := fun x f => (key x (u⁻¹ • f)).symm.trans (iff_of_eq (congrArg _ (smul_inv_smul₀ hu f)))
  constructor
  · intro H x₀ x hx
    obtain ⟨⟨f, hf, hc⟩, H2⟩ := H x ((hPl x).2 ⟨x₀, hx⟩)
    refine ⟨⟨u⁻¹ • f, Submodule.smul_mem _ _ hf, (key' x f).2 hc⟩, fun f hf hc => ?_⟩
    refine GlobalTheory.PhaseRational.eq_of_out (fun γ hγ g => congrArg (_ * ·)
      (GlobalTheory.PhaseRational.mult_leftInv (hmem i A.μ0 _) v₀ γ hγ g))
      (adC'_leftInv T i O.hle O.hV hT _ hdom cc (GlobalTheory.LevelEquivCompare.actLev_mem_sec hL z hf)) fun q => ?_
    have e := (H2 (u • f) (Submodule.smul_mem _ _ hf) ((key x f).2 hc) q).trans (jFn_eq O cc _ ze _ q)
    rw [map_smul, adC'_smul, ← mul_assoc, show O.thAd default x = _ from hA _ x hx] at e
    rw [mul_assoc, inv_mul_eq_iff_eq_mul₀ h0]
    exact e
  · intro H x hx
    obtain ⟨x₀, hx⟩ := (hPl x).1 hx
    obtain ⟨⟨f, hf, hc⟩, H2⟩ := H x₀ x hx
    refine ⟨⟨u • f, Submodule.smul_mem _ _ hf, (key x f).2 hc⟩, fun f hf hc q => ?_⟩
    have e := H2 (u⁻¹ • f) (Submodule.smul_mem _ _ hf) ((key' x f).2 hc) q.out
    rw [mul_assoc, inv_mul_eq_iff_eq_mul₀ h0, mul_assoc, ← adC'_smul, ← map_smul, smul_inv_smul₀ hu] at e
    refine Eq.trans ?_ (jFn_eq O cc _ ze _ q).symm
    rw [show O.thAd default x = _ from hA _ x hx]
    exact e

set_option maxHeartbeats 1000000 in

theorem rationalLaw_iff (ph : ℂ) : RationalLaw T R i O.hle O.hV (wtA κ) κ.n v₀ cc ph ↔
    ∀ x : A.fam.amb.FL i A.μ0, GlobalTheory.PhaseRationalDegenerate.IsRat O κ cc (ph • R.thF i A.μ0 (jVx R i A.μ0 x) v₀) := by
  unfold RationalLaw GlobalTheory.PhaseRationalDegenerate.IsRat
  simp only [adC_eq_phi]
  refine forall_congr' fun x => exists_congr fun m => exists_congr fun a => ⟨fun H => ?_, fun H => ?_⟩
  · obtain ⟨fs, h1, h2⟩ := H
    exact ⟨fun s => ⟨fs s, h1 s⟩, h2⟩
  · obtain ⟨fs, h2⟩ := H
    exact ⟨fun s => fs s, fun s => (fs s).2, h2⟩

theorem phRat_of_rationalLaw (hE : O.EquivAt κ cc) (hχ : R.grp_chiW) (hG : R.thP_thG) {ph : ℂ}
    (H : RationalLaw T R i O.hle O.hV (wtA κ) κ.n v₀ cc ph) : O.PhRat κ v₀ cc ph :=
  GlobalTheory.PhaseRationalDegenerate.of_before_projector O κ v₀ cc hE hχ hG ph ((rationalLaw_iff O κ v₀ cc ph).1 H)

theorem rationalLaw_mul (b : D.what₂.LL) {ph : ℂ} (H : RationalLaw T R i O.hle O.hV (wtA κ) κ.n v₀ cc ph) :
    RationalLaw T R i O.hle O.hV (wtA κ) κ.n v₀ cc (D.what₂.embLL b * ph) :=
  (rationalLaw_iff O κ v₀ cc _).2 fun x => by
    rw [mul_smul]
    exact ((rationalLaw_iff O κ v₀ cc ph).1 H x).mul O κ cc b

end Clauses

section Rows

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}
  (O : OMDat T.toCore R i Unit fun _ => A.μ0) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : (R.MW i (sg0 D A)).Vec)
  (h : O.Cl' () → GA D (Vc D i))

def Reads : Prop :=
  ThAdIs R i A.μ0 h O.c0' v₀ (O.thAd ()) ∧ ∀ x, O.Plc () x ↔ ∃ x₀, Place R i A.μ0 h O.c0' (jVx R i A.μ0 x₀) x

abbrev SecondAt : Prop :=
  OneMapAt T R i O.hle O.hV (wtA κ) κ.n v₀ O.lev2 O.c0' O.io (unitCov (O.dδ ())) h (O.La ()) (O.Nc ()) (O.gam ()) (O.vol ())
    (O.ep ()) (O.w ())

abbrev SecondPins : Prop :=
  LiftPins T R i (wtA κ) v₀ O.lev2 O.c0' O.io O.jL ∧ CoverPins T R i (unitCov (O.dδ ())) ∧
    ClassPins T R i O.c0' (unitCov (O.dδ ())) h (O.La ()) (O.Nc ()) (O.gam ()) (O.vol ()) (O.ep ()) (O.w ())

theorem norm_of_root {z : ℂ} (h : ∃ m : ℕ, 0 < m ∧ z ^ m = 1) : ‖z‖ = 1 :=
  h.elim fun _ h => Complex.norm_eq_one_of_pow_eq_one h.2 h.1.ne'

set_option maxHeartbeats 1000000 in

theorem row_iff {F : Face D A} (hT : LawsJ T) (hC : R.Char F) (hn : κ.n = D.R.nV)
    (hF : O.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange) (hP : O.Pins κ v₀ (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0))
    (hR : Reads O v₀ h) : (∃ cc ph, O.OneMapOf κ v₀ cc ph) ↔ SecondAt O κ v₀ h := by
  obtain ⟨u, ⟨m, hm, hu⟩, hd⟩ := cover_const O κ v₀ hT hC.lev hP
  have hu0 : u ≠ 0 := fun e => by rw [e, zero_pow hm.ne'] at hu; exact zero_ne_one hu
  have hu1 : ‖(u : ℂ)‖ = 1 := norm_of_root ⟨m, hm, (map_pow (inC O.c') u m).symm.trans (by rw [hu, map_one])⟩
  have hu2 : (u : ℂ) ≠ 0 := fun e => hu0 (Subtype.ext e)
  obtain ⟨b, hb⟩ : ∃ b, D.what₂.embLL b = (u : ℂ) := hF.le u.2
  have hrk : κ.n = (Vc D i).rank := hn.trans (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).symm
  have hE := fun cc => equivAt_iff O κ cc hT.toLawsM hP.act.1
  have hI := fun cc => identity_iff O κ v₀ cc h hT.toLawsM hP.act.2 hC.thP.thF_mem hrk hR.1 hR.2 hu0 hd
  constructor
  · rintro ⟨cc, ph, h1, ⟨-, -, -, h2⟩, -⟩
    obtain ⟨c1, c2, z, hz, ze, ⟨b', hb'⟩, hze, h3⟩ := (hI cc ph).1 h2
    have h4 := (rationalLaw_iff O κ v₀ cc ph).2 fun x =>
      GlobalTheory.PhaseRational.lift_rational O κ v₀ cc ph hF hP hT.toLawsM hn hC.thP.thF_mem h1 h2 () A.μ0 rfl x
    refine ⟨cc, (ze * u)⁻¹ * ph, z, c1, ?_, hz, (hE cc).1 h1, h3, ?_⟩
    · rw [norm_mul, norm_inv, norm_mul, norm_of_root hze, hu1, c2]; simp
    · have := rationalLaw_mul O κ v₀ cc (b' * b)⁻¹ h4
      rwa [map_inv₀, map_mul, hb, show D.what₂.embLL b' = ze from hb'] at this
  · rintro ⟨cc, ph, z, c1, c2, hz, h1, h2, h3⟩
    have h4 := (hE cc).2 h1
    refine ⟨cc, u * ph, h4, ⟨hF.ge, (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ O.hle).2 _ _,
      (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ O.hle _ _ hP.act.1).2, (hI cc _).2
        ⟨c1, by rw [norm_mul, hu1, c2, one_mul], z, hz, 1, one_mem _, ⟨1, one_pos, one_pow 1⟩, ?_⟩⟩, ?_⟩
    · rw [one_mul, inv_mul_cancel_left₀ hu2]
      exact h2
    · rw [← hb]
      exact phRat_of_rationalLaw O κ v₀ cc h4 hC.grp.chiW hC.thP.thG (rationalLaw_mul O κ v₀ cc b h3)

set_option maxHeartbeats 1000000 in

theorem secondPins_of_pins {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ} (hP : O.Pins κ v₀ (iotaW T i) x₀) :
    ∃ h, Reads O v₀ h ∧ SecondPins O κ v₀ h := by
  obtain ⟨h, J', h1, h2, h3, h4⟩ := (hP.tuple ()).reps
  have e : embV D O.jL = fun τ => embF O.c' (tauE D τ) := funext fun τ => embV_eq_embF O.c' O.jL hP.lift.field τ
  refine ⟨h, ⟨h3, h4⟩, ⟨hP.lift, hP.act.1, hP.act.2, O.hw, by rw [e]; exact hP.io⟩,
    ⟨covPin_unitCov fun _ => hP.cov (), (hP.tuple ()).half, rfl⟩, O.bad (), J', O.Lh (), O.B (), O.epF (), O.φ (),
    (hP.bad ()).2, h1, (hP.reps ()).1, (hP.reps ()).2, h2, (hP.tuple ()).B, (hP.ep ()).2, (hP.ep ()).1, (hP.tuple ()).phi,
    fun _ => hP.w ()⟩

end Rows

section Back

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}
  {c' : Coeff T.Q.l} (hle : T.Q.c.F ≤ c'.F) (hV : T.V ((i : ℕ) + 1) (sigB T hle) = Wc D i) (jL : D.what₂.LL →+* c'.F)
  (lev : G → ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) ×
    ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La))
  (c0' : VsV D i c'.F →ₛₗ[c'.F.val.toRingHom] (R.cV i).W)
  (io : VsV D i c'.F →ₗ[c'.F] MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) c'.F)
  (dδ : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' (Vc D i).rank) {Cl : Type} [Fintype Cl] (h : Cl → GA D (Vc D i))
  (La : Cl → GenLat D.host.E (Vc D i).rank) (Nc gam : Cl → ℕ) (vol : c'.F) (ep : Cl → c'.F)
  (w : Cl → (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) dδ.l₂) → c'.F) (v₀ : (R.MW i (sg0 D A)).Vec)

structure Extra : Type 1 where
  bad : ℕ
  Lh : Cl → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)
  B : Ideal (𝓞 D.host.E) → c'.F
  epF : Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E) → c'.F
  φ : (Fin (Vc D i).rank → LevQc (T.Q.Dw ((i : ℕ) + 1)) dδ.l₂) → c'.F
  hw : VsV D i c'.F
  U₂ : Unf dδ.Xo₂ dδ.c₂ ((inC c').comp (dδ.eF.symm : dδ.c₂.F →+* c'.F)) D.R.r
  dict₂ : GA D (Wc D i) → Σ k, Frame (U₂.X k).Ψ D.R.r

def firstOf (X : Extra (Cl := Cl) dδ) : OMDat T.toCore R i Unit fun _ => A.μ0 where
  c' := c'
  hle := hle
  jL := jL
  hV := hV
  c0' := c0'
  lev g := (lev g).1
  dδ _ := dδ
  Cl' _ := Cl
  bad _ := X.bad
  Lh _ := X.Lh
  La _ := La
  Nc _ := Nc
  gam _ := gam
  vol _ := vol
  ep _ := ep
  B _ := X.B
  epF _ := X.epF
  io := io
  hw := X.hw
  φ _ := X.φ
  w _ := w
  U₂ _ := X.U₂
  dict₂ _ := X.dict₂
  xi _ := 1
  thAd _ := GlobalTheory.OneMapAll.thAdOf R i A.μ0 h c0' v₀
  Plc _ x := ∃ x₀, Place R i A.μ0 h c0' (jVx R i A.μ0 x₀) x

variable (κ : WeightFamilies.Wt D ((i : ℕ) + 1))

set_option maxHeartbeats 1000000 in

theorem pins_of_secondPins {F : Face D A} (hT : LawsJ T) (hC : R.Char F) (h1 : LiftPins T R i (wtA κ) v₀ lev c0' io jL)
    (h2 : CoverPins T R i dδ) (h3 : ClassPins T R i c0' dδ h La Nc gam vol ep w) :
    ∃ X : Extra (Cl := Cl) dδ, Reads (firstOf hle hV jL lev c0' io dδ h La Nc gam vol ep w v₀ X) v₀ h ∧
      (firstOf hle hV jL lev c0' io dδ h La Nc gam vol ep w v₀ X).Pins κ v₀ (iotaW T i) (T.x₀ ((i : ℕ) + 1) (sigB T hle)) := by
  obtain ⟨a1, a2, a3, hw, a4⟩ := h1
  obtain ⟨b1, b2, b3⟩ := h2
  obtain ⟨bad, J', Lh, B, epF, φ, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := h3
  obtain ⟨U₂, dict₂, d1, d2⟩ := exists_cover_dict T i hle hV hT dδ (b1 ()).2.1 b3
  have hA : T.Q.l.A = 1 := hT.pins.2.1.2
  have e : embV D jL = fun τ => embF c' (tauE D τ) := funext fun τ => embV_eq_embF c' jL a1.field τ
  have hth := GlobalTheory.OneMapAll.thAdIs_thAdOf R i A.μ0 h c0' hC.models.HV c2.2.2.1 c2.2.2.2.2.2.1 v₀
  have e' := fun c : Coeff T.Q.l => GlobalTheory.LevelEquivCompare.actLaws_congr (Xo := T.Q.Xo ((i : ℕ) + 1)) (c := c) (lev := lev)
    (lev' := fun g => ((lev g).1, LinearMap.id)) hA fun _ => rfl
  rw [e] at a4
  refine ⟨⟨bad, Lh, B, epF, φ, hw, U₂, dict₂⟩, ⟨hth, fun _ => Iff.rfl⟩, a1,
    fun _ => ⟨⟨h, J', c2, c5, hth, fun _ => Iff.rfl⟩, c6, fun g x _ => ?_, c9, b2⟩,
    ⟨(e' _).1 a2, (e' _).1 a3⟩,
    fun _ => ⟨Nat.pos_of_ne_zero c2.1, c1⟩, fun _ => ⟨c3, c4⟩, fun _ => ⟨c8, c7⟩, a4, c10, b1, d1, fun _ => d2⟩
  rw [GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hC.lev.xi_base ▸ hC.lev.xi A.μ0) x]
  rfl

set_option maxHeartbeats 1000000 in

theorem secondAt_firstOf (hA : T.Q.l.A = 1) (h1 : dδ.cδ = 1) (X : Extra (Cl := Cl) dδ) :
    SecondAt (firstOf hle hV jL lev c0' io dδ h La Nc gam vol ep w v₀ X) κ v₀ h ↔
      OneMapAt T R i hle hV (wtA κ) κ.n v₀ lev c0' io dδ h La Nc gam vol ep w := by
  obtain ⟨pd, I, l₂, Xo₂, c₂, hF, r, m, nab₂, cδ, φδ⟩ := dδ
  obtain rfl : cδ = 1 := h1
  have e := fun c : Coeff T.Q.l => GlobalTheory.LevelEquivCompare.actLev_congr (Xo := T.Q.Xo ((i : ℕ) + 1)) (c := c) (lev := lev)
    (lev' := fun g => ((lev g).1, LinearMap.id)) hA fun _ => rfl
  unfold OneMapAt LevelLaw ClassSumLaw
  rw [e, e]
  exact Iff.rfl

end Back

section Closed

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
  (i : Fin D.R.m)

def FirstRow : Prop :=
  R.Char F → Nonempty (FWTie T R κ v₀) →
    ∀ O : ∀ i, OMDat T.toCore R i Unit fun _ => A.μ0, OMPins T R κ v₀ O i → OneMapRow0 T R κ v₀ O i

def SecondRowField : Prop :=
  R.Char F → Nonempty (FWTie T R κ v₀) →
    ∀ (c' : Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F) (hV : T.V ((i : ℕ) + 1) (sigB T hle) = Wc D i)
      (jL : D.what₂.LL →+* c'.F)
      (lev : G → ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) ×
        ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La))
      (c0' : VsV D i c'.F →ₛₗ[c'.F.val.toRingHom] (R.cV i).W)
      (io : VsV D i c'.F →ₗ[c'.F] MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) c'.F)
      (dδ : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' (Vc D i).rank)
      (Cl : Type) [Fintype Cl] (h : Cl → GA D (Vc D i))
      (La : Cl → GenLat D.host.E (Vc D i).rank) (Nc gam : Cl → ℕ) (vol : c'.F) (ep : Cl → c'.F)
      (w : Cl → (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) dδ.l₂) → c'.F),
      c'.F = D.what₂.embLL.toRatAlgHom.fieldRange →
      LiftPins T R i (wtA (κ i)) (v₀ i (sg0 D A)) lev c0' io jL → CoverPins T R i dδ →
      ClassPins T R i c0' dδ h La Nc gam vol ep w →
      OneMapAt T R i hle hV (wtA (κ i)) (κ i).n (v₀ i (sg0 D A)) lev c0' io dδ h La Nc gam vol ep w

theorem secondRowField_of (H : OneMapRef T R F κ v₀ i) : SecondRowField T R F κ v₀ i :=
  fun hC fw c' hle hV jL lev c0' io dδ Cl _ h La Nc gam vol ep w _ => H hC fw c' hle hV jL lev c0' io dδ Cl h La Nc gam vol ep w

set_option maxHeartbeats 1000000 in

theorem nonempty_data (hT : LawsJ T) {c' : Coeff T.Q.l} (hle : T.Q.c.F ≤ c'.F) (jL : D.what₂.LL →+* c'.F) (j : Fin D.R.m) :
    Nonempty (OMDat T.toCore R j Unit fun _ => A.μ0) := by
  have hj := GlobalTheory.LevelEquivCompare.inR j
  have hpos : 1 ≤ (T.Q.Dw ((j : ℕ) + 1)).p + (T.Q.Dw ((j : ℕ) + 1)).q := by
    have := (GlobalTheory.Member.exists_iotaOK D T.Q hT.pins _ hj).2
    omega
  have hV : T.V ((j : ℕ) + 1) (sigB T hle) = Wc D j := hT.spaceW _ hj _ rfl
  obtain ⟨d, -, -, -, h1, h2⟩ := GlobalTheory.Survey.CoverPinCounterexample.exists_trivial (n := (Vc D j).rank) (T.Q.Xo ((j : ℕ) + 1)) c' hpos
    hT.pins.2.1.2 Unit
  obtain ⟨U₂, dict₂, -⟩ := exists_cover_dict T j hle hV hT d (h2 ()).2.1 h1
  exact ⟨{ c' := c', hle := hle, jL := jL, hV := hV, c0' := 0, lev := fun _ => 0, dδ := fun _ => d, Cl' := fun _ => Empty,
           bad := fun _ => 0, Lh := fun _ k => k.elim, La := fun _ k => k.elim, Nc := fun _ k => k.elim,
           gam := fun _ k => k.elim, vol := fun _ => 0, ep := fun _ k => k.elim, B := fun _ _ => 0, epF := fun _ _ => 0,
           io := 0, hw := 0, φ := fun _ _ => 0, w := fun _ k => k.elim, U₂ := fun _ => U₂, dict₂ := fun _ => dict₂,
           xi := fun _ => 1, thAd := fun _ _ _ => 0, Plc := fun _ _ => False }⟩

set_option maxHeartbeats 1000000 in

theorem firstRow_iff : FirstRow T R F κ v₀ i ↔ SecondRowField T R F κ v₀ i := by
  refine forall_congr' fun hC => forall_congr' fun ⟨fw⟩ => ?_
  have hn := (fw.kap i (D.eTau.symm 1)).2.2
  constructor
  · intro H c' hle hV jL lev c0' io dδ Cl _ h La Nc gam vol ep w hF h1 h2 h3
    classical
    obtain ⟨X, hR, hP⟩ := pins_of_secondPins hle hV jL lev c0' io dδ h La Nc gam vol ep w _ (κ i) fw.laws hC h1 h2 h3
    refine (secondAt_firstOf hle hV jL lev c0' io dδ h La Nc gam vol ep w _ (κ i) fw.laws.pins.2.1.2 h2.2.2 X).1
      ((row_iff _ (κ i) _ h fw.laws hC hn hF hP hR).1 ?_)
    have key : ∀ O : OMDat T.toCore R i Unit fun _ => A.μ0, O.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange ∧
        O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) →
          ∃ cc ph, O.OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph := fun O => by
      have := H (Function.update (fun j => (nonempty_data T R fw.laws hle jL j).some) i O)
      unfold OMPins OneMapRow0 at this
      rwa [Function.update_self] at this
    exact key _ ⟨hF, hP⟩
  · intro H O hO
    obtain ⟨h, hR, h1, h2, h3⟩ := secondPins_of_pins (O i) (κ i) _ hO.2
    exact (row_iff (O i) (κ i) _ h fw.laws hC hn hO.1 hO.2 hR).2 (H _ _ _ _ _ _ _ _ _ h _ _ _ _ _ _ hO.1 h1 h2 h3)

set_option maxHeartbeats 1000000 in

theorem one_map_typings_equiv :
    (R.Char F → FWTie T R κ v₀ →
      (∀ O : OMDat T.toCore R i Unit fun _ => A.μ0,
        O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) →
        (∃ h, Reads O (v₀ i (sg0 D A)) h ∧ SecondPins O (κ i) (v₀ i (sg0 D A)) h) ∧
        (∀ cc, O.EquivAt (κ i) cc ↔ LevelLaw T R i O.hle O.hV (wtA (κ i)) (κ i).n O.lev2 cc) ∧
        (∃ u : O.c'.F, (∃ m : ℕ, 0 < m ∧ u ^ m = 1) ∧ (O.dδ ()).cδ = (O.dδ ()).eF u • 1 ∧
          ∀ h, Reads O (v₀ i (sg0 D A)) h → ∀ cc ph, GlobalTheory.PhaseRational.IdentityAt O (κ i) cc ph ↔
            (∀ k, ‖cc k‖ = 1) ∧ ‖ph‖ = 1 ∧ ∃ z ∈ Subgroup.center G, ∃ ze ∈ D.what₂.embLL.toRatAlgHom.fieldRange,
              (∃ m : ℕ, 0 < m ∧ ze ^ m = 1) ∧ ClassSum O (κ i) (v₀ i (sg0 D A)) cc h (κ i).n ((ze * u)⁻¹ * ph) z) ∧
        (∀ cc ph, O.EquivAt (κ i) cc → RationalLaw T R i O.hle O.hV (wtA (κ i)) (κ i).n (v₀ i (sg0 D A)) cc ph →
          O.PhRat (κ i) (v₀ i (sg0 D A)) cc ph) ∧
        (O.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange → ∀ h, Reads O (v₀ i (sg0 D A)) h →
          ((∃ cc ph, O.OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph) ↔ SecondAt O (κ i) (v₀ i (sg0 D A)) h))) ∧
      ∀ (c' : Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F) (hV : T.V ((i : ℕ) + 1) (sigB T hle) = Wc D i) jL lev c0' io dδ
        (Cl : Type) [Fintype Cl] (h : Cl → GA D (Vc D i)) La Nc gam vol ep w,
        LiftPins T R i (wtA (κ i)) (v₀ i (sg0 D A)) lev c0' io jL → CoverPins T R i dδ →
        ClassPins T R i c0' dδ h La Nc gam vol ep w →
        ∃ X : Extra (Cl := Cl) dδ,
          Reads (firstOf hle hV jL lev c0' io dδ h La Nc gam vol ep w (v₀ i (sg0 D A)) X) (v₀ i (sg0 D A)) h ∧
          (firstOf hle hV jL lev c0' io dδ h La Nc gam vol ep w (v₀ i (sg0 D A)) X).Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i)
            (T.x₀ ((i : ℕ) + 1) (sigB T hle)) ∧
          (SecondAt (firstOf hle hV jL lev c0' io dδ h La Nc gam vol ep w (v₀ i (sg0 D A)) X) (κ i) (v₀ i (sg0 D A)) h ↔
            OneMapAt T R i hle hV (wtA (κ i)) (κ i).n (v₀ i (sg0 D A)) lev c0' io dδ h La Nc gam vol ep w)) ∧
    (FirstRow T R F κ v₀ i ↔ SecondRowField T R F κ v₀ i) ∧
    (OneMapRef T R F κ v₀ i → FirstRow T R F κ v₀ i) := by
  refine ⟨fun hC fw => ⟨fun O hP => ?_, fun c' hle hV jL lev c0' io dδ Cl _ h La Nc gam vol ep w h1 h2 h3 => ?_⟩,
    firstRow_iff T R F κ v₀ i, fun H => (firstRow_iff T R F κ v₀ i).2 (secondRowField_of T R F κ v₀ i H)⟩
  · have hn := (fw.kap i (D.eTau.symm 1)).2.2
    obtain ⟨u, ⟨m, hm, hu⟩, hd⟩ := cover_const O (κ i) _ fw.laws hC.lev hP
    exact ⟨secondPins_of_pins O _ _ hP, fun cc => equivAt_iff O _ cc fw.laws.toLawsM hP.act.1,
      ⟨u, ⟨m, hm, hu⟩, hd, fun h hR cc => identity_iff O _ _ cc h fw.laws.toLawsM hP.act.2 hC.thP.thF_mem
        (hn.trans (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).symm) hR.1 hR.2
        (fun e => by rw [e, zero_pow hm.ne'] at hu; exact zero_ne_one hu) hd⟩,
      fun cc _ hE => phRat_of_rationalLaw O _ _ cc hE hC.grp.chiW hC.thP.thG,
      fun hF h hR => row_iff O _ _ h fw.laws hC hn hF hP hR⟩
  · obtain ⟨X, hR, hP⟩ := pins_of_secondPins hle hV jL lev c0' io dδ h La Nc gam vol ep w _ (κ i) fw.laws hC h1 h2 h3
    exact ⟨X, hR, hP, secondAt_firstOf hle hV jL lev c0' io dδ h La Nc gam vol ep w _ (κ i) fw.laws.pins.2.1.2 h2.2.2 X⟩

end Closed

end GlobalTheory.OneMapRefCompare
