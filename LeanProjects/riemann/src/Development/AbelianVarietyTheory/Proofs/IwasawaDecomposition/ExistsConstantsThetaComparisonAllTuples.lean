import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Formalism.LocalRingCardinality.DataKap
import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelsCompatible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeometricHalfRealisationGeometricAction
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitModulusConstantsEquivariantDictionaryStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EmbeddingsDifferOnInteger

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.RealGeo.RowAll

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
  Formalism.L2.DIV GlobalTheory.FieldBC Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.MainNotions Formalism.IndefR.Links Formalism.IndefR.Mult GlobalTheory.OneMapAll GlobalTheory.AdTh
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Merge

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}
  {J : Type} {tup : J → T0} (src : ∀ j, OMDat C R i Unit (fun _ => tup j)) (c₃ : Coeff C.Q.l) (h₃ : C.Q.c.F ≤ c₃.F)
  (hs : ∀ j, (src j).c'.F ≤ c₃.F) (jL₃ : D.what₂.LL →+* c₃.F) (hV₃ : C.V ((i : ℕ) + 1) (sOv C c₃ h₃) = Wc D i)
  (c0₃ : VsV D i c₃.F →ₛₗ[inC c₃] (R.cV i).W)
  (lev : G → (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (C.Q.Dw ((i : ℕ) + 1)).La)
  (io₃ : VsV D i c₃.F →ₗ[c₃.F] MvPolynomial (LtN (C.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) c₃.F) (hw₃ : VsV D i c₃.F)
  (u : J → c₃.F) (h : ∀ j, (src j).Cl' () → GA D (Vc D i)) (v₀ : (R.MW i (sg0 D A)).Vec)

set_option maxHeartbeats 1000000 in

theorem pins_merge (hR : R.IsModels) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {ι x₀}
    (hv : ∀ t PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ∀ (ξ : (kP PP)ˣ →* ℂˣ) (x : (kP PP)ˣ), ((ξ x : ℂˣ) : ℂ) ∈ c₃.F)
    (hsrc : ∀ j, (src j).Pins κ v₀ ι x₀)
    (hlift : ThPinsR R i jL₃ (inC c₃) v₀ c0₃ ι C.Q.l.M (Mfr C.Q.l) lev)
    (hact : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c fun g => (lev g, LinearMap.id))
    (hio : IoLFRec c₃ (fun τ => embF c₃ (tauE D τ)) (lamV D i) (wtA κ) io₃ hw₃)
    (hh : ∀ j, ∃ J', RepsR R i (tup j) (h j) ((src j).bad ()) J' ((src j).Lh ()) ((src j).gam ()) ((src j).vol ()))
    (c0 : ℂ) (hc0 : ∃ m : ℕ, 0 < m ∧ c0 ^ m = 1) (cs : J → ℂ) (hu : ∀ j, (u j : ℂ) * cs j = c0)
    (hcs : ∀ j, CXiAt (Wc D i) (rank_Wc i) (inC (src j).c') ((src j).dδ ()) ((src j).U₂ ()) ((src j).dict₂ ()) ι x₀
      ((src j).xi ()) (cs j)) :
    (merge src c₃ h₃ hs jL₃ hV₃ c0₃ lev io₃ hw₃ u h v₀).Pins κ v₀ ι x₀ := by
  have hu0 : ∀ j, u j ≠ 0 := fun j h0 => by
    obtain ⟨m, hm, e⟩ := hc0
    rw [← hu j, h0] at e
    simp [hm.ne'] at e
  refine ⟨hlift, fun j => ⟨?_, ((hsrc j).tuple ()).B, ((hsrc j).tuple ()).xi, ((hsrc j).tuple ()).phi, ((hsrc j).tuple ()).half⟩,
    ⟨hact, (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ h₃ _ _ hact).1⟩, fun j => (hsrc j).bad (), fun j => (hsrc j).reps (),
    fun j => ⟨fun k => congrArg (incF _ c₃ (hs j)) (((hsrc j).ep ()).1 k), epIs_map (hs j) ((hsrc j).ep ()).2⟩, hio,
    fun j k q => phiHat_covBC (hs j) _ (u j) _ _ q ((hsrc j).w () k q),
    fun j => covPin_covBC (hs j) _ (hu0 j) ((hsrc j).cov ()), ?_, fun j => (hsrc j).model₂ ()⟩
  · obtain ⟨J', hr⟩ := hh j
    obtain ⟨_, _, _, hT, hc⟩ := hlift.c0
    exact ⟨h j, J', repsR_map _ hr,
      GlobalTheory.RationalValues.placeEx_of_type_mem R i jL₃ (inC c₃) (tup j) (h j) c0₃ hR.jV hT hc
        (GlobalTheory.RationalValues.type_mem R i (tup j) _ (fun PP hPP x => ⟨⟨_, hv (tup j) PP (Or.inl hPP) _ x⟩, rfl⟩)
          fun PP hPP x => ⟨⟨_, hv (tup j) PP (Or.inr hPP) _ x⟩, rfl⟩),
      thAdIs_thAdOf R i (tup j) (h j) c0₃ hR.HV hr.2.2.1 hr.2.2.2.2.2.1 v₀, fun _ => Iff.rfl⟩
  · refine (cXiVal_iff _ _ _ _ _ _ _ _ _).2 ⟨c0, hc0, fun j => ?_⟩
    rw [← hu j]
    exact GlobalTheory.OneMapAll.cXiAt_covBC D _ _ _ _ _ _ _ _ (hs j) _ _ _ (u j) _ _ _ _ _ _ ((hsrc j).cov ()).1.2.2.2.2.2.2.2.1 (hcs j)

end Merge

section Row

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {κ : WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : (R.MW i (sg0 D A)).Vec}

set_option maxHeartbeats 1600000 in

theorem exists_extension [Finite T0] (hR : R.IsModels) {ι x₀}
    (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) (O' : OMDat T.toCore R i T0 id) (hle : O.c'.F ≤ O'.c'.F)
    (hO : O.Pins κ v₀ ι x₀) (hO' : O'.Pins κ v₀ ι x₀) :
    ∃ M : OMDat T.toCore R i (Option T0) (fun o => o.getD A.μ0), O.c'.F ≤ M.c'.F ∧ M.lev = O.lev ∧
      M.Pins κ v₀ ι x₀ ∧ ∀ (cc : (T.U ((i : ℕ) + 1) T.σ₀).Comp → ℂ) (ph : ℂ), SerOf M κ v₀ cc ph → SerOf O κ v₀ cc ph := by
  classical
  obtain ⟨a, ha, hca⟩ := (cXiVal_iff _ _ _ _ _ _ _ _ _).1 hO.cxi
  obtain ⟨b, hb, hcb⟩ := (cXiVal_iff _ _ _ _ _ _ _ _ _).1 hO'.cxi
  obtain ⟨c₂, h'', haF', hbF'⟩ := exists_coeff_roots O'.c' ha hb
  choose MC hMC hC using fun t => GlobalTheory.PinnedPre.exists_char_field (R.Pg ∪ R.Q t)
  have := c₂.fin
  obtain ⟨c₃, hc₃⟩ := GlobalTheory.TupleCover.exists_coeff_ge T.Q.l (c₂.F ⊔ ⨆ t, MC t)
  have h23 : c₂.F ≤ c₃.F := le_sup_left.trans hc₃
  have h' := h''.trans h23
  have haF := h23 haF'
  have hbF := h23 hbF'
  have hv : ∀ t PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ∀ (ξ : (kP PP)ˣ →* ℂˣ) (x : (kP PP)ˣ), ((ξ x : ℂˣ) : ℂ) ∈ c₃.F :=
    fun t PP hPP ξ x => (((le_iSup MC t).trans le_sup_right).trans hc₃) (hC t PP (Finset.mem_union.2 hPP) ξ x)
  have hb0 : b ≠ 0 := fun h0 => by
    obtain ⟨m, hm, e⟩ := hb
    simp [h0, hm.ne'] at e
  have h₁ : O.c'.F ≤ c₃.F := hle.trans h'
  have h₃ : T.Q.c.F ≤ c₃.F := O.hle.trans h₁
  have hV₃ : T.V ((i : ℕ) + 1) (sOv T.toCore c₃ h₃) = Wc D i := O.hV
  obtain ⟨c0₃, hc0⟩ := exists_coef_ext (incF O.c' c₃ h₁) (σ := inC O.c') (inC c₃) (fun _ => rfl) (lamV D i) O.c0'
  obtain ⟨io₃, hw₃, hio, hover⟩ := GlobalTheory.IoExtend.exists_ioLFRec_over _ _ _ _ O.c' c₃ h₁ _ _ (tauE D) (lamV D i) (wtA κ) O.io O.hw hO.io
  have hlift : ThPinsR R i ((incF O.c' c₃ h₁).comp O.jL) (inC c₃) v₀ c0₃ ι T.Q.l.M (Mfr T.Q.l) O.lev := by
    refine ⟨(RingHom.ext fun _ => rfl : _ = (inC O.c').comp O.jL).trans hO.lift.field, hO.lift.std, hO.lift.v0, ?_,
      hO.lift.lev⟩
    obtain ⟨g, r, c0L, hT, hc⟩ := hO.lift.c0
    refine ⟨g, r, c0L, hT, fun v => ?_⟩
    obtain ⟨v', hv', e⟩ := hc v
    obtain ⟨v'', hv''⟩ := GlobalTheory.FieldBCModel.exists_over h₁ (lamV D i) v'
    exact ⟨v'', by rw [hv'', hv', MvPolynomial.map_map], (hc0 v' v'' hv'').trans e⟩
  obtain ⟨h₀, J₀, hr₀, -, hth₀, hpl₀⟩ := (hO.tuple ()).reps
  choose hh Jt hrt _ using fun t => (hO'.tuple t).reps
  let src : ∀ o : Option T0, OMDat T.toCore R i Unit (fun _ => o.getD A.μ0) := fun o =>
    match o with
    | none => O
    | some t => comap O' (fun _ => t)
  have hs : ∀ o, (src o).c'.F ≤ c₃.F := fun o =>
    match o with
    | none => h₁
    | some _ => h'
  let u : Option T0 → c₃.F := fun o =>
    match o with
    | none => 1
    | some _ => ⟨a, haF⟩ / ⟨b, hbF⟩
  let h : ∀ o, (src o).Cl' () → GA D (Vc D i) := fun o =>
    match o with
    | none => h₀
    | some t => hh t
  have hP := pins_merge src c₃ h₃ hs _ hV₃ c0₃ O.lev io₃ hw₃ u h v₀ hR hv
    (fun o => match o with
      | none => hO
      | some t => pins_comap (fun _ => t) hO') hlift hO.act.1 hio
    (fun o => match o with
      | none => ⟨J₀, hr₀⟩
      | some t => ⟨Jt t, hrt t⟩) a ha (fun o => o.elim a fun _ => b)
    (fun o => match o with
      | none => one_mul a
      | some _ => div_mul_cancel₀ a hb0)
    (fun o => match o with
      | none => hca ()
      | some t => hcb t)
  refine ⟨_, h₁, rfl, hP, fun cc ph hS => ⟨hS.1, hS.2.1, fun t k J' hr y x hy f hf hfx g => ?_⟩⟩
  choose x' hx' using fun k => GlobalTheory.FieldBCModel.exists_over h₁ (lamV D i) (x k)
  have hy' : Place R i A.μ0 k c0₃ y x' := fun k => (hy k).trans (hc0 _ _ (hx' k)).symm
  have e := hS.2.2 none k J' (repsR_map _ hr) y x' hy' (rulBC h₁ f) (GlobalTheory.FieldBCModel.rulBC_mem_sec h₁ hf)
    (isThClsD_covBC_one h₁ (O.dδ ()) rfl _ _ _ _ _ _ O.io io₃ x x' (fun k => hover _ _ (hx' k))
      (hO.cov ()).1.2.2.2.2.2.2.2.1 hf hfx) g
  obtain ⟨m, as, fs, -, hBC⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ O.hle).1 _ _ f hf
  have e1 := GlobalTheory.PhRatCommon.rdU_of_isBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c') hBC (O.dict g).1 (O.dict g).2
  have e2 := GlobalTheory.PhRatCommon.rdU_of_isBC h₃ (T.U ((i : ℕ) + 1)) (inC c₃) (isBC_rulBC_trans O.hle h₁ h₃ hf hBC)
    (O.dict g).1 (O.dict g).2
  exact e.trans (congrArg (fun w => cc (O.dict g).1 * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * O.mu g * w)
    (e2.trans e1.symm))

end Row

section Rational

open GlobalTheory.PhaseRationalDegenerate

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (O : OMDat C R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : (R.MW i (sg0 D A)).Vec)
  (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ)

theorem isRat_act (hE : O.EquivAt κ cc) {chi : G →* D.what₂.LLˣ} (hχ : ChiIs R i chi) (g : G) {F : GA D (Wc D i) → ℂ}
    (h : IsRat O κ cc F) : IsRat O κ cc (Formalism.IndefR.Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) F) := by
  show IsRat O κ cc (Formalism.IndefR.Lev.actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) F)
  unfold Formalism.IndefR.Lev.actG0
  split_ifs with hk
  · obtain ⟨n, a, f, hf⟩ := h
    have e := hE g _ hk.choose_spec
    refine ⟨n, fun k => a k * (((chi g)⁻¹ : D.what₂.LLˣ) : D.what₂.LL), fun k => ⟨_, (e _ (f k).2).1⟩, fun x => ?_⟩
    rw [levChi_flag, inv_one]
    beta_reduce
    rw [one_mul, hf]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e2 := (e _ (f k).2).2 x
    rw [← (hχ g).trans (Units.coe_prod _ _)] at e2
    have e3 : D.what₂.embLL (((chi g)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) * D.what₂.embLL ((chi g : D.what₂.LLˣ) : D.what₂.LL) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    show _ = _ * (_ * O.phi cc (actLev C.Q.c O.lev2 g (f k : C.R ((i : ℕ) + 1))) x)
    rw [e2, map_mul]
    linear_combination (-(D.what₂.embLL (a k) * (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) *
      O.phi cc (f k : C.R ((i : ℕ) + 1)) (x * hk.choose))) * e3
  · exact IsRat.zero O κ cc

set_option maxHeartbeats 1000000 in

theorem phRat_of_before (hE : O.EquivAt κ cc) {chi : G →* D.what₂.LLˣ} (hχ : ChiIs R i chi) (hG : R.thP_thG) (ph : ℂ)
    (h : ∀ x : A.fam.amb.FL i A.μ0, IsRat O κ cc (ph • R.thF i A.μ0 (jVx R i A.μ0 x) v₀)) : O.PhRat κ v₀ cc ph := by
  intro x
  have key : IsRat O κ cc (R.eWf i (sg0 D A) (ph • R.thF i A.μ0 (jVx R i A.μ0 x) v₀)) := by
    unfold RealDat.eWf gaL
    rw [LinearMap.sum_apply]
    refine Finset.sum_induction _ (IsRat O κ cc) (fun _ _ => IsRat.add O κ cc) (IsRat.zero O κ cc) fun g _ => ?_
    have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
    have : RealDat.eC (A := A) (sg0 D A) g = D.what₂.embLL ((idemOf A.X).coeff g) :=
      RingHom.congr_fun hs ((idemOf A.X).coeff g)
    have h2 := IsRat.mul O κ cc ((idemOf A.X).coeff g) (isRat_act O κ cc hE hχ g (h x))
    rw [← this] at h2
    exact h2
  obtain ⟨n, a, f, hf⟩ := key
  refine ⟨n, a, f, fun y => ?_⟩
  rw [← hf y, hG i A.μ0, map_smul]
  rfl

end Rational

section Main

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} {i : Fin D.R.m}

set_option maxHeartbeats 1000000 in

theorem oneMapOf_of_serOf (hR : PreChar R) (hT : TieIn T R κ v₀) {O : OMDat T.toCore R i Unit (fun _ => A.μ0)}
    (hF : O.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange) {ι x₀} (hP : O.Pins (κ i) (v₀ i (sg0 D A)) ι x₀) {cc}
    (hE : O.EquivAt (κ i) cc) (hS : SerOf O (κ i) (v₀ i (sg0 D A)) cc 1)
    (hex : ∀ x, O.Plc () x → ∃ f ∈ cuspOver O (κ i), IsSum O () x f) : O.OneMapOf (κ i) (v₀ i (sg0 D A)) cc 1 := by
  obtain ⟨h, J', hrep, hPl, hA, hPc⟩ := (hP.tuple ()).reps
  refine ⟨hE, ⟨hF.ge, (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ O.hle).2 _ _,
    (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ O.hle _ _ hP.act.1).2, ?_⟩, ?_⟩
  · refine ⟨hS.1, hS.2.1, 1, Subgroup.one_mem _, fun t => ⟨1, one_mem _, ⟨1, Nat.one_pos, one_pow _⟩, fun x hx => ⟨hex x hx, ?_⟩⟩⟩
    intro f hf hc q
    obtain ⟨x₀, hx₀⟩ := (hPc x).1 hx
    have hL := hP.act.2
    have h1 : actLev (Xo := T.Q.Xo ((i : ℕ) + 1)) O.c' O.lev2 1 f = f := actL_one _ _ _ hL.total hL.func hL.one hf.1
    have h2 := hS.2.2 t h J' hrep _ x hx₀ f hf hc q.out
    rw [h1, hA _ x hx₀, one_mul (cc _)]
    refine h2.trans ?_
    rw [mul_assoc (cc _ * _)]
    rfl
  · obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm ⟨1, by simp [Formalism.FrobeniusOrbits.Psi]⟩⟩
    have hn : (κ i).n = (Vc D i).rank :=
      (hT.kap i τ).2.2.trans (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).symm
    refine phRat_of_before O (κ i) _ cc hE (Half.chiIs_chiTop_of_tie T R κ v₀ hR.lev hT i) hR.thP.thG 1 fun x₀ => ?_
    obtain ⟨x, hx⟩ := hPl x₀
    obtain ⟨f, hf, hcl⟩ := hex x ((hPc x).2 ⟨x₀, hx⟩)
    have hf' : f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (κ i).n := by
      rw [hn]; exact hf
    obtain ⟨m, as, fs, hbc⟩ := GlobalTheory.PhRatCommon.exists_rdU_eq_sum O.hle (T.U ((i : ℕ) + 1)) (inC O.c') _ _ f hf'
    have hL : ∀ a : O.c'.F, ∃ b : D.what₂.LL, D.what₂.embLL b = inC O.c' a := fun a => by
      have : (a : ℂ) ∈ D.what₂.embLL.toRatAlgHom.fieldRange := hF ▸ a.2
      exact this
    choose b hb using hL
    refine ⟨m, fun j => b (as j), fs, fun g => ?_⟩
    have := hS.2.2 () h J' hrep _ x hx f hf.1 hcl g
    have e1 := hbc (O.dict g).1 (O.dict g).2
    have e2 : ∀ j, O.phi cc (fs j : T.R ((i : ℕ) + 1)) g = cc (O.dict g).1 * O.mu g *
        rdU (T.U ((i : ℕ) + 1) O.s0) (fs j : T.R ((i : ℕ) + 1)) (O.dict g).1 (O.dict g).2 := fun j => rfl
    exact this.trans (GlobalTheory.PhRatCommon.sum_shape e1 (fun j => hb (as j)) e2)

set_option maxHeartbeats 1000000 in

theorem exists_common [Finite T0] (hR : PreChar R) (hT : TieIn T R κ v₀) {ι x₀}
    (hof : ∀ (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) ι x₀ →
      ∃ cc, M.EquivAt (κ i) cc ∧ SerOf M (κ i) (v₀ i (sg0 D A)) cc 1 ∧ RowAt M (κ i) cc 1)
    (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) (hF : O.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange)
    (hP : O.Pins (κ i) (v₀ i (sg0 D A)) ι x₀) (O' : OMDat T.toCore R i T0 id)
    (hF' : D.what₂.embLL.toRatAlgHom.fieldRange ≤ O'.c'.F) (hP' : O'.Pins (κ i) (v₀ i (sg0 D A)) ι x₀) :
    ∃ cc : (T.U ((i : ℕ) + 1) T.σ₀).Comp → ℂ, O.OneMapOf (κ i) (v₀ i (sg0 D A)) cc 1 ∧
      ∃ N : OMDat T.toCore R i T0 id, D.what₂.embLL.toRatAlgHom.fieldRange ≤ N.c'.F ∧ N.Pins (κ i) (v₀ i (sg0 D A)) ι x₀ ∧
        N.OneMapOf (κ i) (v₀ i (sg0 D A)) cc 1 := by
  obtain ⟨M, h₁, hlev, hM, hdesc⟩ := exists_extension hR.models O O' (hF.le.trans hF') hP hP'
  obtain ⟨cc, hE, hS, hrow⟩ := hof _ _ M hM
  obtain ⟨cc₀, -, -, -, -, z, -, h0⟩ := hof _ _ O hP
  obtain ⟨ze, -, -, h0⟩ := h0 ()
  have e : M.lev2 = O.lev2 := by funext g; simp only [OMDat.lev2, hlev]
  have hE' : O.EquivAt (κ i) cc := by
    unfold OMDat.EquivAt at hE ⊢
    rw [e] at hE
    exact hE
  have hO := oneMapOf_of_serOf hR hT hF hP hE' (hdesc cc 1 hS) fun x hx => (h0 x hx).1
  have hL := hF.ge.trans h₁
  exact ⟨cc, hO, comap M some, hL, pins_comap some hM, oneMapOf_comap some
    ⟨hE, ⟨hL, (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ M.hle).2 _ _,
      (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ M.hle _ _ hM.act.1).2, hrow⟩, hO.2.2⟩⟩

end Main

section Levels

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem exists_symOrd {r : ℕ} (ρ k : ℕ) (h : ρ + k ≤ r) : ∃ π : Equiv.Perm (Fin r), IsSymOrd ρ k π := by
  refine ⟨⟨fun a => ⟨if (a : ℕ) < ρ then k + a else if (a : ℕ) < ρ + k then a - ρ else a, ?_⟩,
    fun b => ⟨if (b : ℕ) < k then b + ρ else if (b : ℕ) < ρ + k then b - k else b, ?_⟩, fun a => Fin.ext ?_, fun b => Fin.ext ?_⟩,
    fun _ => rfl⟩
  · have := a.2
    split_ifs <;> omega
  · have := b.2
    split_ifs <;> omega
  · dsimp only
    split_ifs <;> omega
  · dsimp only
    split_ifs <;> omega

theorem level_ext₂ {Pg : Finset (Pl D.host.E)} {r : ℕ} {L L' : LevelP Pg r ℂ} (h : ∀ g, g ∈ L.H ↔ g ∈ L'.H)
    (h' : ∀ g hg hg', L.chi ⟨g, hg⟩ = L'.chi ⟨g, hg'⟩) : L = L' := by
  obtain ⟨H, c⟩ := L
  obtain ⟨H', c'⟩ := L'
  obtain rfl : H = H' := Subgroup.ext h
  obtain rfl : c = c' := MonoidHom.ext fun g => h' g.1 g.2 g.2
  rfl

theorem chi_ofLocal_map {Pg : Finset (Pl D.host.E)} {r : ℕ} {K : Type} [Field K] (σ : K →+* ℂ)
    (Hl : ∀ PP : Pg, Subgroup (GL (Fin r) (kP PP.1))) (f : ∀ PP : Pg, Hl PP →* Multiplicative (kP PP.1))
    (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) K) (g g' : G0 Pg r) (e : g = g') (hg : g ∈ Subgroup.pi Set.univ Hl)
    (hg' : g' ∈ Subgroup.pi Set.univ Hl) :
    Units.map σ.toMonoidHom ((LevelP.ofLocal Hl fun PP => addCharHom (ψ PP.1) (f PP)).chi ⟨g, hg⟩) =
      (LevelP.ofLocal Hl fun PP => addCharHom (σ.toMonoidHom.compAddChar (ψ PP.1)) (f PP)).chi ⟨g', hg'⟩ := by
  subst e
  refine ((congrArg (Units.map σ.toMonoidHom) (MonoidHom.finsetProd_apply _ _ _)).trans (map_prod _ _ _)).trans
    (Eq.trans ?_ (MonoidHom.finsetProd_apply _ _ _).symm)
  exact Finset.prod_congr rfl fun PP _ => Units.ext rfl

theorem exists_psi (hrec : R.grp_record) (hroot : R.fam_roots) :
    ∃ ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) D.what₂.LL, ∀ PP ∈ R.Pg, ∃ x, ψ PP x ≠ 1 := by
  have key : ∀ PP : Pl D.host.E, ∃ ψ : AddChar (kP PP) D.what₂.LL, PP ∈ R.Pg → ∃ x, ψ x ≠ 1 := fun PP => by
    by_cases hP : PP ∈ R.Pg
    swap
    · exact ⟨1, fun h => absurd h hP⟩
    obtain ⟨-, plg, iso, -⟩ := hrec
    obtain ⟨kv, hkv⟩ := plg.surjective ⟨PP, hP⟩
    obtain rfl : (plg kv).1 = PP := congrArg Subtype.val hkv
    obtain ⟨z, hz⟩ := hroot A.μ0 _ (Or.inl hP)
    have hfin : Finite (kP (plg kv).1) := Ideal.finiteQuotientOfFreeOfNeBot _ (plg kv).1.ne_bot
    have hnt : Nontrivial (kP (plg kv).1) := Ideal.Quotient.nontrivial_iff.2 (plg kv).1.isPrime.ne_top
    have h1 : 1 < Nat.card (kP (plg kv).1) := Finite.one_lt_card
    rw [← Nat.card_congr (iso kv).toEquiv, Nat.card_zmod] at hz h1
    have : NeZero (D.host.g kv.1) := ⟨by omega⟩
    have : Fact (1 < D.host.g kv.1) := ⟨h1⟩
    refine ⟨(AddChar.zmodChar _ hz.pow_eq_one).compAddMonoidHom (iso kv).symm.toAddMonoidHom, fun _ => ⟨iso kv 1, ?_⟩⟩
    show AddChar.zmodChar _ hz.pow_eq_one ((iso kv).symm (iso kv 1)) ≠ 1
    rw [RingEquiv.symm_apply_apply, AddChar.zmodChar_apply, ZMod.val_one, pow_one]
    exact hz.ne_one h1
  choose ψ hψ using key
  exact ⟨ψ, hψ⟩

def reordHom {Pg : Finset (Pl D.host.E)} {r : ℕ} (π : Equiv.Perm (Fin r)) : G0 Pg r →* G0 Pg r :=
  MonoidHom.mk' (reord π) fun a b => funext fun PP => map_mul _ (a PP) (b PP)

theorem exists_face (hrec : R.grp_record) (hroot : R.fam_roots) : ∃ F : Face D A, R.grp_levels F := by
  obtain ⟨ψ, hψ⟩ := exists_psi R hrec hroot
  obtain ⟨π, hπ⟩ := exists_symOrd (r := D.R.r) D.R.rS D.R.k (by
    have := D.R.two_le_m
    unfold Ranks.r Ranks.rS
    omega)
  let L0 := P0 R.Pg D.R.r ψ
  let L1 := PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ
  let e1 : G →* G0 R.Pg D.R.r := (reordHom π).comp R.eG.toMonoidHom
  refine ⟨⟨L0.H.comap R.eG.toMonoidHom, L0.chi.comp (R.eG.toMonoidHom.subgroupComap L0.H), L1.H.comap e1,
    L1.chi.comp (e1.subgroupComap L1.H), fun _ => ⟨Empty, fun _ => 0, fun _ _ => 0, fun _ _ => 0⟩,
    fun _ => ⟨ℂ, inferInstance, inferInstance, fun _ => 0, ⊥⟩, fun _ => ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩,
    fun PP => D.what₂.embLL.toMonoidHom.compAddChar (ψ PP), fun PP hP h => ?_, level_ext₂ (fun g => ?_) fun g hg hg' => ?_,
    π, hπ, fun g => ?_, fun g hg hg' => ?_⟩
  · obtain ⟨x, hx⟩ := hψ PP hP
    exact hx (D.what₂.embLL.injective ((DFunLike.congr_fun h x).trans (map_one _).symm))
  · show R.eG (R.eG.symm g) ∈ L0.H ↔ _
    rw [MulEquiv.apply_symm_apply]
    rfl
  · exact chi_ofLocal_map D.what₂.embLL _ _ ψ _ _ (R.eG.apply_symm_apply g) hg hg'
  · show reord π (R.eG (R.eG.symm g)) ∈ L1.H ↔ _
    rw [MulEquiv.apply_symm_apply]
    rfl
  · exact chi_ofLocal_map D.what₂.embLL _ _ ψ _ _ (congrArg (reord π) (R.eG.apply_symm_apply g)) hg hg'

end Levels

section Weak

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

set_option maxHeartbeats 1600000 in

theorem exists_core (hR : PreChar R) (hT : TieIn T R κ v₀) : ∃ F : Face D A, GlobalTheory.Hk3.Core (topR T R κ v₀) F := by
  have h := Half.preChar_updFW R (nTop T κ) (fun i => formsN T R κ v₀ i (nTop T κ i)) hR
  obtain ⟨F, hF⟩ := exists_face (topR T R κ v₀) h.record h.fam.roots
  exact ⟨F, h.lev, ⟨h.red_R, h.red_L, hF, h.record,
    fun i g => (Half.chiIs_chiTop_of_tie T R κ v₀ hR.lev hT i g).trans (Units.coe_prod _ _)⟩, h.fam, h.models, h.chain, h.thP⟩

set_option maxHeartbeats 1600000 in

theorem exists_serOf (hR : PreChar R) (hT : TieIn T R κ v₀) (hio : IoExt R) (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0)
    (M : OMDat T.toCore R i Tp tup) (hM : M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀)) :
    ∃ cc, M.EquivAt (κ i) cc ∧ SerOf M (κ i) (v₀ i (sg0 D A)) cc 1 ∧ RowAt M (κ i) cc 1 := by
  obtain ⟨F, hF⟩ := exists_core hR hT
  have hT' : TieIn T (topR T R κ v₀) κ v₀ := ⟨hT.laws, hT.alg, hT.kap, hT.hv₀, hT.chiR, hT.x0⟩
  have hM' : (Half.updO T R (nTop T κ) (fun i => formsN T R κ v₀ i (nTop T κ i)) M).Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i)
      (T.x₀ ((i : ℕ) + 1) T.σ₀) := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hM
    refine ⟨⟨h1.field, h1.std, ?_, h1.c0, h1.lev⟩, fun t => ⟨(h2 t).reps, (h2 t).B, (h2 t).xi, (h2 t).phi, (h2 t).half⟩,
      h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    exact h1.v0
  obtain ⟨cc, -, u, -, h1, h2, h3⟩ :=
    GlobalTheory.T.exists_unitModulus_constants_equivariant_dictionary GlobalTheory.ChartFree.chartIndep D G Pl0 T0 A T (topR T R κ v₀) F κ v₀ hF hT' hio i Tp tup _ hM'
  exact ⟨u • cc, h1, h2, h3⟩

end Weak

end GlobalTheory.RealGeo.RowAll

namespace GlobalTheory.RealGeo

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1600000 in

theorem exists_const_oneMapOf_all : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), PreChar R → TieIn T R κ v₀ → T.pb = R.C.P.pb → Finite T0 → QGuard R → IoExt R → ∀ i, VStd D i → OMPins T R κ v₀ O i → ∃ cc : (T.U ((i : ℕ) + 1) T.σ₀).Comp → ℂ, (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) cc 1 ∧ ∃ O' : OMDat T.toCore R i T0 id, D.what₂.embLL.toRatAlgHom.fieldRange ≤ O'.c'.F ∧ O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O'.s0) ∧ O'.OneMapOf (κ i) (v₀ i (sg0 D A)) cc 1 := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hR hT hpb hfin hG hio i hV hO
  obtain ⟨O', hF', hP'⟩ := GlobalTheory.PinnedPre.exists_pins D G Pl0 T0 A T R κ v₀ hR hT hpb hfin hG i hV
  exact RowAll.exists_common (ι := iotaW T i) (x₀ := T.x₀ ((i : ℕ) + 1) T.σ₀) hR hT (RowAll.exists_serOf hR hT hio i) (O i) hO.1 hO.2
    O' hF' hP'

end GlobalTheory.RealGeo
