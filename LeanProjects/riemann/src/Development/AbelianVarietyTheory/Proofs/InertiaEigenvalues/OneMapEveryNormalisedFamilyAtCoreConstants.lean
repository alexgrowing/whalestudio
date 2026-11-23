import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicLiftEqGeometricClassSumAllTuples
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameConstantsOfCharacterisationCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormClassSumNormalisedData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockCoefficientMapExtremalEqPhaseSmulLetters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelOneClassEqClassicalShortSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaOneMapBaseTupleOfCharacterisationExtremal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumsSpanCuspFormsBaseTupleSecondField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGroupActsByLiftTranslationPrincipalType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivAtRecordOfEquivRow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelOfLinearMap

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.SerAll

section Read

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
  Formalism.L2.DIV GlobalTheory.FieldBC Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.MainNotions Formalism.IndefR.Links Formalism.IndefR.Mult GlobalTheory.OneMapAll
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

def valAt (O : OMDat C R i Tp tup) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c')
    (g : GA D (Wc D i)) : ℂ :=
  cc (O.dict g).1 * (O.mu g * rdU (unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c')) f (O.dict g).1 (O.dict g).2)

def ExactAt (O : OMDat C R i Tp tup) (_κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : (R.MW i (sg0 D A)).Vec)
    (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (S a : ℂ) : Prop :=
  ∀ (t : Tp) (h : O.Cl' t → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))),
    RepsR R i (tup t) h (O.bad t) J' (O.Lh t) (O.gam t) (O.vol t) →
    ∀ (y : (R.HV i (tup t)).H) (x : O.Cl' t → VsV D i O.c'.F), Place R i (tup t) h O.c0' y x →
    ∀ f, IsSum O t x f → ∀ g : GA D (Wc D i), a * R.thF i (tup t) y v₀ g =
      S * cc (O.dict g).1 * (O.mu g * rdU (unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c')) f (O.dict g).1 (O.dict g).2)

theorem valAt_of_isBC (O : OMDat C R i Tp tup) (cc) {m : ℕ} {f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c'}
    {as : Fin m → O.c'.F} {fs : Fin m → Rul (C.Q.Xo ((i : ℕ) + 1)) C.Q.c} (h : IsBC O.hle f as fs) (g : GA D (Wc D i)) :
    valAt O cc f g = ∑ k, (as k : ℂ) * O.phi cc (fs k) g := by
  have h2 := congrFun (congrFun (rdU_unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c') h) (O.dict g).1) (O.dict g).2
  rw [Finset.sum_apply, Finset.sum_apply] at h2
  refine (congrArg (fun w => cc (O.dict g).1 * (O.mu g * w)) h2).trans ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show cc _ * (O.mu _ * ((as k : ℂ) * _)) = (as k : ℂ) * (cc _ * O.mu _ * _)
  ring

theorem valAt_leftInv (hL : LawsM C) (O : OMDat C R i Tp tup) (cc) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (hn : κ.n = (Vc D i).rank)
    {f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c'} (hf : f ∈ sec _ O.c' (wtA κ) (Vc D i).rank) :
    ∀ γ ∈ GQ (Wc D i), ∀ g, valAt O cc f (γ * g) = valAt O cc f g := by
  intro γ hγ g
  obtain ⟨m, as, fs, hfs, h⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ O.hle).1 _ _ f hf
  rw [valAt_of_isBC O cc h, valAt_of_isBC O cc h]
  refine Finset.sum_congr rfl fun k _ => congrArg (_ * ·) ?_
  exact GlobalTheory.PhaseRational.adel_muPin_leftInv hL ⟨Nat.le_add_left _ _, i.2⟩ (σ := O.s0) C.good_σ₀ O.hV cc (dom_wtA κ)
    (hn ▸ hfs k) γ hγ g

set_option maxHeartbeats 1000000 in

theorem ser_of_exact (hL : LawsM C) (O : OMDat C R i Unit (fun _ => A.μ0)) (M : OMDat C R i Tp tup) (hle : O.c'.F ≤ M.c'.F)
    (hlev : M.lev = O.lev) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} (hn : κ.n = (Vc D i).rank) {v₀ ι x₀ x₁} (hO : O.Pins κ v₀ ι x₀)
    (hM : M.Pins κ v₀ ι x₁) (hspan : ClassSumsSpan O κ) (cE cF : ∀ s : C.Q.c.F →+* ℂ, (C.U ((i : ℕ) + 1) s).Comp → ℂ)
    {ph S a b : ℂ} (hrow : O.OneMapOf κ v₀ (cE O.s0) ph) (ha : ∃ m : ℕ, 0 < m ∧ a ^ m = 1) (hb : ∃ m : ℕ, 0 < m ∧ b ^ m = 1)
    (eO : ExactAt O κ v₀ (cF O.s0) S a) (eM : ExactAt M κ v₀ (cF M.s0) S b)
    (hrule : ∀ t x, ∃ f ∈ cuspOver M κ, IsSum M t x f) :
    ∃ (ζ : ℂ) (z : G), (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧ z ∈ Subgroup.center G ∧
      ∀ (t : Tp) (h : M.Cl' t → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))),
      RepsR R i (tup t) h (M.bad t) J' (M.Lh t) (M.gam t) (M.vol t) →
      ∀ (y : (R.HV i (tup t)).H) (x : M.Cl' t → VsV D i M.c'.F), Place R i (tup t) h M.c0' y x →
      ∀ f ∈ sec (C.Q.Xo ((i : ℕ) + 1)) M.c' (wtA κ) (Vc D i).rank, IsSum M t x f → ∀ g : GA D (Wc D i),
        ph * R.thF i (tup t) y v₀ g = ζ * cE M.s0 (M.dict g).1 * (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * M.mu g *
          rdU (unfBC M.hle (C.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z f) (M.dict g).1 (M.dict g).2 := by
  have hact := hM.act.1
  obtain ⟨-, ⟨-, -, -, -, -, z, hz, hO'⟩, -⟩ := hrow
  obtain ⟨ζ, -, ⟨m, hm, hζ⟩, hO'⟩ := hO' ()
  obtain ⟨ma, hma, ha⟩ := ha
  obtain ⟨mb, hmb, hb⟩ := hb
  have hb0 : b ≠ 0 := fun h0 => by simp [h0, hmb.ne'] at hb
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s = (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℝ) := ⟨_, rfl⟩
  have mul4 : ∀ a b d : ℂ, a * b * (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℝ) * d = a * s * (b * d) :=
    fun a b d => by rw [hs]; ring
  obtain ⟨h₀, J₀, hr₀, -, hth₀, hpl₀⟩ := (hO.tuple ()).reps
  have key : ∀ q, ∀ f ∈ cuspOver M κ, (a * ζ * s) * geo M (cE M.s0) z f q = (ph * S) * geo M (cF M.s0) 1 f q := by
    intro q
    refine geo_agree O M hle hact hspan q ?_
    rintro g hg ⟨x, hx, hgx⟩
    have hg' := ((mem_cusp _ _ _ _ _ _).1 hg).1
    obtain ⟨y, hy⟩ := (hpl₀ x).1 hx
    have h1 : ph * O.thAd () x q = ζ * s * geo O (cE O.s0) z g q := ((hO' x hx).2 g hg' hgx q).trans (mul4 _ _ _)
    have h0 : actLev (Xo := C.Q.Xo ((i : ℕ) + 1)) O.c' O.lev2 1 g = g :=
      actL_one _ _ _ hO.act.2.total hO.act.2.func hO.act.2.one hg'.1
    have h2 : a * O.thAd () x q = S * geo O (cF O.s0) 1 g q := by
      unfold geo
      rw [h0, hth₀ _ x hy]
      exact (eO () h₀ J₀ hr₀ _ x hy g hgx q.out).trans (mul_assoc _ _ _)
    rw [geo_rulBC O M hle hlev hO.act.1 cE z hg', geo_rulBC O M hle hlev hO.act.1 cF 1 hg']
    linear_combination ph * h2 - a * h1
  refine ⟨a * ζ * b⁻¹, z, ⟨ma * m * mb, by positivity, ?_⟩, hz, fun t h J' hr y x hx f hf hfx g => ?_⟩
  · have a1 : a ^ (ma * m * mb) = 1 := by rw [mul_assoc, pow_mul, ha, one_pow]
    have a2 : ζ ^ (ma * m * mb) = 1 := by rw [mul_comm ma m, mul_assoc, pow_mul, hζ, one_pow]
    have a3 : b ^ (ma * m * mb) = 1 := by rw [mul_comm, pow_mul, hb, one_pow]
    rw [mul_pow, mul_pow, inv_pow, a1, a2, a3]
    simp
  · have hf₀ : f ∈ cuspOver M κ := (hrule t x).elim fun f₀ h =>
      (isSum_unique hM t ((mem_cusp _ _ _ _ _ _).1 h.1).1 hf h.2 hfx) ▸ h.1
    have hA := hM.act.2
    have h0 : actLev (Xo := C.Q.Xo ((i : ℕ) + 1)) M.c' M.lev2 1 f = f := actL_one _ _ _ hA.total hA.func hA.one hf.1
    have hzf : actLev (Xo := C.Q.Xo ((i : ℕ) + 1)) M.c' M.lev2 z f ∈ sec _ M.c' (wtA κ) (Vc D i).rank :=
      actL_mem _ _ _ _ hA.total hA.nat hA.bor _ z hf
    have h2 : (a * ζ * s) * valAt M (cE M.s0) (actLev M.c' M.lev2 z f) g = (ph * S) * valAt M (cF M.s0) f g := by
      refine GlobalTheory.PhaseRational.eq_of_out (V := Wc D i)
        (F := fun g => (a * ζ * s) * valAt M (cE M.s0) (actLev M.c' M.lev2 z f) g)
        (F' := fun g => (ph * S) * valAt M (cF M.s0) f g)
        (fun γ hγ g => congrArg (_ * ·) (valAt_leftInv hL M _ κ hn hzf γ hγ g))
        (fun γ hγ g => congrArg (_ * ·) (valAt_leftInv hL M _ κ hn hf γ hγ g)) (fun q => ?_) g
      have h3 := key q f hf₀
      unfold geo at h3
      rw [h0] at h3
      exact h3
    have h1 : b * R.thF i (tup t) y v₀ g = S * valAt M (cF M.s0) f g :=
      (eM t h J' hr y x hx f hfx g).trans (mul_assoc _ _ _)
    have i1 := mul_inv_cancel₀ hb0
    have mul5 : ∀ a b d e : ℂ, a * s * (b * (d * e)) =
        a * b * (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℝ) * d * e := fun a b d e => by rw [hs]; ring
    refine Eq.trans (b := a * ζ * b⁻¹ * s * valAt M (cE M.s0) (actLev M.c' M.lev2 z f) g) ?_ (mul5 _ _ _ _)
    apply mul_left_cancel₀ hb0
    linear_combination ph * h1 - h2 - (a * ζ * s * valAt M (cE M.s0) (actLev M.c' M.lev2 z f) g) * i1

end Read

section Constants

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {i : Fin D.R.m} {Tp Tp' : Type} {tup : Tp → T0} {tup' : Tp' → T0}

open GlobalTheory.AdTh.CoverVal in

theorem exists_covAt_root (hR : GlobalTheory.Hk3.Core R F) (hT : TieIn T R κ v₀) (O : OMDat T.toCore R i Tp tup)
    (hO : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) :
    ∃ c0 : ℂ, (∃ m : ℕ, 0 < m ∧ c0 ^ m = 1) ∧ GlobalTheory.PtId.CovAt O c0 := by
  obtain ⟨c0, hm, hc⟩ := hO.cxi
  refine ⟨c0, hm, ?_⟩
  intro t X g bas idx e k xk mk hX hp hs hi hL hxk hmk hk y₂ A₂ hA₂
  obtain ⟨hU, hW, g', e', F', ik, φ, th, hth, hD, hval⟩ := hc t
  obtain ⟨hlev, hA, -⟩ := hO.cov t
  obtain ⟨hX₀, hon₀, -, hp₀, -, -, h1, -, hΨ₀, -⟩ := GlobalTheory.AdTh.models_at_record_core D G Pl0 T0 A T R F κ v₀ hR hT i O.s0
    (sOv_eq _ _ _) (T.dict _ O.s0 1).1
  have hσ : GoodEmb (O.dδ t).c₂ ((inC O.c').comp ((O.dδ t).eF.symm : (O.dδ t).c₂.F →+* O.c'.F)) := rfl
  have hmod : ∀ j, IsMod (Wc D i) (rank_Wc i) ((O.U₂ t).X j) := fun j =>
    isMod_of _ _ _ (hW j) fun ρ => ((hU.2.1 j).2 _).2 ((hΨ₀ _).1 ((hX₀.psi _).2 ⟨ρ, rfl⟩))
  have hor : ∀ j, IsOrthogonalFrame ((O.U₂ t).X j) (T.x₀ ((i : ℕ) + 1) O.s0) := fun j τ hτ => by
    have hsp := sameSp_of (hmod j) hX₀ ((hU.2.1 j).1.trans hp₀.symm)
    rw [hsp.gm, hsp.p0]
    exact hon₀ ⟨τ, hsp.psi ▸ hτ⟩
  obtain ⟨Wt⟩ := nonempty_uw ((Formalism.L2.PjFree.isUnf_ofPj _).2 hU)
  obtain ⟨hon, γ, ⟨hγ, hl, hf⟩, hma, -⟩ := GlobalTheory.AdTh.dict_atComp_markAd D _ _ _ _ _ _ _ (O.U₂ t) hσ hU h1 hA R.θ (Wc D i) (rank_Wc i)
    (O.dict₂ t) (iotaW T i) g' e' F' ik φ th _ hR.models.inf hmod hor hth hD Wt k
  obtain ⟨hd, hpt⟩ := point_eq (Formalism.L2.PjFree.Unf.ofPj (O.U₂ t)) hσ hU h1 hA hR.models.inf (Wc D i) (rank_Wc i) (iotaW T i)
    _ Wt (O.dict₂ t k).1 (O.dict₂ t k).2 γ k hγ (hmod _) hl hf hon hma X g bas idx e mk hX hp hs hi hL hmk hk y₂ A₂ hA₂
  obtain ⟨γ', hγ', h2, h3, -⟩ := hD.2 k
  obtain ⟨-, -, hrat, hmul⟩ := GlobalTheory.Member.isDetRoot_laws D (Wc D i)
  obtain ⟨a, ha⟩ := hrat γ' hγ'
  have hv := hval k γ' ⟨hγ', h2, h3⟩
  rw [(hO.tuple t).xi _ _ (hmul _ _ _ _ ha hxk), map_mul, (hR.lev.xi (tup t)).1.2 a, _root_.one_mul] at hv
  exact (evR_eq_of_point _ hlev.2.2.2.2.2.2.2.1 _ y₂ hpt).trans ((dif_pos hd).symm.trans hv)

theorem extC_hw (O : OMDat T.toCore R i Tp tup) (hO : hwOK O.c' (lamV D i) O.hw) {c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W}
    (hc : GlobalTheory.ConjTwist.ExtC R i (inC O.c') O.c0' c) :
    c ⟨_, GlobalTheory.PtId.OneScalar.ten_extremal_mem ℂ (lamV D i)⟩ = O.c0' O.hw := by
  refine hc _ _ ?_
  rw [show (O.hw : Formalism.L2.DIV.Pol O.c'.F D.what₂.Tau (Vc D i).rank) = _ from hO]
  dsimp only
  rw [GlobalTheory.Proof.TensorMapDescent.map_ten]
  simp only [Formalism.L2.DIV.map_extremal]

theorem coefficientMap_extremalTensor_eq_of_sameExtension (O : OMDat T.toCore R i Tp tup) (M : OMDat T.toCore R i Tp' tup') (hO : hwOK O.c' (lamV D i) O.hw)
    (hM : hwOK M.c' (lamV D i) M.hw)
    (h : ∀ c, GlobalTheory.ConjTwist.ExtC R i (inC O.c') O.c0' c ↔ GlobalTheory.ConjTwist.ExtC R i (inC M.c') M.c0' c) :
    O.c0' O.hw = M.c0' M.hw := by
  obtain ⟨c, hc⟩ := GlobalTheory.OneMapAll.exists_coef_ext (inC O.c') (σ := inC O.c') (RingHom.id ℂ) (fun _ => rfl) (lamV D i) O.c0'
  exact (extC_hw O hO (c := c) hc).symm.trans (extC_hw M hM ((h c).1 hc))

set_option maxHeartbeats 1000000 in

theorem ioAt_transfer (hC : GlobalTheory.Hk3.Core R F) (hT : TieIn T R κ v₀) (hI : IoExt R) (O₀ : OMDat T.toCore R i Tp tup)
    (O : OMDat T.toCore R i Tp' tup') (hP₀ : O₀.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O₀.s0))
    (hP : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) (he : O₀.c0' O₀.hw = O.c0' O.hw) {ka₀ : ℂ}
    (hk₀ : GlobalTheory.PtId.IoAt O₀ (v₀ i (sg0 D A)) ka₀) : GlobalTheory.PtId.IoAt O (v₀ i (sg0 D A)) ka₀ := by
  obtain ⟨ka, -, hk⟩ := GlobalTheory.AdTh.PhaseMapCore.io_eq_phase_smul_core D G Pl0 T0 A T R F κ v₀ hC hT hI i Tp' tup' O hP
  intro lt hlt u hu
  suffices h : ka = ka₀ by
    subst h
    exact hk lt hlt u hu
  have e1 := hk lt hlt u hu A.μ0 O.hw
  have e2 := hk₀ lt hlt u hu A.μ0 O₀.hw
  obtain ⟨hw1, cga, -, hinj, -, -, -, -, hio, -⟩ := hP.io
  obtain ⟨hw2, cga', -, -, -, -, -, -, hio₀, -⟩ := hP₀.io
  have hne : O.io O.hw ≠ 0 := by
    intro h0
    have h1 : O.hw = 0 := hinj (h0.trans (map_zero _).symm)
    have h2 := (GlobalTheory.AdTh.OverCore.coefMap_norm_equivariant_basis D G Pl0 T0 A T R F κ v₀ hC hT i Tp' tup' O hP).1
    rw [h1, map_zero, norm_zero] at h2
    exact zero_ne_one h2
  rw [he, hio₀, GlobalTheory.PtId.OneScalar.map_pG_eq O₀.c' O.c' (inC O₀.c') (inC O.c'), ← hio, e1] at e2
  have hV := hP.lift.std
  obtain ⟨f1, f2, f3, f4, f5⟩ := GlobalTheory.AdTh.VecFockCore.vec_fock_core D G Pl0 T0 A T.Q.c.F R F hC i A.μ0 hV
  have hON : ∀ τ, IsONBasis (gramAt D (Vc D i) τ) 1 1 (Vc D i).rank := fun τ => by
    refine ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, ?_, ?_⟩
    · simp [gramAt, hV.1]
    · simp
  have hinjP := GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ (Vc D i) (Wc D i) (hC.thP.ωP i A.μ0).std hC.models.inf
    (fun _ => 1) (fun _ => 1) (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) (fun _ => (Vc D i).rank) _ f4 f3 hON f5
    (D.sp.V_sig _) (D.sp.W_sig _) (R.vP i A.μ0) f1 f2 (GlobalTheory.AdTh.VecNeCore.thetaVector_ne_zero_core D G Pl0 T0 A T.Q.c.F R F hC i hV)
  have hlti : Function.Injective lt := GlobalTheory.PtId.OneScalar.lt_injective (fun ρ => hT.laws.pins.1.2.2.2 ρ) lt hlt
  refine smul_left_injective ℂ (fun h0 => hne ?_) e2
  have h1 := hinjP (h0.trans (map_zero _).symm)
  have h2 := MvPolynomial.rename_injective lt hlti (h1.trans (map_zero _).symm)
  exact MvPolynomial.map_injective _ (inC O.c').injective (h2.trans (map_zero _).symm)

omit [Algebra T.Q.c.F D.what₂.LL] in

theorem exists_ccIs_family {θ : InfFam D} {V W : HSp D} {hr : W.rank = D.R.r} {j : ℕ} {σ : T.Q.c.F →+* ℂ}
    (hV : T.V j σ = W) {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f₀ : WO V W → ℂ} {cst : (T.U j σ).Comp → ℂ}
    (h : CcIs θ V W hr (T.U j σ) (castDict hV (T.dict j σ)) (castDict hV (T.mu j σ)) (T.x₀ j σ) om f₀ cst) :
    ∃ cF : ∀ s : T.Q.c.F →+* ℂ, (T.U j s).Comp → ℂ, ∀ (s : T.Q.c.F →+* ℂ) (_ : σ = s) (hV' : T.V j s = W),
      CcIs θ V W hr (T.U j s) (castDict hV' (T.dict j s)) (castDict hV' (T.mu j s)) (T.x₀ j s) om f₀ (cF s) := by
  refine ⟨fun s => if e : σ = s then e ▸ cst else fun _ => 1, fun s e hV' => ?_⟩
  subst e
  simp only [dif_pos]
  exact h

set_option maxHeartbeats 1000000 in

theorem exists_common (hCI : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2) (hC : GlobalTheory.Hk3.Core R F) (hT : TieIn T R κ v₀) (hI : IoExt R)
    (O : OMDat T.toCore R i Tp tup) (M : OMDat T.toCore R i Tp' tup')
    (hO : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0))
    (hM : M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0)) (he : O.c0' O.hw = M.c0' M.hw) :
    ∃ (S a b : ℂ) (cF : ∀ s : T.Q.c.F →+* ℂ, (T.U ((i : ℕ) + 1) s).Comp → ℂ), (∃ m : ℕ, 0 < m ∧ a ^ m = 1) ∧
      (∃ m : ℕ, 0 < m ∧ b ^ m = 1) ∧ ExactAt O (κ i) (v₀ i (sg0 D A)) (cF O.s0) S a ∧
      ExactAt M (κ i) (v₀ i (sg0 D A)) (cF M.s0) S b := by
  have hs : O.s0 = T.toCore.σ₀ := sOv_eq _ _ _
  obtain ⟨h1, h2, -⟩ := GlobalTheory.PtId.dict_cast T hT.laws _ (inR i) O.s0 (hs ▸ T.toCore.good_σ₀) (Wc D i) O.hV (rank_Wc i)
  obtain ⟨δ, hδ⟩ := GlobalTheory.AdTh.ShortSeriesCore.thetaKO_eq_short_series_core D G Pl0 T0 A _ R F hC i hO.lift.std _ _ (iotaW T i) h1 h2
  obtain ⟨ka, -, hio⟩ := GlobalTheory.AdTh.PhaseMapCore.io_eq_phase_smul_core D G Pl0 T0 A T R F κ v₀ hC hT hI i Tp tup O hO
  have hio' := ioAt_transfer hC hT hI O M hO hM he hio
  obtain ⟨a, ha, hca⟩ := exists_covAt_root hC hT O hO
  obtain ⟨b, hb, hcb⟩ := exists_covAt_root hC hT M hM
  obtain ⟨cc, hcc⟩ := GlobalTheory.AdTh.CcExCore.exists_ccIs_core hCI D G Pl0 T0 A T R F κ v₀ hC hT i Tp tup O hO
  obtain ⟨cF, hF⟩ := exists_ccIs_family O.hV hcc
  exact ⟨_, a, b, cF, ha, hb,
    fun t h J' hr y x hx f hf g => GlobalTheory.AdTh.SerCore.exact_identity_core hC hT O hO hio hδ hca (hF _ rfl O.hV) t h J' hr y x hx f hf g,
    fun t h J' hr y x hx f hf g => GlobalTheory.AdTh.SerCore.exact_identity_core hC hT M hM hio' hδ hcb
      (hF _ (hs.trans (sOv_eq _ M.c' M.hle).symm) M.hV) t h J' hr y x hx f hf g⟩

end Constants

section Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 1000000 in

theorem ser_at_core_constants : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → M.lev = (O i).lev → (∀ c, ExtC R i (inC (O i).c') (O i).c0' c ↔ ExtC R i (inC M.c') M.c0' c) → ∃ (ζ : ℂ) (z : G), IsRoot1 ζ ∧ z ∈ Subgroup.center G ∧ ∀ (t : Tp) (h : M.Cl' t → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))), RepsR R i (tup t) h (M.bad t) J' (M.Lh t) (M.gam t) (M.vol t) → ∀ (y : (R.HV i (tup t)).H) (x : M.Cl' t → VsV D i M.c'.F), Place R i (tup t) h M.c0' y x → ∀ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank, GlobalTheory.OneMapAll.IsSum M t x f → ∀ g : GA D (Wc D i), ph i * R.thF i (tup t) y (v₀ i (sg0 D A)) g = ζ * T.cE ((i : ℕ) + 1) M.s0 (M.dict g).1 * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * M.mu g * rdU (unfBC M.hle (T.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z f) (M.dict g).1 (M.dict g).2 := by
  intro hCI D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hsz hR _ ⟨fw⟩ hI _ i hpins htie Tp tup M hM hlev hext
  have hT : TieIn T R κ v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  have hrow0 := GlobalTheory.OneMapTies.oneMapRow0_of_ties_core hCI D G Pl0 T0 A T R F κ v₀ hR hT hI O i hpins
  have hspan := GlobalTheory.ClassSumSpanCore.classSumsSpan_core D G Pl0 T0 A T R F κ v₀ O hsz hR ⟨fw⟩ hI i hpins hrow0
  have hle : (O i).c'.F ≤ M.c'.F := by
    refine hpins.1.le.trans ?_
    rintro _ ⟨a, rfl⟩
    have e : ((M.jL a : M.c'.F) : ℂ) = D.what₂.embLL a := RingHom.congr_fun hM.lift.field a
    exact (show ((M.jL a : M.c'.F) : ℂ) = _ from e) ▸ (M.jL a).2
  have hn : (κ i).n = (Vc D i).rank :=
    (fw.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2).symm
  obtain ⟨S, a, b, cF, ha, hb, eO, eM⟩ := exists_common hCI hR hT hI (O i) M hpins.2 hM
    (coefficientMap_extremalTensor_eq_of_sameExtension (O i) M hpins.2.io.1 hM.io.1 hext)
  exact ser_of_exact fw.laws.toLawsM (O i) M hle hlev hn hpins.2 hM hspan (T.cE ((i : ℕ) + 1)) cF (htie hrow0) ha hb eO eM
    (GlobalTheory.ClassSumRule.exists_cusp_isThClsD_core hCI D G Pl0 T0 A T R F κ v₀ hR hT i Tp tup M hM)

end Top

end GlobalTheory.SerAll
