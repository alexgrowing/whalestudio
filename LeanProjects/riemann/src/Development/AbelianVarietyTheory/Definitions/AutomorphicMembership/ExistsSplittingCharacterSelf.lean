import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SplitFacTwistRight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmAdeleUnitCharacterReadingHeckeChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueNormalizedHaarMeasureAdelicUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaFunNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterInfinityExponentGroupLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyBesselPeriodPositionOneData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaConj
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoInfMulProd

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Th

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def AdmE (V W : HSp D) (χ χ' : IdC D) : Prop :=
  V.rank = W.rank ∧ IsHC D χ ∧ IsHC D χ' ∧ ResEta D χ V.rank ∧ ResEta D χ' W.rank

theorem admissibleEven_trivial {V W : HSp D} (h : V.rank = W.rank) (hV : Even V.rank) : AdmE V W 1 1 := by
  have h0 : ResEta D 1 0 := ⟨GlobalTheory.VolHeckeCompare.exists_isEta D, fun _ _ _ => by simp⟩
  have h1 := resEta_parity (m := V.rank) h0 (by rw [Nat.even_iff] at hV; omega)
  exact ⟨h, isHC_one D, isHC_one D, h1, h ▸ h1⟩

theorem exists_splittingCharacter_self {V W : HSp D} (e : V.rank = W.rank) : ∃ χ : IdC D, AdmE V W χ χ := by
  obtain ⟨η, h1, h2, h3, -⟩ := GlobalTheory.Mem.EtaTilde.exists_etaTilde D
  rcases Nat.even_or_odd V.rank with h | h
  · exact ⟨1, admissibleEven_trivial e h⟩
  · have := resEta_parity (m := V.rank) h3 (by rw [Nat.odd_iff] at h; omega)
    exact ⟨η, e, ⟨h1, fun τ => ⟨_, h2 τ⟩⟩, ⟨h1, fun τ => ⟨_, h2 τ⟩⟩, this, e ▸ this⟩

theorem IsHC.mul {χ ν : IdC D} (h : IsHC D χ) (k : IsHC D ν) : IsHC D (χ * ν) :=
  ⟨⟨h.1.1.mul k.1.1, fun x => by rw [MonoidHom.mul_apply, h.1.2, k.1.2, mul_one]⟩, fun τ =>
    (h.2 τ).elim fun _ ha => (k.2 τ).elim fun _ hb => ⟨_, GlobalTheory.Chain.StepVac.hasInfExp_mul ha hb⟩⟩

theorem AdmE.mul_right {V W : HSp D} {χ χ' ν : IdC D} (h : AdmE V W χ χ') (h1 : IsHC D ν) (h2 : ResEta D ν 0) :
    AdmE V W χ (χ' * ν) := ⟨h.1, h.2.1, h.2.2.1.mul h1, h.2.2.2.1, resEta_mul h.2.2.2.2 h2⟩

theorem AdmE.mul_left {V W : HSp D} {χ χ' ν : IdC D} (h : AdmE V W χ χ') (h1 : IsHC D ν) (h2 : ResEta D ν 0) :
    AdmE V W (χ * ν) χ' := ⟨h.1, h.2.1.mul h1, h.2.2.1, resEta_mul h.2.2.2.1 h2, h.2.2.2.2⟩

structure WeilFun.EqRank {ψ : AddChar (AF D.host.F) ℂ} (Wf : WeilFun D ψ) : Prop where
  weil : ∀ (V W : HSp D) χ χ', AdmE V W χ χ' → IsWeilOn ψ V W χ χ' (Wf.om V W χ χ')
  twW : ∀ (V W : HSp D) χ χ' ν, AdmE V W χ χ' → IsHC D ν → ResEta D ν 0 → ∀ g h x, IsDetRoot V g x →
    Wf.om V W χ (χ' * ν) (g, h) = (((ν x)⁻¹ : Circle) : ℂ) • Wf.om V W χ χ' (g, h)
  twV : ∀ (V W : HSp D) χ χ' ν, AdmE V W χ χ' → IsHC D ν → ResEta D ν 0 → ∀ g h x, IsDetRoot W h x →
    Wf.om V W (χ * ν) χ' (g, h) = ((ν x : Circle) : ℂ) • Wf.om V W χ χ' (g, h)

def WeilOnEqEx (D : D7) : Prop := ∀ ψ, IsStdChar D ψ (-1) → ∀ (V W : HSp D) χ χ', AdmE V W χ χ' → ∃ om, IsWeilOn ψ V W χ χ' om

def WeilTwEq (D : D7) : Prop := ∀ ψ, IsStdChar D ψ (-1) → ∀ (V W : HSp D) χ χ' ν, AdmE V W χ χ' → IsHC D ν → ResEta D ν 0 →
  ∀ om, IsWeilOn ψ V W χ χ' om →
    (∀ om', IsWeilOn ψ V W χ (χ' * ν) om' → ∀ g h x, IsDetRoot V g x → om' (g, h) = (((ν x)⁻¹ : Circle) : ℂ) • om (g, h)) ∧
    ∀ om', IsWeilOn ψ V W (χ * ν) χ' om' → ∀ g h x, IsDetRoot W h x → om' (g, h) = ((ν x : Circle) : ℂ) • om (g, h)

open Classical in

def WeilFun.patch {ψ : AddChar (AF D.host.F) ℂ} (Wf : WeilFun D ψ)
    (o : ∀ V W : HSp D, IdC D → IdC D → (GA D V × GA D W →* Module.End ℂ (ThS ψ V W))) : WeilFun D ψ :=
  let om := fun (V W : HSp D) χ χ' => if V.rank = W.rank then o V W χ χ' else Wf.om V W χ χ'
  have e : ∀ {V W : HSp D}, V.rank ≠ W.rank → ∀ χ χ', om V W χ χ' = Wf.om V W χ χ' := fun h _ _ => if_neg h
  { om := om
    om_heis := fun V W χ χ' ha => by rw [e ha.1]; exact Wf.om_heis V W χ χ' ha
    om_aut := fun V W χ χ' ha => by rw [e ha.1]; exact Wf.om_aut V W χ χ' ha
    om_cont := fun V W χ χ' ha => by rw [e ha.1]; exact Wf.om_cont V W χ χ' ha
    om_unit := fun V W χ χ' ha => by rw [e ha.1]; exact Wf.om_unit V W χ χ' ha
    om_split := fun V W χ χ' ha => by rw [e ha.1]; exact Wf.om_split V W χ χ' ha
    twW := fun V W χ χ' ν ha => by rw [e ha.1, e ha.1]; exact Wf.twW V W χ χ' ν ha
    twV := fun V W χ χ' ν ha => by rw [e ha.1, e ha.1]; exact Wf.twV V W χ χ' ν ha
    om_swap := fun V W χ χ' ha => by rw [e ha.1, e ha.1.symm]; exact Wf.om_swap V W χ χ' ha
    om_unr := fun V W χ χ' ha => by rw [e ha.1]; exact Wf.om_unr V W χ χ' ha }

theorem WeilFun.patch_om_eq {ψ : AddChar (AF D.host.F) ℂ} (Wf : WeilFun D ψ) (o) {V W : HSp D} (h : V.rank = W.rank) (χ χ') :
    (Wf.patch o).om V W χ χ' = o V W χ χ' := if_pos h

theorem WeilFun.patch_om_ne {ψ : AddChar (AF D.host.F) ℂ} (Wf : WeilFun D ψ) (o) {V W : HSp D} (h : V.rank ≠ W.rank) (χ χ') :
    (Wf.patch o).om V W χ χ' = Wf.om V W χ χ' := if_neg h

theorem WeilFun.exists_eqRank (he : WeilOnEqEx D) (ht : WeilTwEq D) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (Wf : WeilFun D ψ) : ∃ Wf' : WeilFun D ψ, Wf'.EqRank ∧
      ∀ V W χ χ', V.rank ≠ W.rank → Wf'.om V W χ χ' = Wf.om V W χ χ' := by
  classical
  choose o ho using he ψ hψ
  refine ⟨Wf.patch fun V W χ χ' => if k : AdmE V W χ χ' then o V W χ χ' k else 1, ⟨fun V W χ χ' k => ?_,
    fun V W χ χ' ν k h1 h2 g x y hy => ?_, fun V W χ χ' ν k h1 h2 g x y hy => ?_⟩,
    fun V W χ χ' h => WeilFun.patch_om_ne _ _ h _ _⟩
  · rw [WeilFun.patch_om_eq _ _ k.1, dif_pos k]; exact ho _ _ _ _ k
  · rw [WeilFun.patch_om_eq _ _ k.1, WeilFun.patch_om_eq _ _ k.1, dif_pos k, dif_pos (k.mul_right h1 h2)]
    exact (ht ψ hψ V W χ χ' ν k h1 h2 _ (ho _ _ _ _ k)).1 _ (ho _ _ _ _ _) g x y hy
  · rw [WeilFun.patch_om_eq _ _ k.1, WeilFun.patch_om_eq _ _ k.1, dif_pos k, dif_pos (k.mul_left h1 h2)]
    exact (ht ψ hψ V W χ χ' ν k h1 h2 _ (ho _ _ _ _ k)).2 _ (ho _ _ _ _ _) g x y hy

theorem isWeilOn_both_zero (ψ : AddChar (AF D.host.F) ℂ) {V W : HSp D} (hV : V.rank = 0) (hW : W.rank = 0) (χ χ' : IdC D) :
    IsWeilOn ψ V W χ χ' 1 := by
  haveI : IsEmpty (Fin W.rank) := by rw [hW]; infer_instance
  haveI : IsEmpty (Fin V.rank) := by rw [hV]; infer_instance
  have hs : ∀ x y : WA V W, x = y := fun x y => Matrix.ext fun _ j => isEmptyElim j
  refine ⟨fun g h w₀ Φ Φ' e => ?_, fun _ _ _ _ _ => rfl,
    fun Φ w => (continuous_const : Continuous fun _ : GA D V × GA D W => Φ.1 w), fun _ _ _ _ _ _ => rfl,
    fun e _ g h _ _ x y hx hy => ⟨1, one_pos, fun ℓ _ Φ => ?_⟩⟩
  · rw [hs (actHom V W g h w₀) w₀]; exact e
  · have hy1 : y = 1 := Units.ext (by rw [hy, Matrix.det_isEmpty]; simp)
    have hx1 : x = 1 := Units.ext (by rw [hx, Matrix.det_isEmpty]; simp)
    simp [splitFac, hy1, hx1]

theorem splitFac_twist_eq {V W : HSp D} (h : V.rank = W.rank) (χ χ' ν : IdC D) (x y : (AE D)ˣ) :
    splitFac V W χ (χ' * ν) x y = (ν x)⁻¹ * splitFac V W χ χ' x y ∧
      splitFac V W (χ * ν) χ' x y = ν y * splitFac V W χ χ' x y := by
  unfold splitFac
  simp only [if_pos h.le, MonoidHom.mul_apply]
  exact ⟨by rw [_root_.mul_inv_rev, mul_assoc], by rw [mul_comm (χ y), mul_left_comm]⟩

def LiftAutEq (D : D7) : Prop := ∀ θ : InfF D, IsInfFam θ → ∀ ψ, IsStdChar D ψ (-1) → ∀ (V W : HSp D) χ χ', AdmE V W χ χ' →
  ∀ om, IsWeilOn ψ V W χ χ' om → ∀ μ 𝓕, IsQuot V μ 𝓕 → ∀ (Φ : ThS ψ V W) F, IsCuspForm θ V F →
    (∀ h, IntegrableOn (fun g => (om (g, h) Φ).1 0 * F g) 𝓕 μ) ∧
    IsAutFunSm θ W fun h => ∫ g in 𝓕, (om (g, h) Φ).1 0 * F g ∂μ

structure RealisesE {θ : InfF D} {X : ThetaX D} {T : ThetaTied D X} {W : WeilTied D X T} (B : BesselTied D X T W)
    (Wf : WeilFun D W.ψ) (Tw : Tow D) (Rc : RecFun D θ W.ψ) : Prop where
  inf : IsInfFam θ

  eqRank : Wf.EqRank := by assumption

  forms : ∀ V, Set.range (T.ev V) = {φ | IsAutFunSm θ V φ}
  typ : ∀ V P F, F ∈ X.typ V P ↔ T.ev V F ∈ TypS θ V P

  sch : ∀ V V', Set.range (W.evS V V') = {f | IsThetaFun W.ψ V V' f}
  chr : ∀ μ j, T.eChr (X.chrOf μ j) = Rc.chr μ j
  eta : T.eChr X.etaT = Rc.eta
  col : ∀ u μ j φ, T.ev _ (X.colAF u μ j φ).1 = (Rc.col u μ j φ).1
  row : ∀ μ j F, T.ev _ (X.rowAF μ j F).1 = (Rc.row μ j F).1
  phi : ∀ μ j, W.evS _ _ (X.PhiY μ j) = (Rc.Phi μ j).1
  phiUp : PhiYupTied W
  mY : X.mY = Rc.mY
  petF : T.petF = Rc.petF
  petR : T.petR = Rc.meas.petR
  xs : X.Xs = Tw.Xs
  ys : X.Ys = Tw.Ys
  ysLow : X.YsLow = Tw.YsLow
  iXYs : ∀ t j, HEq (X.iXYs t j) (Tw.iXYs t j)
  iYXm : ∀ t, HEq (X.iYXm t) (Tw.iYXm t)
  om : ∀ V V' χ χ' p (Φ : X.Sch V V') (f : ThS W.ψ V V'), W.evS V V' Φ = f.1 →
    W.evS V V' (W.om V V' χ χ' p Φ) = (Wf.om V V' (T.eChr χ) (T.eChr χ') p f).1

  thOff : ∀ (V V' : HSp D) χ χ', ¬ ((admitted V V' (T.eChr χ) (T.eChr χ') ∨ AdmE V V' (T.eChr χ) (T.eChr χ')) ∧ V.SigOK) →
    X.th V V' χ χ' = 0

  thEq : ∀ (V V' : HSp D) χ χ', AdmE V V' (T.eChr χ) (T.eChr χ') → V.SigOK → ∀ μ 𝓕, IsVolPair D V μ 𝓕 →
    ∀ (Φ : X.Sch V V') (F : X.cusp V) (h : GA D V'), T.ev V' (X.th V V' χ χ' Φ F) h =
      (T.petC V : ℂ) * ∫ g in 𝓕, W.evS V V' (W.om V V' χ χ' (g, h) Φ) 0 * T.ev V (F : X.AF V) g ∂μ

  fact : ∀ V V' Φ, Φ ∈ X.fact V V' ↔ IsPureFun W.ψ V V' (W.evS V V' Φ)

  kfin : ∃ K : KfinTied W, K.cpt = Rc.dec.cpt ∧ K.bas = Rc.dec.bas

  posDat : ∀ u ho, B.dat _ _ _ ho (X.posSym u) = Rc.posSym u ∧ B.dat _ _ _ ho (X.pos1 u) = Rc.pos1 u

  pos1Val : ∀ u σ μ 𝓕, IsVolPair D (D.sp.X 0) μ 𝓕 → ∀ ν 𝓝, (Rc.per1.dat u).bes.IsUnitPair ν 𝓝 →
    ∀ s : GA D (D.sp.X 0) → GA D (D.sp.Y 0), (∀ h, EmbRel (D.sp.Y 0) (D.sp.X 0) (D.sp.iXY 0) (s h) h) →
    ∀ (φ : X.AF (D.sp.X 0)) (F : X.cusp (D.sp.Y 0)), X.Bper _ _ _ (X.pos1 u) σ φ F = (T.petC (D.sp.X 0) : ℂ) *
      (Rc.per1.dat u).period W.ψ μ 𝓕 ν 𝓝 s (fun g => star (T.ev _ φ g)) (T.ev _ (F : X.AF (D.sp.Y 0)))

  besAll : ∀ (A A' : HSp D) (ι : A.V →ₗ[D.host.E] A'.V) ho, A.SigOK → HSpace.IsIsomEmb A A' ι →
    ∀ d : BesDat A A' ι, (d.y : GA D A') = 1 → ∃ p, B.dat A A' ι ho p = d ∧ BesGlob T W.ψ d p

  besOnly : ∀ (A A' : HSp D) (ι : A.V →ₗ[D.host.E] A'.V) ho, A.SigOK → HSpace.IsIsomEmb A A' ι →
    ∀ p, BesGlob T W.ψ (B.dat A A' ι ho p) p ∨ ∃ u,
      (⟨A, A', ι, p⟩ : Σ (A A' : HSp D) (ι : A.V →ₗ[D.host.E] A'.V), X.Pos A A' ι) = ⟨_, _, _, X.pos1 u⟩

def RealisedExE (D : D7) : Prop := ∀ θ : InfF D, IsInfFam θ → ∀ ψ, IsStdChar D ψ (-1) →
  ∀ Wf : WeilFun D ψ, Wf.EqRank → ∀ (Tw : Tow D) (Rc : RecFun D θ ψ),
    ∃ (X : ThetaX D) (T : ThetaTied D X) (W : WeilTied D X T) (B : BesselTied D X T W) (h : W.ψ = ψ),
      RealisesE (θ := θ) B (h ▸ Wf) Tw (h ▸ Rc)

section Lift

variable {θ : InfF D} {X : ThetaX D} {T : ThetaTied D X} {W : WeilTied D X T} {B : BesselTied D X T W}
  {Wf : WeilFun D W.ψ} {Tw : Tow D} {Rc : RecFun D θ W.ψ}

set_option maxHeartbeats 1000000 in

theorem Realises.exists_liftEq (h : Realises B Wf Tw Rc) (hE : Wf.EqRank) (hL : LiftAutEq D) (V V' : HSp D) (χ χ' : X.Chr) :
    ∃ t : X.Sch V V' →ₗ[ℂ] X.cusp V →ₗ[ℂ] X.AF V',
      (¬ (AdmE V V' (T.eChr χ) (T.eChr χ') ∧ V.SigOK) → t = X.th V V' χ χ') ∧
      (AdmE V V' (T.eChr χ) (T.eChr χ') → V.SigOK → ∀ μ 𝓕, IsVolPair D V μ 𝓕 → ∀ Φ F x, T.ev V' (t Φ F) x =
        (T.petC V : ℂ) * ∫ g in 𝓕, W.evS V V' (W.om V V' χ χ' (g, x) Φ) 0 * T.ev V (F : X.AF V) g ∂μ) := by
  by_cases ha : AdmE V V' (T.eChr χ) (T.eChr χ') ∧ V.SigOK
  swap
  · exact ⟨_, fun _ => rfl, fun h1 h2 => absurd ⟨h1, h2⟩ ha⟩
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨μ, hμ, hu⟩ := GlobalTheory.Mem.VolMeasure.existsUnique_isVolMeasG D V ha.2
  obtain ⟨-, 𝓕, h𝓕⟩ := GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ hμ.1
  have hw := hE.weil _ _ _ _ ha.1
  have hth : ∀ Φ : X.Sch V V', W.evS V V' Φ ∈ ThS W.ψ V V' := fun Φ => by
    have hf : W.evS V V' Φ ∈ Set.range (W.evS V V') := ⟨Φ, rfl⟩
    rw [h.sch] at hf
    exact mem_ThS.2 hf
  have hom := fun p Φ => h.om V V' χ χ' p Φ ⟨_, hth Φ⟩ rfl
  have hc : ∀ F : X.cusp V, IsCuspForm θ V (T.ev V F) := fun F => by
    have hf : T.ev V F ∈ Set.range (T.ev V) := ⟨F, rfl⟩
    rw [h.forms] at hf
    exact ⟨hf, (T.cusp V F).1 F.2⟩
  have k := fun Φ (F : X.cusp V) => hL θ h.inf W.ψ W.ψ_std V V' _ _ ha.1 _ hw μ 𝓕 ⟨hμ.1, h𝓕⟩ ⟨_, hth Φ⟩ _ (hc F)
  simp only [← hom] at k
  have k2 : ∀ Φ (F : X.cusp V), ∃ G : X.AF V', T.ev V' G =
      fun x => ∫ g in 𝓕, W.evS V V' (W.om V V' χ χ' (g, x) Φ) 0 * T.ev V (F : X.AF V) g ∂μ := fun Φ F => by
    have := (k Φ F).2
    rw [← Set.mem_setOf_eq (p := fun φ => IsAutFunSm θ V' φ), ← h.forms] at this
    exact this
  choose G hG using k2
  refine ⟨(T.petC V : ℂ) • LinearMap.mk₂ ℂ G ?_ ?_ ?_ ?_, fun h' => absurd ha h', fun _ _ μ' 𝓕' hμ' Φ F x => ?_⟩
  · intro Φ Φ' F
    refine T.ev_inj V' (funext fun x => ?_)
    rw [map_add, Pi.add_apply, hG, hG, hG, ← integral_add ((k Φ F).1 x) ((k Φ' F).1 x)]
    simp [add_mul]
  · intro c Φ F
    refine T.ev_inj V' (funext fun x => ?_)
    rw [map_smul, Pi.smul_apply, hG, hG, ← integral_smul]
    simp [mul_assoc]
  · intro Φ F F'
    refine T.ev_inj V' (funext fun x => ?_)
    rw [map_add, Pi.add_apply, hG, hG, hG, ← integral_add ((k Φ F).1 x) ((k Φ F').1 x)]
    simp [mul_add]
  · intro c Φ F
    refine T.ev_inj V' (funext fun x => ?_)
    rw [map_smul, Pi.smul_apply, hG, hG, ← integral_smul]
    simp only [Submodule.coe_smul, map_smul, Pi.smul_apply, smul_eq_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun g => mul_left_comm _ _ _)
  · obtain rfl : μ' = μ := hu _ hμ'.1
    haveI := hμ.1
    rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, Pi.smul_apply, LinearMap.mk₂_apply, hG, smul_eq_mul]
    congr 1
    refine h𝓕.setIntegral_eq hμ'.2 fun γ g => ?_
    have e : Wf.om V V' (T.eChr χ) (T.eChr χ') ((γ : GA D V) * g, x) =
        Wf.om V V' (T.eChr χ) (T.eChr χ') (γ, 1) * Wf.om V V' (T.eChr χ) (T.eChr χ') (g, x) := by
      rw [← map_mul, Prod.mk_mul_mk, one_mul]
    show W.evS V V' (W.om V V' χ χ' ((γ : GA D V) * g, x) Φ) 0 * T.ev V F ((γ : GA D V) * g) = _
    rw [hom, hom, e, Module.End.mul_apply, hw.aut γ γ.2 1 (one_mem _), (hc F).1.left γ γ.2]

abbrev withLifts (X : ThetaX D) (t : ∀ V V', X.Chr → X.Chr → X.Sch V V' →ₗ[ℂ] X.cusp V →ₗ[ℂ] X.AF V') : ThetaX D :=
  { X with th := t }

theorem Realises.exists_realisesE (h : Realises B Wf Tw Rc) (hE : Wf.EqRank) (hL : LiftAutEq D) :
    ∃ (X' : ThetaX D) (T' : ThetaTied D X') (W' : WeilTied D X' T') (B' : BesselTied D X' T' W') (e : W'.ψ = W.ψ),
      RealisesE (θ := θ) B' (e ▸ Wf) Tw (e ▸ Rc) := by
  choose t t1 t2 using h.exists_liftEq hE hL
  let T' : ThetaTied D (withLifts X t) := { T with }
  let W' : WeilTied D (withLifts X t) T' :=
    { W with
      om_tw := ⟨W.om_tw.1, W.om_tw.2, W.om_tw.3, W.om_tw.4⟩
      th := fun V V' χ χ' hr h1 h2 hV μ 𝓕 hμ Φ F x => by
        show T.ev V' (t V V' χ χ' Φ F) x = _
        rw [t1 V V' χ χ' fun k => hr k.1.1]
        exact W.th V V' χ χ' hr h1 h2 hV μ 𝓕 hμ Φ F x }
  let B' : BesselTied D (withLifts X t) T' W' := { B with }
  obtain ⟨K, k1, k2⟩ := h.kfin
  refine ⟨withLifts X t, T', W', B', rfl,
    { h with
      eqRank := hE
      thOff := fun V V' χ χ' k => ?_
      thEq := t2
      kfin := ⟨{ K with }, k1, k2⟩
      besOnly := h.besOnly }⟩
  exact (t1 V V' χ χ' fun k' => k ⟨Or.inr k'.1, k'.2⟩).trans (h.thOff V V' χ χ' fun k' => k ⟨Or.inl k'.1, k'.2⟩)

end Lift

theorem realisedExE_of (h : RealisedEx D) (hL : LiftAutEq D) : RealisedExE D := fun θ hθ ψ hψ Wf hE Tw Rc => by
  obtain ⟨X, T, W, B, rfl, k⟩ := h θ hθ ψ hψ Wf Tw Rc
  exact Realises.exists_realisesE k hE hL

structure WeilThetaCompatibility {X : ThetaX D} {T : ThetaTied D X} (W : WeilTied D X T) : Prop where
  range : ∀ V V' : HSp D, V.rank = V'.rank → Set.range (W.evS V V') = {f | IsThetaFun W.ψ V V' f}
  Heisenberg₂ : ∀ (V V' : HSp D) χ χ', V.rank = V'.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') V'.rank →
    ∀ g h w₀ Φ Φ', W.evS V V' Φ' = Heisenberg₂ W.ψ V V' w₀ (W.evS V V' Φ) →
      W.evS V V' (W.om V V' χ χ' (g, h) Φ') =
        Formalism.L2.Theta.Heisenberg₂ W.ψ V V' (actHom V V' g h w₀) (W.evS V V' (W.om V V' χ χ' (g, h) Φ))
  aut : ∀ (V V' : HSp D) χ χ', V.rank = V'.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') V'.rank →
    ∀ γ ∈ GQ V, ∀ γ' ∈ GQ V', ∀ Φ, W.evS V V' (W.om V V' χ χ' (γ, γ') Φ) 0 = W.evS V V' Φ 0
  cont : ∀ (V V' : HSp D) χ χ', V.rank = V'.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') V'.rank →
    ∀ Φ w, Continuous fun p : GA D V × GA D V' => W.evS V V' (W.om V V' χ χ' p Φ) w
  unit : ∀ (V V' : HSp D) χ χ', V.rank = V'.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') V'.rank →
    ∀ (μ : Measure (WA V V')) (𝓕 : Set (WA V V')), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL V V') 𝓕 μ →
    ∀ p Φ, ∫ w in 𝓕, ‖W.evS V V' (W.om V V' χ χ' p Φ) w‖ ^ 2 ∂μ = ∫ w in 𝓕, ‖W.evS V V' Φ w‖ ^ 2 ∂μ
  split : ∀ (V V' : HSp D) χ χ', V.rank = V'.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') V'.rank →
    ∀ e, IsSplitIdem D e → ∀ g h, SuppAt e V g → SuppAt e V' h → ∀ x y, IsDetAt e V g x → IsDetAt e V' h y →
    ∃ r : ℝ, 0 < r ∧ ∀ ℓ : X.Sch V V' →ₗ[ℂ] ℂ,
      (∀ u : WA V V', (∀ i j, cA D e * u i j = u i j) → ∀ Φ Φ',
        W.evS V V' Φ' = Formalism.L2.Theta.Heisenberg₂ W.ψ V V' u (W.evS V V' Φ) → ℓ Φ' = ℓ Φ) →
      ∀ Φ, ℓ (W.om V V' χ χ' (g, h) Φ) = (r : ℂ) * (splitFac V V' (T.eChr χ) (T.eChr χ') x y : ℂ) * ℓ Φ
  twW : ∀ (V V' : HSp D) χ χ' ν, V.rank = V'.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') V'.rank →
    ResEta D (T.eChr ν) 0 → ∀ g h x, IsDetRoot V g x →
      W.om V V' χ (χ' * ν) (g, h) = (((T.eChr ν x)⁻¹ : Circle) : ℂ) • W.om V V' χ χ' (g, h)
  twV : ∀ (V V' : HSp D) χ χ' ν, V.rank = V'.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') V'.rank →
    ResEta D (T.eChr ν) 0 → ∀ g h x, IsDetRoot V' h x →
      W.om V V' (χ * ν) χ' (g, h) = ((T.eChr ν x : Circle) : ℂ) • W.om V V' χ χ' (g, h)
  th : ∀ (V V' : HSp D) χ χ', V.rank = V'.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') V'.rank → V.SigOK →
    ∀ μ 𝓕, IsVolPair D V μ 𝓕 → ∀ (Φ : X.Sch V V') (F : X.cusp V) (h : GA D V'),
      T.ev V' (X.th V V' χ χ' Φ F) h =
        (T.petC V : ℂ) * ∫ g in 𝓕, W.evS V V' (W.om V V' χ χ' (g, h) Φ) 0 * T.ev V (F : X.AF V) g ∂μ

namespace RealisesE

variable {θ : InfF D} {X : ThetaX D} {T : ThetaTied D X} {W : WeilTied D X T} {B : BesselTied D X T W}
  {Wf : WeilFun D W.ψ} {Tw : Tow D} {Rc : RecFun D θ W.ψ} (h : RealisesE B Wf Tw Rc)

include h

theorem eq_of_isInfFam {θ' : InfF D} (h' : IsInfFam θ') : θ' = θ :=
  ((GlobalTheory.AutFunCompare.isInfFam_iff θ').1 h').trans ((GlobalTheory.AutFunCompare.isInfFam_iff θ).1 h.inf).symm

theorem afTiedSm : ThetaSmoothnessCondition T := ⟨⟨θ, h.inf⟩, fun _ h' V _ => by rw [h.eq_of_isInfFam h']; exact h.forms V⟩

theorem formSub : FormSub D := fun θ' h' V φ => by
  rw [h.eq_of_isInfFam h']
  refine ⟨fun hφ => ?_, fun hφ => Submodule.subset_span hφ⟩
  have : AFs θ V ≤ LinearMap.range (T.ev V) := Submodule.span_le.2 (by rw [LinearMap.coe_range, h.forms V])
  have h2 : φ ∈ Set.range (T.ev V) := this hφ
  rwa [h.forms V] at h2

theorem typTied (ht : TypAdd D) : TypTied T := ⟨⟨θ, h.inf⟩, fun _ h' V hV P hP => by
  intros
  rename_i F
  rw [h.eq_of_isInfFam h', h.typ, mem_TypS h.formSub ht h.inf hV hP]
  have : T.ev V F ∈ Set.range (T.ev V) := ⟨F, rfl⟩
  rw [h.forms V] at this
  exact ⟨fun k => k.2, fun k => ⟨this, k⟩⟩⟩

theorem weilUnrTied : WeilUnramifiedCondition W := fun V V' χ χ' hr h1 h2 S u1 u2 k hk k' hk' Φ hΦ => by
  have hc : ∀ χ, IsHC D (T.eChr χ) := fun χ => by
    have : T.eChr χ ∈ Set.range T.eChr := ⟨χ, rfl⟩
    rwa [T.eChr_range] at this
  have hf : W.evS V V' Φ ∈ Set.range (W.evS V V') := ⟨Φ, rfl⟩
  rw [h.sch] at hf
  refine W.evS_inj V V' ?_
  rw [h.om V V' χ χ' (k, k') Φ ⟨_, mem_ThS.2 hf⟩ rfl,
    Wf.om_unr V V' _ _ ⟨hr, hc χ, hc χ', h1, h2⟩ S u1 u2 k hk k' hk' _ hΦ]

def schEquiv (V V' : HSp D) : X.Sch V V' ≃ₗ[ℂ] ThS W.ψ V V' :=
  LinearEquiv.ofBijective ((W.evS V V').codRestrict _ fun Φ => mem_ThS.2 (by
      have hf : W.evS V V' Φ ∈ Set.range (W.evS V V') := ⟨Φ, rfl⟩
      rwa [h.sch] at hf))
    ⟨fun _ _ e => W.evS_inj V V' (congrArg Subtype.val e), fun f => by
      have hf : f.1 ∈ Set.range (W.evS V V') := by rw [h.sch]; exact mem_ThS.1 f.2
      exact hf.imp fun _ e => Subtype.ext e⟩

theorem schEquiv_om (V V' : HSp D) (χ χ') (p) (Φ : X.Sch V V') :
    h.schEquiv V V' (W.om V V' χ χ' p Φ) = Wf.om V V' (T.eChr χ) (T.eChr χ') p (h.schEquiv V V' Φ) :=
  Subtype.ext (h.om V V' χ χ' p Φ _ rfl)

theorem eqTied : WeilThetaCompatibility W := by
  have hc : ∀ χ, IsHC D (T.eChr χ) := fun χ => by
    have : T.eChr χ ∈ Set.range T.eChr := ⟨χ, rfl⟩
    rwa [T.eChr_range] at this
  have ha : ∀ {V V' : HSp D} {χ χ'}, V.rank = V'.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') V'.rank →
      AdmE V V' (T.eChr χ) (T.eChr χ') := fun hr h1 h2 => ⟨hr, hc _, hc _, h1, h2⟩
  have ho := fun V V' χ χ' p Φ => h.om V V' χ χ' p Φ (h.schEquiv V V' Φ) rfl
  refine ⟨fun V V' _ => h.sch V V', fun V V' χ χ' hr h1 h2 g x w₀ Φ Φ' e => ?_, fun V V' χ χ' hr h1 h2 γ hγ γ' hγ' Φ => ?_,
    fun V V' χ χ' hr h1 h2 Φ w => ?_, fun V V' χ χ' hr h1 h2 μ 𝓕 hμ h𝓕 p Φ => ?_,
    fun V V' χ χ' hr h1 h2 e he g x hg hx a b k1 k2 => ?_, fun V V' χ χ' ν hr h1 h2 h3 g x a k => ?_,
    fun V V' χ χ' ν hr h1 h2 h3 g x a k => ?_, fun V V' χ χ' hr h1 h2 => h.thEq V V' χ χ' (ha hr h1 h2)⟩
  · rw [ho, ho]; exact (h.eqRank.weil _ _ _ _ (ha hr h1 h2)).Heisenberg₂ g x w₀ _ _ e
  · rw [ho]; exact (h.eqRank.weil _ _ _ _ (ha hr h1 h2)).aut γ hγ γ' hγ' _
  · simp only [ho]; exact (h.eqRank.weil _ _ _ _ (ha hr h1 h2)).cont _ w
  · rw [ho]; exact (h.eqRank.weil _ _ _ _ (ha hr h1 h2)).unit μ 𝓕 hμ h𝓕 p _
  · obtain ⟨r, hr0, k⟩ := (h.eqRank.weil _ _ _ _ (ha hr h1 h2)).split e he g x hg hx a b k1 k2
    refine ⟨r, hr0, fun ℓ hℓ Φ => ?_⟩
    have := k (ℓ ∘ₗ (h.schEquiv V V').symm.toLinearMap) (fun u hu f f' e' => by
      obtain ⟨Ψ, rfl⟩ := (h.schEquiv V V').surjective f
      obtain ⟨Ψ', rfl⟩ := (h.schEquiv V V').surjective f'
      simpa using hℓ u hu Ψ Ψ' e') (h.schEquiv V V' Φ)
    rw [← h.schEquiv_om] at this
    simpa using this
  · refine LinearMap.ext fun Φ => (h.schEquiv V V').injective ?_
    rw [LinearMap.smul_apply, map_smul, h.schEquiv_om, h.schEquiv_om, map_mul,
      h.eqRank.twW _ _ _ _ _ (ha hr h1 h2) (hc ν) h3 g x a k, LinearMap.smul_apply]
  · refine LinearMap.ext fun Φ => (h.schEquiv V V').injective ?_
    rw [LinearMap.smul_apply, map_smul, h.schEquiv_om, h.schEquiv_om, map_mul,
      h.eqRank.twV _ _ _ _ _ (ha hr h1 h2) (hc ν) h3 g x a k, LinearMap.smul_apply]

theorem allTied (ht : TypAdd D) {A : ProvA} (hr : RealTied D) (hp : ProvisionCompatibility D A) : Nonempty (AllTied D X A) := by
  obtain ⟨K, -⟩ := h.kfin
  exact ⟨⟨T, h.afTiedSm, h.typTied ht, W, h.weilUnrTied, K, h.phiUp, B, hr, hp⟩⟩

theorem petC_eq (V : HSp D) : T.petC V = Rc.petC V := by
  unfold ThetaTied.petC RecFun.petC; rw [h.petF, h.petR]

theorem tieRowIsom (hi : Rc.RowIsom) : X.TieRowIsom := fun μ j hj x y => by
  obtain ⟨⟨m, hm⟩, h2⟩ := hi μ j hj x y
  have e := T.pet _ (D.sp.Y_sig j) m.1 m.2 hm (X.rowAF μ j x) (X.rowAF μ j y)
  unfold ThetaX.petY
  rw [e, (h2 m hm).2, h.row, h.row, h.mY, ← h.petC_eq]
  simp only [ThetaTied.petC, Complex.ofReal_mul, mul_assoc]

theorem tieBm (hi : Rc.TopTie) : X.TieBm := fun u μ φ F => by
  have hι : HSpace.IsIsomEmb (D.sp.Y D.R.m) (D.sp.X D.R.m) (D.sp.iX'.comp D.sp.eYm.symm.toLinearMap) := fun x y => by
    have h1 := D.sp.iX'_isom (D.sp.eYm.symm x) (D.sp.eYm.symm y)
    have h2 := D.sp.eYm_isom (D.sp.eYm.symm x) (D.sp.eYm.symm y)
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h2
    exact h1.trans h2.symm
  have hs := fun g => (GlobalTheory.AutFunCompare.embRel_iff _ _ _ hι _ g).2 rfl
  obtain ⟨⟨m, hm⟩, h2⟩ := hi u μ φ F _ hs
  rw [T.btop _ _ _ (D.sp.Y_sig _) hι m.1 m.2 hm _ hs, (h2 m hm).2]
  simp only [T.conj, star_star, h.col, h.row, h.mY, ← h.petC_eq, ThetaTied.petC, Complex.ofReal_mul, mul_assoc]

theorem carY_eq (μ s i) : T.eChr (X.carY μ s i) = Rc.carY μ s i := by
  unfold ThetaX.carY RecFun.carY
  split_ifs
  · rw [map_mul, map_inv, h.chr, h.eta]
  · exact h.chr _ _

theorem tieIo (hi : Rc.IoTie Wf) : X.TieIo := fun μ j hj y x => by
  obtain ⟨L, hL, hx⟩ := hi μ j hj y
  obtain ⟨⟨m, hm⟩, h2⟩ := hx x
  have e : T.ev _ (X.dnY μ j (X.rowAF μ (j + 1) y)) = L := by
    funext g
    obtain ⟨⟨n, hn⟩, h3⟩ := hL g
    have k := W.th _ _ _ _ (rank_Y_ne X j hj) (row_lift_ok T μ (j + 1) (by omega) hj (j + 1) hj)
      (row_lift_ok T μ (j + 1) (by omega) hj j hj.le) (D.sp.Y_sig _) n.1 n.2 hn (X.PhiY μ j) (X.rowAF μ (j + 1) y) g
    unfold ThetaX.dnY
    rw [LinearMap.smul_apply, map_smul, Pi.smul_apply, k, (h3 n hn).2]
    simp only [h.om _ _ _ _ _ _ _ (h.phi μ j), h.carY_eq, h.row, h.mY, ← h.petC_eq, WeilFun.ker, Complex.ofReal_mul,
      mul_assoc, smul_eq_mul]
  unfold ThetaX.petY
  rw [T.pet _ (D.sp.Y_sig j) m.1 m.2 hm, (h2 m hm).2, e, h.row, h.mY, ← h.petC_eq]
  simp only [ThetaTied.petC, Complex.ofReal_mul, mul_assoc]

end RealisesE

structure ChrRead {X : ThetaX D} (T : ThetaTied D X) (C : Formalism.L2.Host.CharFrame D)
    (xi : D.what₂.Tup → Formalism.L2.Host.HChar D.host.E) : Prop where
  chr : ∀ μ (j : Fin D.R.m), Formalism.IndefR.Links.ChrEq (T.eChr (X.chrOf μ (j.1 + 1))) (C.mu0 j * xi μ)
  eta : Formalism.IndefR.Links.ChrEq (T.eChr X.etaT) C.eta

structure RecFun.ChrIs {θ : InfF D} {ψ : AddChar (AF D.host.F) ℂ} (Rc : RecFun D θ ψ) (C : Formalism.L2.Host.CharFrame D)
    (xi : D.what₂.Tup → Formalism.L2.Host.HChar D.host.E) : Prop where
  chr : ∀ μ (j : Fin D.R.m), Formalism.IndefR.Links.ChrEq (Rc.chr μ (j.1 + 1)) (C.mu0 j * xi μ)
  eta : Formalism.IndefR.Links.ChrEq Rc.eta C.eta

open Formalism.IndefR.Links in

theorem RecFun.exists_chrIs (C : Formalism.L2.Host.CharFrame D) (xi : D.what₂.Tup → Formalism.L2.Host.HChar D.host.E)
    (hf : ∀ μ, ∃ n : ℕ, 0 < n ∧ (xi μ).OrderDvd n) (ht : ∀ μ, (xi μ).TrivOn D.host.F) (θ : InfF D)
    (ψ : AddChar (AF D.host.F) ℂ) : ∃ Rc : RecFun D θ ψ, Rc.ChrIs C xi := by
  choose n hn ho using hf
  choose m hm using fun j => GlobalTheory.CharTransport.exists_chrEq D (C.mu0 j) (C.isMu0 j).unitary
  choose x hx using fun μ => GlobalTheory.CharTransport.exists_chrEq D (xi μ) (Formalism.L2.Host.HChar.isUnitary_of_order (hn μ) (ho μ))
  obtain ⟨η, hη⟩ := GlobalTheory.CharTransport.exists_chrEq D C.eta C.isEta.unitary
  obtain ⟨θ₀, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  have hres := GlobalTheory.Mem.EtaTilde.isEta_res D η C.eta hη C.isEta
  obtain ⟨P⟩ := GlobalTheory.PosOneData.nonempty_besselPeriodPositionOneData D
  obtain ⟨Dc⟩ := GlobalTheory.Mem.ThModel.nonempty_orthDec D
  obtain ⟨R⟩ := nonempty_recFun θ ψ (GlobalTheory.Mem.AntiChar.exists_char D) (GlobalTheory.Mem.EtaTilde.exists_etaTilde D)
    (GlobalTheory.Mem.ThetaNonzero.exists_thetaFun_ne_zero D ψ) Dc P
  have h2 := D.R.two_le_m
  have hexp : ∀ μ (j : Fin D.R.m) τ, HasInfExp D (m j * x μ) τ (-(D.hc τ).e j) := fun μ j τ => by
    have := GlobalTheory.Chain.StepVac.hasInfExp_mul (GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hm j)
      (GlobalTheory.Chain.StepVac.hasInfQ_tau (C.isMu0 j).inf) τ)
      (GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ (hx μ) (hn μ) (ho μ) τ)
    rwa [add_zero, Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at this
  have heq : ∀ μ j, ChrEq (m j * x μ) (C.mu0 j * xi μ) := fun μ j =>
    ⟨⟨(hm j).1.1.mul (hx μ).1.1, fun y => by rw [MonoidHom.mul_apply, (hm j).1.2, (hx μ).1.2, mul_one]⟩,
      fun P e he k y hy => by
        rw [MonoidHom.mul_apply, Circle.coe_mul, (hm j).2 P e he k y hy, (hx μ).2 P e he k y hy, ← Units.val_mul]; rfl⟩
  have e : ∀ j : Fin D.R.m, (⟨(j.1 + 1 - 1) % D.R.m, Nat.mod_lt _ (by omega)⟩ : Fin D.R.m) = j := fun j =>
    Fin.ext (by simp [Nat.mod_eq_of_lt j.2])
  refine ⟨{ R with
    chr := fun μ j => m ⟨(j - 1) % D.R.m, Nat.mod_lt _ (by omega)⟩ * x μ
    chr_hc := fun μ _ => ⟨(heq μ _).1, fun τ => ⟨_, hexp μ _ τ⟩⟩
    chr_inf := fun μ j τ => by rw [e]; exact hexp μ j τ
    chr_res := fun μ _ _ _ => ⟨⟨_, hres⟩, fun η' _ a => by
      rw [pow_zero, MonoidHom.mul_apply, GlobalTheory.GridWeil.triv_base (hm _) (C.isMu0 _).triv a,
        GlobalTheory.GridWeil.triv_base (hx μ) (ht μ) a, mul_one]⟩
    eta := η, eta_hc := hη.1
    eta_inf := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hη
      (GlobalTheory.Chain.StepVac.hasInfQ_tau (a := fun _ => 1 / 2) ⟨_, fun _ => by norm_num, C.isEta.inf⟩)
    eta_res := ⟨⟨_, hres⟩, fun η' hη' a => by
      rw [(GlobalTheory.IdeleNormChar.existsUnique_isEta D).unique hη' hres, pow_one, MonoidHom.comp_apply]⟩
    eta_unr := GlobalTheory.EtaConjExist.unram_of_chrEq hη C.isEta.unr }, fun μ j => ?_, hη⟩
  show ChrEq (m _ * x μ) _
  rw [e]; exact heq μ j

def RowsAreForms (D : D7) (C : Formalism.L2.Host.CharFrame D) (xi : D.what₂.Tup → Formalism.L2.Host.HChar D.host.E) : Prop :=
  ∀ θ : InfF D, IsInfFam θ → ∀ ψ, IsStdChar D ψ (-1) → ∀ Wf : WeilFun D ψ,
    ∃ Rc : RecFun D θ ψ, Rc.ChrIs C xi ∧ Rc.RowIsom ∧ Rc.IoTie Wf

def RecordIsForms (D : D7) (C : Formalism.L2.Host.CharFrame D) (xi : D.what₂.Tup → Formalism.L2.Host.HChar D.host.E) : Prop :=
  ∀ θ : InfF D, IsInfFam θ → ∀ ψ, IsStdChar D ψ (-1) → ∀ Wf : WeilFun D ψ,
    ∃ Rc : RecFun D θ ψ, Rc.ChrIs C xi ∧ Rc.OfRecord Wf

theorem RecordIsForms.what₂ {C : Formalism.L2.Host.CharFrame D} {xi : D.what₂.Tup → Formalism.L2.Host.HChar D.host.E}
    (h : RecordIsForms D C xi) : RowsAreForms D C xi := fun θ hθ ψ hψ Wf =>
  (h θ hθ ψ hψ Wf).imp fun _ k => ⟨k.1, k.2.rowIsom, k.2.io⟩

theorem RealisesE.chrRead {θ : InfF D} {X : ThetaX D} {T : ThetaTied D X} {W : WeilTied D X T} {B : BesselTied D X T W}
    {Wf : WeilFun D W.ψ} {Tw : Tow D} {Rc : RecFun D θ W.ψ} (h : RealisesE B Wf Tw Rc) {C : Formalism.L2.Host.CharFrame D}
    {xi : D.what₂.Tup → Formalism.L2.Host.HChar D.host.E} (k : Rc.ChrIs C xi) : ChrRead T C xi :=
  ⟨fun μ j => by rw [h.chr]; exact k.chr μ j, by rw [h.eta]; exact k.eta⟩

theorem exists_chrRead (hX : RealisedExE D) (hW : WeilEx D) (he : WeilOnEqEx D) (htw : WeilTwEq D) (Tw : Tow D)
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (C : Formalism.L2.Host.CharFrame D)
    (xi : D.what₂.Tup → Formalism.L2.Host.HChar D.host.E) (hf : ∀ μ, ∃ n : ℕ, 0 < n ∧ (xi μ).OrderDvd n)
    (ht : ∀ μ, (xi μ).TrivOn D.host.F) :
    ∃ (X : ThetaX D) (T : ThetaTied D X) (W : WeilTied D X T), WeilThetaCompatibility W ∧ ChrRead T C xi := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  obtain ⟨Wf₀⟩ := hW ψ hψ
  obtain ⟨Wf, hE, -⟩ := Wf₀.exists_eqRank he htw hψ
  obtain ⟨Rc, hR⟩ := RecFun.exists_chrIs C xi hf ht θ ψ
  obtain ⟨X, T, W, B, rfl, k⟩ := hX θ hθ ψ hψ Wf hE Tw Rc
  exact ⟨X, T, W, k.eqTied, k.chrRead hR⟩

example (C : Formalism.L2.Host.CharFrame D) (θ : InfF D) (ψ : AddChar (AF D.host.F) ℂ) :
    ∃ Rc : RecFun D θ ψ, Rc.ChrIs C fun _ => 1 :=
  RecFun.exists_chrIs C _ (fun _ => ⟨1, one_pos, one_pow _⟩) (fun _ => ⟨fun _ _ => by
    rw [Formalism.L2.Host.HChar.resFin, MonoidHom.finset_prod_apply]; exact Finset.prod_eq_one fun _ _ => rfl, fun _ _ => by
    rw [Formalism.L2.Host.HChar.resInf, MonoidHom.finset_prod_apply]; exact Finset.prod_eq_one fun _ _ => rfl⟩) θ ψ

example {C : Formalism.L2.Host.CharFrame D} {nch} (Tp : Formalism.L2.Host.TupTied D C nch) (θ : InfF D) (ψ : AddChar (AF D.host.F) ℂ) :
    ∃ Rc : RecFun D θ ψ, Rc.ChrIs C Tp.xi := RecFun.exists_chrIs C _ Tp.xi_fin Tp.xi_triv θ ψ

example {V W : HSp D} (hV : V.rank = 0) (hW : W.rank = 0) : AdmE V W 1 1 := by
  have h0 : ResEta D 1 0 := ⟨GlobalTheory.VolHeckeCompare.exists_isEta D, fun _ _ _ => by simp⟩
  exact ⟨hV.trans hW.symm, isHC_one D, isHC_one D, hV ▸ h0, hW ▸ h0⟩

example {V W : HSp D} {χ χ' : IdC D} (h : admitted V W χ χ') : ¬ AdmE V W χ χ' := fun k => h.1 k.1

end GlobalTheory.Mem.Th

end
