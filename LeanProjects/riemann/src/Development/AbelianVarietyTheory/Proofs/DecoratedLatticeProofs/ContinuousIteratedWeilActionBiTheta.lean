import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumThetaJointlyContinuous
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTensorRuleOrthogonalSumSourceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTensorRuleTargetOrthogonalSumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianPairStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBiThetaIffJoin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaFunNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BiActCont

variable {D : D7} {X Y A S A' : HSp D} (d : OrthDec X S A) (e : OrthDec Y S A')

def four (C : WO A S → WO S A' → ℂ) (φ₁ : WO A A' → ℂ) (φ₂ : WO S S → ℂ) : WO X Y → ℂ := fun x =>
  C (sandwich e.pA d.jB x) (sandwich e.pB d.jA x) * (φ₁ (sandwich e.pB d.jB x) * φ₂ (sandwich e.pA d.jA x))

theorem four_eq (C : WO A S → WO S A' → ℂ) (φ₁ : WO A A' → ℂ) (φ₂ : WO S S → ℂ) (x : WO X Y) :
    four d e C φ₁ φ₂ x = C (e.resT A (d.resS Y x).2).1 (e.resT S (d.resS Y x).1).2 *
      (φ₁ (e.resT A (d.resS Y x).2).2 * φ₂ (e.resT S (d.resS Y x).1).1) := by
  simp only [four, sandwich_apply, OrthDec.resT_apply, OrthDec.resS_apply, Matrix.mul_assoc]

theorem four_symm (C : WO A S → WO S A' → ℂ) (φ₁ : WO A A' → ℂ) (φ₂ : WO S S → ℂ) (s₁ : WO S S) (s₂ : WO S A')
    (u₁ : WO A S) (u₂ : WO A A') :
    four d e C φ₁ φ₂ ((d.resS Y).symm ((e.resT S).symm (s₁, s₂), (e.resT A).symm (u₁, u₂))) =
      C u₁ s₂ * (φ₁ u₂ * φ₂ s₁) := by
  simp only [four_eq, AddEquiv.apply_symm_apply]

theorem symplOH_four (x y : WO X Y) : symplOH X Y x y =
    symplOH A S (sandwich e.pA d.jB x) (sandwich e.pA d.jB y) + symplOH S A' (sandwich e.pB d.jA x) (sandwich e.pB d.jA y) +
    (symplOH A A' (sandwich e.pB d.jB x) (sandwich e.pB d.jB y) +
      symplOH S S (sandwich e.pA d.jA x) (sandwich e.pA d.jA y)) := by
  rw [d.symplOH_resS, e.symplOH_resT, e.symplOH_resT]
  simp only [sandwich_apply, OrthDec.resT_apply, OrthDec.resS_apply, Matrix.mul_assoc]
  ring

variable {ψ : AddChar (AF D.host.F) ℂ} {C : WO A S → WO S A' → ℂ} {φ₁ : WO A A' → ℂ} {φ₂ : WO S S → ℂ}

theorem isThetaFunO_four (h : IsBiTheta ψ A S A' C) (h₁ : IsThetaFunO ψ A A' φ₁) (h₂ : IsThetaFunO ψ S S φ₂) :
    IsThetaFunO ψ X Y (four d e C φ₁ φ₂) where
  quasi γ w := by
    have e₁ : sandwich e.pA d.jB (ratW Y X γ) = ratW S A (e.qA * γ * d.iB) := by
      rw [ratW_eq, ratW_eq, rat_mul, rat_mul]; rfl
    have e₂ : sandwich e.pB d.jA (ratW Y X γ) = ratW A' S (e.qB * γ * d.iA) := by
      rw [ratW_eq, ratW_eq, rat_mul, rat_mul]; rfl
    have e₃ : sandwich e.pB d.jB (ratW Y X γ) = ratW A' A (e.qB * γ * d.iB) := by
      rw [ratW_eq, ratW_eq, rat_mul, rat_mul]; rfl
    have e₄ : sandwich e.pA d.jA (ratW Y X γ) = ratW S S (e.qA * γ * d.iA) := by
      rw [ratW_eq, ratW_eq, rat_mul, rat_mul]; rfl
    rw [symplOH_four d e]
    simp only [four, map_add]
    rw [e₁, e₂, e₃, e₄, h.quasiL, h.quasiR, h₁.quasi, h₂.quasi]
    simp only [neg_add, AddChar.map_add_eq_mul]
    ring
  level := by
    obtain ⟨U₁, hU₁, k₁⟩ := h.levL
    obtain ⟨U₂, hU₂, k₂⟩ := h.levR
    obtain ⟨U₃, hU₃, k₃⟩ := h₁.level
    obtain ⟨U₄, hU₄, k₄⟩ := h₂.level
    refine ⟨(U₁.comap (sandwich e.pA d.jB) ⊓ U₂.comap (sandwich e.pB d.jA)) ⊓
      (U₃.comap (sandwich e.pB d.jB) ⊓ U₄.comap (sandwich e.pA d.jA)),
      ((hU₁.preimage (continuous_sandwich _ _)).inter (hU₂.preimage (continuous_sandwich _ _))).inter
      ((hU₃.preimage (continuous_sandwich _ _)).inter (hU₄.preimage (continuous_sandwich _ _))), fun u hu h0 => ?_⟩
    funext w
    have e₁ := congrFun (k₁ _ hu.1.1 (map_sandwich _ _ _ h0) (sandwich e.pB d.jA w + sandwich e.pB d.jA u))
      (sandwich e.pA d.jB w)
    have e₂ := congrFun (k₂ _ hu.1.2 (map_sandwich _ _ _ h0) (sandwich e.pA d.jB w)) (sandwich e.pB d.jA w)
    have e₃ := congrFun (k₃ _ hu.2.1 (map_sandwich _ _ _ h0)) (sandwich e.pB d.jB w)
    have e₄ := congrFun (k₄ _ hu.2.2 (map_sandwich _ _ _ h0)) (sandwich e.pA d.jA w)
    simp only [heisO] at e₁ e₂ e₃ e₄ ⊢
    rw [symplOH_four d e]
    simp only [four, map_add, AddChar.map_add_eq_mul]
    rw [← e₂, ← e₁, ← e₃, ← e₄]
    ring
  cont := (h.cont.comp ((continuous_sandwich _ _).prodMk (continuous_sandwich _ _))).mul
    ((h₁.cont.comp (continuous_sandwich _ _)).mul (h₂.cont.comp (continuous_sandwich _ _)))
  smooth k L hL h0 w := by
    simp only [four, map_add]
    exact (h.smooth k ((sandwich e.pA d.jB).comp L) ((sandwich e.pB d.jA).comp L) ((continuous_sandwich _ _).comp hL)
      ((continuous_sandwich _ _).comp hL) (fun t => map_sandwich _ _ _ (h0 t)) (fun t => map_sandwich _ _ _ (h0 t)) _ _).mul
      ((h₁.smooth k ((sandwich e.pB d.jB).comp L) ((continuous_sandwich _ _).comp hL)
        (fun t => map_sandwich _ _ _ (h0 t)) _).mul
      (h₂.smooth k ((sandwich e.pA d.jA).comp L) ((continuous_sandwich _ _).comp hL)
        (fun t => map_sandwich _ _ _ (h0 t)) _))

theorem end_const_mul {Z : Type} (L : Module.End ℂ (Z → ℂ)) (c : ℂ) (f : Z → ℂ) (z : Z) :
    L (fun y => c * f y) z = c * L f z :=
  congrFun (L.map_smul c f) z

theorem om_four {χA χS χS' χA' : (AE D)ˣ →* Circle} {oma : Om A S} {omb : Om S A'} {Ω : Om X Y} {ΩS : Om S Y}
    {ΩA : Om A Y} {ω₁ : Om A A'} {ω₂ : Om S S} (ha : IsWeilDatumO ψ A S χA χS oma) (hb : IsWeilDatumO ψ S A' χS' χA' omb)
    (hΩ : IsWeilDatumO ψ X Y (χS' * χA) (χS * χA') Ω) (hS : IsWeilDatumO ψ S Y χS' (χS * χA') ΩS)
    (hA : IsWeilDatumO ψ A Y χA (χS * χA') ΩA) (hω₁ : IsWeilDatumO ψ A A' χA χA' ω₁) (hω₂ : IsWeilDatumO ψ S S χS' χS ω₂)
    (hΦ : IsThetaFunO ψ X Y (four d e C φ₁ φ₂)) (a : GA D A) (h h' : GA D S) (b : GA D A') (w : WO A S) (w' : WO S A') :
    Ω (d.emb (h', a), e.emb (h, b)) (four d e C φ₁ φ₂)
        ((d.resS Y).symm ((e.resT S).symm (0, w'), (e.resT A).symm (w, 0))) =
      (ω₁ (a, b) φ₁ 0 * ω₂ (h', h) φ₂ 0) * omb (h', b) (fun v => oma (a, h) (fun u => C u v) w) w' := by
  have hψ := ha.std
  have tS := GlobalTheory.T.thetaTensorRule_orthogonalSum_source D ψ hψ X S A d Y
  have tA := GlobalTheory.T.thetaTensorRule_targetOrthogonalSum D ψ hψ Y S A' e A
  have tB := GlobalTheory.T.thetaTensorRule_targetOrthogonalSum D ψ hψ Y S A' e S
  obtain ⟨th, ev⟩ := tS.om_slice χS' χA (χS * χA') Ω ΩS ΩA hΩ hS hA h' a (e.emb (h, b)) _ hΦ ((e.resT A).symm (w, 0))
  have inner : ∀ s₁ s₂, ΩA (a, e.emb (h, b))
      (fun v' => four d e C φ₁ φ₂ ((d.resS Y).symm ((e.resT S).symm (s₁, s₂), v'))) ((e.resT A).symm (w, 0)) =
      (ω₁ (a, b) φ₁ 0 * φ₂ s₁) * oma (a, h) (fun u => C u s₂) w := by
    intro s₁ s₂
    rw [(tA.om_slice χA χS χA' ΩA oma ω₁ hA ha hω₁ a h b _ ((tS.slice_theta _ hΦ).2 _) 0).2 w, ← end_const_mul]
    refine congrArg (fun f => oma (a, h) f w) (funext fun u => ?_)
    have : (fun v' => four d e C φ₁ φ₂ ((d.resS Y).symm ((e.resT S).symm (s₁, s₂), (e.resT A).symm (u, v')))) =
        fun v' => (C u s₂ * φ₂ s₁) * φ₁ v' := by
      funext v'; rw [four_symm]; ring
    rw [this, end_const_mul]; ring
  rw [ev, (tB.om_slice χS' χS χA' ΩS ω₂ omb hS hω₂ hb h' h b _ th w').2 0]
  simp only [inner, end_const_mul]
  have : (fun s₁ => ω₁ (a, b) φ₁ 0 * φ₂ s₁ * omb (h', b) (fun v => oma (a, h) (fun u => C u v) w) w') =
      fun s₁ => (ω₁ (a, b) φ₁ 0 * omb (h', b) (fun v => oma (a, h) (fun u => C u v) w) w') * φ₂ s₁ := by
    funext s₁; ring
  rw [this, end_const_mul]; ring

theorem exists_kernel_ne_zero {V W : HSp D} {χ χ' : (AE D)ˣ →* Circle} {om : Om V W} (h : IsWeilDatumO ψ V W χ χ' om)
    (p : GA D V × GA D W) : ∃ f, IsThetaFunO ψ V W f ∧ om p f 0 ≠ 0 := by
  obtain ⟨f, hf, f0⟩ := GlobalTheory.Mem.ThetaNonzero.exists_thetaO_ne_zero h.std V W
  obtain ⟨w, hw⟩ := Function.ne_iff.1 f0
  refine ⟨om p⁻¹ (heisO ψ V W w f), h.om_pres _ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all h.std hf w), ?_⟩
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, heisO, zero_add,
    symplOH_zero_left, AddChar.map_zero_eq_one, one_mul]
  exact hw

theorem hecke_mul {χ χ' : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) (h' : IsHeckeChar D χ') : IsHeckeChar D (χ * χ') :=
  ⟨h.1.mul h'.1, fun x => by rw [MonoidHom.mul_apply, h.2, h'.2, mul_one]⟩

theorem continuous_biAct : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (χA χS χS' χA' : (AE D)ˣ →* Circle) (oma : Om A S) (omb : Om S A'), IsWeilDatumO ψ A S χA χS oma → IsWeilDatumO ψ S A' χS' χA' omb → ∀ C, IsBiTheta ψ A S A' C → Continuous fun x : (GA D A × GA D S) × (GA D S × GA D A') × WO A S × WO S A' => omb x.2.1 (fun v => oma x.1 (fun u => C u v) x.2.2.1) x.2.2.2 := by
  intro D ψ A S A' χA χS χS' χA' oma omb ha hb C hC
  have hψ := ha.std
  have ex := GlobalTheory.T.exists_weilDatum_hermitianPair D
  obtain ⟨X, ⟨d⟩⟩ : ∃ X, Nonempty (OrthDec X S A) := ⟨_, ⟨GlobalTheory.BiTransfer.sumDec S A⟩⟩
  obtain ⟨Y, ⟨e⟩⟩ : ∃ Y, Nonempty (OrthDec Y S A') := ⟨_, ⟨GlobalTheory.BiTransfer.sumDec S A'⟩⟩
  have hY := hecke_mul ha.hecT hb.hecT
  have rY : ResEta D (χS * χA') Y.rank := e.rank_add ▸ resEta_mul ha.resT hb.resT
  have rX : ResEta D (χS' * χA) X.rank := d.rank_add ▸ resEta_mul hb.resS ha.resS
  obtain ⟨Ω, hΩ⟩ := ex X Y ψ _ _ hψ (hecke_mul hb.hecS ha.hecS) hY rX rY
  obtain ⟨ΩS, hS⟩ := ex S Y ψ _ _ hψ hb.hecS hY hb.resS rY
  obtain ⟨ΩA, hA⟩ := ex A Y ψ _ _ hψ ha.hecS hY ha.resS rY
  obtain ⟨ω₁, hω₁⟩ := ex A A' ψ _ _ hψ ha.hecS hb.hecT ha.resS hb.resT
  obtain ⟨ω₂, hω₂⟩ := ex S S ψ _ _ hψ hb.hecS ha.hecT hb.resS ha.resT
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨φ₁, h₁, n₁⟩ := exists_kernel_ne_zero hω₁ (x₀.1.1, x₀.2.1.2)
  obtain ⟨φ₂, h₂, n₂⟩ := exists_kernel_ne_zero hω₂ (x₀.2.1.1, x₀.1.2)
  have hΦ := isThetaFunO_four d e hC h₁ h₂
  have cK : Continuous fun x : (GA D A × GA D S) × (GA D S × GA D A') × WO A S × WO S A' =>
      ω₁ (x.1.1, x.2.1.2) φ₁ 0 * ω₂ (x.2.1.1, x.1.2) φ₂ 0 :=
    ((hω₁.om_cont _ h₁ 0).comp (continuous_fst.fst.prodMk continuous_snd.fst.snd)).mul
      ((hω₂.om_cont _ h₂ 0).comp (continuous_snd.fst.fst.prodMk continuous_fst.snd))
  have cG : Continuous fun x : (GA D A × GA D S) × (GA D S × GA D A') × WO A S × WO S A' =>
      ((d.emb (x.2.1.1, x.1.1), e.emb (x.1.2, x.2.1.2)),
        (d.resS Y).symm ((e.resT S).symm (0, x.2.2.2), (e.resT A).symm (x.2.2.1, 0))) :=
    ((d.continuous_emb.comp (continuous_snd.fst.fst.prodMk continuous_fst.fst)).prodMk
      (e.continuous_emb.comp (continuous_fst.snd.prodMk continuous_snd.fst.snd))).prodMk
      ((d.continuous_resS_symm Y).comp
        (((e.continuous_resT_symm S).comp (continuous_const.prodMk continuous_snd.snd.snd)).prodMk
          ((e.continuous_resT_symm A).comp (continuous_snd.snd.fst.prodMk continuous_const))))
  have cN := (GlobalTheory.Unf.jointCont_all D ψ X Y _ _ Ω hΩ _ hΦ).comp cG
  have nK := mul_ne_zero n₁ n₂
  refine (cN.continuousAt.div cK.continuousAt nK).congr ?_
  filter_upwards [cK.continuousAt.eventually_ne nK] with x hx
  rw [Pi.div_apply, div_eq_iff hx, mul_comm]
  exact om_four d e ha hb hΩ hS hA hω₁ hω₂ hΦ _ _ _ _ _ _

end GlobalTheory.BiActCont

end
