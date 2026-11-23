import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.GaussRMulFactor
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeisGFixOfMemLattice
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticCharacterRealFinitePointsMatchStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPointsClassicalModelRealVectorSpaceStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompactStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionSpaceHeisenbergLawsStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HomSymplecticHalfFormAlgebraicLawsContinuous
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.ZakEx

open GlobalTheory.WeilVacMove

variable {D : D7} {S T : HSp D}

theorem sym_sub_left (x x' y : WO S T) : symplOH S T (x - x') y = symplOH S T x y - symplOH S T x' y := by
  rw [eq_sub_iff_add_eq, ← symplOH_add_left, sub_add_cancel]

theorem sym_sub_right (x y y' : WO S T) : symplOH S T x (y - y') = symplOH S T x y - symplOH S T x y' := by
  rw [eq_sub_iff_add_eq, ← symplOH_add_right, sub_add_cancel]

theorem psi_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {γ γ' : WO S T} (h : γ ∈ ratL T S)
    (h' : γ' ∈ ratL T S) : ψ (symplOH S T γ γ') = 1 := by
  obtain ⟨a, ha⟩ := (GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.2.2.1 γ h γ' h'
  rw [ha, hψ.1.2.2.1]

theorem exists_extension {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (p : WO S T →+ V) (hp : Continuous p) (F : V → ℂ) (hF : ContDiff ℝ ∞ F)
    (O : AddSubgroup (WO S T)) (hO : IsOpen (O : Set (WO S T))) (hre : ∀ w, IsRealPt w → w ∈ O)
    (hcov : ∀ w, ∃ γ ∈ ratL T S, w - γ ∈ O)
    (hq : ∀ δ ∈ ratL T S, δ ∈ O → ∀ w ∈ O, F (p (w + δ)) = ψ (-symplOH S T δ w) * F (p w))
    (hl : ∀ u ∈ O, IsFinPt u → p u = 0 ∧ ∀ w ∈ O, ψ (symplOH S T w u) = 1) :
    ∃ f, IsThetaFunO ψ S T f ∧ ∀ w, IsRealPt w → f w = F (p w) := by
  haveI : IsTopologicalAddGroup (Formalism.L2.Theta.AE D) := IsTopologicalRing.to_topologicalAddGroup
  haveI : IsTopologicalAddGroup (WO S T) := Pi.topologicalAddGroup
  haveI : ContinuousSub (WO S T) := IsTopologicalAddGroup.to_continuousSub
  choose c hc hcO using hcov
  let f : WO S T → ℂ := fun w => ψ (-symplOH S T (c w) w) * F (p (w - c w))
  have key : ∀ γ ∈ ratL T S, ∀ w, w - γ ∈ O → f w = ψ (-symplOH S T γ w) * F (p (w - γ)) := by
    intro γ hγ w hw
    have h1 : γ - c w ∈ O := by
      have := O.sub_mem (hcO w) hw
      rwa [sub_sub_sub_cancel_left] at this
    have h2 := hq _ ((ratL T S).sub_mem hγ (hc w)) h1 _ hw
    rw [sub_add_sub_cancel] at h2
    have h3 := psi_rat hψ ((ratL T S).sub_mem hγ (hc w)) hγ
    show ψ (-symplOH S T (c w) w) * F (p (w - c w)) = _
    rw [h2, ← mul_assoc, ← AddChar.map_add_eq_mul, ← one_mul (ψ (-symplOH S T γ w)), ← h3,
      ← AddChar.map_add_eq_mul, sym_sub_right, sym_sub_left γ (c w) w]
    congr 2
    ring
  refine ⟨f, ⟨fun γ w => ?_, ⟨O, hO, fun u hu hu' => ?_⟩, ?_, fun k L hL hL' w => ?_⟩, fun w hw => ?_⟩
  · have hγ : ratW T S γ ∈ ratL T S := ⟨γ, rfl⟩
    have h3 := psi_rat hψ hγ ((ratL T S).add_mem hγ (hc w))
    rw [key _ ((ratL T S).add_mem hγ (hc w)) _ (by rw [add_sub_add_left_eq_sub]; exact hcO w),
      add_sub_add_left_eq_sub, symplOH_add_right]
    rw [symplOH_skew] at h3
    show _ = _ * (ψ (-symplOH S T (c w) w) * F (p (w - c w)))
    rw [neg_add, AddChar.map_add_eq_mul, h3, one_mul, symplOH_add_left, neg_add, AddChar.map_add_eq_mul, mul_assoc]
  · funext w
    obtain ⟨h1, h2⟩ := hl u hu hu'
    have h3 : w + u - c w ∈ O := by
      rw [add_sub_right_comm]; exact O.add_mem (hcO w) hu
    show ψ (symplOH S T w u) * f (w + u) = ψ (-symplOH S T (c w) w) * F (p (w - c w))
    rw [key _ (hc w) _ h3, add_sub_right_comm, map_add, h1, add_zero, ← mul_assoc, ← AddChar.map_add_eq_mul,
      ← one_mul (ψ (-symplOH S T (c w) w)), ← h2 _ (hcO w), ← AddChar.map_add_eq_mul, sym_sub_left,
      symplOH_add_right]
    congr 2
    ring
  · refine continuous_iff_continuousAt.2 fun w₀ => ?_
    have h1 : Continuous fun w => ψ (-symplOH S T (c w₀) w) * F (p (w - c w₀)) :=
      (hψ.1.1.comp (continuous_symplOH S T continuous_const continuous_id).neg).mul
        (hF.continuous.comp (hp.comp (continuous_id.sub continuous_const)))
    refine h1.continuousAt.congr ?_
    have h2 : {w : WO S T | w - c w₀ ∈ O} ∈ 𝓝 w₀ :=
      (hO.preimage (continuous_id.sub continuous_const)).mem_nhds (hcO w₀)
    exact Filter.mem_of_superset h2 fun w hw => (key _ (hc w₀) w hw).symm
  · obtain ⟨lam, hlam, hlam'⟩ := exists_log hψ
    let φ : (Fin k → ℝ) →+ ℂ := lam.comp
      ((AddMonoidHom.mk' (fun v => symplOH S T v (c w)) fun a b => symplOH_add_left S T a b _).comp L)
    have hφ : ContDiff ℝ ∞ φ := contDiff_additive φ (hlam.comp (continuous_symplOH S T hL continuous_const))
    have hpL : ContDiff ℝ ∞ (p.comp L) := ((p.comp L).toRealLinearMap (hp.comp hL)).contDiff
    have e : (fun t => f (w + L t)) =
        fun t => ψ (-symplOH S T (c w) w) * cexp (φ t) * F (p (w - c w) + p.comp L t) := by
      funext t
      rw [key _ (hc w) _ (by rw [add_sub_right_comm]; exact O.add_mem (hcO w) (hre _ (hL' t))), add_sub_right_comm,
        map_add, symplOH_add_right, neg_add, AddChar.map_add_eq_mul, ← symplOH_skew S T (c w) (L t),
        hlam' _ (snd_symplOH S T _ _ (Or.inl (hL' t)))]
      rfl
    rw [e]
    exact (contDiff_const.mul hφ.cexp).mul (hF.comp (contDiff_const.add hpL))
  · rw [key 0 (ratL T S).zero_mem w (by rw [sub_zero]; exact hre w hw), symplOH_zero_left, neg_zero,
      AddChar.map_zero_eq_one, one_mul, sub_zero]

theorem sym_nsmul_left (n : ℕ) (x y : WO S T) : symplOH S T (n • x) y = n • symplOH S T x y :=
  map_nsmul (AddMonoidHom.mk' (fun v => symplOH S T v y) fun a b => symplOH_add_left S T a b _) n x

theorem row_mem {E : Type} [Field E] [NumberField E] {n r : ℕ} {L : Lt E r} {y : Matrix (Fin n) (Fin r) E}
    (hy : y ∈ tens (GlobalTheory.SW.stdL E n) L) (k : Fin n) : y k ∈ L := by
  induction hy using AddSubgroup.closure_induction with
  | mem y h =>
    obtain ⟨v, hv, u, hu, rfl⟩ := h
    have : ∃ a : 𝓞 E, v k = a := by
      induction hv using Submodule.span_induction with
      | mem v h =>
        obtain ⟨a, rfl⟩ := h
        by_cases e : k = a
        · exact ⟨1, by simp [e]⟩
        · exact ⟨0, by simp [e]⟩
      | zero => exact ⟨0, by simp⟩
      | add v v' _ _ h h' =>
        obtain ⟨a, h⟩ := h
        obtain ⟨b, h'⟩ := h'
        exact ⟨a + b, by simp [h, h']⟩
      | smul c v _ h =>
        obtain ⟨a, h⟩ := h
        exact ⟨c * a, by simp [h, Algebra.smul_def]⟩
    obtain ⟨a, ha⟩ := this
    have e : vecMulVec v u k = a • u := by
      funext i
      simp [vecMulVec_apply, ha, Algebra.smul_def]
    rw [e]
    exact L.smul_mem a hu
  | zero => exact L.zero_mem
  | add y y' _ _ h h' => exact L.add_mem h h'
  | neg y _ h => exact L.neg_mem h

theorem stdL_full (E : Type) [Field E] [NumberField E] (n : ℕ) :
    (GlobalTheory.SW.stdL E n).FG ∧ Submodule.span E (GlobalTheory.SW.stdL E n : Set (Fin n → E)) = ⊤ := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  rw [GlobalTheory.SW.stdL, Submodule.span_span_of_tower]
  have := (Pi.basisFun E (Fin n)).span_eq
  convert this using 3
  funext a
  simp

theorem psi_hat (C : Ctx S T) {u u' : WO S T} (hu : u ∈ hatA S T (tens (GlobalTheory.SW.stdL D.host.E S.rank) C.X.Λ))
    (hu' : u' ∈ hatA S T (tens (GlobalTheory.SW.stdL D.host.E S.rank) C.X.Λ)) : C.ψ (symplOH S T (2 • u) u') = 1 := by
  obtain ⟨-, h2, h3, h4, -⟩ := GlobalTheory.T.completedTensorLattice_strongApprox_open_compact D S T C _ C.X.Λ (stdL_full _ _) ⟨C.X.Λ_fg, C.X.Λ_span⟩
  obtain ⟨-, -, s3, -⟩ := GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C
  have rat : ∀ y ∈ tens (GlobalTheory.SW.stdL D.host.E S.rank) C.X.Λ, ∀ y' ∈ tens (GlobalTheory.SW.stdL D.host.E S.rank) C.X.Λ,
      C.ψ (symplOH S T (finW S T y) (finW S T y')) ^ 2 = 1 := by
    intro y hy y' hy'
    have : ∀ k, ∃ m : ℤ, EF C.X (y k) (y' k) = m := fun k => by
      have := C.sympl (C.bas.symm ⟨_, row_mem hy k⟩) (C.bas.symm ⟨_, row_mem hy' k⟩)
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this
      exact ⟨-_, this.trans (Int.cast_neg _).symm⟩
    choose m hm using this
    rw [s3, ← Complex.exp_nat_mul, ← Complex.exp_int_mul_two_pi_mul_I (-∑ k, m k)]
    simp only [hm]
    congr 1
    push_cast
    ring
  obtain ⟨M, hM, hM'⟩ := h4 _ (GlobalTheory.FinTranslate.isOpen_annSub (S := S) (T := T) C.std.1 (h3 u' hu').1)
  obtain ⟨y, hy, u₁, hu₁, rfl⟩ := (h3 u hu).2 M hM
  obtain ⟨M', hN, hN'⟩ := h4 _ (GlobalTheory.FinTranslate.isOpen_annSub (S := S) (T := T) C.std.1 (h3 _ ((h2 y).2 hy)).1)
  obtain ⟨y', hy', u₂, hu₂, e⟩ := (h3 u' hu').2 M' hN
  rw [sym_nsmul_left, AddChar.map_nsmul_eq_pow, symplOH_add_left, AddChar.map_add_eq_mul, (hM' u₁ hu₁).1, mul_one,
    e, symplOH_add_right, AddChar.map_add_eq_mul, (hN' u₂ hu₂).2, mul_one]
  exact rat y hy y' hy'

theorem real_add {w w' : WO S T} (h : IsRealPt w) (h' : IsRealPt w') : IsRealPt (w + w') := by
  unfold IsRealPt at *
  rw [Matrix.map_add _ (map_add (finPart D)), h, h', add_zero]

theorem real_neg {w : WO S T} (h : IsRealPt w) : IsRealPt (-w) := by
  unfold IsRealPt at *
  rw [Matrix.map_neg _ (map_neg (finPart D)), h, neg_zero]

theorem fin_sub {w w' : WO S T} (h : IsFinPt w) (h' : IsFinPt w') : IsFinPt (w - w') := by
  unfold IsFinPt at *
  rw [Matrix.map_sub _ (map_sub (infPart D)), h, h', sub_zero]

def thick (H : AddSubgroup (WO S T)) (N : ℕ) : AddSubgroup (WO S T) where
  carrier := {w | ∃ u ∈ H, IsRealPt (w - N • u)}
  zero_mem' := ⟨0, H.zero_mem, by rw [nsmul_zero, sub_zero]; exact Matrix.map_zero _ (map_zero _)⟩
  add_mem' := by
    rintro a b ⟨u, hu, h⟩ ⟨u', hu', h'⟩
    refine ⟨u + u', H.add_mem hu hu', ?_⟩
    rw [nsmul_add, add_sub_add_comm]
    exact real_add h h'
  neg_mem' := by
    rintro a ⟨u, hu, h⟩
    refine ⟨-u, H.neg_mem hu, ?_⟩
    rw [neg_nsmul, neg_sub_neg, ← neg_sub]
    exact real_neg h

theorem nsmul_cancel' (K : Type) {M : Type} [Field K] [CharZero K] [AddCommGroup M] [Module K M] {N : ℕ} (hN : 0 < N)
    {u u' : M} (h : N • u = N • u') : u = u' := by
  have hN' : (N : K) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  rw [← Nat.cast_smul_eq_nsmul K, ← Nat.cast_smul_eq_nsmul K] at h
  rw [← inv_smul_smul₀ hN' u, h, inv_smul_smul₀ hN']

theorem nsmul_cancel {N : ℕ} (hN : 0 < N) {u u' : WO S T} (h : N • u = N • u') : u = u' :=
  Matrix.ext fun i j => nsmul_cancel' D.host.F hN (congrFun (congrFun h i) j)

theorem exists_isZak (C : Ctx S T) {x : Frame C.X.Ψ T.rank} (hx : x ∈ C.X.dom) {φ : TF S.rank C.g}
    (hφ : SW.IsSB φ) : ∃ f, C.IsZak x φ f := by
  obtain ⟨N, hN, hfix⟩ := heisG_fix_of_mem_lattice _ _ C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even φ hφ
  obtain ⟨hsm, hth, -⟩ := thR_laws _ _ C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even x hx φ hφ
  obtain ⟨h1, h2, h3, -, h5, -⟩ := GlobalTheory.T.completedTensorLattice_strongApprox_open_compact D S T C _ C.X.Λ (stdL_full _ _) ⟨C.X.Λ_fg, C.X.Λ_span⟩
  obtain ⟨-, s2, -, -, -, -, -, s8⟩ := GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C
  obtain ⟨R, -, r1, r2, r3, r4, r5, r6, -⟩ := GlobalTheory.T.realPoints_classicalModel_realVectorSpace D S T C
  set H := hatA S T (tens (GlobalTheory.SW.stdL D.host.E S.rank) C.X.Λ) with hH
  let p : WO S T →+ WR C.X S.rank := AddMonoidHom.mk' C.realPt r2
  let q : Matrix (Fin S.rank) (Fin T.rank) D.host.E →+ WO S T :=
    AddMonoidHom.mk' (finW S T) fun y y' => (s8 y).2.2.2 y'
  have hfin : ∀ u ∈ H, IsFinPt ((2 * N) • u) := fun u hu => (h3 _ (H.nsmul_mem hu _)).1
  have hz : ∀ w : WO S T, IsRealPt w → IsFinPt w → w = 0 := fun w h h' => by rw [← r4 w h, r6 w h', map_zero]
  have hB : ∀ w ∈ thick H (2 * N), ∀ w' ∈ thick H (2 * N),
      C.ψ (symplOH S T w w') = cexp (π * I * (EFR C.X (C.realPt w) (C.realPt w') : ℝ)) := by
    rintro w ⟨u, hu, h⟩ w' ⟨u', hu', h'⟩
    have e : ∀ (w u : WO S T), u ∈ H → C.realPt w = C.realPt (w - (2 * N) • u) := fun w u hu => by
      have := r2 (w - (2 * N) • u) ((2 * N) • u)
      rwa [sub_add_cancel, r6 _ (hfin u hu), add_zero] at this
    have e2 := psi_hat C (H.nsmul_mem hu N) (H.nsmul_mem hu' (2 * N))
    rw [← mul_nsmul'] at e2
    rw [e w u hu, e w' u' hu', ← s2 _ _ h h']
    conv_lhs => rw [← sub_add_cancel w ((2 * N) • u), ← sub_add_cancel w' ((2 * N) • u')]
    rw [symplOH_add_left, symplOH_add_right, symplOH_add_right, (symplOH_fin_real S T _ _ (hfin u hu) h').1,
      (symplOH_fin_real S T _ _ (hfin u' hu') h).2, add_zero, zero_add, AddChar.map_add_eq_mul, e2, mul_one]
  refine exists_extension C.std p r1 (thR C.X C.bas C.idx φ x) hsm (thick H (2 * N)) (h5 _ (by omega))
    (fun w hw => ⟨0, H.zero_mem, by rwa [nsmul_zero, sub_zero]⟩) (fun w => ?_) ?_ (fun u hu hu' => ?_)
  · obtain ⟨y, hy⟩ := h1 _ (r5 w)
    obtain ⟨y', -, u, hu, e⟩ := (h3 _ hy).2 (2 * N) (by omega)
    refine ⟨ratW T S (y + y')ᵀ, ⟨_, rfl⟩, u, hu, ?_⟩
    have : w - ratW T S (y + y')ᵀ - (2 * N) • u =
        R (C.realPt w) + -(ratW T S (y + y')ᵀ - finW S T (y + y')) := by
      rw [eq_sub_of_add_eq' e.symm, (s8 y).2.2.2]
      abel
    rw [this]
    exact real_add (r3 _).1 (real_neg (s8 _).2.2.1)
  · rintro _ ⟨γ, rfl⟩ hγ w hw
    obtain ⟨y, rfl⟩ : ∃ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, yᵀ = γ := ⟨γᵀ, rfl⟩
    change ratW T S yᵀ ∈ thick H (2 * N) at hγ
    change thR C.X C.bas C.idx φ x (C.realPt (w + ratW T S yᵀ)) =
      C.ψ (-symplOH S T (ratW T S yᵀ) w) * thR C.X C.bas C.idx φ x (C.realPt w)
    have hfx : heisG C.X C.bas y φ = φ := by
      obtain ⟨u, hu, h⟩ := hγ
      have e := hz (finW S T y - (2 * N) • u) (by
        have := real_add h (real_neg (s8 y).2.2.1)
        rwa [neg_sub, add_comm, sub_add_sub_cancel] at this) (fin_sub (s8 y).2.1 (hfin u hu))
      have hN' : ((2 * N : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      obtain ⟨y₀, rfl⟩ : ∃ y₀ : Matrix (Fin S.rank) (Fin T.rank) D.host.E, ((2 * N : ℕ) : D.host.E) • y₀ = y :=
        ⟨_, smul_inv_smul₀ hN' y⟩
      have e' : finW S T (((2 * N : ℕ) : D.host.E) • y₀) = (2 * N) • finW S T y₀ := by
        rw [Nat.cast_smul_eq_nsmul]
        exact map_nsmul q _ _
      rw [sub_eq_zero, e'] at e
      have := nsmul_cancel (by omega) e
      exact hfix y₀ (row_mem ((h2 y₀).1 (this ▸ hu))) 2
    have := hth y (C.realPt w)
    rw [hfx] at this
    rw [← symplOH_skew, hB _ hw _ hγ, r2, (s8 y).1, this, ← mul_assoc, ← Complex.exp_add, add_neg_cancel,
      Complex.exp_zero, one_mul]
  · refine ⟨r6 u hu', fun w hw => ?_⟩
    rw [hB _ hw _ hu, r6 u hu']
    simp [EFR, hermC]

theorem isZak_Th : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ x ∈ C.X.dom, ∀ φ : TF S.rank C.g, SW.IsSB φ → C.IsZak x φ (C.Th x φ) ∧ ∀ f, C.IsZak x φ f → f = C.Th x φ := by
  intro D S T C x hx φ hφ
  have h := exists_isZak C hx hφ
  have h1 : C.IsZak x φ (C.Th x φ) := by
    rw [Ctx.Th, dif_pos h]
    exact h.choose_spec
  exact ⟨h1, fun f hf => ((GlobalTheory.T.thetaFunction_space_heisenberg_laws D S T C).2.1 f _ hf.1 h1.1).2 fun w hw => (hf.2 w hw).trans (h1.2 w hw).symm⟩

end GlobalTheory.Ker.ZakEx
