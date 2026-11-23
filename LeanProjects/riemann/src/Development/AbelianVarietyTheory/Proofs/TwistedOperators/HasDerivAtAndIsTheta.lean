import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealDirectionThetaNonzero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HomSymplecticHalfFormAlgebraicLawsContinuous
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAdeleCharEqCompMulTotallyReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaFunNeZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsInfFamAndStdChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped TensorProduct ContDiff Topology

namespace GlobalTheory.ThetaAllChar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.FockCompare GlobalTheory.WeilVacMove GlobalTheory.IndefiniteRowSideFullHecke.RealDirectionThetaNonzero

variable {D : D7}

def IsExpChar (ψ : AddChar (AF D.host.F) ℂ) : Prop :=
  Continuous ψ ∧ (∀ x, ‖ψ x‖ = 1) ∧
    ∃ lam : AF D.host.F →+ ℂ, Continuous lam ∧ ∀ a, sndA D.host.F a = 0 → ψ a = Complex.exp (lam a)

theorem isExpChar_one : IsExpChar (1 : AddChar (AF D.host.F) ℂ) :=
  ⟨continuous_const, fun x => by simp, 0, continuous_const, fun a _ => by simp⟩

theorem exists_std {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) :
    ∃ ψ₀ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ₀ (-1) ∧ ∃ a : D.host.F, a ≠ 0 ∧
      ∀ x, ψ x = ψ₀ (algebraMap D.host.F (AF D.host.F) a * x) := by
  obtain ⟨-, ψ₀, h₀⟩ := GlobalTheory.Ker.exists_infFam_and_stdChar D
  haveI := D.sp.cm.totReal
  exact ⟨ψ₀, h₀, GlobalTheory.AdeleCharTwist.exists_mul_eq D.host.F ψ₀ ψ h₀.1 hψ⟩

theorem isExpChar_of_isCharAF {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) : IsExpChar ψ := by
  obtain ⟨ψ₀, h₀, a, -, ha⟩ := exists_std hψ
  obtain ⟨lam, hl, hlam⟩ := exists_log h₀
  refine ⟨hψ.1, hψ.2.1, lam.comp (AddMonoidHom.mulLeft (algebraMap D.host.F (AF D.host.F) a)),
    hl.comp (continuous_const.mul continuous_id), fun x hx => ?_⟩
  rw [ha, hlam _ (by rw [map_mul, hx, mul_zero])]
  rfl

variable {ψ ψ' : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem exists_chart (D : D7) : ∃ (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ := by
  obtain ⟨⟨θ, hθ⟩, -⟩ := GlobalTheory.Ker.exists_infFam_and_stdChar D
  exact ⟨θ, GlobalTheory.RealLineAt.exists_inverse_chart hθ⟩

theorem isTheta_heis_real (hψ : IsExpChar ψ) {v : WO S T} (hv : v.map (finPart D) = 0) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (heisO ψ S T v f) := by
  obtain ⟨θ, σ, h⟩ := exists_chart D
  obtain ⟨hc, -, lam, hl, hlam⟩ := hψ
  have hsm := (smooth_iff_sm_and_real_lines D θ σ h T S).1
  have hs : Sm (iotaW σ T S) (heisO ψ S T v f) := by
    have e : heisO ψ S T v f = fun w => Complex.exp (phase lam S T v w) * f (w + v) := by
      funext w
      rw [heisO, hlam _ (snd_symplOH S T w v (Or.inr hv))]
      rfl
    rw [e]
    exact sm_translate _ _ (contDiff_phase h hl v) f ((hsm f).1 hf.smooth) v
  have hlev : ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧
      ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u (heisO ψ S T v f) = heisO ψ S T v f := by
    obtain ⟨U, hU, h1⟩ := hf.level
    exact ⟨U, hU, fun u hu h0 => heisO_fix_of_real u v h0 hv f (h1 u hu h0)⟩
  exact ⟨heisO_quasi ψ S T v f hf.quasi, hlev, continuous_of_level h hc _ hlev hs, (hsm _).2 hs⟩

theorem isTheta_heis (hψ : IsExpChar ψ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (u : WO S T) :
    IsThetaFunO ψ S T (heisO ψ S T u f) := by
  have hr : (GlobalTheory.FinTranslate.eInf D • u : WO S T).map (finPart D) = 0 := by
    ext i j; exact GlobalTheory.ThetaClosed.finPart_eInf_smul (u i j)
  have hn : ((1 - GlobalTheory.FinTranslate.eInf D) • u : WO S T).map (infPart D) = 0 := by
    ext i j; exact GlobalTheory.ThetaClosed.infPart_one_sub_eInf_smul (u i j)
  have h := isTheta_heis_real hψ hr (GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1 hψ.2.1 hf hn)
  rwa [heisO_heisO, GlobalTheory.FinTranslate.symplOH_real_fin hn hr, ψ.map_zero_eq_one, one_smul, ← add_smul, add_sub_cancel,
    one_smul] at h

theorem hasLevel_dHeis {L : ℝ →+ WO S T} (hL : IsRealDir L) {U : AddSubgroup (WO S T)} {f : WO S T → ℂ}
    (hf : HasLevel ψ S T U f) : HasLevel ψ S T U (dHeis ψ S T L f) := by
  intro u hu h0
  funext w
  have : (fun t => heisO ψ S T (L t) f w) = fun t => heisO ψ S T u (heisO ψ S T (L t) f) w := by
    funext t; rw [heisO_fix_of_real u _ h0 (hL.2 t) f (hf u hu h0)]
  conv_rhs => unfold dHeis; rw [this]
  unfold dHeis
  rw [heisO, ← deriv_const_mul_field]
  rfl

theorem hasDerivAt_and_isTheta (hψ : IsExpChar ψ) {L : ℝ →+ WO S T} (hL : IsRealDir L) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) :
    (∀ w, HasDerivAt (fun t : ℝ => heisO ψ S T (L t) f w) (dHeis ψ S T L f w) 0) ∧
      IsThetaFunO ψ S T (dHeis ψ S T L f) := by
  obtain ⟨θ, σ, h⟩ := exists_chart D
  obtain ⟨hc, -, lam, hl, hlam⟩ := hψ
  have hsm := (smooth_iff_sm_and_real_lines D θ σ h T S).1
  have hline := (smooth_iff_sm_and_real_lines D θ σ h T S).2.1 L hL
  have hfs := (hsm f).1 hf.smooth
  have hd : ∀ w, HasDerivAt (fun t : ℝ => heisO ψ S T (L t) f w) (phase lam S T (L 1) w * f w +
      fderiv ℝ (fun x => f (w + iotaW σ T S x)) 0 (piW θ T S (L 1))) 0 := by
    intro w
    have e : (fun t : ℝ => heisO ψ S T (L t) f w) = fun t : ℝ => Complex.exp (t * phase lam S T (L 1) w) *
        f (w + iotaW σ T S (t • piW θ T S (L 1))) := by
      funext t
      rw [heisO, psi_sympl_line hl hlam hL.1 hL.2, ← hline t]
    rw [e]
    exact hasDerivAt_exp_mul _ _ f hfs _ w
  have hs : Sm (iotaW σ T S) (dHeis ψ S T L f) := by
    have e : dHeis ψ S T L f = fun w => phase lam S T (L 1) w * f w +
        fderiv ℝ (fun x => f (w + iotaW σ T S x)) 0 (piW θ T S (L 1)) := funext fun w => (hd w).deriv
    rw [e]
    exact sm_deriv _ _ (contDiff_phase h hl _) f hfs _
  have hlev : ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧
      ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u (dHeis ψ S T L f) = dHeis ψ S T L f := by
    obtain ⟨U, hU, h1⟩ := hf.level
    exact ⟨U, hU, hasLevel_dHeis hL h1⟩
  refine ⟨fun w => (hd w).differentiableAt.hasDerivAt, fun γ w => ?_, hlev,
    continuous_of_level h hc _ hlev hs, (hsm _).2 hs⟩
  unfold dHeis
  rw [← deriv_const_mul_field]
  congr 1
  funext t
  exact heisO_quasi ψ S T (L t) f hf.quasi γ w

theorem isTheta_dHeisWord (hψ : IsExpChar ψ) {Ls : List (ℝ →+ WO S T)} (hL : ∀ L ∈ Ls, IsRealDir L) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (dHeisWord ψ S T Ls f) := by
  induction Ls with
  | nil => exact hf
  | cons L Ls ih =>
    exact (hasDerivAt_and_isTheta hψ (hL L List.mem_cons_self) (ih fun M hM => hL M (List.mem_cons_of_mem _ hM))).2

theorem dHeisWord_concat (Ls : List (ℝ →+ WO S T)) (L : ℝ →+ WO S T) (f : WO S T → ℂ) :
    dHeisWord ψ S T (Ls ++ [L]) f = dHeisWord ψ S T Ls (dHeis ψ S T L f) := by
  unfold dHeisWord
  rw [List.foldr_append]
  rfl

theorem heisO_add (u : WO S T) (f g : WO S T → ℂ) : heisO ψ S T u (f + g) = heisO ψ S T u f + heisO ψ S T u g :=
  (GlobalTheory.FinTranslate.heisL S T ψ u).map_add f g

theorem heisO_smul (u : WO S T) (c : ℂ) (f : WO S T → ℂ) : heisO ψ S T u (c • f) = c • heisO ψ S T u f :=
  (GlobalTheory.FinTranslate.heisL S T ψ u).map_smul c f

theorem dHeis_add (hψ : IsExpChar ψ) {L : ℝ →+ WO S T} (hL : IsRealDir L) {f g : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
    dHeis ψ S T L (f + g) = dHeis ψ S T L f + dHeis ψ S T L g := by
  funext w
  have h := ((hasDerivAt_and_isTheta hψ hL hf).1 w).add ((hasDerivAt_and_isTheta hψ hL hg).1 w)
  refine HasDerivAt.deriv (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_))
  exact congrFun (heisO_add (L t) f g) w

theorem dHeis_smul (L : ℝ →+ WO S T) (c : ℂ) (f : WO S T → ℂ) : dHeis ψ S T L (c • f) = c • dHeis ψ S T L f := by
  funext w
  show _ = c * deriv _ _
  rw [← deriv_const_mul_field]
  unfold dHeis
  congr 1
  funext t
  exact congrFun (heisO_smul (L t) c f) w

theorem dHeisWord_add (hψ : IsExpChar ψ) {Ls : List (ℝ →+ WO S T)} (hL : ∀ L ∈ Ls, IsRealDir L) {f g : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
    dHeisWord ψ S T Ls (f + g) = dHeisWord ψ S T Ls f + dHeisWord ψ S T Ls g := by
  induction Ls with
  | nil => rfl
  | cons L Ls ih =>
    have h' : ∀ M ∈ Ls, IsRealDir M := fun M hM => hL M (List.mem_cons_of_mem _ hM)
    show dHeis ψ S T L (dHeisWord ψ S T Ls (f + g)) = _
    rw [ih h', dHeis_add hψ (hL L List.mem_cons_self) (isTheta_dHeisWord hψ h' hf) (isTheta_dHeisWord hψ h' hg)]
    rfl

theorem dHeisWord_smul (Ls : List (ℝ →+ WO S T)) (c : ℂ) (f : WO S T → ℂ) :
    dHeisWord ψ S T Ls (c • f) = c • dHeisWord ψ S T Ls f := by
  induction Ls with
  | nil => rfl
  | cons L Ls ih =>
    show dHeis ψ S T L (dHeisWord ψ S T Ls (c • f)) = _
    rw [ih, dHeis_smul]
    rfl

theorem heisO_mul (u : WO S T) (f g : WO S T → ℂ) :
    heisO (ψ * ψ') S T u (f * g) = heisO ψ S T u f * heisO ψ' S T u g := by
  funext w
  simp only [heisO, AddChar.mul_apply, Pi.mul_apply]
  ring

theorem isTheta_mul {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ' S T g) :
    IsThetaFunO (ψ * ψ') S T (f * g) where
  quasi γ w := by
    simp only [Pi.mul_apply, hf.quasi, hg.quasi, AddChar.mul_apply]
    ring
  level := by
    obtain ⟨U, hU, h1⟩ := hf.level
    obtain ⟨U', hU', h2⟩ := hg.level
    exact ⟨U ⊓ U', hU.inter hU', fun u hu h0 => by rw [heisO_mul, h1 u hu.1 h0, h2 u hu.2 h0]⟩
  cont := hf.cont.mul hg.cont
  smooth k L h1 h2 w := (hf.smooth k L h1 h2 w).mul (hg.smooth k L h1 h2 w)

theorem star_char (hn : ∀ x, ‖ψ x‖ = 1) (x : AF D.host.F) : star (ψ x) = ψ⁻¹ x := by
  have h1 : ψ⁻¹ x * ψ x = 1 := by
    rw [AddChar.inv_apply, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have h2 : star (ψ x) * ψ x = 1 := by
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
  have h0 : ψ x ≠ 0 := fun h => by simpa [h] using hn x
  exact mul_right_cancel₀ h0 (h2.trans h1.symm)

theorem isTheta_star (hn : ∀ x, ‖ψ x‖ = 1) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ⁻¹ S T (star f) where
  quasi γ w := by rw [Pi.star_apply, Pi.star_apply, hf.quasi, star_mul', star_char hn]
  level := by
    obtain ⟨U, hU, h1⟩ := hf.level
    refine ⟨U, hU, fun u hu h0 => ?_⟩
    funext w
    rw [Pi.star_apply, ← congrFun (h1 u hu h0) w, heisO, heisO, star_mul', star_char hn, Pi.star_apply]
  cont := hf.cont.star
  smooth k L h1 h2 w := Complex.conjCLE.contDiff.comp (hf.smooth k L h1 h2 w)

theorem isTheta_mul_star (hn : ∀ x, ‖ψ x‖ = 1) {f h : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hh : IsThetaFunO ψ S T h) : IsThetaFunO 1 S T (f * star h) := by
  have := isTheta_mul hf (isTheta_star hn hh)
  rwa [mul_inv_cancel] at this

theorem isTheta_one_mul {Φ g : WO S T → ℂ} (hΦ : IsThetaFunO 1 S T Φ) (hg : IsThetaFunO ψ S T g) :
    IsThetaFunO ψ S T (Φ * g) := by
  have := isTheta_mul hΦ hg
  rwa [one_mul] at this

theorem heisO_one_mul (u : WO S T) (Φ g : WO S T → ℂ) :
    heisO ψ S T u (Φ * g) = heisO 1 S T u Φ * heisO ψ S T u g := by
  rw [← heisO_mul, one_mul]

theorem heisO_one_apply (u : WO S T) (Φ : WO S T → ℂ) (w : WO S T) : heisO 1 S T u Φ w = Φ (w + u) := by
  rw [heisO, AddChar.one_apply, one_mul]

theorem periodic_of_one {Φ : WO S T → ℂ} (hΦ : IsThetaFunO 1 S T Φ) : ∀ γ ∈ ratL T S, ∀ x, Φ (γ + x) = Φ x := by
  rintro _ ⟨γ, rfl⟩ x
  have := hΦ.quasi γ x
  rwa [AddChar.one_apply, one_mul] at this

theorem dHeis_one_mul (hψ : IsExpChar ψ) {L : ℝ →+ WO S T} (hL : IsRealDir L) {Φ g : WO S T → ℂ}
    (hΦ : IsThetaFunO 1 S T Φ) (hg : IsThetaFunO ψ S T g) :
    dHeis ψ S T L (Φ * g) = dHeis 1 S T L Φ * g + Φ * dHeis ψ S T L g := by
  funext w
  have h := ((hasDerivAt_and_isTheta isExpChar_one hL hΦ).1 w).mul ((hasDerivAt_and_isTheta hψ hL hg).1 w)
  simp only [map_zero, heisO_zero] at h
  refine HasDerivAt.deriv (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_))
  exact congrFun (heisO_one_mul (L t) Φ g) w

theorem norm_periodic' (hn : ∀ x, ‖ψ x‖ = 1) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    ∀ γ ∈ ratL T S, ∀ w, ‖f (γ + w)‖ = ‖f w‖ := by
  rintro _ ⟨γ, rfl⟩ w
  have := congrArg norm (hf.quasi γ w)
  rwa [norm_mul, hn, one_mul] at this

theorem exists_bound (hn : ∀ x, ‖ψ x‖ = 1) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w, ‖f w‖ ≤ B := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hf.cont.continuousOn
  have : ∀ w, ‖f w‖ ≤ B := fun w => by
    obtain ⟨γ, hγ, hk⟩ := hcov w
    rw [← norm_periodic' hn hf γ hγ]
    exact hB _ hk
  exact ⟨B, (norm_nonneg _).trans (this 0), this⟩

def chi (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (γ x : WO S T) : ℂ := ψ (symplOH S T x γ + symplOH S T x γ)

theorem chi_add (γ x y : WO S T) : chi ψ S T γ (x + y) = chi ψ S T γ x * chi ψ S T γ y := by
  unfold chi
  rw [← AddChar.map_add_eq_mul, symplOH_add_left]
  exact congrArg ψ (add_add_add_comm _ _ _ _)

theorem chi_add_left (γ γ' x : WO S T) : chi ψ S T (γ + γ') x = chi ψ S T γ x * chi ψ S T γ' x := by
  unfold chi
  rw [← AddChar.map_add_eq_mul, symplOH_add_right]
  exact congrArg ψ (add_add_add_comm _ _ _ _)

theorem chi_zero_left (x : WO S T) : chi ψ S T 0 x = 1 := by
  rw [chi, GlobalTheory.WeilVacMove.symplOH_zero_right, add_zero, AddChar.map_zero_eq_one]

theorem chi_zero (γ : WO S T) : chi ψ S T γ 0 = 1 := by
  rw [chi, GlobalTheory.WeilVacMove.symplOH_zero_left, add_zero, AddChar.map_zero_eq_one]

theorem continuous_chi (hc : Continuous ψ) (γ : WO S T) : Continuous (chi ψ S T γ) := by
  have h := GlobalTheory.FinTranslate.continuous_symplOH S T γ
  have h2 : Continuous fun x : WO S T => symplOH S T x γ + symplOH S T x γ := h.add h
  unfold chi
  exact hc.comp h2

theorem chi_rat (hψ : IsCharAF D.host.F ψ) {γ γ' : WO S T} (h : γ ∈ ratL T S) (h' : γ' ∈ ratL T S) :
    chi ψ S T γ γ' = 1 := by
  obtain ⟨a, ha⟩ := (GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.2.2.1 γ' h' γ h
  rw [chi, ha, ← map_add]
  exact hψ.2.2.1 _

theorem heisO_rat {γ : WO S T} (h : γ ∈ ratL T S) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) :
    heisO ψ S T γ g = chi ψ S T γ * g := by
  obtain ⟨γ, rfl⟩ := h
  funext w
  have := hg.quasi γ w
  rw [← symplOH_skew, add_comm] at this
  rw [heisO, Pi.mul_apply, chi, AddChar.map_add_eq_mul, mul_assoc]
  exact congrArg _ this

theorem isTheta_chi (hψ : IsCharAF D.host.F ψ) {γ : WO S T} (h : γ ∈ ratL T S) : IsThetaFunO 1 S T (chi ψ S T γ) where
  quasi γ' w := by rw [chi_add, chi_rat hψ h (γ' := ratW T S γ') ⟨γ', rfl⟩, AddChar.one_apply]
  level := by
    haveI := (GlobalTheory.AdelicMatrixLattice.lattice D T S).1
    let K : AddSubgroup (WO S T) :=
      { carrier := {w | ψ (pairA D.host.F 0 (symplOH S T w γ).2) = 1}
        zero_mem' := by
          show ψ _ = 1
          rw [GlobalTheory.WeilVacMove.symplOH_zero_left]
          exact ψ.map_zero_eq_one
        add_mem' := fun {a b} ha hb => by
          have ha' : ψ _ = 1 := ha
          have hb' : ψ _ = 1 := hb
          show ψ _ = 1
          rw [← one_mul (1 : ℂ)]
          conv_rhs => rw [← ha']; arg 2; rw [ha', ← hb']
          rw [← AddChar.map_add_eq_mul, symplOH_add_left]
          congr 1
          exact Prod.ext (add_zero _).symm rfl
        neg_mem' := fun {a} ha => by
          have ha' : ψ _ = 1 := ha
          show ψ _ = 1
          have e : symplOH S T (-a) γ = -symplOH S T a γ := by
            rw [symplOH_skew, GlobalTheory.FinTranslate.symplOH_neg_right, neg_neg, symplOH_skew]
          have e2 : pairA D.host.F 0 (symplOH S T (-a) γ).2 = -pairA D.host.F 0 (symplOH S T a γ).2 := by
            rw [e]; exact Prod.ext neg_zero.symm rfl
          rw [e2, AddChar.map_neg_eq_inv, ha', inv_one] }
    have hK : IsOpen (K : Set (WO S T)) := by
      refine K.isOpen_of_mem_nhds (g := 0) ?_
      have h1 : Continuous fun w : WO S T => (symplOH S T w γ).2 :=
        continuous_snd.comp (GlobalTheory.FinTranslate.continuous_symplOH S T γ)
      exact h1.continuousAt.preimage_mem_nhds (x := 0) (t := {a | ψ (pairA D.host.F 0 a) = 1})
        (by rw [GlobalTheory.WeilVacMove.symplOH_zero_left]; exact GlobalTheory.FinTranslate.ker_mem_nhds hψ.1 hψ.2.1)
    refine ⟨K, hK, fun u hu h0 => ?_⟩
    funext w
    have h4 : symplOH S T u γ = pairA D.host.F 0 (symplOH S T u γ).2 :=
      Prod.ext (fst_symplOH S T u γ (Or.inl h0)) rfl
    have h5 : ψ (symplOH S T u γ) = 1 := by rw [h4]; exact hu
    rw [heisO_one_apply, chi_add, chi, chi, AddChar.map_add_eq_mul ψ (symplOH S T u γ), h5, mul_one, mul_one]
  cont := continuous_chi hψ.1 γ
  smooth k L hL h0 w := by
    obtain ⟨-, -, lam, hl, hlam⟩ := isExpChar_of_isCharAF hψ
    have e : (fun t => chi ψ S T γ (w + L t)) = fun t => chi ψ S T γ w *
        (Complex.exp (((phase lam S T γ).comp L) t) * Complex.exp (((phase lam S T γ).comp L) t)) := by
      funext t
      rw [chi_add]
      congr 1
      rw [chi, AddChar.map_add_eq_mul, hlam _ (snd_symplOH S T _ γ (Or.inl (h0 t)))]
      rfl
    have hs : ContDiff ℝ ∞ ((phase lam S T γ).comp L) :=
      contDiff_additive _ (hl.comp (continuous_symplOH S T hL continuous_const))
    rw [e]
    exact contDiff_const.mul (hs.cexp.mul hs.cexp)

theorem smul_mem_ratL (b : D.host.F) {γ : WO S T} (h : γ ∈ ratL T S) :
    (algebraMap D.host.F (AF D.host.F) b • γ : WO S T) ∈ ratL T S := by
  obtain ⟨γ, rfl⟩ := h
  refine ⟨b • γ, ?_⟩
  funext i j
  show (1 : AF D.host.F) ⊗ₜ[D.host.F] (b • γ i j) =
    algebraMap D.host.F (AF D.host.F) b • ((1 : AF D.host.F) ⊗ₜ[D.host.F] γ i j)
  rw [algebraMap_smul]
  exact (TensorProduct.mk D.host.F (AF D.host.F) D.host.E 1).map_smul b (γ i j)

theorem smul_fin' (c : AF D.host.F) {u : WO S T} (hu : u.map (infPart D) = 0) :
    (c • u : WO S T).map (infPart D) = 0 := by
  have h : (c • u : WO S T) = (1 - GlobalTheory.FinTranslate.eInf D) • (c • u) := by
    rw [sub_smul, one_smul, smul_comm, GlobalTheory.FinTranslate.smul_fin hu, smul_zero, sub_zero]
  rw [h]
  ext i j; exact GlobalTheory.ThetaClosed.infPart_one_sub_eInf_smul _

theorem smul_real' (c : AF D.host.F) {u : WO S T} (hu : u.map (finPart D) = 0) :
    (c • u : WO S T).map (finPart D) = 0 := by
  have h : (c • u : WO S T) = GlobalTheory.FinTranslate.eInf D • (c • u) := by
    rw [smul_comm, GlobalTheory.FinTranslate.smul_real hu]
  rw [h]
  ext i j; exact GlobalTheory.ThetaClosed.finPart_eInf_smul _

theorem continuous_smul' (c : AF D.host.F) : Continuous fun u : WO S T => (c • u : WO S T) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI i1 : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul _ _
  haveI : ContinuousConstSMul (AF D.host.F) (AE D) := @ContinuousSMul.continuousConstSMul _ _ _ _ _ i1
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have h : Continuous fun u : WO S T => u i j := (continuous_apply j).comp (continuous_apply i)
  exact h.const_smul c

theorem isTheta_scale (b : D.host.F) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO (ψ.mulShift (algebraMap D.host.F (AF D.host.F) (b * b))) S T
      fun w => f (algebraMap D.host.F (AF D.host.F) b • w) := by
  have key : ∀ x y : WO S T, symplOH S T (algebraMap D.host.F (AF D.host.F) b • x)
      (algebraMap D.host.F (AF D.host.F) b • y) = algebraMap D.host.F (AF D.host.F) (b * b) * symplOH S T x y := by
    intro x y
    rw [GlobalTheory.FinTranslate.symplOH_smul_left, GlobalTheory.FinTranslate.symplOH_smul_right, map_mul, mul_assoc]
  refine ⟨fun γ w => ?_, ?_, hf.cont.comp (continuous_smul' _), fun k L hL h0 w => ?_⟩
  · obtain ⟨γ', h'⟩ := smul_mem_ratL (S := S) (T := T) b (γ := ratW T S γ) ⟨γ, rfl⟩
    have h'' : ratW T S γ' = algebraMap D.host.F (AF D.host.F) b • ratW T S γ := h'
    have := hf.quasi γ' (algebraMap D.host.F (AF D.host.F) b • w)
    rw [h'', key] at this
    rw [smul_add, AddChar.mulShift_apply, mul_neg]
    exact this
  · obtain ⟨U, hU, h1⟩ := hf.level
    refine ⟨U.comap (DistribSMul.toAddMonoidHom (WO S T) (algebraMap D.host.F (AF D.host.F) b)),
      hU.preimage (continuous_smul' _), fun u hu h0 => ?_⟩
    funext w
    have := congrFun (h1 _ hu (smul_fin' _ h0)) (algebraMap D.host.F (AF D.host.F) b • w)
    rw [heisO] at this ⊢
    rw [smul_add, AddChar.mulShift_apply, ← key]
    exact this
  · have := hf.smooth k ((DistribSMul.toAddMonoidHom (WO S T) (algebraMap D.host.F (AF D.host.F) b)).comp L)
      ((continuous_smul' _).comp hL) (fun t => smul_real' _ (h0 t)) (algebraMap D.host.F (AF D.host.F) b • w)
    simp only [smul_add]
    exact this

theorem exists_zero_ne (hψ : IsExpChar ψ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (h0 : f ≠ 0) :
    ∃ g, IsThetaFunO ψ S T g ∧ g 0 ≠ 0 := by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
  exact ⟨_, isTheta_heis hψ hf x, by rwa [heisO_apply_zero]⟩

theorem exists_theta_zero_ne (hψ : IsCharAF D.host.F ψ) (S T : HSp D) : ∃ g, IsThetaFunO ψ S T g ∧ g 0 ≠ 0 := by
  obtain ⟨ψ₀, h₀, a, -, ha⟩ := exists_std hψ
  obtain ⟨f₀, hf₀, hne⟩ := GlobalTheory.Mem.ThetaNonzero.exists_thetaO_ne_zero h₀ S T
  obtain ⟨f, hf, h0⟩ := exists_zero_ne (isExpChar_of_isCharAF h₀.1) hf₀ hne
  have h := isTheta_mul (isTheta_scale ((a + 1) / 2) hf)
    (isTheta_star (fun x => by rw [AddChar.mulShift_apply]; exact h₀.1.2.1 _) (isTheta_scale ((a - 1) / 2) hf))
  have e : ψ₀.mulShift (algebraMap D.host.F (AF D.host.F) ((a + 1) / 2 * ((a + 1) / 2))) *
      (ψ₀.mulShift (algebraMap D.host.F (AF D.host.F) ((a - 1) / 2 * ((a - 1) / 2))))⁻¹ = ψ := by
    ext x
    rw [AddChar.mul_apply, AddChar.inv_apply, AddChar.mulShift_apply, AddChar.mulShift_apply,
      ← AddChar.map_add_eq_mul, ha, mul_neg, ← sub_eq_add_neg, ← sub_mul, ← map_sub]
    congr 3
    ring
  rw [e] at h
  refine ⟨_, h, ?_⟩
  simp only [Pi.mul_apply, Pi.star_apply, smul_zero]
  exact mul_ne_zero h0 (star_ne_zero.2 h0)

end GlobalTheory.ThetaAllChar

end
