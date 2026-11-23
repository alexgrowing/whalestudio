import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointFormulaOfKernel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaKernelFiniteAdelicLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionLiftPairStepVectorInvLevelChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnOfRapidDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelModerateGrowthBothVariables
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResidueCharIsOfFinOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.AdjUp

noncomputable section

namespace GlobalTheory.AdjRange

open GlobalTheory.TraceIncl

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem inner_sum_eq {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ W) (Φ : W → ℂ) (hadd : ∀ w w', Φ (w + w') = Φ w + Φ w')
    (hsmul : ∀ (c : ℂ) w, Φ (c • w) = star c * Φ w) (w : W) :
    ⟪w, ∑ k, Φ (b k) • b k⟫_ℂ = Φ w := by
  have hsum : ∀ s : Finset (Fin n), Φ (∑ k ∈ s, ⟪b k, w⟫_ℂ • b k) = ∑ k ∈ s, star ⟪b k, w⟫_ℂ * Φ (b k) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have h0 := hsmul 0 0
      simp only [zero_smul, star_zero, zero_mul] at h0
      simpa using h0
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, hsmul, ih]
  conv_rhs => rw [← b.sum_repr' w]
  rw [hsum, inner_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_smul_right, mul_comm]
  congr 1
  exact (inner_conj_symm (𝕜 := ℂ) w (b k)).symm

theorem star_inv_of_finOrder (u : ℂˣ) (hu : IsOfFinOrder u) : star (((u⁻¹ : ℂˣ) : ℂ)) = (u : ℂ) := by
  obtain ⟨n, hn, hpow⟩ := hu.exists_pow_eq_one
  have h1 : ‖(u : ℂ)‖ = 1 := by
    have : ‖(u : ℂ)‖ ^ n = 1 := by
      rw [← norm_pow, ← Units.val_pow_eq_pow_val, hpow, Units.val_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
  have hne : (u : ℂ) ≠ 0 := u.ne_zero
  rw [Units.val_inv_eq_inv_val, star_inv₀, Complex.star_def, Complex.inv_def, Complex.normSq_eq_norm_sq,
    Complex.norm_conj, h1]
  simp

variable (R : RealDat D A Ks) (i : Fin D.R.m) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (y : (R.HW i (sg0 D A)).H)

def phi (K : (R.cV i).W →ₗ[ℂ] Ser R i) (w : (R.cV i).W) : ℂ :=
  ∫ g in R.fdW i, star (K w v g) * val R i v y g ∂(R.νW i)

def coVec {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W) (K : (R.cV i).W →ₗ[ℂ] Ser R i) : (R.cV i).W :=
  ∑ k, phi R i v y K (b k) • b k

theorem inner_coVec {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W) (K : (R.cV i).W →ₗ[ℂ] Ser R i)
    (hI : ∀ w, IntegrableOn (fun g => star (K w v g) * val R i v y g) (R.fdW i) (R.νW i)) (w : (R.cV i).W) :
    ⟪w, coVec R i v y b K⟫_ℂ = phi R i v y K w := by
  refine inner_sum_eq b _ (fun w w' => ?_) (fun c w => ?_) w
  · unfold phi
    rw [← integral_add (hI w) (hI w')]
    refine integral_congr_ae (.of_forall fun g => ?_)
    simp only [map_add, Pi.add_apply, star_add, add_mul]
  · unfold phi
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun g => ?_)
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, star_mul', mul_assoc]

end GlobalTheory.AdjRange

namespace GlobalTheory.AdjRange

open GlobalTheory.TraceIncl

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem integrable_kernA (hP : GlobalTheory.Published.CuspRapidDecay) (R : RealDat D A Ks) (F : Face D A) (hL : Laws R F)
    (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (y : (R.HW i (sg0 D A)).H) (h : GA D (Vc D i))
    (w : (R.cV i).W) :
    IntegrableOn (fun g => star (kernA R i t h w v g) * val R i v y g) (R.fdW i) (R.νW i) := by
  have hω := hL.thP.ωP i t
  have hf := hL.thP.pt_theta i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ρ h⁻¹ w))
  have hMem : (R.HW i (sg0 D A)).e y ∈ R.Wall i (sg0 D A) := by
    rw [← (hL.models.HW i (sg0 D A)).2.1]
    exact LinearMap.mem_range_self _ y
  have hMM := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hMem
  have hR : GlobalTheory.Grow.RapidDec (Wc D i) (val R i v y) :=
    GlobalTheory.Grow.rapidDec_of_cuspForm hP hL.models.inf (hMM.aut _) (hMM.cusp _)
  have : BorelSpace (GA D (Wc D i)) := ⟨rfl⟩
  have hm : GlobalTheory.Grow.ModGrowth (Wc D i) (fun g => star (thetaKO (R.ωP i t) h g
      (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ρ h⁻¹ w))))) :=
    ((GlobalTheory.Core.Rk.ThetaGrowthBoth.thetaKO_modGrowth₂ D _ _ _ _ _ _ hω _ hf).right h).of_le
      (fun g => (norm_star _).le)
  have hl : ∀ γ ∈ GQ (Wc D i), ∀ g, star (thetaKO (R.ωP i t) h (γ * g)
      (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ρ h⁻¹ w)))) =
      star (thetaKO (R.ωP i t) h g (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ρ h⁻¹ w)))) :=
    fun γ hγ g => by rw [GlobalTheory.Chain.LiftConv.thetaKO_left hω hf h γ hγ g]
  have hms := ((GlobalTheory.Chain.LiftConv.thetaKO_continuous hω hf h).star).measurable.aestronglyMeasurable
    (μ := (R.νW i).restrict (R.fdW i))
  exact hR.integrableOn_modGrowth_mul (hL.models.νW i).1.1 (hL.models.νW i).2 hm hl hms

theorem integrable_kern (hP : GlobalTheory.Published.CuspRapidDecay) (R : RealDat D A Ks) (F : Face D A) (hL : Laws R F)
    (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (y : (R.HW i (sg0 D A)).H)
    (x : Formalism.IndefR.Bridge.Gf (Vc D i)) (w : (R.cV i).W) :
    IntegrableOn (fun g => star (kern R i t x w v g) * val R i v y g) (R.fdW i) (R.νW i) := by
  obtain ⟨h, -, rfl⟩ := KernLaws.exists_finite_lift _ x
  rw [KernLaws.kern_fin R i t hL.thP.ioP]
  exact integrable_kernA hP R F hL i t v y h w

theorem inner_rho (R : RealDat D A Ks) (F : Face D A) (hL : Laws R F) (i : Fin D.R.m) (h : GA D (Vc D i))
    (x z : (R.cV i).W) : ⟪x, (R.cV i).ρ h z⟫_ℂ = ⟪(R.cV i).ρ h⁻¹ x, z⟫_ℂ := by
  rw [← (hL.models.cV i).2.1 h⁻¹ x ((R.cV i).ρ h z), ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply]

theorem upVec_eq (hP : GlobalTheory.Published.CuspRapidDecay) (R : RealDat D A Ks) (F : Face D A) (hL : Laws R F)
    (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W) (y : (R.HW i (sg0 D A)).H) (h : GA D (Vc D i)) :
    upVec R i t v b y h = (R.cV i).ρ h⁻¹ (coVec R i v y b (kern R i t (Formalism.IndefR.FWT.fin (Vc D i) h))) := by
  have hinv : ∀ x : (R.cV i).W, (R.cV i).ρ h⁻¹ ((R.cV i).ρ h x) = x := fun x => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hin := inner_coVec R i v y b (kernA R i t h) (integrable_kernA hP R F hL i t v y h)
  apply ext_inner_left ℂ
  intro w
  rw [inner_rho R F hL, inv_inv, KernLaws.kern_fin R i t hL.thP.ioP, hin]
  have e2 : upVec R i t v b y h = ∑ k, phi R i v y (kernA R i t h) ((R.cV i).ρ h (b k)) • b k := by
    unfold upVec
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    unfold upLift phi
    refine integral_congr_ae (.of_forall fun g => ?_)
    dsimp only
    rw [KernLaws.kernA_apply, hinv]
    rfl
  rw [e2]
  refine inner_sum_eq b (fun w => phi R i v y (kernA R i t h) ((R.cV i).ρ h w)) (fun w w' => ?_) (fun c w => ?_) w
  · simp only [map_add, ← hin, inner_add_left]
  · simp only [map_smul, ← hin, inner_smul_left, Complex.star_def]

set_option maxHeartbeats 1000000 in

theorem coVec_level (R : RealDat D A Ks) (F : Face D A) (hL : Laws R F) (i : Fin D.R.m) (t : T)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W)
    (y : (R.HW i (sg0 D A)).H) (hT : DatumType R i t) (z : Formalism.IndefR.Bridge.Gf (Vc D i))
    (k : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J) :
    coVec R i v y b (kern R i t (z * k)) =
      (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k : ℂˣ) : ℂ) • coVec R i v y b (kern R i t z) := by
  have hlev := (kern_laws R i t hL.models.inf hL.models.cV hL.thP.ωP hL.thP.pt_theta hL.thP.ioP hT).2.2.1
  unfold coVec
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]
  congr 1
  unfold phi
  rw [← integral_const_mul]
  refine integral_congr_ae (.of_forall fun g => ?_)
  rw [hlev]
  simp only [Pi.smul_apply, smul_eq_mul, star_mul']
  rw [star_inv_of_finOrder _ (GlobalTheory.LevelCharOrder.levEnv_chi_isOfFinOrder (Vc D i) (R.βV i) (R.datVt i t) k), mul_assoc]

theorem coVec_rat (hP : GlobalTheory.Published.CuspRapidDecay) (R : RealDat D A Ks) (F : Face D A) (hL : Laws R F)
    (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W)
    (y : (R.HW i (sg0 D A)).H) (hT : DatumType R i t) (γ : GQ (Vc D i)) (x : Formalism.IndefR.Bridge.Gf (Vc D i)) :
    coVec R i v y b (kern R i t (Formalism.IndefR.Bridge.ratF (Vc D i) γ * x)) =
      (R.cV i).ρ (γ : GA D (Vc D i)) (coVec R i v y b (kern R i t x)) := by
  have hrat := (kern_laws R i t hL.models.inf hL.models.cV hL.thP.ωP hL.thP.pt_theta hL.thP.ioP hT).2.1
  apply ext_inner_left ℂ
  intro w
  rw [inner_coVec R i v y b _ (integrable_kern hP R F hL i t v y _), inner_rho R F hL,
    inner_coVec R i v y b _ (integrable_kern hP R F hL i t v y x)]
  unfold phi
  have e := hrat γ x ((R.cV i).ρ (γ : GA D (Vc D i))⁻¹ w)
  have e' : (R.cV i).coef.ρ γ ((R.cV i).ρ (γ : GA D (Vc D i))⁻¹ w) = w := by
    show (R.cV i).ρ (γ : GA D (Vc D i)) ((R.cV i).ρ (γ : GA D (Vc D i))⁻¹ w) = w
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [e'] at e
  rw [e]

theorem coefExt_apply {V : HSp D} (c : CoefA V) (f : Formalism.IndefR.Bridge.Gf V → c.W) (h : GA D V) :
    c.ext f h = c.ρ h⁻¹ (f (Formalism.IndefR.FWT.fin V h)) := rfl

set_option maxHeartbeats 2000000 in

theorem upVec_mem_range : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W) (y : (R.HW i (sg0 D A)).H), ∃ u : (R.HV i t).H, R.extV i t u = upVec R i t v b y := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R F hL _ i t v n b y
  have hT : DatumType R i t := fun g0 κ κ' h1 h2 =>
    GlobalTheory.VecInv.omega_lifts_vP R hL.lev hL.models.inf hL.thP.ωP hL.thP.vP i t g0 κ κ' h1 h2
  obtain ⟨f, hfd⟩ : ∃ f : Formalism.IndefR.Bridge.Gf (Vc D i) → (R.cV i).W, ∀ x, f x = coVec R i v y b (kern R i t x) :=
    ⟨_, fun _ => rfl⟩
  have hext : (R.cV i).ext f = upVec R i t v b y := by
    funext h
    rw [coefExt_apply, upVec_eq hP R F hL i t v b y h, hfd]
  have hmem : ∀ (γ : GQ (Vc D i)) (x : Formalism.IndefR.Bridge.Gf (Vc D i)) (k : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J),
      f (Formalism.IndefR.Bridge.ratF (Vc D i) γ * x * k) =
        (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k : ℂˣ) : ℂ) • (R.cV i).ρ (γ : GA D (Vc D i)) (f x) := by
    intro γ x k
    rw [hfd, hfd]
    exact (coVec_level R F hL i t v b y hT (Formalism.IndefR.Bridge.ratF (Vc D i) γ * x) k).trans
      (congrArg _ (coVec_rat hP R F hL i t v b y hT γ x))
  obtain ⟨u, hu⟩ : f ∈ LinearMap.range (R.HV i t).e := by
    rw [(hL.models.HV i t).2.1]
    exact hmem
  refine ⟨u, ?_⟩
  show (R.cV i).ext ((R.HV i t).e u) = _
  rw [hu, hext]

end GlobalTheory.AdjRange
