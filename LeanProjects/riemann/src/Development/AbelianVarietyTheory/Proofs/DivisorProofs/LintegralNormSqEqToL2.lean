import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFourierGau
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharacterHalfSymplecticFormRealPoint
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealSymplecticFormAlternatingInvariantDefinite
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FockVacuumAnnihilationEquationRealCoordinates
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Kronecker ContDiff ComplexOrder BoundedContinuousFunction

namespace GlobalTheory.RealWeil

section Mat

variable {O : Type} [Fintype O] [DecidableEq O] {m n : ℕ}

def unvecL : ((Fin m × Fin n) × O → ℂ) →L[ℝ] (O → Fin m → Fin n → ℂ) :=
  ContinuousLinearMap.pi fun τ => ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    ContinuousLinearMap.proj ((i, j), τ)

def vecL : (O → Fin m → Fin n → ℂ) →L[ℝ] ((Fin m × Fin n) × O → ℂ) :=
  ContinuousLinearMap.pi fun p => (ContinuousLinearMap.proj (φ := fun _ : Fin n => ℂ) p.1.2).comp
    ((ContinuousLinearMap.proj (φ := fun _ : Fin m => Fin n → ℂ) p.1.1).comp
      (ContinuousLinearMap.proj (φ := fun _ : O => Fin m → Fin n → ℂ) p.2))

omit [Fintype O] [DecidableEq O] in
theorem unv_vecL (x : O → Fin m → Fin n → ℂ) : unvecL (vecL x) = x := rfl

omit [Fintype O] [DecidableEq O] in
theorem vecL_unv (x : (Fin m × Fin n) × O → ℂ) : vecL (unvecL x) = x := rfl

def cpt (v : (Fin m × Fin n) × O → ℂ) (τ : O) : Matrix (Fin m) (Fin n) ℂ := Matrix.of fun i j => v ((i, j), τ)

def blk (b : O → Matrix (Fin m) (Fin m) ℂ) (a : O → Matrix (Fin n) (Fin n) ℂ) :
    Matrix ((Fin m × Fin n) × O) ((Fin m × Fin n) × O) ℂ :=
  blockDiagonal fun τ => b τ ⊗ₖ (a τ)ᵀ

theorem blockDiagonal_mulVec {κ : Type} [Fintype κ] (M : O → Matrix κ κ ℂ) (v : κ × O → ℂ) (i : κ) (τ : O) :
    (blockDiagonal M *ᵥ v) (i, τ) = (M τ *ᵥ fun j => v (j, τ)) i := by
  simp only [mulVec, dotProduct, Fintype.sum_prod_type, blockDiagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

theorem cpt_blk (b : O → Matrix (Fin m) (Fin m) ℂ) (a : O → Matrix (Fin n) (Fin n) ℂ)
    (v : (Fin m × Fin n) × O → ℂ) (τ : O) : cpt (blk b a *ᵥ v) τ = b τ * cpt v τ * a τ := by
  ext i j
  simp only [cpt, blk, of_apply, blockDiagonal_mulVec]
  simp only [mulVec, dotProduct, Fintype.sum_prod_type, kroneckerMap_apply,
    transpose_apply, mul_apply, of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem blk_mul (b b' : O → Matrix (Fin m) (Fin m) ℂ) (a a' : O → Matrix (Fin n) (Fin n) ℂ) :
    blk b a * blk b' a' = blk (fun τ => b τ * b' τ) fun τ => a' τ * a τ := by
  simp only [blk, ← blockDiagonal_mul, ← mul_kronecker_mul, transpose_mul]

omit [Fintype O] in
theorem blk_one : blk (O := O) (m := m) (n := n) (fun _ => 1) (fun _ => 1) = 1 := by
  simp only [blk, transpose_one, one_kronecker_one]
  exact blockDiagonal_one

omit [Fintype O] in
theorem blk_conjTranspose (b : O → Matrix (Fin m) (Fin m) ℂ) (a : O → Matrix (Fin n) (Fin n) ℂ) :
    (blk b a)ᴴ = blk (fun τ => (b τ)ᴴ) fun τ => (a τ)ᴴ := by
  simp only [blk, blockDiagonal_conjTranspose, conjTranspose_kronecker]
  rfl

omit [DecidableEq O] in
theorem star_dotProduct_eq (x y : (Fin m × Fin n) × O → ℂ) :
    star y ⬝ᵥ x = ∑ τ, ((cpt y τ)ᴴ * cpt x τ).trace := by
  simp only [dotProduct, Fintype.sum_prod_type, trace, diag_apply, mul_apply, conjTranspose_apply, cpt, of_apply,
    Pi.star_apply]
  rw [Finset.sum_comm]
  simp only [Finset.sum_comm (s := (Finset.univ : Finset (Fin m))) (t := (Finset.univ : Finset O))]
  rw [Finset.sum_comm]

theorem detPlus_blockDiagonal (sT b : O → Matrix (Fin m) (Fin m) ℂ) (sS a : O → Matrix (Fin n) (Fin n) ℂ) :
    dP (blk sT sS) (blk b a) = ∏ τ, GlobalTheory.WeilParts.detPlus (sS τ) (sT τ) (a τ) (b τ) := by
  unfold dP GlobalTheory.WeilParts.detPlus blk
  rw [← det_blockDiagonal, ← blockDiagonal_one, ← blockDiagonal_add, ← blockDiagonal_sub, ← blockDiagonal_mul,
    ← blockDiagonal_smul, ← blockDiagonal_smul, ← blockDiagonal_add]
  rfl

theorem blk_posDef {b : O → Matrix (Fin m) (Fin m) ℂ} {a : O → Matrix (Fin n) (Fin n) ℂ} (hb : ∀ τ, (b τ).PosDef)
    (ha : ∀ τ, (a τ).PosDef) : (blk b a).PosDef := by
  have hk : ∀ τ, (b τ ⊗ₖ (a τ)ᵀ).PosDef := fun τ => (hb τ).kronecker (ha τ).transpose
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · unfold IsHermitian blk
    rw [blockDiagonal_conjTranspose]
    congr 1
    funext τ
    exact (hk τ).1
  · have e : star x ⬝ᵥ blk b a *ᵥ x = ∑ τ, star (fun j => x (j, τ)) ⬝ᵥ (b τ ⊗ₖ (a τ)ᵀ) *ᵥ fun j => x (j, τ) := by
      rw [dotProduct, Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => ?_
      rw [blk, blockDiagonal_mulVec]
      rfl
    rw [e]
    obtain ⟨⟨i, τ⟩, h⟩ := Function.ne_iff.1 hx
    exact Finset.sum_pos' (fun τ _ => (hk τ).posSemidef.dotProduct_mulVec_nonneg _)
      ⟨τ, Finset.mem_univ _, (hk τ).dotProduct_mulVec_pos (Function.ne_iff.2 ⟨i, h⟩)⟩

omit [Fintype O] in
theorem continuous_blk {Y : Type} [TopologicalSpace Y] {b : Y → O → Matrix (Fin m) (Fin m) ℂ}
    {a : Y → O → Matrix (Fin n) (Fin n) ℂ} (hb : ∀ τ, Continuous fun y => b y τ) (ha : ∀ τ, Continuous fun y => a y τ) :
    Continuous fun y => blk (b y) (a y) := by
  refine Continuous.matrix_blockDiagonal (continuous_pi fun τ => continuous_matrix fun p q => ?_)
  exact ((hb τ).matrix_elem p.1 q.1).mul ((ha τ).matrix_elem q.2 p.2)

end Mat

section Quasi

variable {X Γ : Type} [AddCommGroup X] [TopologicalSpace X] {r : Γ → X} {q : Γ → X → ℂ}

def QB (r : Γ → X) (q : Γ → X → ℂ) : Submodule ℂ (X →ᵇ ℂ) where
  carrier := {f | ∀ γ w, f (r γ + w) = q γ w * f w}
  add_mem' := fun {f g} hf hg γ w => by
    rw [BoundedContinuousFunction.add_apply, BoundedContinuousFunction.add_apply, hf, hg, mul_add]
  zero_mem' := fun γ w => by simp
  smul_mem' := fun a f hf γ w => by
    rw [BoundedContinuousFunction.smul_apply, BoundedContinuousFunction.smul_apply, hf, smul_eq_mul, smul_eq_mul,
      mul_left_comm]

instance : CompleteSpace (QB r q) := by
  have : IsClosed (QB r q : Set (X →ᵇ ℂ)) := by
    show IsClosed {f : X →ᵇ ℂ | ∀ γ w, f (r γ + w) = q γ w * f w}
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun γ => isClosed_iInter fun w => isClosed_eq (continuous_eval_const _)
      (continuous_const.mul (continuous_eval_const _))
  exact this.completeSpace_coe

def ev (r : Γ → X) (q : Γ → X → ℂ) (x : X) : QB r q →L[ℂ] ℂ :=
  (BoundedContinuousFunction.evalCLM ℂ x).comp (QB r q).subtypeL

theorem ev_apply (x : X) (f : QB r q) : ev r q x f = f.1 x := rfl

theorem norm_ev_le (x : X) (f : QB r q) : ‖f.1 x‖ ≤ ‖f‖ := f.1.norm_coe_le_norm x

theorem norm_QB_le (f : QB r q) {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, ‖f.1 x‖ ≤ C) : ‖f‖ ≤ C :=
  (BoundedContinuousFunction.norm_le hC).2 h

theorem QB_ext {f g : QB r q} (h : ∀ x, f.1 x = g.1 x) : f = g := Subtype.ext (BoundedContinuousFunction.ext h)

def mkB (f : X → ℂ) (hc : Continuous f) (hb : ∃ C, ∀ x, ‖f x‖ ≤ C) (hq : ∀ γ w, f (r γ + w) = q γ w * f w) : QB r q :=
  ⟨BoundedContinuousFunction.ofNormedAddCommGroup f hc hb.choose hb.choose_spec, hq⟩

theorem coe_mkB (f : X → ℂ) (hc : Continuous f) (hb : ∃ C, ∀ x, ‖f x‖ ≤ C)
    (hq : ∀ γ w, f (r γ + w) = q γ w * f w) : ((mkB f hc hb hq).1 : X → ℂ) = f := rfl

variable [ContinuousAdd X]

def trB (b : X → ℂ) (w : X) (hb : Continuous b) (hn : ∀ x, ‖b x‖ = 1)
    (hq : ∀ f : X → ℂ, (∀ γ x, f (r γ + x) = q γ x * f x) →
      ∀ γ x, b (r γ + x) * f (r γ + x + w) = q γ x * (b x * f (x + w))) : QB r q →L[ℂ] QB r q :=
  LinearMap.mkContinuous
    { toFun := fun f => mkB (fun x => b x * f.1 (x + w)) (hb.mul (f.1.continuous.comp (continuous_add_right w)))
        ⟨‖f‖, fun x => by rw [norm_mul, hn, one_mul]; exact norm_ev_le _ f⟩ (hq f.1 f.2)
      map_add' := fun f g => QB_ext fun x => mul_add _ _ _
      map_smul' := fun a f => QB_ext fun x => mul_left_comm _ _ _ }
    1 fun f => by
      rw [one_mul]
      refine norm_QB_le _ (norm_nonneg _) fun x => ?_
      show ‖b x * f.1 (x + w)‖ ≤ _
      rw [norm_mul, hn, one_mul]; exact norm_ev_le _ f

theorem coe_trB (b : X → ℂ) (w : X) (hb hn hq) (f : QB r q) :
    ((trB b w hb hn hq f).1 : X → ℂ) = fun x => b x * f.1 (x + w) := rfl

def toL2 [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] (r : Γ → X) (q : Γ → X → ℂ) (ν : Measure X)
    [IsFiniteMeasure ν] : QB r q →L[ℂ] Lp ℂ 2 ν :=
  (BoundedContinuousFunction.toLp 2 ν ℂ).comp (QB r q).subtypeL

omit [ContinuousAdd X] in
theorem lintegral_norm_sq_eq_toL2 [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] (ν : Measure X)
    [IsFiniteMeasure ν] (f : QB r q) : ∫⁻ w, ‖f.1 w‖ₑ ^ 2 ∂ν = ‖toL2 r q ν f‖ₑ ^ 2 := by
  have h := eLpNorm_congr_ae (p := 2) (BoundedContinuousFunction.coeFn_toLp 2 ν ℂ f.1)
  have e : ‖toL2 r q ν f‖ₑ = eLpNorm f.1 2 ν := by rw [← h]; exact Lp.enorm_def _
  rw [e, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat, ← ENNReal.rpow_two,
    ← ENNReal.rpow_mul]
  simp

end Quasi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

abbrev BB (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Submodule ℂ (WO S T →ᵇ ℂ) :=
  QB (ratW T S) fun γ w => ψ (-(symplOH S T (ratW T S γ) w))

instance : IsTopologicalAddGroup (WO S T) := (GlobalTheory.AdelicMatrixLattice.lattice D T S).1

def rhoB (hψ : IsStdChar D ψ (-1)) (w : WO S T) : BB ψ S T →L[ℂ] BB ψ S T :=
  trB (fun x => ψ (symplOH S T x w)) w (hψ.1.1.comp (continuous_symplOH continuous_id continuous_const))
    (fun _ => hψ.1.2.1 _) fun f hf => heisO_quasi w f hf

theorem coe_rhoB (hψ : IsStdChar D ψ (-1)) (w : WO S T) (f : BB ψ S T) :
    ((rhoB hψ w f).1 : WO S T → ℂ) = heisO ψ S T w f.1 := coe_trB _ _ _ _ _ f

theorem norm_rhoB (hψ : IsStdChar D ψ (-1)) (w : WO S T) (f : BB ψ S T) : ‖rhoB hψ w f‖ = ‖f‖ := by
  refine le_antisymm (norm_QB_le _ (norm_nonneg _) fun x => ?_) (norm_QB_le _ (norm_nonneg _) fun x => ?_)
  · rw [coe_rhoB, GlobalTheory.HeisOrtho.norm_heisO hψ.1]; exact norm_ev_le _ f
  · have := norm_ev_le (x - w) (rhoB hψ w f)
    rwa [coe_rhoB, GlobalTheory.HeisOrtho.norm_heisO hψ.1, sub_add_cancel] at this

theorem rhoB_rhoB (hψ : IsStdChar D ψ (-1)) (w w' : WO S T) (f : BB ψ S T) :
    rhoB hψ w (rhoB hψ w' f) = ψ (symplOH S T w w') • rhoB hψ (w + w') f :=
  QB_ext fun x => congrFun (heisO_heisO w w' f.1) x

theorem BB_norm_periodic (hψ : IsStdChar D ψ (-1)) (f : BB ψ S T) : ∀ γ ∈ ratL T S, ∀ w, ‖f.1 (γ + w)‖ = ‖f.1 w‖ := by
  rintro _ ⟨γ, rfl⟩ w
  have := congrArg norm (f.2 γ w)
  rw [norm_mul, hψ.1.2.1, one_mul] at this
  exact this

theorem continuous_rhoB (hψ : IsStdChar D ψ (-1)) (f : BB ψ S T) : Continuous fun w => rhoB hψ w f := by
  obtain ⟨i1, -, -, -, -, K, hK, hc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let F : C(WO S T × K, ℂ) := ⟨fun p => heisO ψ S T p.1 f.1 p.2,
    (hψ.1.1.comp (continuous_symplOH (continuous_subtype_val.comp continuous_snd) continuous_fst)).mul
      (f.1.continuous.comp ((continuous_subtype_val.comp continuous_snd).add continuous_fst))⟩
  refine continuous_iff_continuousAt.2 fun w₀ => ?_
  have h1 := tendsto_iff_norm_sub_tendsto_zero.1 (F.curry.continuous.tendsto w₀)
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _) (fun w => ?_) h1)
  refine norm_QB_le _ (norm_nonneg _) fun x => ?_
  obtain ⟨γ, hγ, h⟩ := hc x
  rw [← BB_norm_periodic hψ _ γ hγ]
  exact (F.curry w - F.curry w₀).norm_coe_le_norm ⟨γ + x, h⟩

abbrev Ix (S T : HSp D) : Type := (Fin T.rank × Fin S.rank) × D.what₂.Tau

def iotaV (σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D) (S T : HSp D) (v : Ix S T → ℂ) : WO S T := iotaW σ T S (unvecL v)

open Classical in

def HM (S T : HSp D) : Matrix (Ix S T) (Ix S T) ℂ :=
  blk (fun τ => ((2 * (tauE D τ D.host.xi0).im : ℝ) : ℂ) • gramAt D T τ) fun τ => (gramAt D S τ)⁻¹

theorem im_HM (x y : Ix S T → ℂ) : (star y ⬝ᵥ HM S T *ᵥ x).im = -GlobalTheory.VacUnique.omO S T (unvecL x) (unvecL y) := by
  classical
  rw [star_dotProduct_eq, GlobalTheory.VacUnique.omO_apply, Complex.im_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have e : ((cpt y τ)ᴴ * cpt (HM S T *ᵥ x) τ).trace =
      ((2 * (tauE D τ D.host.xi0).im : ℝ) : ℂ) * GlobalTheory.VacUnique.hAt S T τ (cpt x τ) (cpt y τ) := by
    unfold HM GlobalTheory.VacUnique.hAt
    rw [cpt_blk, ← Matrix.mul_assoc, trace_mul_comm, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, trace_smul,
      smul_eq_mul]
    simp only [Matrix.mul_assoc]
  rw [e, Complex.im_ofReal_mul]
  show _ = -(2 * (tauE D τ D.host.xi0 * GlobalTheory.VacUnique.hAt S T τ (cpt x τ) (cpt y τ)).re)
  rw [Complex.mul_re, GlobalTheory.RealSymplForm.realPlace_imaginaryGenerator_re_eq_zero]
  ring

theorem iotaV_add (x y : Ix S T → ℂ) : iotaV σ S T (x + y) = iotaV σ S T x + iotaV σ S T y := by
  unfold iotaV
  rw [map_add, AddMonoidHom.map_add]

theorem real_iotaV (h : Chart θ σ) (x : Ix S T → ℂ) : (iotaV σ S T x).map (finPart D) = 0 := h.real_iota T S _

theorem continuous_iotaV (h : Chart θ σ) : Continuous (iotaV σ S T) :=
  (h.continuous_iota T S).comp (unvecL (O := D.what₂.Tau) (m := T.rank) (n := S.rank)).continuous

def rhoV (hψ : IsStdChar D ψ (-1)) (σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D) (S T : HSp D) (v : Ix S T → ℂ) :
    BB ψ S T →L[ℂ] BB ψ S T := rhoB hψ (iotaV σ S T v)

theorem coe_rhoV (hψ : IsStdChar D ψ (-1)) (v : Ix S T → ℂ) (f : BB ψ S T) :
    ((rhoV hψ σ S T v f).1 : WO S T → ℂ) = heisO ψ S T (iotaV σ S T v) f.1 := coe_rhoB _ _ _

theorem isHeis_rhoB (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) :
    IsHeis (fun x y => (star y ⬝ᵥ HM S T *ᵥ x).im) (rhoV hψ σ S T) := by
  refine ⟨fun f => QB_ext fun x => ?_, fun u v f => ?_, fun u f => norm_rhoB hψ _ f, fun f => ?_⟩
  · have : iotaV σ S T 0 = 0 := by unfold iotaV; rw [map_zero, AddMonoidHom.map_zero]
    rw [coe_rhoV, this, heisO_zero]
  · have e : ψ (symplOH S T (iotaV σ S T u) (iotaV σ S T v)) =
        Complex.exp (Real.pi * Complex.I * ((star v ⬝ᵥ HM S T *ᵥ u).im : ℂ)) := by
      rw [GlobalTheory.OrientedChar.char_symplOH D θ ψ h.inf hψ S T _ _ (Or.inl (real_iotaV h u)), im_HM u v]
      unfold iotaV
      rw [h.pi_iota, h.pi_iota]
      push_cast
      congr 1
      ring
    show rhoB hψ (iotaV σ S T u) (rhoB hψ (iotaV σ S T v) f) = _ • rhoB hψ (iotaV σ S T (u + v)) f
    rw [rhoB_rhoB, iotaV_add, e]
  · exact (continuous_rhoB hψ f).comp (continuous_iotaV h)

theorem HM_herm : (HM S T)ᴴ = HM S T := by
  classical
  unfold HM
  rw [blk_conjTranspose]
  congr 1 <;> funext τ
  · rw [conjTranspose_smul, GlobalTheory.SmoothForms.RealPts.gramAt_herm]
    simp
  · rw [conjTranspose_nonsing_inv, GlobalTheory.SmoothForms.RealPts.gramAt_herm]

theorem two_im_pos (τ : D.what₂.Tau) : (0 : ℂ) < ((2 * (tauE D τ D.host.xi0).im : ℝ) : ℂ) := by
  have := xi_zero_im_pos D τ
  exact Complex.zero_lt_real.2 (by linarith)

open Classical in
theorem HM_det : (HM S T).det ≠ 0 := by
  have : HM S T * blk (fun τ => ((2 * (tauE D τ D.host.xi0).im : ℝ) : ℂ)⁻¹ • (gramAt D T τ)⁻¹) (gramAt D S) = 1 := by
    unfold HM
    rw [blk_mul, ← blk_one]
    congr 1 <;> funext τ
    · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ (two_im_pos τ).ne', one_smul,
        mul_nonsing_inv _ (GlobalTheory.SmoothForms.RealPts.gramAt_unit T τ)]
    · rw [mul_nonsing_inv _ (GlobalTheory.SmoothForms.RealPts.gramAt_unit S τ)]
  exact (isUnit_det_of_right_inverse this).ne_zero

open Classical in

def mM (θ : InfFam D) (S T : HSp D) : GA D S × GA D T →* Matrix (Ix S T) (Ix S T) ℂ where
  toFun p := blk (fun τ => compAt θ τ (Formalism.L2.Theta.mt T p.2)) fun τ => compAt θ τ (Formalism.L2.Theta.mt S p.1⁻¹)
  map_one' := by
    simp only [Prod.snd_one, Prod.fst_one, inv_one, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one]
    exact blk_one
  map_mul' p q := by
    rw [blk_mul]
    simp only [Prod.snd_mul, Prod.fst_mul, _root_.mul_inv_rev, GlobalTheory.WeilVacMove.mt_mul, GlobalTheory.WeilVacMove.compAt_mul]

open Classical in
theorem mM_apply (g : GA D S) (h : GA D T) : mM θ S T (g, h) =
    blk (fun τ => compAt θ τ (Formalism.L2.Theta.mt T h)) fun τ => compAt θ τ (Formalism.L2.Theta.mt S g⁻¹) := rfl

theorem compAt_unitary (hθ : IsInfFam θ) (V : HSp D) (g : GA D V) (τ : D.what₂.Tau) :
    (compAt θ τ (Formalism.L2.Theta.mt V g))ᴴ * gramAt D V τ * compAt θ τ (Formalism.L2.Theta.mt V g) = gramAt D V τ :=
  GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ

open Classical in
theorem mM_unitary (hθ : IsInfFam θ) (p : GA D S × GA D T) : (mM θ S T p)ᴴ * HM S T * mM θ S T p = HM S T := by
  obtain ⟨g, h⟩ := p
  unfold HM
  rw [mM_apply, blk_conjTranspose, blk_mul, blk_mul]
  congr 1 <;> funext τ
  · rw [Matrix.mul_smul, Matrix.smul_mul, compAt_unitary hθ]
  · have h1 := compAt_unitary hθ S g τ
    have h2 := GlobalTheory.WeilVacMove.compAt_mt_mul_inv θ τ S g
    conv_rhs => rw [← h1, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← conjTranspose_nonsing_inv, inv_eq_right_inv h2]

theorem continuous_mt (V : HSp D) : Continuous (Formalism.L2.Theta.mt V) ∧ Continuous fun g : GA D V => Formalism.L2.Theta.mt V g⁻¹ := by
  have h : Continuous fun g : GA D V => matHom V g := continuous_subtype_val
  refine ⟨Units.continuous_val.comp h, ?_⟩
  have e : (fun g : GA D V => Formalism.L2.Theta.mt V g⁻¹) = fun g => ((matHom V g)⁻¹).1 := by
    funext g
    unfold Formalism.L2.Theta.mt
    rw [map_inv]
  rw [e]
  exact Units.continuous_coe_inv.comp h

theorem continuous_compAt (hθ : IsInfFam θ) (τ : D.what₂.Tau) (m n : ℕ) : Continuous fun x : Mx D m n => compAt θ τ x :=
  continuous_id.matrix_map (continuous_comp hθ τ)

open Classical in
theorem continuous_mM (hθ : IsInfFam θ) : Continuous (mM θ S T) := by
  have h1 : Continuous fun p : GA D S × GA D T => Formalism.L2.Theta.mt T p.2 := (continuous_mt T).1.comp continuous_snd
  have h2 : Continuous fun p : GA D S × GA D T => Formalism.L2.Theta.mt S p.1⁻¹ := (continuous_mt S).2.comp continuous_fst
  exact continuous_blk (b := fun (p : GA D S × GA D T) τ => compAt θ τ (Formalism.L2.Theta.mt T p.2))
    (a := fun (p : GA D S × GA D T) τ => compAt θ τ (Formalism.L2.Theta.mt S p.1⁻¹))
    (fun τ => (continuous_compAt hθ τ _ _).comp h1) fun τ => (continuous_compAt hθ τ _ _).comp h2

theorem compAt_fin {V : HSp D} {g : GA D V} (hg : g ∈ GfC V) (τ : D.what₂.Tau) :
    compAt θ τ (Formalism.L2.Theta.mt V g) = 1 := by
  have h1 : (Formalism.L2.Theta.mt V g).map (infPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hg)
  have h2 : compAt θ τ (Formalism.L2.Theta.mt V g) = ((Formalism.L2.Theta.mt V g).map (infPart D)).map (θ τ) := rfl
  rw [h2, h1, Matrix.map_one _ (map_zero _) (map_one _)]

open Classical in
theorem mM_fin {g : GA D S} {h : GA D T} (hg : g ∈ GfC S) (hh : h ∈ GfC T) : mM θ S T (g, h) = 1 := by
  rw [mM_apply]
  simp only [compAt_fin hh, compAt_fin (inv_mem hg)]
  exact blk_one

open Classical in
theorem actO_iotaV (hc : Chart θ σ) (g : GA D S) (h : GA D T) (v : Ix S T → ℂ) :
    actO S T g h (iotaV σ S T v) = iotaV σ S T (mM θ S T (g, h) *ᵥ v) := by
  refine hc.real_ext (V := T) (W := S) ?_ (real_iotaV hc _) ?_
  · show (actO S T g h (iotaV σ S T v)).map (finPart D) = 0
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, real_iotaV hc, Matrix.mul_zero, Matrix.zero_mul]
  · funext τ
    have e : ∀ v, compAt θ τ (iotaV σ S T v) = cpt v τ := fun v => congrFun (hc.pi_iota T S (unvecL v)) τ
    show compAt θ τ (actO S T g h (iotaV σ S T v)) = compAt θ τ (iotaV σ S T (mM θ S T (g, h) *ᵥ v))
    rw [GlobalTheory.WeilVacMove.compAt_actO, e, e, mM_apply, cpt_blk]

theorem actO_fin (hc : Chart θ σ) {g : GA D S} {h : GA D T} (hg : g ∈ GinfC S) (hh : h ∈ GinfC T) {u : WO S T}
    (hu : u.map (infPart D) = 0) : actO S T g h u = u := by
  have h1 : (Formalism.L2.Theta.mt T h).map (finPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hh)
  have h2 : (Formalism.L2.Theta.mt S g⁻¹).map (finPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 (inv_mem hg))
  have h3 : (actO S T g h u).map (finPart D) = u.map (finPart D) := by
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, h1, h2, Matrix.one_mul, Matrix.mul_one]
  have h4 : (actO S T g h u).map (infPart D) = u.map (infPart D) := by
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, hu, Matrix.mul_zero, Matrix.zero_mul]
  ext i j
  rw [← sub_eq_zero]
  refine hc.ext _ ?_ fun τ => ?_
  · have : finPart D (actO S T g h u i j) = finPart D (u i j) := congrFun (congrFun h3 i) j
    rw [RingHom.map_sub, this, sub_self]
  · have : infPart D (actO S T g h u i j) = infPart D (u i j) := congrFun (congrFun h4 i) j
    rw [RingHom.map_sub, this, sub_self, RingHom.map_zero]

open Classical in
theorem HM_cartan {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ))
    (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) :
    blk sT sS * blk sT sS = 1 ∧ (HM S T * blk sT sS).PosDef := by
  constructor
  · rw [blk_mul]
    simp only [fun τ => (hS τ).1, fun τ => (hT τ).1]
    exact blk_one
  · unfold HM
    rw [blk_mul]
    refine blk_posDef (fun τ => ?_) fun τ => ?_
    · rw [Matrix.smul_mul]
      exact (hT τ).2.2.smul (two_im_pos τ)
    · rw [← GlobalTheory.RealSymplForm.cartan_inv_mul (hS τ)]
      exact (hS τ).2.2.inv

end GlobalTheory.RealWeil

end
