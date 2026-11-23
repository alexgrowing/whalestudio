import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiFacts

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

namespace Ps1

local notation "𝕄" => Fin n → Fin n → ℂ

lemma contDiffAt_zpow {f : 𝕄 → ℂ} {x : 𝕄}
    (hf : ContDiffAt ℂ 1 f x) (hx : f x ≠ 0) (m : ℤ) : ContDiffAt ℂ 1 (fun y => f y ^ m) x := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · simpa only [zpow_natCast] using hf.pow k
  · refine ((hf.pow k).inv (pow_ne_zero k hx)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => ?_)
    simp [_root_.zpow_neg]

lemma contDiff_lead (i : ℕ) : ContDiff ℂ 1 (fun z : 𝕄 => lead i z) := by
  by_cases h : i ≤ n
  · have e : (fun z : 𝕄 => lead i z) = fun z =>
        ∑ σ : Equiv.Perm (Fin i), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
          ∏ j, z (Fin.castLE h (σ j)) (Fin.castLE h j) := by
      funext z
      simp only [lead, dif_pos h, Matrix.det_apply']
      rfl
    rw [e]
    exact ContDiff.sum fun σ _ => contDiff_const.mul
      (contDiff_prod fun j _ => contDiff_apply_apply ℂ ℂ _ _)
  · have e : (fun z : 𝕄 => lead i z) = fun _ => 0 := by
      funext z
      simp only [lead, dif_neg h]
    rw [e]
    exact contDiff_const

def PhiP (μ : Fin n → ℤ) : 𝕄 → ℂ := fun y => PhiM μ y

lemma contDiffAt_phiP (μ : Fin n → ℤ) {z : 𝕄} (hz : z ∈ OmegaSet n) :
    ContDiffAt ℂ 1 (PhiP μ) z := by
  show ContDiffAt ℂ 1 (fun y : 𝕄 => ∏ i : Fin n, lead ((i : ℕ) + 1) y ^ (-(μ i - muNext μ i))) z
  exact contDiffAt_prod fun i _ => contDiffAt_zpow (contDiff_lead _).contDiffAt (hz i) _

lemma isOpen_omega' : IsOpen (OmegaSet n) := by
  have e : OmegaSet n = ⋂ i : Fin n, {z | lead ((i : ℕ) + 1) z ≠ 0} := by
    ext z
    simp [OmegaSet]
  rw [e]
  exact isOpen_iInter_of_finite fun i => isOpen_ne_fun (contDiff_lead _).continuous continuous_const

lemma continuousOn_fderiv_phiP (μ : Fin n → ℤ) :
    ContinuousOn (fderiv ℂ (PhiP μ)) (OmegaSet n : Set 𝕄) :=
  ContDiffOn.continuousOn_fderiv_of_isOpen (fun _ hz => (contDiffAt_phiP μ hz).contDiffWithinAt)
    isOpen_omega' le_rfl

lemma continuousOn_phiP (μ : Fin n → ℤ) : ContinuousOn (PhiP μ) (OmegaSet n : Set 𝕄) :=
  fun _ hz => (contDiffAt_phiP μ hz).continuousAt.continuousWithinAt

def conjLin (A B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun H := A * H * B
  map_add' H H' := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c H := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

def conjCLM (A B : Matrix (Fin n) (Fin n) ℂ) : 𝕄 →L[ℂ] 𝕄 :=
  LinearMap.toContinuousLinearMap (conjLin A B : 𝕄 →ₗ[ℂ] 𝕄)

lemma conjCLM_apply (A B H : Matrix (Fin n) (Fin n) ℂ) : conjCLM A B H = A * H * B := rfl

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

lemma continuous_toMK' : Continuous fun k : KG ε => toMK k :=
  (continuous_toM ε).comp continuous_subtype_val

lemma continuous_toMK_inv : Continuous fun k : KG ε => toMK k⁻¹ :=
  continuous_toMK'.comp continuous_inv

lemma continuous_conj :
    Continuous fun p : Matrix (Fin n) (Fin n) ℂ × KG ε => toMK p.2⁻¹ * p.1 * toMK p.2 :=
  ((continuous_toMK_inv.comp continuous_snd).matrix_mul continuous_fst).matrix_mul
    (continuous_toMK'.comp continuous_snd)

lemma continuous_P (T : KType ε Λ) : Continuous fun k : KG ε => T.op k * projW T * T.op k⁻¹ := by
  have h : Continuous fun k : KG ε => T.op k := continuous_subtype_val.comp T.cont
  exact (h.mul continuous_const).mul (h.comp continuous_inv)

lemma toMK_inv_eq (k : KG ε) : toMK k⁻¹ = (toMK k)ᴴ := by
  have h : toMK k⁻¹ = star (toMK k) :=
    Units.inv_eq_of_mul_eq_one_right (Unitary.mul_star_self_of_mem k.2.1)
  rw [h, Matrix.star_eq_conjTranspose]

def Uset (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {z | ∀ k : KG ε, toMK k⁻¹ * z * toMK k ∈ OmegaSet n}

lemma isOpen_Uset [CompactSpace (KG ε)] : IsOpen (Uset ε) := by
  have hC : IsClosed ((fun p : Matrix (Fin n) (Fin n) ℂ × KG ε => toMK p.2⁻¹ * p.1 * toMK p.2) ⁻¹'
      (OmegaSet n)ᶜ) :=
    isOpen_omega'.isClosed_compl.preimage continuous_conj
  have e : (Uset ε)ᶜ = Prod.fst ''
      ((fun p : Matrix (Fin n) (Fin n) ℂ × KG ε => toMK p.2⁻¹ * p.1 * toMK p.2) ⁻¹' (OmegaSet n)ᶜ) := by
    ext z
    constructor
    · intro hz
      simp only [Uset, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall] at hz
      obtain ⟨k, hk⟩ := hz
      exact ⟨(z, k), hk, rfl⟩
    · rintro ⟨p, hp, rfl⟩ hz
      exact hp (hz p.2)
  rw [← isClosed_compl_iff, e]
  exact isClosedMap_fst_of_compactSpace _ hC

lemma posSet_subset_Uset : posSet n ⊆ Uset ε := by
  intro x hx k
  apply posSet_subset_omega
  show (toMK k⁻¹ * x * toMK k).PosDef
  rw [toMK_inv_eq]
  refine Matrix.PosDef.conjTranspose_mul_mul_same hx ?_
  intro v w hvw
  have h1 : (toMK k)ᴴ * toMK k = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mul_self_of_mem k.2.1
  have := congrArg (fun u => (toMK k)ᴴ *ᵥ u) hvw
  simpa only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] using this

def GintD (T : KType ε Λ) (μ : Fin n → ℤ) (x : Matrix (Fin n) (Fin n) ℂ) (k : KG ε) :
    𝕄 →L[ℂ] (T.V →L[ℂ] T.V) :=
  fderiv ℂ (fun y : 𝕄 => Gint T μ y k) x

lemma hasFDerivAt_Gint0 (T : KType ε Λ) (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (k : KG ε)
    (hx : toMK k⁻¹ * x * toMK k ∈ OmegaSet n) :
    HasFDerivAt (fun y : 𝕄 => Gint T μ y k)
      (((fderiv ℂ (PhiP μ) (toMK k⁻¹ * x * toMK k)).comp (conjCLM (toMK k⁻¹) (toMK k))).smulRight
        (T.op k * projW T * T.op k⁻¹)) x := by
  have h1 : HasFDerivAt (fun y : 𝕄 => toMK k⁻¹ * Matrix.of y * toMK k)
      (conjCLM (toMK k⁻¹) (toMK k)) x :=
    (conjCLM (toMK k⁻¹) (toMK k)).hasFDerivAt
  have h2 : HasFDerivAt (PhiP μ) (fderiv ℂ (PhiP μ) (toMK k⁻¹ * x * toMK k)) (toMK k⁻¹ * x * toMK k) :=
    (contDiffAt_phiP μ hx).differentiableAt_one.hasFDerivAt
  exact (h2.comp x h1).smul_const (T.op k * projW T * T.op k⁻¹)

lemma hasFDerivAt_Gint (T : KType ε Λ) (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (k : KG ε)
    (hx : toMK k⁻¹ * x * toMK k ∈ OmegaSet n) :
    HasFDerivAt (fun y : 𝕄 => Gint T μ y k) (GintD T μ x k) x :=
  (hasFDerivAt_Gint0 T μ k hx).differentiableAt.hasFDerivAt

lemma GintD_apply (T : KType ε Λ) (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (k : KG ε)
    (hx : toMK k⁻¹ * x * toMK k ∈ OmegaSet n) (H : 𝕄) :
    GintD T μ x k H = fderiv ℂ (PhiP μ) (toMK k⁻¹ * x * toMK k) (toMK k⁻¹ * Matrix.of H * toMK k) •
      (T.op k * projW T * T.op k⁻¹) := by
  rw [GintD, (hasFDerivAt_Gint0 T μ k hx).fderiv]
  rfl

lemma continuousOn_GintD (T : KType ε Λ) (μ : Fin n → ℤ) :
    ContinuousOn (fun p : Matrix (Fin n) (Fin n) ℂ × KG ε => GintD T μ p.1 p.2)
      (Uset ε ×ˢ Set.univ) := by
  refine continuousOn_clm_apply.mpr fun H => ?_
  have hmaps : Set.MapsTo (fun p : Matrix (Fin n) (Fin n) ℂ × KG ε => toMK p.2⁻¹ * p.1 * toMK p.2)
      (Uset ε ×ˢ Set.univ) (OmegaSet n) := fun p hp => hp.1 p.2
  have hA : ContinuousOn (fun p : Matrix (Fin n) (Fin n) ℂ × KG ε =>
      fderiv ℂ (PhiP μ) (toMK p.2⁻¹ * p.1 * toMK p.2)) (Uset ε ×ˢ Set.univ) :=
    (continuousOn_fderiv_phiP μ).comp continuous_conj.continuousOn hmaps
  have hB : Continuous (fun p : Matrix (Fin n) (Fin n) ℂ × KG ε =>
      toMK p.2⁻¹ * Matrix.of H * toMK p.2) :=
    ((continuous_toMK_inv.comp continuous_snd).matrix_mul continuous_const).matrix_mul
      (continuous_toMK'.comp continuous_snd)
  refine ((hA.clm_apply hB.continuousOn).smul
    ((continuous_P T).comp continuous_snd).continuousOn).congr ?_
  intro p hp
  exact GintD_apply T μ p.2 (hp.1 p.2) H

lemma continuous_Gint (T : KType ε Λ) (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : x ∈ Uset ε) : Continuous (Gint T μ x) := by
  have h1 : Continuous fun k : KG ε => toMK k⁻¹ * x * toMK k :=
    (continuous_toMK_inv.matrix_mul continuous_const).matrix_mul continuous_toMK'
  exact ((continuousOn_phiP μ).comp_continuous h1 hx).smul (continuous_P T)

lemma continuous_GintD (T : KType ε Λ) (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : x ∈ Uset ε) : Continuous (GintD T μ x) := by
  refine continuous_clm_apply.mpr fun H => ?_
  have h1 : Continuous fun k : KG ε => toMK k⁻¹ * x * toMK k :=
    (continuous_toMK_inv.matrix_mul continuous_const).matrix_mul continuous_toMK'
  have hA := (continuousOn_fderiv_phiP μ).comp_continuous h1 hx
  have hB : Continuous fun k : KG ε => toMK k⁻¹ * Matrix.of H * toMK k :=
    (continuous_toMK_inv.matrix_mul continuous_const).matrix_mul continuous_toMK'
  have e : (fun k => GintD T μ x k H) = fun k => fderiv ℂ (PhiP μ) (toMK k⁻¹ * x * toMK k)
      (toMK k⁻¹ * Matrix.of H * toMK k) • (T.op k * projW T * T.op k⁻¹) :=
    funext fun k => GintD_apply T μ k (hx k) H
  rw [e]
  exact (hA.clm_apply hB).smul (continuous_P T)

lemma integrable_GintD [CompactSpace (KG ε)] (T : KType ε Λ) (μ : Fin n → ℤ)
    {x : Matrix (Fin n) (Fin n) ℂ} (hx : x ∈ Uset ε) : Integrable (GintD T μ x) (muK ε) := by
  have : IsFiniteMeasureOnCompacts (muK ε) := by unfold muK; infer_instance
  exact integrableOn_univ.mp
    ((continuous_GintD T μ hx).continuousOn.integrableOn_compact isCompact_univ)

lemma integrable_Gint [CompactSpace (KG ε)] (T : KType ε Λ) (μ : Fin n → ℤ)
    {x : Matrix (Fin n) (Fin n) ℂ} (hx : x ∈ Uset ε) : Integrable (Gint T μ x) (muK ε) := by
  have : IsFiniteMeasureOnCompacts (muK ε) := by unfold muK; infer_instance
  exact integrableOn_univ.mp
    ((continuous_Gint T μ hx).continuousOn.integrableOn_compact isCompact_univ)

lemma hasFDerivAt_intG [CompactSpace (KG ε)] (T : KType ε Λ) (μ : Fin n → ℤ)
    {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ Uset ε) :
    HasFDerivAt (fun x : 𝕄 => ∫ k, Gint T μ x k ∂(muK ε)) (∫ k, GintD T μ z k ∂(muK ε)) z := by
  have : IsFiniteMeasureOnCompacts (muK ε) := by unfold muK; infer_instance
  have : IsFiniteMeasure (muK ε) := inferInstance
  have hU : IsOpen (Uset ε : Set 𝕄) := isOpen_Uset
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU z hz
  have hδ : (0 : ℝ) < r / 2 := half_pos hr
  have hcl : Metric.closedBall (z : 𝕄) (r / 2) ⊆ (Uset ε : Set 𝕄) :=
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans hball
  have hK : IsCompact (Metric.closedBall (z : 𝕄) (r / 2) ×ˢ (Set.univ : Set (KG ε))) :=
    (isCompact_closedBall _ _).prod isCompact_univ
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((continuousOn_GintD T μ).mono (Set.prod_mono hcl le_rfl))
  have hin : ∀ x ∈ Metric.ball (z : 𝕄) (r / 2), x ∈ (Uset ε : Set 𝕄) :=
    fun x hx => hcl (Metric.ball_subset_closedBall hx)
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C)
    (F' := fun x k => GintD T μ x k)
    (Metric.ball_mem_nhds (z : 𝕄) hδ)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds (z : 𝕄) hδ)
      fun x hx => (continuous_Gint T μ (hin x hx)).aestronglyMeasurable)
    (integrable_Gint T μ hz) (continuous_GintD T μ hz).aestronglyMeasurable
    (Filter.Eventually.of_forall fun k x hx => hC (x, k) ⟨Metric.ball_subset_closedBall hx, trivial⟩)
    (integrable_const C)
    (Filter.Eventually.of_forall fun k x hx => hasFDerivAt_Gint T μ k (hin x hx k))

lemma hasFDerivAt_psM [CompactSpace (KG ε)] (T : KType ε Λ) (μ : Fin n → ℤ)
    {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ Uset ε) :
    HasFDerivAt (fun x : 𝕄 => psM T μ x)
      (((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
        ∫ k, GintD T μ z k ∂(muK ε)) z := by
  have h := (hasFDerivAt_intG T μ hz).const_smul
    ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ))
  exact h

end Ps1

theorem psM_holo {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ) :
    ∃ U : Set (Matrix (Fin n) (Fin n) ℂ), IsOpen U ∧ posSet n ⊆ U ∧
      (∀ z ∈ U, ∀ k : KG ε, toMK k⁻¹ * z * toMK k ∈ OmegaSet n) ∧
      DifferentiableOn ℂ (psM T μ) U ∧
      ∀ z ∈ U, ∀ H : Matrix (Fin n) (Fin n) ℂ, fderiv ℂ (psM T μ) z H =
        ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
          ∫ k, fderiv ℂ (PhiM μ) (toMK k⁻¹ * z * toMK k) (toMK k⁻¹ * H * toMK k) •
            (T.op k * projW T * T.op k⁻¹) ∂(muK ε) := by
  have := compactSpace_KG ε
  refine ⟨Ps1.Uset ε, Ps1.isOpen_Uset, Ps1.posSet_subset_Uset, fun z hz k => hz k,
    fun z hz => ?_, fun z hz H => ?_⟩
  · have h : DifferentiableAt ℂ (psM T μ) z := (Ps1.hasFDerivAt_psM T μ hz).differentiableAt
    exact h.differentiableWithinAt
  · rw [show fderiv ℂ (psM T μ) z H =
        fderiv ℂ (fun x : Fin n → Fin n → ℂ => psM T μ x) z (Matrix.of.symm H) from rfl,
      (Ps1.hasFDerivAt_psM T μ hz).fderiv, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.integral_apply (Ps1.integrable_GintD T μ hz)]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    exact Ps1.GintD_apply T μ k (hz k) (Matrix.of.symm H)

end ReciprocityTheory.ChartRestriction.DS.S7
