import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DerivG
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ByParts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DTauFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DerivGA

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}

namespace InfKA

lemma contDiffAt_zpow {f : Matrix (Fin n) (Fin n) ℂ → ℂ} {x : Matrix (Fin n) (Fin n) ℂ}
    (hf : ContDiffAt ℂ 1 f x) (hx : f x ≠ 0) (m : ℤ) : ContDiffAt ℂ 1 (fun y => f y ^ m) x := by
  cases m with
  | ofNat k =>
    have e : (fun y => f y ^ (Int.ofNat k)) = fun y => f y ^ k :=
      funext fun y => by rw [Int.ofNat_eq_coe, zpow_natCast]
    rw [e]
    exact hf.pow k
  | negSucc k =>
    have e : (fun y => f y ^ (Int.negSucc k)) = fun y => (f y ^ (k + 1))⁻¹ :=
      funext fun y => zpow_negSucc _ _
    rw [e]
    exact (hf.pow (k + 1)).inv (pow_ne_zero _ hx)

lemma contDiff_lead (i : ℕ) : ContDiff ℂ 1 (fun z : Matrix (Fin n) (Fin n) ℂ => lead i z) := by
  have he : ∀ a b : Fin n, ContDiff ℂ 1 (fun z : Matrix (Fin n) (Fin n) ℂ => z a b) := by
    intro a b
    first
    | exact contDiff_apply_apply ℂ ℂ a b
    | exact contDiff_apply_apply a b
    | exact ((ContinuousLinearMap.proj b).comp (ContinuousLinearMap.proj a)).contDiff
    | fun_prop
  unfold lead
  by_cases h : i ≤ n
  · simp only [dif_pos h, Matrix.det_apply, Matrix.submatrix_apply, Units.smul_def, zsmul_eq_mul]
    exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun j _ => he _ _)
  · simp only [dif_neg h]
    exact contDiff_const

lemma contDiffAt_phiM (μ : Fin n → ℤ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    ContDiffAt ℂ 1 (PhiM μ) z := by
  show ContDiffAt ℂ 1 (fun z => ∏ i : Fin n, lead ((i : ℕ) + 1) z ^ (-(μ i - muNext μ i))) z
  first
  | exact contDiffAt_prod fun i _ => InfKA.contDiffAt_zpow (contDiff_lead _).contDiffAt (hz i) _
  | exact contDiffAt_finset_prod fun i _ => InfKA.contDiffAt_zpow (contDiff_lead _).contDiffAt (hz i) _

lemma isOpen_omega' : IsOpen (OmegaSet n) := by
  have e : OmegaSet n = ⋂ i : Fin n, {z | lead ((i : ℕ) + 1) z ≠ 0} := by
    ext z
    simp [OmegaSet]
  rw [e]
  first
  | exact isOpen_iInter_of_finite fun i => isOpen_ne_fun (contDiff_lead _).continuous continuous_const
  | exact isOpen_iInter fun i => isOpen_ne_fun (contDiff_lead _).continuous continuous_const

lemma continuousOn_fderiv_phiM (μ : Fin n → ℤ) : ContinuousOn (fderiv ℂ (PhiM μ)) (OmegaSet n) := by
  exact ContDiffOn.continuousOn_fderiv_of_isOpen
    (fun z hz => (contDiffAt_phiM μ hz).contDiffWithinAt) isOpen_omega' le_rfl

lemma continuousOn_phiM (μ : Fin n → ℤ) : ContinuousOn (PhiM μ) (OmegaSet n) := by
  exact fun z hz => (contDiffAt_phiM μ hz).continuousAt.continuousWithinAt

lemma continuous_toMK' : Continuous fun k : KG ε => toMK k := by
  first
    | fun_prop
    | exact continuous_subtype_val.comp continuous_subtype_val
    | exact Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
    | exact (continuous_subtype_val.comp continuous_subtype_val).comp continuous_subtype_val
    | continuity

lemma continuous_toMK_inv : Continuous fun k : KG ε => toMK k⁻¹ := by
  exact continuous_toMK'.comp continuous_inv

lemma continuous_P (T : KType ε Λ) : Continuous fun k : KG ε => T.op k * projW T * T.op k⁻¹ := by
  have hop : Continuous fun k : KG ε => T.op k := continuous_subtype_val.comp T.cont
  exact (hop.mul continuous_const).mul (hop.comp continuous_inv)

private lemma toMK_conjTranspose_mul_self (k : KG ε) : (toMK k)ᴴ * toMK k = 1 := by
  have h : toM (k : UJ ε) ∈ Kset ε := k.2
  obtain ⟨hU, -⟩ := h
  first
  | exact Unitary.star_mul_self_of_mem hU
  | exact (Matrix.mem_unitaryGroup_iff').1 hU
  | exact hU.1

lemma toMK_inv_eq (k : KG ε) : toMK k⁻¹ = (toMK k)ᴴ := by
  have hu : star (toMK k) * toMK k = 1 := toMK_conjTranspose_mul_self k
  have hv : toMK k * toMK k⁻¹ = 1 := by
    first
    | exact Units.mul_inv _
    | (simp only [toMK, toM]; simp)
    | (unfold toMK toM; simp)
    | (unfold toMK; simp)
  calc toMK k⁻¹ = (star (toMK k) * toMK k) * toMK k⁻¹ := by rw [hu, Matrix.one_mul]
    _ = star (toMK k) * (toMK k * toMK k⁻¹) := by rw [Matrix.mul_assoc]
    _ = (toMK k)ᴴ := by rw [hv, Matrix.mul_one]; rfl

lemma conj_mem_omega {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) (k : KG ε) :
    toMK k⁻¹ * x * toMK k ∈ OmegaSet n := by
  rw [toMK_inv_eq]
  have hinj : Function.Injective (toMK k).mulVec := fun v w h => by
    have h2 := congrArg (toMK k)ᴴ.mulVec h
    simpa [Matrix.mulVec_mulVec, toMK_conjTranspose_mul_self] using h2
  have hP : ((toMK k)ᴴ * x * toMK k).PosDef := hx.conjTranspose_mul_mul_same hinj
  show ∀ i : Fin n, lead ((i : ℕ) + 1) ((toMK k)ᴴ * x * toMK k) ≠ 0
  intro i
  unfold lead
  rw [dif_pos (show (i : ℕ) + 1 ≤ n from i.isLt)]
  first
  | exact (hP.submatrix (Fin.castLE_injective _)).det_pos.ne'
  | exact (hP.submatrix (Fin.castLEEmb (show (i : ℕ) + 1 ≤ n from i.isLt))).det_pos.ne'
  | exact (hP.submatrix _ (Fin.castLE_injective _)).det_pos.ne'

def entryCLM (a b : Fin n) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M a b
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

@[simp] lemma entryCLM_apply (a b : Fin n) (M : Matrix (Fin n) (Fin n) ℂ) : entryCLM a b M = M a b := rfl

def DkL (T : KType ε Λ) (μ : Fin n → ℤ) (x : Matrix (Fin n) (Fin n) ℂ) (k : KG ε) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (T.V →L[ℂ] T.V) where
  toFun Y := fderiv ℂ (PhiM μ) (toMK k⁻¹ * x * toMK k)
        (toMK k⁻¹ * x * toMK k * Y - Y * (toMK k⁻¹ * x * toMK k)) • (T.op k * projW T * T.op k⁻¹) +
      PhiM μ (toMK k⁻¹ * x * toMK k) • (T.op k * (T.dτ Y * projW T - projW T * T.dτ Y) * T.op k⁻¹)
  map_add' Y Y' := by
    simp only [Matrix.mul_add, Matrix.add_mul, map_add, map_sub, add_mul, mul_add, sub_mul, mul_sub,
      add_smul, sub_smul, smul_add, smul_sub]
    abel
  map_smul' c Y := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, map_smul, map_sub, smul_mul_assoc, mul_smul_comm,
      mul_sub, sub_mul, smul_sub, smul_eq_mul, RingHom.id_apply, smul_add]
    module

lemma DkL_apply (T : KType ε Λ) (μ : Fin n → ℤ) (x : Matrix (Fin n) (Fin n) ℂ) (k : KG ε)
    (Y : Matrix (Fin n) (Fin n) ℂ) : DkL T μ x k Y =
      fderiv ℂ (PhiM μ) (toMK k⁻¹ * x * toMK k)
        (toMK k⁻¹ * x * toMK k * Y - Y * (toMK k⁻¹ * x * toMK k)) • (T.op k * projW T * T.op k⁻¹) +
      PhiM μ (toMK k⁻¹ * x * toMK k) • (T.op k * (T.dτ Y * projW T - projW T * T.dτ Y) * T.op k⁻¹) :=
  rfl

def Ek (T : KType ε Λ) (μ : Fin n → ℤ) (x : Matrix (Fin n) (Fin n) ℂ)
    (φ : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ) (A M : Matrix (Fin n) (Fin n) ℂ) (k : KG ε) : T.V →L[ℂ] T.V :=
  φ (toMK k⁻¹ * A * toMK k) • DkL T μ x k M +
    φ (toMK k⁻¹ * A * toMK k * M - M * (toMK k⁻¹ * A * toMK k)) • Gint T μ x k

lemma continuous_B (A : Matrix (Fin n) (Fin n) ℂ) : Continuous fun k : KG ε => toMK k⁻¹ * A * toMK k := by
  first
    | exact (continuous_toMK_inv.matrix_mul continuous_const).matrix_mul continuous_toMK'
    | exact ((continuous_toMK_inv (ε := ε)).mul continuous_const).mul continuous_toMK'

lemma continuous_Gint (T : KType ε Λ) (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : x.PosDef) : Continuous (Gint T μ x) := by
  have hphi : Continuous fun k : KG ε => PhiM μ (toMK k⁻¹ * x * toMK k) :=
    (continuousOn_phiM μ).comp_continuous (continuous_B x) (fun k => conj_mem_omega hx k)
  show Continuous fun k => PhiM μ (toMK k⁻¹ * x * toMK k) • (T.op k * projW T * T.op k⁻¹)
  exact hphi.smul (continuous_P T)

lemma continuous_DkL (T : KType ε Λ) (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef)
    (Y : Matrix (Fin n) (Fin n) ℂ) : Continuous fun k => DkL T μ x k Y := by
  have hB : Continuous fun k : KG ε => toMK k⁻¹ * x * toMK k := continuous_B x
  have hmem : ∀ k : KG ε, toMK k⁻¹ * x * toMK k ∈ OmegaSet n := fun k => conj_mem_omega hx k
  have hop : Continuous fun k : KG ε => T.op k := continuous_subtype_val.comp T.cont
  have hphi : Continuous fun k : KG ε => PhiM μ (toMK k⁻¹ * x * toMK k) :=
    (continuousOn_phiM μ).comp_continuous hB hmem
  have hd : Continuous fun k : KG ε => fderiv ℂ (PhiM μ) (toMK k⁻¹ * x * toMK k) :=
    (continuousOn_fderiv_phiM μ).comp_continuous hB hmem
  have harg : Continuous fun k : KG ε => toMK k⁻¹ * x * toMK k * Y - Y * (toMK k⁻¹ * x * toMK k) :=
    (hB.matrix_mul continuous_const).sub (continuous_const.matrix_mul hB)
  simp only [DkL_apply]
  exact ((hd.clm_apply harg).smul (continuous_P T)).add
    (hphi.smul ((hop.mul continuous_const).mul (hop.comp continuous_inv)))

lemma continuous_Ek (T : KType ε Λ) (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef)
    (φ : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ) (A M : Matrix (Fin n) (Fin n) ℂ) : Continuous (Ek T μ x φ A M) := by
  have hBA : Continuous fun k : KG ε => toMK k⁻¹ * A * toMK k := continuous_B A
  show Continuous fun k => φ (toMK k⁻¹ * A * toMK k) • DkL T μ x k M +
    φ (toMK k⁻¹ * A * toMK k * M - M * (toMK k⁻¹ * A * toMK k)) • Gint T μ x k
  exact ((φ.continuous.comp hBA).smul (continuous_DkL T μ hx M)).add
    ((φ.continuous.comp ((hBA.matrix_mul continuous_const).sub (continuous_const.matrix_mul hBA))).smul
      (continuous_Gint T μ hx))

lemma integrable_of_cont [CompactSpace (KG ε)] {E : Type*} [NormedAddCommGroup E] {f : KG ε → E}
    (hf : Continuous f) : Integrable f (muK ε) := by
  first
    | exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
    | (unfold muK; exact integrableOn_univ.1 (hf.continuousOn.integrableOn_compact isCompact_univ))
    | (unfold muK; exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f))
    | exact integrableOn_univ.1 (hf.continuousOn.integrableOn_compact isCompact_univ)

lemma integral_Ek_inK [CompactSpace (KG ε)] (T : KType ε Λ) (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : x.PosDef) (φ : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) : ∫ k, Ek T μ x φ A Z k ∂(muK ε) = 0 := by
  obtain ⟨γ, -, hγ, hmul⟩ := exists_oneParam ε hZ
  have hγ0 : γ 0 = 1 := gamma_zero hmul
  have hmk : ∀ a b : KG ε, toMK (a * b) = toMK a * toMK b := fun _ _ => rfl
  have hinv_t : ∀ t : ℝ, toMK (γ t)⁻¹ = NormedSpace.exp (-((t : ℂ) • Z)) := by
    intro t
    have h1 : toMK (γ t)⁻¹ * toMK (γ t) = 1 := by rw [← hmk, inv_mul_cancel]; rfl
    calc toMK (γ t)⁻¹ = toMK (γ t)⁻¹ * (toMK (γ t) * NormedSpace.exp (-((t : ℂ) • Z))) := by
          rw [hγ, kfa_exp_mul_neg, Matrix.mul_one]
      _ = NormedSpace.exp (-((t : ℂ) • Z)) := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  refine kByParts ε (fun k => φ (toMK k⁻¹ * A * toMK k) • Gint T μ x k) (Ek T μ x φ A Z) hZ γ hγ
    ((φ.continuous.comp (continuous_B A)).smul (continuous_Gint T μ hx)) (continuous_Ek T μ hx φ A Z) ?_
  intro k
  set Bk := toMK k⁻¹ * A * toMK k with hBk
  have hφ : HasDerivAt
      (fun t : ℝ => φ (NormedSpace.exp (-((t : ℂ) • Z)) * Bk * NormedSpace.exp ((t : ℂ) • Z)))
      (φ (Bk * Z - Z * Bk)) 0 :=
    (φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (dga_path Z Bk)
  have h := hφ.smul (hasDerivAt_Gint T μ hx k hZ γ hγ)
  convert h using 1
  · funext t
    congr 2
    rw [_root_.mul_inv_rev, hmk, hmk, hinv_t, hγ, hBk]
    simp only [Matrix.mul_assoc]
  · simp only [Ek, DkL_apply, hγ0, mul_one, Complex.ofReal_zero, zero_smul, neg_zero, NormedSpace.exp_zero,
      Matrix.one_mul, Matrix.mul_one, hBk]

lemma Ek_decomp (T : KType ε Λ) (μ : Fin n → ℤ) (x : Matrix (Fin n) (Fin n) ℂ)
    (φ : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ) (A P Q : Matrix (Fin n) (Fin n) ℂ) (k : KG ε) :
    Ek T μ x φ A (P + Complex.I • Q) k = Ek T μ x φ A P k + Complex.I • Ek T μ x φ A Q k := by
  have h1 : toMK k⁻¹ * A * toMK k * (P + Complex.I • Q) - (P + Complex.I • Q) * (toMK k⁻¹ * A * toMK k) =
      (toMK k⁻¹ * A * toMK k * P - P * (toMK k⁻¹ * A * toMK k)) +
        Complex.I • (toMK k⁻¹ * A * toMK k * Q - Q * (toMK k⁻¹ * A * toMK k)) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
    abel
  simp only [Ek, h1, map_add, map_smul, smul_eq_mul]
  first
  | module
  | (simp only [smul_add, add_smul, smul_smul, mul_comm]; abel)

lemma integral_Ek_block [CompactSpace (KG ε)] (T : KType ε Λ) (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : x.PosDef) (φ : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    {M : Matrix (Fin n) (Fin n) ℂ} (hM : IsBlock ε M) : ∫ k, Ek T μ x φ A M k ∂(muK ε) = 0 := by
  have key : ∀ X : Matrix (Fin n) (Fin n) ℂ, IsBlock ε X → Xᴴ = -X → inK ε X := by
    intro X hX hs
    have hc : X * Jm ε = Jm ε * X := by
      ext a b
      simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
      by_cases h : ε a = ε b
      · rw [h]; ring
      · rw [hX a b h]; ring
    show inG ε X ∧ X * Jm ε = Jm ε * X
    refine ⟨?_, hc⟩
    show Xᴴ * Jm ε + Jm ε * X = 0
    rw [hs, Matrix.neg_mul, hc]
    abel
  have hMh : ∀ a b, ε a ≠ ε b → Mᴴ a b = 0 := fun a b h => by
    simp [Matrix.conjTranspose_apply, hM b a (Ne.symm h)]
  obtain ⟨P, Q, hP, hQ, rfl⟩ : ∃ P Q : Matrix (Fin n) (Fin n) ℂ,
      inK ε P ∧ inK ε Q ∧ M = P + Complex.I • Q := by
    refine ⟨(1 / 2 : ℂ) • (M - Mᴴ), (-Complex.I / 2) • (M + Mᴴ), key _ ?_ ?_, key _ ?_ ?_, ?_⟩
    · intro a b h
      first
      | simp only [Matrix.smul_apply, Matrix.sub_apply, hM a b h, hMh a b h, sub_zero, smul_zero]
      | simp [hM a b h, hMh a b h]
    · ext a b
      first
      | (simp [Matrix.conjTranspose_apply]; ring)
      | (simp [Matrix.conjTranspose_apply, Complex.star_def]; ring)
      | simp [Matrix.conjTranspose_apply]
      | simp [Matrix.conjTranspose_apply, Complex.star_def]
    · intro a b h
      first
      | simp only [Matrix.smul_apply, Matrix.add_apply, hM a b h, hMh a b h, add_zero, smul_zero]
      | simp [hM a b h, hMh a b h]
    · ext a b
      first
      | (simp [Matrix.conjTranspose_apply, Complex.star_def]; ring)
      | (simp [Matrix.conjTranspose_apply]; ring)
      | simp [Matrix.conjTranspose_apply, Complex.star_def]
      | simp [Matrix.conjTranspose_apply]
    · ext a b
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
      linear_combination (M a b + Mᴴ a b) / 2 * Complex.I_sq
  have hIP : Integrable (Ek T μ x φ A P) (muK ε) := integrable_of_cont (continuous_Ek T μ hx φ A P)
  have hIQ : Integrable (fun k => Complex.I • Ek T μ x φ A Q k) (muK ε) :=
    (integrable_of_cont (continuous_Ek T μ hx φ A Q)).smul Complex.I
  simp_rw [Ek_decomp]
  rw [integral_add hIP hIQ, integral_smul, integral_Ek_inK T μ hx φ A hP, integral_Ek_inK T μ hx φ A hQ,
    smul_zero, add_zero]

end InfKA

end ReciprocityTheory.ChartRestriction.DS.S7
