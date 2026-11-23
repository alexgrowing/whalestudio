import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvSubOneMem
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRiemannianHaarOnSubgroupMapMulRightUnitary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagLeviMaxCompactClosedSubgroups
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.IwConst

variable {n d : ℕ}

def nrm (X : Matrix (Fin n) (Fin n) ℂ) : ℝ := Real.sqrt (Formalism.REAL.hs X)

def len (x : Fin d → ℝ) : ℝ := Real.sqrt (∑ i, x i ^ 2)

def crd (E : Fin d → Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) : Fin d → ℝ :=
  fun i => ((X * (E i)ᴴ).trace).re

def cmb (E : Fin d → Matrix (Fin n) (Fin n) ℂ) (x : Fin d → ℝ) : Matrix (Fin n) (Fin n) ℂ := ∑ i, x i • E i

def IsON (E : Fin d → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0

def IsCut (ε : Fin n → Bool) (S : Set (Formalism.REAL.UJ ε)) (E : Fin d → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) ∧ IsON E ∧
    (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) ∧ S = {g | uMat g - 1 ∈ A}

def ballVol (d : ℕ) : ENNReal := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)

def Vag {α V : Type} [MeasurableSpace α] [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    (μ : Measure α) (c : α → V) (lam : Measure V) (d : ℕ) : Prop :=
  ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ →
    Filter.Tendsto (fun r : ℝ => (r ^ d)⁻¹ * ∫ g, φ (r⁻¹ • c g) ∂μ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ t, φ t ∂lam))

def gau {a b c e : ℕ} (EN : Fin a → Matrix (Fin n) (Fin n) ℂ) (EM : Fin b → Matrix (Fin n) (Fin n) ℂ)
    (EK : Fin c → Matrix (Fin n) (Fin n) ℂ) (EL : Fin e → Matrix (Fin n) (Fin n) ℂ)
    (v : (Fin a → ℝ) × (Fin b → ℝ) × (Fin c → ℝ)) : ℝ :=
  max (nrm (cmb EN v.1 + cmb EM v.2.1 + cmb EK v.2.2)) (len (crd EL (cmb EK v.2.2)))

def LieRel {a b c e : ℕ} (EN : Fin a → Matrix (Fin n) (Fin n) ℂ) (EM : Fin b → Matrix (Fin n) (Fin n) ℂ)
    (EK : Fin c → Matrix (Fin n) (Fin n) ℂ) (EL : Fin e → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ i k, (EN i * (EM k)ᴴ).trace = 0) ∧ (∀ i k, (EN i * EM k).trace = 0) ∧ (∀ i k, (EN i * EN k).trace = 0) ∧
    (∀ i, EL i ∈ Submodule.span ℝ (Set.range EM)) ∧ (∀ i, EL i ∈ Submodule.span ℝ (Set.range EK)) ∧
    (∀ i, (EL i)ᴴ = -EL i) ∧ ∀ i, EN i - (EN i)ᴴ ∈ Submodule.span ℝ (Set.range EK)

def slab (ε : Fin n → Bool) (E : Fin d → Matrix (Fin n) (Fin n) ℂ) (ρ r : ℝ) : Set (Formalism.REAL.UJ ε) :=
  {k | nrm (uMat k - 1) < ρ ∧ len (crd E (uMat k - 1)) ≤ r}

def hsBall (ε : Fin n → Bool) (r : ℝ) : Set (Formalism.REAL.UJ ε) := {g | nrm (uMat g - 1) ≤ r}

def dlt {ε : Fin n → Bool} {a : ℕ} (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ))
    (m : Formalism.REAL.UJ ε) : ENNReal := ENNReal.ofReal (layerProd n 1 j (locSize j W (uMat m)) id)

def perp (ε : Fin n → Bool) (V : Submodule ℂ (Fin n → ℂ)) : Submodule ℂ (Fin n → ℂ) where
  carrier := {y | ∀ x ∈ V, star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro y z hy hz x hx
    rw [Matrix.mulVec_add, dotProduct_add, hy x hx, hz x hx, add_zero]
  smul_mem' := by
    intro c y hy x hx
    rw [Matrix.mulVec_smul, dotProduct_smul, hy x hx, smul_zero]

def into (V V' : Submodule ℂ (Fin n → ℂ)) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | ∀ y ∈ V, X *ᵥ y ∈ V'}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY y hy
    rw [Matrix.add_mulVec]
    exact V'.add_mem (hX y hy) (hY y hy)
  smul_mem' := by
    intro c X hX y hy
    rw [Matrix.smul_mulVec]
    exact V'.smul_of_tower_mem c (hX y hy)

theorem mem_perp {ε : Fin n → Bool} {V : Submodule ℂ (Fin n → ℂ)} {y : Fin n → ℂ} :
    y ∈ perp ε V ↔ ∀ x ∈ V, star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0 := Iff.rfl

theorem mem_into {V V' : Submodule ℂ (Fin n → ℂ)} {X : Matrix (Fin n) (Fin n) ℂ} :
    X ∈ into V V' ↔ ∀ y ∈ V, X *ᵥ y ∈ V' := Iff.rfl

def lowers (ε : Fin n → Bool) {a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) :
    Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) :=
  (⨅ i : Fin a, into (W i.succ) (W i.castSucc)) ⊓ into (perp ε (W (Fin.last a))) (W (Fin.last a)) ⊓
    ⨅ i : Fin a, into (perp ε (W i.castSucc)) (perp ε (W i.succ))

def keeps (ε : Fin n → Bool) {a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) :
    Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) :=
  (⨅ i, into (W i) (W i)) ⊓ ⨅ i, into (perp ε (W i)) (perp ε (W i))

section Norm

open scoped Matrix.Norms.Frobenius

theorem nrm_eq (X : Matrix (Fin n) (Fin n) ℂ) : nrm X = ‖X‖ := by
  simp only [nrm, Formalism.REAL.hs, Matrix.frobenius_norm_def, Real.sqrt_eq_rpow, Real.rpow_two]

theorem nrm_add_le (X Y : Matrix (Fin n) (Fin n) ℂ) : nrm (X + Y) ≤ nrm X + nrm Y := by
  rw [nrm_eq, nrm_eq, nrm_eq]
  exact norm_add_le X Y

theorem nrm_sub_le (X Y : Matrix (Fin n) (Fin n) ℂ) : nrm (X - Y) ≤ nrm X + nrm Y := by
  rw [nrm_eq, nrm_eq, nrm_eq]
  exact norm_sub_le X Y

theorem nrm_mul_le (X Y : Matrix (Fin n) (Fin n) ℂ) : nrm (X * Y) ≤ nrm X * nrm Y := by
  rw [nrm_eq, nrm_eq, nrm_eq]
  exact Matrix.frobenius_norm_mul X Y

theorem nrm_neg (X : Matrix (Fin n) (Fin n) ℂ) : nrm (-X) = nrm X := by rw [nrm_eq, nrm_eq, norm_neg]

theorem nrm_smul (c : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) : nrm (c • X) = |c| * nrm X := by rw [nrm_eq, nrm_eq, norm_smul, Real.norm_eq_abs]

theorem nrm_conjTranspose (X : Matrix (Fin n) (Fin n) ℂ) : nrm Xᴴ = nrm X := by rw [nrm_eq, nrm_eq, Matrix.frobenius_norm_conjTranspose]

theorem nrm_eq_zero {X : Matrix (Fin n) (Fin n) ℂ} : nrm X = 0 ↔ X = 0 := by rw [nrm_eq, norm_eq_zero]

end Norm

theorem nrm_nonneg (X : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ nrm X := Real.sqrt_nonneg _

theorem hs_nonneg (X : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ Formalism.REAL.hs X := by
  unfold Formalism.REAL.hs
  positivity

theorem nrm_sq (X : Matrix (Fin n) (Fin n) ℂ) : nrm X ^ 2 = Formalism.REAL.hs X := Real.sq_sqrt (hs_nonneg X)

theorem continuous_nrm : Continuous (nrm : Matrix (Fin n) (Fin n) ℂ → ℝ) := by
  show Continuous fun X : Matrix (Fin n) (Fin n) ℂ => Real.sqrt (∑ i, ∑ j, ‖X i j‖ ^ 2)
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => ((continuous_apply j).comp (continuous_apply i)).norm.pow 2)

theorem len_nonneg (x : Fin d → ℝ) : 0 ≤ len x := Real.sqrt_nonneg _

theorem len_sq (x : Fin d → ℝ) : len x ^ 2 = ∑ i, x i ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (x i))

theorem len_eq (x : Fin d → ℝ) : len x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ := by
  rw [EuclideanSpace.norm_eq, len]
  simp [Real.norm_eq_abs, sq_abs]

theorem len_add_le (x y : Fin d → ℝ) : len (x + y) ≤ len x + len y := by
  rw [len_eq, len_eq, len_eq, WithLp.toLp_add]
  exact norm_add_le _ _

theorem len_neg (x : Fin d → ℝ) : len (-x) = len x := by rw [len_eq, len_eq, WithLp.toLp_neg, norm_neg]

theorem len_smul (c : ℝ) (x : Fin d → ℝ) : len (c • x) = |c| * len x := by rw [len_eq, len_eq, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

theorem continuous_len : Continuous (len : (Fin d → ℝ) → ℝ) := by
  unfold len
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => (continuous_apply i).pow 2)

theorem crd_add (E : Fin d → Matrix (Fin n) (Fin n) ℂ) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    crd E (X + Y) = crd E X + crd E Y := by
  funext i
  simp [crd, Matrix.add_mul, Matrix.trace_add]

theorem crd_sub (E : Fin d → Matrix (Fin n) (Fin n) ℂ) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    crd E (X - Y) = crd E X - crd E Y := by
  funext i
  simp [crd, Matrix.sub_mul, Matrix.trace_sub]

theorem crd_smul (E : Fin d → Matrix (Fin n) (Fin n) ℂ) (c : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) :
    crd E (c • X) = c • crd E X := by
  funext i
  simp [crd, Matrix.trace_smul]

theorem continuous_crd (E : Fin d → Matrix (Fin n) (Fin n) ℂ) : Continuous (crd E) := by
  unfold crd
  exact continuous_pi fun i =>
    Complex.continuous_re.comp ((continuous_id.matrix_mul continuous_const).matrix_trace)

theorem cmb_add (E : Fin d → Matrix (Fin n) (Fin n) ℂ) (x y : Fin d → ℝ) : cmb E (x + y) = cmb E x + cmb E y := by simp [cmb, add_smul, Finset.sum_add_distrib]

theorem cmb_smul (E : Fin d → Matrix (Fin n) (Fin n) ℂ) (c : ℝ) (x : Fin d → ℝ) : cmb E (c • x) = c • cmb E x := by simp [cmb, Finset.smul_sum, mul_smul]

theorem continuous_cmb (E : Fin d → Matrix (Fin n) (Fin n) ℂ) : Continuous (cmb E) := by
  unfold cmb
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const

private theorem re_trace_cmb_mul_eq_sum (E : Fin d → Matrix (Fin n) (Fin n) ℂ) (x : Fin d → ℝ)
    (Y : Matrix (Fin n) (Fin n) ℂ) : ((cmb E x * Y).trace).re = ∑ k, x k * ((E k * Y).trace).re := by
  simp [cmb, Finset.sum_mul, Matrix.trace_sum, Matrix.trace_smul]

theorem crd_cmb {E : Fin d → Matrix (Fin n) (Fin n) ℂ} (h : IsON E) (x : Fin d → ℝ) : crd E (cmb E x) = x := by
  funext i
  show ((cmb E x * (E i)ᴴ).trace).re = x i
  rw [re_trace_cmb_mul_eq_sum]
  have hk : ∀ k, x k * ((E k * (E i)ᴴ).trace).re = if k = i then x k else 0 := fun k => by
    rw [h k i]
    split_ifs <;> simp
  simp [hk]

theorem cmb_crd {E : Fin d → Matrix (Fin n) (Fin n) ℂ} (h : IsON E) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ Submodule.span ℝ (Set.range E)) : cmb E (crd E X) = X := by
  obtain ⟨y, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hX
  have hy : cmb E y = ∑ i, y i • E i := rfl
  rw [← hy, crd_cmb h]

theorem re_trace_mul_cmb (E : Fin d → Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (x : Fin d → ℝ) :
    ((X * (cmb E x)ᴴ).trace).re = ∑ i, x i * crd E X i := by
  simp [cmb, crd, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.mul_sum,
    Matrix.trace_sum, Matrix.trace_smul]

theorem re_trace_symm (X Y : Matrix (Fin n) (Fin n) ℂ) : ((X * Yᴴ).trace).re = ((Y * Xᴴ).trace).re := by
  rw [show Y * Xᴴ = (X * Yᴴ)ᴴ by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose], Matrix.trace_conjTranspose]
  simp

theorem hs_add (X Y : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.hs (X + Y) = Formalism.REAL.hs X + Formalism.REAL.hs Y + 2 * ((X * Yᴴ).trace).re := by
  rw [GlobalTheory.GaugeRightInv.hs_eq_re_trace, GlobalTheory.GaugeRightInv.hs_eq_re_trace X,
    GlobalTheory.GaugeRightInv.hs_eq_re_trace Y]
  simp only [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  rw [re_trace_symm Y X]
  ring

theorem hs_cmb {E : Fin d → Matrix (Fin n) (Fin n) ℂ} (h : IsON E) (x : Fin d → ℝ) :
    Formalism.REAL.hs (cmb E x) = ∑ i, x i ^ 2 := by
  rw [GlobalTheory.GaugeRightInv.hs_eq_re_trace, re_trace_mul_cmb, crd_cmb h]
  simp [sq]

theorem nrm_cmb {E : Fin d → Matrix (Fin n) (Fin n) ℂ} (h : IsON E) (x : Fin d → ℝ) : nrm (cmb E x) = len x := by rw [nrm, hs_cmb h, len]

theorem hs_sub_cmb {E : Fin d → Matrix (Fin n) (Fin n) ℂ} (h : IsON E) (X : Matrix (Fin n) (Fin n) ℂ)
    (x : Fin d → ℝ) : Formalism.REAL.hs (X - cmb E x) =
      Formalism.REAL.hs (X - cmb E (crd E X)) + ∑ i, (crd E X i - x i) ^ 2 := by
  have hsplit : X - cmb E x = (X - cmb E (crd E X)) + cmb E (crd E X - x) := by
    simp only [cmb, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
    abel
  have hzero : crd E (X - cmb E (crd E X)) = 0 := by rw [crd_sub, crd_cmb h, sub_self]
  rw [hsplit, hs_add, hs_cmb h, re_trace_mul_cmb, hzero]
  simp [Pi.sub_apply]

theorem len_crd_le {E : Fin d → Matrix (Fin n) (Fin n) ℂ} (h : IsON E) (X : Matrix (Fin n) (Fin n) ℂ) :
    len (crd E X) ≤ nrm X := by
  have h0 := hs_sub_cmb h X 0
  have hc : cmb E 0 = 0 := by simp [cmb]
  rw [hc, sub_zero] at h0
  simp only [Pi.zero_apply, sub_zero] at h0
  rw [len, nrm]
  apply Real.sqrt_le_sqrt
  rw [h0]
  linarith [hs_nonneg (X - cmb E (crd E X))]

theorem nrm_sub_proj_le {E : Fin d → Matrix (Fin n) (Fin n) ℂ} (h : IsON E) (X : Matrix (Fin n) (Fin n) ℂ)
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y ∈ Submodule.span ℝ (Set.range E)) :
    nrm (X - cmb E (crd E X)) ≤ nrm (X - Y) := by
  have hY' := cmb_crd h hY
  rw [← hY', nrm, nrm]
  apply Real.sqrt_le_sqrt
  rw [hs_sub_cmb h X (crd E Y)]
  have hnn : 0 ≤ ∑ i, (crd E X i - crd E Y i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith

theorem continuous_gau {a b c e : ℕ} (EN : Fin a → Matrix (Fin n) (Fin n) ℂ) (EM : Fin b → Matrix (Fin n) (Fin n) ℂ)
    (EK : Fin c → Matrix (Fin n) (Fin n) ℂ) (EL : Fin e → Matrix (Fin n) (Fin n) ℂ) :
    Continuous (gau EN EM EK EL) := by
  unfold gau
  have h1 : Continuous fun v : (Fin a → ℝ) × (Fin b → ℝ) × (Fin c → ℝ) =>
      cmb EN v.1 + cmb EM v.2.1 + cmb EK v.2.2 :=
    (((continuous_cmb EN).comp continuous_fst).add
      ((continuous_cmb EM).comp (continuous_fst.comp continuous_snd))).add
      ((continuous_cmb EK).comp (continuous_snd.comp continuous_snd))
  exact (continuous_nrm.comp h1).max
    (continuous_len.comp ((continuous_crd EL).comp
      ((continuous_cmb EK).comp (continuous_snd.comp continuous_snd))))

theorem gau_smul {a b c e : ℕ} (EN : Fin a → Matrix (Fin n) (Fin n) ℂ) (EM : Fin b → Matrix (Fin n) (Fin n) ℂ)
    (EK : Fin c → Matrix (Fin n) (Fin n) ℂ) (EL : Fin e → Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (hs : 0 ≤ s)
    (v : (Fin a → ℝ) × (Fin b → ℝ) × (Fin c → ℝ)) : gau EN EM EK EL (s • v) = s * gau EN EM EK EL v := by
  obtain ⟨v1, v2, v3⟩ := v
  simp only [gau, Prod.smul_mk, cmb_smul, ← smul_add, nrm_smul, crd_smul, len_smul, abs_of_nonneg hs]
  rw [mul_max_of_nonneg _ _ hs]

theorem gau_nonneg {a b c e : ℕ} (EN : Fin a → Matrix (Fin n) (Fin n) ℂ) (EM : Fin b → Matrix (Fin n) (Fin n) ℂ)
    (EK : Fin c → Matrix (Fin n) (Fin n) ℂ) (EL : Fin e → Matrix (Fin n) (Fin n) ℂ)
    (v : (Fin a → ℝ) × (Fin b → ℝ) × (Fin c → ℝ)) : 0 ≤ gau EN EM EK EL v := le_max_of_le_left (nrm_nonneg _)

theorem continuous_nrm_uMat (ε : Fin n → Bool) : Continuous fun g : Formalism.REAL.UJ ε => nrm (uMat g - 1) := continuous_nrm.comp (GlobalTheory.FlagLeviGroup.continuous_uMat.sub continuous_const)

theorem continuous_crd_uMat (ε : Fin n → Bool) (E : Fin d → Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun g : Formalism.REAL.UJ ε => crd E (uMat g - 1) := (continuous_crd E).comp (GlobalTheory.FlagLeviGroup.continuous_uMat.sub continuous_const)

theorem measurableSet_hsBall (ε : Fin n → Bool) (r : ℝ) : MeasurableSet (hsBall ε r) := (isClosed_le (continuous_nrm_uMat ε) continuous_const).measurableSet

theorem measurableSet_slab (ε : Fin n → Bool) (E : Fin d → Matrix (Fin n) (Fin n) ℂ) (ρ r : ℝ) :
    MeasurableSet (slab ε E ρ r) := (isOpen_lt (continuous_nrm_uMat ε) continuous_const).measurableSet.inter
    (isClosed_le (continuous_len.comp (continuous_crd_uMat ε E)) continuous_const).measurableSet

theorem isCompact_hsBall (ε : Fin n → Bool) (r : ℝ) : IsCompact (hsBall ε r) := by
  obtain ⟨hemb, -⟩ := Formalism.REAL.uJEmb n ε
  have hC : IsCompact ({g : Matrix (Fin n) (Fin n) ℂ | Formalism.REAL.inUJ ε g ∧
      Formalism.REAL.hs g ≤ (r + nrm (1 : Matrix (Fin n) (Fin n) ℂ)) ^ 2} ∩ {g | nrm (g - 1) ≤ r}) :=
    ((Formalism.REAL.hSBall n ε).1 _).inter_right
      (isClosed_le (continuous_nrm.comp (continuous_id.sub continuous_const)) continuous_const)
  convert hemb.isCompact_preimage hC using 1
  ext g
  simp only [hsBall, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_inter_iff]
  constructor
  · intro hg
    refine ⟨⟨g.2, ?_⟩, hg⟩
    rw [← nrm_sq]
    have h1 : nrm (uMat g) ≤ r + nrm (1 : Matrix (Fin n) (Fin n) ℂ) := by
      have h2 := nrm_add_le (uMat g - 1) 1
      rw [sub_add_cancel] at h2
      linarith
    exact pow_le_pow_left₀ (nrm_nonneg _) h1 2
  · intro hg
    exact hg.2

theorem isCompact_maxK (ε : Fin n → Bool) : IsCompact (maxK ε) := by
  have hsub : maxK ε ⊆ hsBall ε (2 * nrm (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    intro g hg
    have hg' : (uMat g)ᴴ * uMat g = 1 := hg
    have hg'' : uMat g * (uMat g)ᴴ = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp hg'
    have hn : nrm (uMat g) = nrm (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [nrm, nrm, GlobalTheory.GaugeRightInv.hs_eq_re_trace,
        GlobalTheory.GaugeRightInv.hs_eq_re_trace (1 : Matrix (Fin n) (Fin n) ℂ), hg'',
        Matrix.conjTranspose_one, Matrix.mul_one]
    show nrm (uMat g - 1) ≤ 2 * nrm 1
    have h3 := nrm_sub_le (uMat g) 1
    linarith
  exact (isCompact_hsBall ε _).of_isClosed_subset GlobalTheory.FlagLeviGroup.isClosed_maxK hsub

theorem IsCut.isON {ε : Fin n → Bool} {S : Set (Formalism.REAL.UJ ε)} {E : Fin d → Matrix (Fin n) (Fin n) ℂ}
    (h : IsCut ε S E) : IsON E := by
  obtain ⟨A, -, hON, -, -⟩ := h
  exact hON

theorem IsCut.subgroup {ε : Fin n → Bool} {S : Set (Formalism.REAL.UJ ε)} {E : Fin d → Matrix (Fin n) (Fin n) ℂ}
    (h : IsCut ε S E) : ∃ H : Subgroup (Formalism.REAL.UJ ε), (H : Set (Formalism.REAL.UJ ε)) = S ∧ IsClosed S := by
  obtain ⟨A, hA, -, -, rfl⟩ := h
  exact ⟨GlobalTheory.GaugeSubLoc.algSub ε A hA, rfl, GlobalTheory.GaugeSubLoc.isClosed_algSub A hA⟩

theorem IsCut.inG {ε : Fin n → Bool} {S : Set (Formalism.REAL.UJ ε)} {E : Fin d → Matrix (Fin n) (Fin n) ℂ}
    (h : IsCut ε S E) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ Submodule.span ℝ (Set.range E)) :
    Formalism.REAL.inG ε X := by
  obtain ⟨A, -, -, hiff, -⟩ := h
  exact ((hiff X).mpr hX).2

end GlobalTheory.IwConst
