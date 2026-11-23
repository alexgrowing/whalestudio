import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtMapComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapMoebiusDenomUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameMapContraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameMapWedgeCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReframeVerticalDerivative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FderivReframeHorizontalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MoebImaginaryPartTransformStatement

set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge
open scoped ContDiff

namespace GlobalTheory.TorsionForm.Gauge.NablaConj

open GlobalTheory.ExtFunctor GlobalTheory.TorsionForm.FrameContr

section Alg

variable {m : ℕ}

def der (M : Matrix (Fin m) (Fin m) ℂ) : Ext m →ₗ[ℂ] Ext m :=
  ∑ i, wedgeVec (M i) ∘ₗ contrLin i

theorem der_apply (M : Matrix (Fin m) (Fin m) ℂ) (w : Ext m) :
    der M w = ∑ i, wedgeVec (M i) (contr i w) := by
  simp [der, LinearMap.sum_apply, contrLin_apply]

theorem der_wedgeVec (M : Matrix (Fin m) (Fin m) ℂ) (u : Fin m → ℂ) (x : Ext m) :
    der M (wedgeVec u x) = wedgeVec (u ᵥ* M) x + wedgeVec u (der M x) := by
  have e : wedgeVec (u ᵥ* M) x = ∑ i, u i • wedgeVec (M i) x := by
    simp only [wedgeVec_apply, Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct,
      Finset.sum_smul]
    exact Finset.sum_comm
  rw [e, der_apply, der_apply, map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [contr_wedgeVec, map_sub, map_smul, wedgeVec_comm (M i) u, sub_neg_eq_add]

theorem single_insert {a : Fin m} {T : Finset (Fin m)} (hmin : ∀ x ∈ T, a < x) :
    (Pi.single (insert a T) (1 : ℂ) : Ext m) = wedge a (Pi.single T 1) := by
  have haT : a ∉ T := fun h => lt_irrefl a (hmin a h)
  rw [wedge_single, if_neg haT, sgn_of_lt_all hmin, one_smul]

theorem der_empty (M : Matrix (Fin m) (Fin m) ℂ) : der M (Pi.single ∅ 1) = 0 := by
  simp [der_apply, contr_single_empty]

theorem wedge_eq_wedgeVec (a : Fin m) (x : Ext m) : wedge a x = wedgeVec (Pi.single a 1) x := by
  rw [wedgeVec_apply, Finset.sum_eq_single a] <;> simp +contextual [Pi.single_apply]

theorem extMap_der (ψ M N : Matrix (Fin m) (Fin m) ℂ) (h : N * ψ = ψ * M) (w : Ext m) :
    extMap ψ (der N w) = der M (extMap ψ w) := by
  have key : ∀ S : Finset (Fin m),
      extMap ψ (der N (Pi.single S 1)) = der M (extMap ψ (Pi.single S 1)) := by
    intro S
    refine Finset.induction_on_min S ?_ ?_
    · rw [extMap_single, genProd_empty, der_empty, der_empty, map_zero]
    · intro a T hmin ih
      rw [single_insert hmin, extMap_wedge, der_wedgeVec, wedge_eq_wedgeVec, der_wedgeVec,
        ← wedge_eq_wedgeVec, map_add, extMap_wedge, ih, Matrix.single_one_vecMul]
      congr 1
      have := extMap_wedgeVec ψ N a (Pi.single T 1)
      rw [h] at this
      exact this
  have : ((extMap ψ).toLinearMap ∘ₗ der N) = der M ∘ₗ (extMap ψ).toLinearMap :=
    (Pi.basisFun ℂ (Finset (Fin m))).ext fun S => by
      rw [Pi.basisFun_apply]; exact key S
  exact LinearMap.congr_fun this w

end Alg

section Der

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {m : ℕ}

def mder {ι κ : Type} (f : V → Matrix ι κ ℂ) (b v : V) : Matrix ι κ ℂ :=
  Matrix.of fun i k => fderiv ℝ (fun b' => f b' i k) b v

theorem wedgeVec_fderiv (u : V → Fin m → ℂ) (x : V → Ext m) (b : V)
    (hu : ∀ k, DifferentiableAt ℝ (fun b' => u b' k) b) (hx : DifferentiableAt ℝ x b) :
    DifferentiableAt ℝ (fun b' => wedgeVec (u b') (x b')) b ∧ ∀ v,
      fderiv ℝ (fun b' => wedgeVec (u b') (x b')) b v =
        wedgeVec (fun k => fderiv ℝ (fun b' => u b' k) b v) (x b) + wedgeVec (u b) (fderiv ℝ x b v) := by
  let L : Fin m → Ext m →L[ℝ] Ext m := fun k =>
    (LinearMap.toContinuousLinearMap (wedgeLin k)).restrictScalars ℝ
  have hL : ∀ k w, L k w = wedge k w := fun k w => rfl
  have h := HasFDerivAt.fun_sum (u := Finset.univ) fun k _ =>
    (hu k).hasFDerivAt.smul ((L k).hasFDerivAt.comp b hx.hasFDerivAt)
  have e : (fun b' => wedgeVec (u b') (x b')) = fun b' => ∑ k, u b' k • L k (x b') := by
    funext b'; rw [wedgeVec_apply]; rfl
  rw [e]
  refine ⟨h.differentiableAt, fun v => ?_⟩
  erw [h.fderiv]
  simp [wedgeVec_apply, ContinuousLinearMap.sum_apply, hL, Finset.sum_add_distrib, add_comm]

theorem genProd_fderiv (ψ : V → Matrix (Fin m) (Fin m) ℂ) (b : V)
    (hψ : ∀ i k, DifferentiableAt ℝ (fun b' => ψ b' i k) b) (v : V) (M : Matrix (Fin m) (Fin m) ℂ)
    (hM : mder ψ b v = ψ b * M) (S : Finset (Fin m)) :
    DifferentiableAt ℝ (fun b' => genProd (ψ b') S) b ∧
      fderiv ℝ (fun b' => genProd (ψ b') S) b v = der M (genProd (ψ b) S) := by
  refine Finset.induction_on_min S ?_ ?_
  · simp only [genProd_empty, der_empty]; simp
  · intro a T hmin ih
    simp only [genProd_insert_min _ hmin]
    obtain ⟨h1, h2⟩ := wedgeVec_fderiv (fun b' => ψ b' a) (fun b' => genProd (ψ b') T) b (hψ a) ih.1
    refine ⟨h1, ?_⟩
    have e : (fun k => fderiv ℝ (fun b' => ψ b' a k) b v) = ψ b a ᵥ* M := by
      funext k
      have := congrFun (congrFun hM a) k
      simpa [mder, Matrix.mul_apply, Matrix.vecMul, dotProduct] using this
    rw [h2, ih.2, der_wedgeVec, e]

theorem extMap_fderiv (ψ : V → Matrix (Fin m) (Fin m) ℂ) (x : V → Ext m) (b : V)
    (hψ : ∀ i k, DifferentiableAt ℝ (fun b' => ψ b' i k) b) (hx : DifferentiableAt ℝ x b)
    (v : V) (M : Matrix (Fin m) (Fin m) ℂ) (hM : mder ψ b v = ψ b * M) :
    fderiv ℝ (fun b' => extMap (ψ b') (x b')) b v =
      der M (extMap (ψ b) (x b)) + extMap (ψ b) (fderiv ℝ x b v) := by
  have hxS : ∀ S, HasFDerivAt (fun b' => x b' S)
      ((ContinuousLinearMap.proj S : Ext m →L[ℝ] ℂ).comp (fderiv ℝ x b)) b := fun S =>
    hasFDerivAt_pi'.1 hx.hasFDerivAt S
  have h := HasFDerivAt.fun_sum (u := Finset.univ) fun S _ =>
    (hxS S).smul (genProd_fderiv ψ b hψ v M hM S).1.hasFDerivAt
  simp only [extMap_apply]
  erw [h.fderiv]
  simp [ContinuousLinearMap.sum_apply, Finset.sum_add_distrib, map_sum,
    fun S => (genProd_fderiv ψ b hψ v M hM S).2]

theorem mder_mul {ι κ μ : Type} [Fintype κ] (f : V → Matrix ι κ ℂ) (f' : V → Matrix κ μ ℂ) (b v : V)
    (hf : ∀ i k, DifferentiableAt ℝ (fun b' => f b' i k) b)
    (hf' : ∀ i k, DifferentiableAt ℝ (fun b' => f' b' i k) b) :
    mder (fun b' => f b' * f' b') b v = mder f b v * f' b + f b * mder f' b v := by
  ext i j
  have h := HasFDerivAt.fun_sum (u := Finset.univ) fun k _ =>
    (hf i k).hasFDerivAt.mul (hf' k j).hasFDerivAt
  simp only [mder, Matrix.mul_apply, Matrix.of_apply, Matrix.add_apply]
  erw [h.fderiv]
  simp [ContinuousLinearMap.sum_apply, Finset.sum_add_distrib, add_comm, mul_comm]

theorem diff_mul {ι κ μ : Type} [Fintype κ] (f : V → Matrix ι κ ℂ) (f' : V → Matrix κ μ ℂ) (b : V)
    (hf : ∀ i k, DifferentiableAt ℝ (fun b' => f b' i k) b)
    (hf' : ∀ i k, DifferentiableAt ℝ (fun b' => f' b' i k) b) (i : ι) (j : μ) :
    DifferentiableAt ℝ (fun b' => (f b' * f' b') i j) b := by
  simp only [Matrix.mul_apply]
  exact DifferentiableAt.fun_sum fun k _ => (hf i k).mul (hf' k j)

theorem mder_conjTranspose {ι κ : Type} (f : V → Matrix ι κ ℂ) (b v : V)
    (hf : ∀ i k, DifferentiableAt ℝ (fun b' => f b' i k) b) :
    mder (fun b' => (f b')ᴴ) b v = (mder f b v)ᴴ := by
  ext i j
  have h := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp b (hf j i).hasFDerivAt
  simp only [mder, Matrix.of_apply, conjTranspose_apply]
  erw [h.fderiv]
  simp

end Der

def fibZero (n : ℕ) {g : ℕ} (a : Matrix (Fin g) (Fin g) ℂ) :
    Matrix (Fin (n + n + g)) (Fin (n + n + g)) ℂ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 0 0 a)

section Fib

variable (n : ℕ) {g : ℕ}

theorem fibMat_mul_fibZero (a a' : Matrix (Fin g) (Fin g) ℂ) :
    fibMat n a * fibZero n a' = fibZero n (a * a') := by
  simp [fibMat, fibZero, Matrix.fromBlocks_multiply]

theorem fibZero_mul_fibMat (a a' : Matrix (Fin g) (Fin g) ℂ) :
    fibZero n a * fibMat n a' = fibZero n (a * a') := by
  simp [fibMat, fibZero, Matrix.fromBlocks_multiply]

theorem der_fibZero (a : Matrix (Fin g) (Fin g) ℂ) (w : Ext (n + n + g)) :
    der (fibZero n a) w = ∑ c, ∑ d, a c d • wedge (dzb n d) (contr (dzb n c) w) := by
  simp [der_apply, wedgeVec_apply, Fin.sum_univ_add, fibZero, dzb]

theorem der_fibZero_add (a a' : Matrix (Fin g) (Fin g) ℂ) (w : Ext (n + n + g)) :
    der (fibZero n (a + a')) w = der (fibZero n a) w + der (fibZero n a') w := by
  simp [der_fibZero, add_smul, Finset.sum_add_distrib]

theorem der_fibZero_smul (c : ℂ) (a : Matrix (Fin g) (Fin g) ℂ) (w : Ext (n + n + g)) :
    der (fibZero n (c • a)) w = c • der (fibZero n a) w := by
  simp [der_fibZero, Finset.smul_sum, smul_smul]

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem diff_fibMat (f : V → Matrix (Fin g) (Fin g) ℂ) (b : V)
    (hf : ∀ i k, DifferentiableAt ℝ (fun b' => f b' i k) b) (i k : Fin (n + n + g)) :
    DifferentiableAt ℝ (fun b' => fibMat n (f b') i k) b := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun k => ?_) (fun k => ?_) k <;> simp [fibMat, hf]

theorem mder_fibMat (f : V → Matrix (Fin g) (Fin g) ℂ) (b v : V) :
    mder (fun b' => fibMat n (f b')) b v = fibZero n (mder f b v) := by
  ext i k
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun k => ?_) (fun k => ?_) k <;> simp [fibMat, fibZero, mder]

end Fib

end GlobalTheory.TorsionForm.Gauge.NablaConj

namespace GlobalTheory.TorsionForm.Gauge.NablaConj

open GlobalTheory.ExtFunctor

section Main

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}

theorem mder_fst {ι κ : Type} (f : E → Matrix ι κ ℂ) (P : Pt E g) (w : Pt E g)
    (hf : ∀ i k, DifferentiableAt ℝ (fun b => f b i k) P.1) :
    mder (fun Q : Pt E g => f Q.1) P w = mder f P.1 w.1 := by
  ext i k
  simp only [mder, Matrix.of_apply]
  show fderiv ℝ ((fun b => f b i k) ∘ Prod.fst) P w = _
  rw [((hf i k).hasFDerivAt.comp P hasFDerivAt_fst).fderiv]
  rfl

theorem mder_congr {ι κ : Type} {f f' : E → Matrix ι κ ℂ} {b : E} (hev : f =ᶠ[𝓝 b] f') (v : E) :
    mder f b v = mder f' b v := by
  ext i k
  simp only [mder, Matrix.of_apply]
  have h' : (fun x => f x i k) =ᶠ[𝓝 b] fun x => f' x i k := hev.mono fun x hx => congrArg (fun M : Matrix ι κ ℂ => M i k) hx
  rw [h'.fderiv_eq]

theorem mder_I {ι κ : Type} (f : E → Matrix ι κ ℂ) (b v : E)
    (hf : ∀ i k, DifferentiableAt ℂ (fun b => f b i k) b) :
    mder f b (Complex.I • v) = Complex.I • mder f b v := by
  ext i k
  simp only [mder, Matrix.of_apply, Matrix.smul_apply]
  rw [(hf i k).fderiv_restrictScalars ℝ]
  simp

theorem dmat_eq {ι κ : Type} (f : E → Matrix ι κ ℂ) (b v : E) :
    (Matrix.of fun a e => d01 (fun b' => f b' a e) b v) =
      (1 / 2 : ℂ) • (mder f b v + Complex.I • mder f b (Complex.I • v)) := by
  ext a e
  simp [d01, mder, smul_eq_mul]

theorem d01_comp_continuousLinearMap {m : ℕ} (f : Pt E g → Ext m) (R : Pt E g → Pt E g) (P v : Pt E g)
    (hR : DifferentiableAt ℂ R P) (hf : DifferentiableAt ℝ f (R P)) :
    d01 (fun Q => f (R Q)) P v = d01 f (R P) (fderiv ℝ R P v) := by
  have hc : fderiv ℝ (fun Q => f (R Q)) P = (fderiv ℝ f (R P)).comp (fderiv ℝ R P) :=
    fderiv_comp P hf (hR.restrictScalars ℝ)
  have hRr : fderiv ℝ R P = (fderiv ℂ R P).restrictScalars ℝ := hR.fderiv_restrictScalars ℝ
  simp only [d01, hc, ContinuousLinearMap.comp_apply, hRr, ContinuousLinearMap.coe_restrictScalars',
    map_smul]

theorem d10_comp_continuousLinearMap {m : ℕ} (f : Pt E g → Ext m) (R : Pt E g → Pt E g) (P v : Pt E g)
    (hR : DifferentiableAt ℂ R P) (hf : DifferentiableAt ℝ f (R P)) :
    d10 (fun Q => f (R Q)) P v = d10 f (R P) (fderiv ℝ R P v) := by
  have hc : fderiv ℝ (fun Q => f (R Q)) P = (fderiv ℝ f (R P)).comp (fderiv ℝ R P) :=
    fderiv_comp P hf (hR.restrictScalars ℝ)
  have hRr : fderiv ℝ R P = (fderiv ℂ R P).restrictScalars ℝ := hR.fderiv_restrictScalars ℝ
  simp only [d10, hc, ContinuousLinearMap.comp_apply, hRr, ContinuousLinearMap.coe_restrictScalars',
    map_smul]

theorem d10_comp_of_differentiableAt (f : Pt E g → ℂ) (R : Pt E g → Pt E g) (P v : Pt E g)
    (hR : DifferentiableAt ℂ R P) (hf : DifferentiableAt ℝ f (R P)) :
    d10 (fun Q => f (R Q)) P v = d10 f (R P) (fderiv ℝ R P v) := by
  have hc : fderiv ℝ (fun Q => f (R Q)) P = (fderiv ℝ f (R P)).comp (fderiv ℝ R P) :=
    fderiv_comp P hf (hR.restrictScalars ℝ)
  have hRr : fderiv ℝ R P = (fderiv ℂ R P).restrictScalars ℝ := hR.fderiv_restrictScalars ℝ
  simp only [d10, hc, ContinuousLinearMap.comp_apply, hRr, ContinuousLinearMap.coe_restrictScalars',
    map_smul]

theorem alg1 {k : ℕ} (φ' Y Di φ mY mY2 Gr : Matrix (Fin k) (Fin k) ℂ) :
    (1 / 2 : ℂ) • (((φ' * Y + φ * mY) * Di + φ * Y * Gr) +
      Complex.I • ((((-Complex.I) • φ') * Y + φ * mY2) * Di + φ * Y * (Complex.I • Gr))) =
      φ' * Y * Di + φ * ((1 / 2 : ℂ) • (mY + Complex.I • mY2)) * Di := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, smul_add, smul_smul, mul_neg,
    neg_mul, Complex.I_mul_I, neg_neg, neg_smul, Matrix.mul_assoc]
  match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

theorem alg2 {k : ℕ} (P Y Di D Yi Pi Q X : Matrix (Fin k) (Fin k) ℂ) (h1 : Di * D = 1)
    (h2 : Y * Yi = 1) (h3 : Pi * P = 1) :
    (Q * Y * Di + P * X * Di) * (D * Yi * Pi) * P = Q + P * (X * Yi) := by
  have e : ∀ Z, Z * Di * (D * Yi * Pi) * P = Z * Yi := by
    intro Z
    simp only [Matrix.mul_assoc]
    rw [h3, Matrix.mul_one, ← Matrix.mul_assoc Di D, h1, Matrix.one_mul]
  rw [add_mul, add_mul, e, e]
  simp only [Matrix.mul_assoc, h2, Matrix.mul_one]

end Main

end GlobalTheory.TorsionForm.Gauge.NablaConj

namespace GlobalTheory.TorsionForm.Gauge.NablaConj

open GlobalTheory.ExtFunctor

theorem nablaE_gauge : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {g n : ℕ} (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (γ : Sp g) (h : Pt E g → ℝ)
    (β : Fin n → E) (s : Pt E g → Ext (n + n + g)), IsPeriodMap B τ →
    IsPeriodMap B (fun b => moeb γ (τ b)) → ContDiffOn ℝ ∞ h (cov B g) →
    (∀ P ∈ cov B g, 0 < h P) → DifferentiableOn ℝ s (cov B g) →
    ∀ P ∈ cov B g, nablaE τ (fun Q => h (reframe τ γ Q)) β (gauge n τ γ s) P =
      frameAt n τ γ P.1 (nablaE (fun b => moeb γ (τ b)) h β s (reframe τ γ P)) := by
  intro E _ _ _ g n B τ γ h β s hτ hτ' hh hpos hs P hP
  have hb : P.1 ∈ B := hP.1
  have hcovOpen : IsOpen (cov B g) := hτ.1.prod isOpen_univ
  have hRP : reframe τ γ P ∈ cov B g := ⟨hb, trivial⟩
  have hDu : ∀ b ∈ B, IsUnit (den γ (τ b)) := GlobalTheory.SiegelAction.den_isUnit_of_isPeriodMap B τ γ hτ'
  have hD : IsUnit (den γ (τ P.1)) := hDu P.1 hb
  have hDd : IsUnit (den γ (τ P.1)).det := (Matrix.isUnit_iff_isUnit_det _).1 hD
  obtain ⟨hRc, -⟩ := GlobalTheory.ReframeVert.reframe_vert B τ γ hτ hτ' P hP
  have hsR : DifferentiableAt ℝ s (reframe τ γ P) := hs.differentiableAt (hcovOpen.mem_nhds hRP)
  have hu : DifferentiableAt ℝ (fun Q => s (reframe τ γ Q)) P := hsR.comp P (hRc.restrictScalars ℝ)
  have hhR : DifferentiableAt ℝ h (reframe τ γ P) :=
    ((hh.contDiffAt (hcovOpen.mem_nhds hRP)).differentiableAt (by simp))
  have hlog : DifferentiableAt ℝ (fun Q => (Real.log (h Q) : ℂ)) (reframe τ γ P) :=
    Complex.ofRealCLM.differentiableAt.comp _ (hhR.log (hpos _ hRP).ne')

  set b := P.1 with hbdef
  set τ' : E → Matrix (Fin g) (Fin g) ℂ := fun b => moeb γ (τ b) with hτ'def
  set Dinv : E → Matrix (Fin g) (Fin g) ℂ := fun b => (den γ (τ b))⁻¹ with hDinv
  set φ : E → Matrix (Fin g) (Fin g) ℂ := fun b => (Dinv b)ᴴ with hφdef
  set Φ := frameAt n τ γ b with hΦ
  have hΦe : Φ = extMap (fibMat n (φ b)) := rfl
  have hDi : ∀ i k, DifferentiableAt ℂ (fun b => Dinv b i k) b := fun i k =>
    GlobalTheory.ReframeVert.differentiableAt_inv_apply _ b
      (fun i j => GlobalTheory.ReframeVert.differentiableAt_den_apply B τ γ hτ hb i j) hD i k
  have hDiR : ∀ i k, DifferentiableAt ℝ (fun b => Dinv b i k) b := fun i k => (hDi i k).restrictScalars ℝ
  have hφd : ∀ i k, DifferentiableAt ℝ (fun b => φ b i k) b := fun i k => (hDiR k i).star
  have hφQ : ∀ i k, DifferentiableAt ℝ (fun Q : Pt E g => φ Q.1 i k) P := fun i k =>
    DifferentiableAt.comp (g := fun b => φ b i k) (f := Prod.fst) P (hφd i k) differentiableAt_fst
  have hφu : IsUnit (φ b).det := by
    simp only [hφdef, Matrix.det_conjTranspose, isUnit_star]
    exact (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_nonsing_inv_det _ hDd |>
      (Matrix.isUnit_iff_isUnit_det _).2)

  set K : E → Matrix (Fin g) (Fin g) ℂ := fun v => (φ b)⁻¹ * mder φ b v with hK
  have hφI : ∀ v, mder φ b (Complex.I • v) = (-Complex.I) • mder φ b v := by
    intro v
    simp only [hφdef]
    rw [mder_conjTranspose _ _ _ hDiR, mder_conjTranspose _ _ _ hDiR, mder_I _ _ _ hDi,
      Matrix.conjTranspose_smul]
    simp [Complex.star_def]
  have hKI : ∀ v, K (Complex.I • v) = (-Complex.I) • K v := by
    intro v; simp only [hK, hφI, Matrix.mul_smul]
  have hG : ∀ w : Pt E g, fderiv ℝ (gauge n τ γ s) P w =
      der (fibZero n (K w.1)) (Φ (s (reframe τ γ P))) +
        Φ (fderiv ℝ (fun Q => s (reframe τ γ Q)) P w) := by
    intro w
    have e : gauge n τ γ s = fun Q => extMap (fibMat n (φ Q.1)) (s (reframe τ γ Q)) := rfl
    have hM : mder (fun Q : Pt E g => fibMat n (φ Q.1)) P w = fibMat n (φ b) * fibZero n (K w.1) := by
      have h1 := mder_fibMat n (fun Q : Pt E g => φ Q.1) P w
      rw [h1, mder_fst _ _ _ hφd, fibMat_mul_fibZero, hK, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hφu, Matrix.one_mul]
    rw [e, extMap_fderiv (fun Q : Pt E g => fibMat n (φ Q.1)) _ P (diff_fibMat n _ P hφQ) hu w _ hM]
    rfl

  have hd10 : ∀ x : Pt E g, d10 (gauge n τ γ s) P x = Φ (d10 (fun Q => s (reframe τ γ Q)) P x) := by
    intro x
    have ex : (Complex.I • x).1 = Complex.I • x.1 := rfl
    simp only [d10]
    rw [hG, hG, ex, hKI, der_fibZero_smul]
    simp only [map_add, map_sub, map_smul]
    match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring
  have hd01 : ∀ x : Pt E g, d01 (gauge n τ γ s) P x =
      der (fibZero n (K x.1)) (Φ (s (reframe τ γ P))) + Φ (d01 (fun Q => s (reframe τ γ Q)) P x) := by
    intro x
    have ex : (Complex.I • x).1 = Complex.I • x.1 := rfl
    simp only [d01]
    rw [hG, hG, ex, hKI, der_fibZero_smul]
    simp only [map_add, map_smul]
    match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring
  have hHol : ∀ v, Pullback.nabHol τ (fun Q => h (reframe τ γ Q)) (gauge n τ γ s) P v =
      Φ (Pullback.nabHol τ' h s (reframe τ γ P) v) := by
    intro v
    simp only [Pullback.nabHol, pointDifference]
    rw [hd10, d10_comp_continuousLinearMap s _ P _ hRc hsR,
      d10_comp_of_differentiableAt (fun Q => (Real.log (h Q) : ℂ)) _ P _ hRc hlog,
      GlobalTheory.T.fderiv_reframe_horizontal B τ γ hτ hτ' P hP v, map_add, map_smul]
    rfl

  have hYd : ∀ (T : E → Matrix (Fin g) (Fin g) ℂ), IsPeriodMap B T →
      ∀ i k, DifferentiableAt ℝ (fun b => imPart T b i k) b := by
    intro T hT i k
    have hTd : DifferentiableAt ℝ (fun b => T b i k) b :=
      ((hT.2.1 i k).differentiableAt (hT.1.mem_nhds hb)).restrictScalars ℝ
    exact Complex.ofRealCLM.differentiableAt.comp _ (Complex.imCLM.differentiableAt.comp _ hTd)
  have hYu : IsUnit (imPart τ b).det := by
    have e : imPart τ b = (Complex.ofRealHom).mapMatrix ((τ b).map Complex.im) := by
      ext i k; simp [imPart]
    rw [e, ← RingHom.map_det, isUnit_iff_ne_zero]
    exact Complex.ofReal_ne_zero.2 (hτ.2.2 b hb).2.det_pos.ne'
  have hev : (imPart τ') =ᶠ[𝓝 b] fun b' => φ b' * imPart τ b' * Dinv b' := by
    filter_upwards [hτ.1.mem_nhds hb] with b' hb'
    exact GlobalTheory.T.moeb_imaginary_part_transform γ (τ b') (hτ.2.2 b' hb').1 (hDu b' hb')
  have hDiu : IsUnit (Dinv b).det := Matrix.isUnit_nonsing_inv_det _ hDd
  have hmY' : ∀ u, mder (imPart τ') b u =
      (mder φ b u * imPart τ b + φ b * mder (imPart τ) b u) * Dinv b +
        φ b * imPart τ b * mder Dinv b u := by
    intro u
    rw [mder_congr hev, mder_mul _ _ _ _ (diff_mul _ _ _ hφd (hYd τ hτ)) hDiR,
      mder_mul _ _ _ _ hφd (hYd τ hτ)]
  have hA : ∀ v, ((Matrix.of fun a e => d01 (fun b' => imPart τ' b' a e) b v) * (imPart τ' b)⁻¹) * φ b =
      mder φ b v + φ b * ((Matrix.of fun a e => d01 (fun b' => imPart τ b' a e) b v) * (imPart τ b)⁻¹) := by
    intro v
    have e1 : (Matrix.of fun a e => d01 (fun b' => imPart τ' b' a e) b v) =
        mder φ b v * imPart τ b * Dinv b +
          φ b * (Matrix.of fun a e => d01 (fun b' => imPart τ b' a e) b v) * Dinv b := by
      rw [dmat_eq (imPart τ'), dmat_eq (imPart τ), hmY', hmY', hφI, mder_I _ _ _ hDi]
      exact alg1 _ _ _ _ _ _ _
    have e2 : (imPart τ' b)⁻¹ = (Dinv b)⁻¹ * (imPart τ b)⁻¹ * (φ b)⁻¹ := by
      rw [hev.eq_of_nhds, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc]
    rw [e1, e2]
    exact alg2 _ _ _ _ _ _ _ _ (Matrix.mul_nonsing_inv _ hDiu) (Matrix.mul_nonsing_inv _ hYu)
      (Matrix.nonsing_inv_mul _ hφu)

  have hconn : ∀ (T : E → Matrix (Fin g) (Fin g) ℂ) (v : E) (w : Ext (n + n + g)), connForm T b v w =
      der (fibZero n ((Matrix.of fun a e => d01 (fun b' => imPart T b' a e) b v) * (imPart T b)⁻¹)) w := by
    intro T v w; rw [der_fibZero]; rfl
  have hAnti : ∀ v, Pullback.nabAnti τ (gauge n τ γ s) P v =
      Φ (Pullback.nabAnti τ' s (reframe τ γ P) v) := by
    intro v
    have hx1 : (hor τ P v).1 = v := rfl
    have hR1 : (reframe τ γ P).1 = b := rfl
    simp only [Pullback.nabAnti]
    rw [hd01, hx1, d01_comp_continuousLinearMap s _ P _ hRc hsR, GlobalTheory.T.fderiv_reframe_horizontal B τ γ hτ hτ' P hP v, map_add, hR1,
      hconn τ, hconn τ']
    have hfix : fibZero n ((Matrix.of fun a e => d01 (fun b' => imPart τ' b' a e) b v) *
          (imPart τ' b)⁻¹) * fibMat n (φ b) =
        fibMat n (φ b) * fibZero n (K v +
          (Matrix.of fun a e => d01 (fun b' => imPart τ b' a e) b v) * (imPart τ b)⁻¹) := by
      rw [fibZero_mul_fibMat, fibMat_mul_fibZero, hA, Matrix.mul_add]
      congr 2
      show _ = φ b * ((φ b)⁻¹ * mder φ b v)
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hφu, Matrix.one_mul]
    rw [hΦe, extMap_der _ _ _ hfix, der_fibZero_add, ← hΦe]
    change _ + _ + der _ (Φ (s (reframe τ γ P))) = _
    abel
  rw [Pullback.nablaE_eq_sum, Pullback.nablaE_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pullback.nabPiece]
  have hw := fun w => (GlobalTheory.TorsionForm.FrameWedge.frameMap_wedge n (den γ (τ b)) w).2 i
  rw [hHol, hAnti, map_add]
  exact congrArg₂ (· + ·) (hw _).1.symm (hw _).2.symm

end GlobalTheory.TorsionForm.Gauge.NablaConj
