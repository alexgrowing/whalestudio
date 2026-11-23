import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open MeasureTheory Matrix Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum

namespace GlobalTheory.TypeSum.FrameChange

variable {n : ℕ} {ε : Fin n → Bool} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {σ : Mx n → (H →L[ℂ] H)} {σ' : Mx n → (H' →L[ℂ] H')}

private theorem one_mem_UJset' : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
  show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε * 1 = Formalism.REAL.Jm ε
  simp

private theorem mul_mem_UH_Hpk' {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ UJset ε) (hb : b ∈ UJset ε) :
    a * b ∈ UJset ε := by
  have ha' : aᴴ * Formalism.REAL.Jm ε * a = Formalism.REAL.Jm ε := ha
  have hb' : bᴴ * Formalism.REAL.Jm ε * b = Formalism.REAL.Jm ε := hb
  show (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = Formalism.REAL.Jm ε
  rw [Matrix.conjTranspose_mul]
  calc _ = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [ha', hb']

private theorem exp_smul_mem_UJset' {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieSet ε) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ UJset ε := by
  have hX' : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := hX
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  have hJinv : (Formalism.REAL.Jm ε)⁻¹ = Formalism.REAL.Jm ε := Matrix.inv_eq_left_inv hJJ
  have hJu : IsUnit (Formalism.REAL.Jm ε) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse hJJ)
  have hXh : Xᴴ = -(Formalism.REAL.Jm ε * X * Formalism.REAL.Jm ε) := by
    have h1 : Xᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := eq_neg_of_add_eq_zero_left hX'
    calc Xᴴ = Xᴴ * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = -(Formalism.REAL.Jm ε * X * Formalism.REAL.Jm ε) := by rw [h1, Matrix.neg_mul]
  have hYh : (t • X)ᴴ = Formalism.REAL.Jm ε * (-(t • X)) * (Formalism.REAL.Jm ε)⁻¹ := by
    rw [Matrix.conjTranspose_smul, star_trivial, hXh, hJinv]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, smul_neg]
  have hEu : IsUnit (NormedSpace.exp (t • X)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _)
  show (NormedSpace.exp (t • X))ᴴ * Formalism.REAL.Jm ε * NormedSpace.exp (t • X) = Formalism.REAL.Jm ε
  rw [← Matrix.exp_conjTranspose, hYh, Matrix.exp_conj _ _ hJu, hJinv, Matrix.exp_neg]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε), hJJ, Matrix.one_mul,
    Matrix.nonsing_inv_mul _ hEu, Matrix.mul_one]

theorem prod_mem {k : ℕ} {Xs : Fin k → Mx n} (hX : ∀ i, Xs i ∈ lieSet ε) (t : Fin k → ℝ) :
    (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod ∈ UJset ε := by
  have key : ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ a ∈ l, a ∈ UJset ε) → l.prod ∈ UJset ε := by
    intro l
    induction l with
    | nil => intro _; simpa using (one_mem_UJset' (ε := ε))
    | cons a l ih =>
      intro h
      rw [List.prod_cons]
      exact mul_mem_UH_Hpk' (h a (by simp)) (ih fun b hb => h b (by simp [hb]))
  apply key
  intro a ha
  rw [List.mem_ofFn] at ha
  obtain ⟨i, rfl⟩ := ha
  exact exp_smul_mem_UJset' (hX i) (t i)

def toReal (U : H' ≃ₗᵢ[ℂ] H) : H' ≃L[ℝ] H :=
  { U.toLinearEquiv.restrictScalars ℝ with
    continuous_toFun := U.continuous
    continuous_invFun := U.symm.continuous }

theorem toReal_apply (U : H' ≃ₗᵢ[ℂ] H) (x : H') : toReal U x = U x := rfl

theorem symm_intertwines (U : H' ≃ₗᵢ[ℂ] H) (hU : ∀ g ∈ UJset ε, ∀ w, U (σ' g w) = σ g (U w)) :
    ∀ g ∈ UJset ε, ∀ w, U.symm (σ g w) = σ' g (U.symm w) := by
  intro g hg w
  apply U.injective
  rw [hU g hg, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]

theorem smooth_map (U : H' ≃ₗᵢ[ℂ] H) (hU : ∀ g ∈ UJset ε, ∀ w, U (σ' g w) = σ g (U w)) {w : H'}
    (hw : SmoothVec (lieSet ε) σ' w) : SmoothVec (lieSet ε) σ (U w) := by
  intro k Xs hXs
  have h := hw k Xs hXs
  have e : (fun t : Fin k → ℝ => σ ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) (U w)) =
      fun t => (toReal U) (σ' ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) w) := by
    funext t
    rw [toReal_apply, hU _ (prod_mem hXs t)]
  rw [e]
  exact (toReal U).contDiff.comp h

private theorem deriv_continuousLinearMap_comp_zero {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] (A : E →L[ℂ] E') (B : E' →L[ℂ] E) (hBA : ∀ x, B (A x) = x)
    (f : ℝ → E) : deriv (fun t => A (f t)) 0 = A (deriv f 0) := by
  by_cases hf : DifferentiableAt ℝ f 0
  · exact ((A.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hf.hasDerivAt).deriv
  · have hg : ¬ DifferentiableAt ℝ (fun t => A (f t)) 0 := by
      intro h
      apply hf
      have h2 := (B.restrictScalars ℝ).differentiableAt.comp (0 : ℝ) h
      have heq : f = (B.restrictScalars ℝ) ∘ fun t => A (f t) := by
        funext t
        simp [hBA]
      rw [heq]
      exact h2
    rw [deriv_zero_of_not_differentiableAt hf, deriv_zero_of_not_differentiableAt hg, map_zero]

theorem dRep_map (U : H' ≃ₗᵢ[ℂ] H) (hU : ∀ g ∈ UJset ε, ∀ w, U (σ' g w) = σ g (U w)) {X : Mx n}
    (hX : X ∈ lieSet ε) (w : H') : dRep σ X (U w) = U (dRep σ' X w) := by
  show deriv (fun t : ℝ => σ (NormedSpace.exp (t • X)) (U w)) 0 =
    U (deriv (fun t : ℝ => σ' (NormedSpace.exp (t • X)) w) 0)
  have e : (fun t : ℝ => σ (NormedSpace.exp (t • X)) (U w)) =
      fun t => (U.toContinuousLinearEquiv : H' →L[ℂ] H) (σ' (NormedSpace.exp (t • X)) w) := by
    funext t
    exact (hU _ (exp_smul_mem_UJset' hX t) w).symm
  rw [e]
  exact deriv_continuousLinearMap_comp_zero _ (U.symm.toContinuousLinearEquiv : H →L[ℂ] H') (fun x => U.symm_apply_apply x) _

theorem word_map (U : H' ≃ₗᵢ[ℂ] H) (hU : ∀ g ∈ UJset ε, ∀ w, U (σ' g w) = σ g (U w)) (l : List (Mx n))
    (hl : ∀ X ∈ l, X ∈ lieSet ε) (w : H') : l.foldr (dRep σ) (U w) = U (l.foldr (dRep σ') w) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    simp only [List.foldr_cons]
    rw [ih (fun Y hY => hl Y (List.mem_cons_of_mem _ hY)), dRep_map U hU (hl X (by simp))]

theorem sobNorm_map (U : H' ≃ₗᵢ[ℂ] H) (hU : ∀ g ∈ UJset ε, ∀ w, U (σ' g w) = σ g (U w))
    {S : List (List (Mx n))} (hS : ∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) (w : H') :
    (S.map fun l => ‖l.foldr (dRep σ) (U w)‖).sum = (S.map fun l => ‖l.foldr (dRep σ') w‖).sum := by
  congr 1
  apply List.map_congr_left
  intro l hl
  rw [word_map U hU l (hS l hl), LinearIsometryEquiv.norm_map]

theorem sobCont_map (U : H' ≃ₗᵢ[ℂ] H) (hU : ∀ g ∈ UJset ε, ∀ w, U (σ' g w) = σ g (U w)) {ℓ : H' →ₗ[ℂ] ℂ}
    (hℓ : Sobolev₂ (lieSet ε) σ' ℓ) :
    Sobolev₂ (lieSet ε) σ (ℓ ∘ₗ (U.symm.toLinearEquiv : H →ₗ[ℂ] H')) := by
  obtain ⟨S, C, hS, hb⟩ := hℓ
  refine ⟨S, C, hS, fun w hw => ?_⟩
  have hw' : SmoothVec (lieSet ε) σ' (U.symm w) := smooth_map U.symm (symm_intertwines U hU) hw
  have h1 := hb (U.symm w) hw'
  have e := sobNorm_map U hU hS (U.symm w)
  rw [LinearIsometryEquiv.apply_symm_apply] at e
  show ‖ℓ (U.symm w)‖ ≤ _
  rw [e]
  exact h1

private theorem mul_inv_mem_UJset_of_conjTranspose_Jm_eq {P P' G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    (hG : Pᴴ * Formalism.REAL.Jm ε * P = G) (hG' : P'ᴴ * Formalism.REAL.Jm ε * P' = G) : P' * P⁻¹ ∈ UJset ε := by
  have hd := (Matrix.isUnit_iff_isUnit_det P).mp hP
  show (P' * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P' * P⁻¹) = Formalism.REAL.Jm ε
  rw [Matrix.conjTranspose_mul]
  calc _ = (P⁻¹)ᴴ * (P'ᴴ * Formalism.REAL.Jm ε * P') * P⁻¹ := by simp only [Matrix.mul_assoc]
    _ = (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ := by rw [hG', hG]
    _ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
      rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [Matrix.mul_nonsing_inv _ hd]; simp

private theorem mul_mul_mem_lieSet_of_mem_UJset_of_mem_lieSet {Q R X : Matrix (Fin n) (Fin n) ℂ} (hQ : Q ∈ UJset ε) (hR : R ∈ UJset ε)
    (hQR : Q * R = 1) (hRQ : R * Q = 1) (hX : X ∈ lieSet ε) : R * X * Q ∈ lieSet ε := by
  have hQ' : Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.REAL.Jm ε := hQ
  have hR' : Rᴴ * Formalism.REAL.Jm ε * R = Formalism.REAL.Jm ε := hR
  have hX' : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := hX
  have e1 : Rᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * Q := by
    calc Rᴴ * Formalism.REAL.Jm ε = Rᴴ * Formalism.REAL.Jm ε * (R * Q) := by rw [hRQ, Matrix.mul_one]
      _ = (Rᴴ * Formalism.REAL.Jm ε * R) * Q := by simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε * Q := by rw [hR']
  have e2 : Formalism.REAL.Jm ε * R = Qᴴ * Formalism.REAL.Jm ε := by
    calc Formalism.REAL.Jm ε * R = (Qᴴ * Formalism.REAL.Jm ε * Q) * R := by rw [hQ']
      _ = Qᴴ * Formalism.REAL.Jm ε * (Q * R) := by simp only [Matrix.mul_assoc]
      _ = Qᴴ * Formalism.REAL.Jm ε := by rw [hQR, Matrix.mul_one]
  show (R * X * Q)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * (R * X * Q) = 0
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  calc _ = Qᴴ * (Xᴴ * (Rᴴ * Formalism.REAL.Jm ε)) + (Formalism.REAL.Jm ε * R) * X * Q := by
        simp only [Matrix.mul_assoc]
    _ = Qᴴ * (Xᴴ * (Formalism.REAL.Jm ε * Q)) + Qᴴ * Formalism.REAL.Jm ε * X * Q := by rw [e1, e2]
    _ = Qᴴ * (Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X) * Q := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX', Matrix.mul_zero, Matrix.zero_mul]

private theorem mul_list_prod_mul_eq_prod_map_conj {Q R : Matrix (Fin n) (Fin n) ℂ} (hQR : Q * R = 1) (hRQ : R * Q = 1)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) : R * l.prod * Q = (l.map fun a => R * a * Q).prod := by
  induction l with
  | nil => simp [hRQ]
  | cons a l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons, ← ih]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q R, hQR, Matrix.one_mul]

private theorem mul_exp_smul_mul_eq_exp_smul_conj {Q R : Matrix (Fin n) (Fin n) ℂ} (hQR : Q * R = 1)
    (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    R * NormedSpace.exp (t • X) * Q = NormedSpace.exp (t • (R * X * Q)) := by
  have hRi : R⁻¹ = Q := Matrix.inv_eq_left_inv hQR
  have hRu : IsUnit R := (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse hQR)
  rw [show t • (R * X * Q) = R * (t • X) * R⁻¹ by rw [hRi, Matrix.mul_smul, Matrix.smul_mul],
    Matrix.exp_conj _ _ hRu, hRi]

private theorem mul_prod_ofFn_exp_smul_mul_eq_prod_exp_smul_conj {Q R : Matrix (Fin n) (Fin n) ℂ} (hQR : Q * R = 1) (hRQ : R * Q = 1) {k : ℕ}
    (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ) (t : Fin k → ℝ) :
    R * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * Q =
      (List.ofFn fun i => NormedSpace.exp (t i • (R * Xs i * Q))).prod := by
  rw [mul_list_prod_mul_eq_prod_map_conj hQR hRQ, List.map_ofFn]
  exact congrArg List.prod (congrArg List.ofFn (funext fun i => mul_exp_smul_mul_eq_exp_smul_conj hQR (Xs i) (t i)))

private theorem smoothVec_translate_of_smoothVec (hσ : IsURepOn (UJset ε) σ) {Q R : Matrix (Fin n) (Fin n) ℂ}
    (hQ : Q ∈ UJset ε) (hR : R ∈ UJset ε) (hQR : Q * R = 1) (hRQ : R * Q = 1) {v : H}
    (hv : SmoothVec (lieSet ε) σ v) : SmoothVec (lieSet ε) σ (σ Q v) := by
  intro k Xs hXs
  have hXs' : ∀ i, R * Xs i * Q ∈ lieSet ε := fun i => mul_mul_mem_lieSet_of_mem_UJset_of_mem_lieSet hQ hR hQR hRQ (hXs i)
  have h := hv k (fun i => R * Xs i * Q) hXs'
  have e : (fun t : Fin k → ℝ => σ ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) (σ Q v)) =
      fun t => ((σ Q).restrictScalars ℝ)
        (σ ((List.ofFn fun i => NormedSpace.exp (t i • (R * Xs i * Q))).prod) v) := by
    funext t
    rw [← mul_prod_ofFn_exp_smul_mul_eq_prod_exp_smul_conj hQR hRQ Xs t]
    have hA := prod_mem hXs t
    set A := (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod with hAdef
    have hB := mul_mem_UH_Hpk' (mul_mem_UH_Hpk' hR hA) hQ
    have hm : A * Q = Q * (R * A * Q) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQR, Matrix.one_mul]
    calc σ A (σ Q v) = σ (A * Q) v := by rw [hσ.1.2 _ hA _ hQ]; rfl
      _ = σ (Q * (R * A * Q)) v := by rw [hm]
      _ = σ Q (σ (R * A * Q) v) := by rw [hσ.1.2 _ hQ _ hB]; rfl
  rw [e]
  exact ((σ Q).restrictScalars ℝ).contDiff.comp h

private theorem dRep_apply_translate_eq_translate_dRep_conj (hσ : IsURepOn (UJset ε) σ) {Q R : Matrix (Fin n) (Fin n) ℂ}
    (hQ : Q ∈ UJset ε) (hR : R ∈ UJset ε) (hQR : Q * R = 1) (hRQ : R * Q = 1) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ lieSet ε) (x : H) : dRep σ X (σ Q x) = σ Q (dRep σ (R * X * Q) x) := by
  show deriv (fun t : ℝ => σ (NormedSpace.exp (t • X)) (σ Q x)) 0 =
    σ Q (deriv (fun t : ℝ => σ (NormedSpace.exp (t • (R * X * Q))) x) 0)
  have e : (fun t : ℝ => σ (NormedSpace.exp (t • X)) (σ Q x)) =
      fun t => σ Q (σ (NormedSpace.exp (t • (R * X * Q))) x) := by
    funext t
    have hA := exp_smul_mem_UJset' hX t
    have hB := mul_mem_UH_Hpk' (mul_mem_UH_Hpk' hR hA) hQ
    have hm : NormedSpace.exp (t • X) * Q = Q * (R * NormedSpace.exp (t • X) * Q) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQR, Matrix.one_mul]
    rw [← mul_exp_smul_mul_eq_exp_smul_conj hQR X t]
    calc σ (NormedSpace.exp (t • X)) (σ Q x) = σ (NormedSpace.exp (t • X) * Q) x := by
          rw [hσ.1.2 _ hA _ hQ]; rfl
      _ = σ (Q * (R * NormedSpace.exp (t • X) * Q)) x := by rw [hm]
      _ = σ Q (σ (R * NormedSpace.exp (t • X) * Q) x) := by rw [hσ.1.2 _ hQ _ hB]; rfl
  rw [e]
  refine deriv_continuousLinearMap_comp_zero (σ Q) (σ R) (fun y => ?_) _
  rw [show σ R (σ Q y) = ((σ R).comp (σ Q)) y from rfl, ← hσ.1.2 _ hR _ hQ, hRQ, hσ.1.1]
  rfl

private theorem foldr_dRep_translate_eq_translate_foldr_conj (hσ : IsURepOn (UJset ε) σ) {Q R : Matrix (Fin n) (Fin n) ℂ}
    (hQ : Q ∈ UJset ε) (hR : R ∈ UJset ε) (hQR : Q * R = 1) (hRQ : R * Q = 1)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) (hl : ∀ X ∈ l, X ∈ lieSet ε) (x : H) :
    l.foldr (dRep σ) (σ Q x) = σ Q ((l.map fun X => R * X * Q).foldr (dRep σ) x) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    simp only [List.foldr_cons, List.map_cons]
    rw [ih (fun Y hY => hl Y (List.mem_cons_of_mem _ hY)),
      dRep_apply_translate_eq_translate_dRep_conj hσ hQ hR hQR hRQ (hl X (by simp))]

private theorem sobCont_comp_translate_of_sobCont (hσ : IsURepOn (UJset ε) σ) {Q R : Matrix (Fin n) (Fin n) ℂ}
    (hQ : Q ∈ UJset ε) (hR : R ∈ UJset ε) (hQR : Q * R = 1) (hRQ : R * Q = 1) {ℓ : H →ₗ[ℂ] ℂ}
    (hℓ : Sobolev₂ (lieSet ε) σ ℓ) : Sobolev₂ (lieSet ε) σ (ℓ ∘ₗ (σ Q : H →ₗ[ℂ] H)) := by
  obtain ⟨S, C, hS, hb⟩ := hℓ
  refine ⟨S.map (List.map fun X => R * X * Q), C, ?_, fun w hw => ?_⟩
  · intro l hl X hX
    obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.mp hl
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hX
    exact mul_mul_mem_lieSet_of_mem_UJset_of_mem_lieSet hQ hR hQR hRQ (hS l₀ hl₀ Y hY)
  · have h1 := hb (σ Q w) (smoothVec_translate_of_smoothVec hσ hQ hR hQR hRQ hw)
    have e : (S.map fun l => ‖l.foldr (dRep σ) (σ Q w)‖).sum =
        ((S.map (List.map fun X => R * X * Q)).map fun l => ‖l.foldr (dRep σ) w‖).sum := by
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro l hl
      simp only [Function.comp_apply]
      rw [foldr_dRep_translate_eq_translate_foldr_conj hσ hQ hR hQR hRQ l (hS l hl), hσ.2.1 Q hQ]
    show ‖ℓ (σ Q w)‖ ≤ _
    rw [← e]
    exact h1

theorem coef_frame_change : GlobalTheory.Published.DiscreteSeriesUpqUnique → ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ),
    Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
    IsDS ε lam σ → IsDS ε lam σ' →
    ∀ (P P' G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → IsUnit P' → Pᴴ * Formalism.REAL.Jm ε * P = G →
      P'ᴴ * Formalism.REAL.Jm ε * P' = G →
    ∀ (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (ℓ : H' →ₗ[ℂ] ℂ) (v : H'), Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ' ℓ →
      SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ' v → (∀ y ∈ UJset ε, F (P'⁻¹ * y * P') = ℓ (σ' y v)) →
    ∃ (ℓ' : H →ₗ[ℂ] ℂ) (v' : H), Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ ℓ' ∧
      SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ v' ∧ ∀ y ∈ UJset ε, F (P⁻¹ * y * P) = ℓ' (σ y v') := by
  intro hDS n ε lam hlam H H' _ _ _ _ σ σ' hσ hσ' P P' G hP hP' hG hG' F ℓ v hℓ hv hF
  obtain ⟨U, hU⟩ := hDS n ε lam hlam H' H σ' σ hσ' hσ
  have hdP := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hdP' := (Matrix.isUnit_iff_isUnit_det P').mp hP'
  have hQ : P' * P⁻¹ ∈ UJset ε := mul_inv_mem_UJset_of_conjTranspose_Jm_eq hP hG hG'
  have hR : P * P'⁻¹ ∈ UJset ε := mul_inv_mem_UJset_of_conjTranspose_Jm_eq hP' hG' hG
  have hQR : P' * P⁻¹ * (P * P'⁻¹) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc P⁻¹ P, Matrix.nonsing_inv_mul _ hdP, Matrix.one_mul,
      Matrix.mul_nonsing_inv _ hdP']
  have hRQ : P * P'⁻¹ * (P' * P⁻¹) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc P'⁻¹ P', Matrix.nonsing_inv_mul _ hdP', Matrix.one_mul,
      Matrix.mul_nonsing_inv _ hdP]
  have hσ'U : IsURepOn (UJset ε) σ' := hσ'.2.2.1
  refine ⟨(ℓ ∘ₗ (σ' (P' * P⁻¹) : H' →ₗ[ℂ] H')) ∘ₗ (U.symm.toLinearEquiv : H →ₗ[ℂ] H'),
    U (σ' (P * P'⁻¹) v), ?_, ?_, ?_⟩
  · exact sobCont_map U hU (sobCont_comp_translate_of_sobCont hσ'U hQ hR hQR hRQ hℓ)
  · exact smooth_map U hU (smoothVec_translate_of_smoothVec hσ'U hR hQ hRQ hQR hv)
  · intro y hy
    have hy' : P' * P⁻¹ * y * (P * P'⁻¹) ∈ UJset ε := mul_mem_UH_Hpk' (mul_mem_UH_Hpk' hQ hy) hR
    have hm : P'⁻¹ * (P' * P⁻¹ * y * (P * P'⁻¹)) * P' = P⁻¹ * y * P := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P'⁻¹ P', Matrix.nonsing_inv_mul _ hdP', Matrix.one_mul, Matrix.mul_one]
    rw [← hm, hF _ hy']
    show ℓ (σ' (P' * P⁻¹ * y * (P * P'⁻¹)) v) =
      ℓ (σ' (P' * P⁻¹) (U.symm (σ y (U (σ' (P * P'⁻¹) v)))))
    rw [symm_intertwines U hU y hy, LinearIsometryEquiv.symm_apply_apply,
      hσ'U.1.2 _ (mul_mem_UH_Hpk' hQ hy) _ hR, hσ'U.1.2 _ hQ _ hy]
    rfl

end GlobalTheory.TypeSum.FrameChange

end
