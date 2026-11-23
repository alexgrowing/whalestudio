import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolRepOfIsTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialActionOneMulAdjointStatement

noncomputable section

namespace GlobalTheory.FockHol

open Matrix

section Diff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z : E} {n : ℕ}

theorem diff_prod {ι : Type} (s : Finset ι) {f : ι → E → ℂ} (h : ∀ i ∈ s, DifferentiableAt ℂ (f i) z) :
    DifferentiableAt ℂ (fun w => ∏ i ∈ s, f i w) z := by
  classical
  exact (HasFDerivAt.finset_prod fun i hi => (h i hi).hasFDerivAt).differentiableAt

def EntryDiff (M : E → Matrix (Fin n) (Fin n) ℂ) (z : E) : Prop :=
  ∀ i j, DifferentiableAt ℂ (fun w => M w i j) z

theorem EntryDiff.const (A : Matrix (Fin n) (Fin n) ℂ) : EntryDiff (fun _ : E => A) z :=
  fun _ _ => differentiableAt_const _

theorem EntryDiff.det {M : E → Matrix (Fin n) (Fin n) ℂ} (h : EntryDiff M z) :
    DifferentiableAt ℂ (fun w => (M w).det) z := by
  simp only [Matrix.det_apply']
  refine DifferentiableAt.fun_sum fun σ _ => (differentiableAt_const _).mul ?_
  exact diff_prod _ fun i _ => h _ _

theorem EntryDiff.transpose {M : E → Matrix (Fin n) (Fin n) ℂ} (h : EntryDiff M z) :
    EntryDiff (fun w => (M w)ᵀ) z := fun i j => h j i

theorem EntryDiff.affine {M : E → Matrix (Fin n) (Fin n) ℂ} (h : EntryDiff M z) (A B : Matrix (Fin n) (Fin n) ℂ) :
    EntryDiff (fun w => A * M w + B) z := by
  intro i j
  simp only [Matrix.add_apply, Matrix.mul_apply]
  exact (DifferentiableAt.fun_sum fun k _ => (differentiableAt_const _).mul (h _ _)).add (differentiableAt_const _)

theorem EntryDiff.inv {M : E → Matrix (Fin n) (Fin n) ℂ} (h : EntryDiff M z) (hu : IsUnit (M z)) :
    EntryDiff (fun w => (M w)⁻¹) z := by
  intro i j
  have hd : (M z).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_apply]
  refine (h.det.inv hd).mul (EntryDiff.det ?_)
  intro a b
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact differentiableAt_const _
  · exact h _ _

theorem EntryDiff.zpow_det {M : E → Matrix (Fin n) (Fin n) ℂ} (h : EntryDiff M z) (hd : (M z).det ≠ 0) (x : ℤ) :
    DifferentiableAt ℂ (fun w => (M w).det ^ x) z :=
  h.det.zpow (Or.inl hd)

def CoeffDiff {σ : Type} (F : E → MvPolynomial σ ℂ) (z : E) : Prop :=
  ∀ d, DifferentiableAt ℂ (fun w => (F w).coeff d) z

theorem CoeffDiff.mul {σ : Type} {F G : E → MvPolynomial σ ℂ} (hF : CoeffDiff F z) (hG : CoeffDiff G z) :
    CoeffDiff (fun w => F w * G w) z := by
  classical
  intro d
  simp only [MvPolynomial.coeff_mul]
  exact DifferentiableAt.fun_sum fun k _ => (hF _).mul (hG _)

theorem CoeffDiff.aeval {σ : Type} {F : E → σ → MvPolynomial σ ℂ} (hF : ∀ v, CoeffDiff (fun w => F w v) z)
    (y : MvPolynomial σ ℂ) : CoeffDiff (fun w => MvPolynomial.aeval (F w) y) z := by
  induction y using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.aeval_C]
    exact fun _ => differentiableAt_const _
  | add p q hp hq =>
    intro d
    simp only [map_add, MvPolynomial.coeff_add]
    exact (hp d).add (hq d)
  | mul_X p v hp =>
    simp only [map_mul, MvPolynomial.aeval_X]
    exact hp.mul (hF v)

theorem CoeffDiff.fock {σ : Type} {F : E → MvPolynomial σ ℂ} (hF : CoeffDiff F z) (x : MvPolynomial σ ℂ) :
    DifferentiableAt ℂ (fun w => Formalism.L2.DIV.fockL x (F w)) z := by
  simp only [Formalism.L2.DIV.fockL_apply, Formalism.L2.DIV.fockS]
  exact DifferentiableAt.fun_sum fun k _ => ((differentiableAt_const _).mul (hF _)).mul (differentiableAt_const _)

end Diff

theorem fockL_aniso {σ : Type} (f : MvPolynomial σ ℂ) (h : Formalism.L2.DIV.fockL f f = 0) : f = 0 := by
  by_contra hf
  have e : Formalism.L2.DIV.fockL f f =
      ((∑ m ∈ f.support, ‖f.coeff m‖ ^ 2 * (Formalism.L2.DIV.mfact m : ℝ) : ℝ) : ℂ) := by
    rw [Formalism.L2.DIV.fockL_apply]
    unfold Formalism.L2.DIV.fockS
    push_cast
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Complex.conj_mul']
    rfl
  rw [e, Complex.ofReal_eq_zero] at h
  refine ne_of_gt (Finset.sum_pos (fun m hm => mul_pos (pow_pos (norm_pos_iff.mpr
    (MvPolynomial.mem_support_iff.mp hm)) 2) ?_) (MvPolynomial.support_nonempty.mpr hf)) h
  exact_mod_cast Finset.prod_pos fun k _ => Nat.factorial_pos _

section KC

open GlobalTheory.Dec GlobalTheory.JointHarm Formalism.REAL

variable {m : ℕ} {ε : Fin m → Bool}

theorem Jm_mul_self : Jm ε * Jm ε = 1 := by
  rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp

theorem detPlus_mul_detMinus {k : Matrix (Fin m) (Fin m) ℂ} (hk : k ∈ KC ε) : detP ε k * detM ε k = k.det := by
  rw [detP, detM, ← Matrix.det_mul]
  congr 1
  have h1 := Jm_mul_self (ε := ε)
  have h2 : k * Jm ε = Jm ε * k := hk.2
  have h3 : ∀ x, Jm ε * (Jm ε * x) = x := fun x => by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have h4 : ∀ x, k * (Jm ε * x) = Jm ε * (k * x) := fun x => by rw [← Matrix.mul_assoc, h2, Matrix.mul_assoc]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one, h1, h2, h3, h4]
  module

theorem det_ne {k : Matrix (Fin m) (Fin m) ℂ} (hk : IsUnit k) : k.det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).1 hk).ne_zero

theorem one_mem_KC : (1 : Matrix (Fin m) (Fin m) ℂ) ∈ KC ε := ⟨isUnit_one, by simp⟩

theorem invT_mem_KC {k : Matrix (Fin m) (Fin m) ℂ} (hk : k ∈ KC ε) : (k⁻¹)ᵀ ∈ KC ε := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hk.1
  refine ⟨(Matrix.isUnit_transpose _).2 (Matrix.isUnit_nonsing_inv_iff.2 hk.1), ?_⟩
  have hJ : (Jm ε)ᵀ = Jm ε := Matrix.diagonal_transpose _
  have h2 : k * Jm ε = Jm ε * k := hk.2
  have : Jm ε * k⁻¹ = k⁻¹ * Jm ε := by
    calc Jm ε * k⁻¹ = k⁻¹ * (k * Jm ε) * k⁻¹ := by rw [Matrix.nonsing_inv_mul_cancel_left _ _ hd]
      _ = k⁻¹ * Jm ε := by rw [h2, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hd]
  rw [← hJ, ← Matrix.transpose_mul, ← Matrix.transpose_mul, this]

theorem mulSingle_mem_KC {ι : Type} [DecidableEq ι] {ε : ι → Fin m → Bool} {τ : ι} {g : Matrix (Fin m) (Fin m) ℂ}
    (hg : g ∈ KC (ε τ)) (τ' : ι) : (Pi.mulSingle τ g : ι → Matrix (Fin m) (Fin m) ℂ) τ' ∈ KC (ε τ') := by
  by_cases h : τ' = τ
  · subst h; simpa using hg
  · simpa [h] using one_mem_KC

theorem mulSingle_conjTranspose {ι : Type} [DecidableEq ι] (τ τ' : ι) (g : Matrix (Fin m) (Fin m) ℂ) :
    ((Pi.mulSingle τ g : ι → Matrix (Fin m) (Fin m) ℂ) τ')ᴴ =
      (Pi.mulSingle τ gᴴ : ι → Matrix (Fin m) (Fin m) ℂ) τ' := by
  by_cases h : τ' = τ
  · subst h; simp
  · simp [h]

theorem entryDiff_mulSingle {ι : Type} [DecidableEq ι] (τ τ' : ι) (z : Fin m → Fin m → ℂ) :
    EntryDiff (fun g : Fin m → Fin m → ℂ => (Pi.mulSingle τ (Matrix.of g) : ι → Matrix (Fin m) (Fin m) ℂ) τ') z := by
  by_cases h : τ' = τ
  · subst h
    intro i j
    simp only [Pi.mulSingle_eq_same, Matrix.of_apply]
    fun_prop
  · simp only [Pi.mulSingle_eq_of_ne h]
    exact EntryDiff.const _

open scoped Classical in

theorem isHolFam_of {ι P : Type} [AddCommGroup P] [Module ℂ P] {ε : ι → Fin m → Bool}
    {B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ} {ϖ : (ι → Matrix (Fin m) (Fin m) ℂ) → Module.End ℂ P}
    (h0 : ∀ x, B x x = 0 → x = 0) (h1 : ϖ 1 = 1)
    (hm : ∀ a b, (∀ τ, a τ ∈ KC (ε τ)) → (∀ τ, b τ ∈ KC (ε τ)) → ϖ (a * b) = ϖ a * ϖ b)
    (ha : ∀ a, (∀ τ, a τ ∈ KC (ε τ)) → ∀ x y, B (ϖ a x) y = B x (ϖ (fun τ => (a τ)ᴴ) y))
    (hd : ∀ (a : (Fin m → Fin m → ℂ) → ι → Matrix (Fin m) (Fin m) ℂ) (z : Fin m → Fin m → ℂ),
      (∀ τ, a z τ ∈ KC (ε τ)) → (∀ τ, EntryDiff (fun w => a w τ) z) → ∀ x y,
        DifferentiableAt ℂ (fun w => B x (ϖ (a w) y)) z) :
    IsHolFam ε B ϖ := by
  refine ⟨h0, h1, hm, fun τ => ⟨h0, ?_, fun a ha' b hb => ?_, fun g hg x y => ?_, fun x y z hz => ?_⟩⟩
  · simp only [Pi.mulSingle_one, h1]
  · simp only [Pi.mulSingle_mul]
    exact hm _ _ (mulSingle_mem_KC ha') (mulSingle_mem_KC hb)
  · rw [ha _ (mulSingle_mem_KC hg)]
    simp only [mulSingle_conjTranspose]
  · exact (hd (fun g => Pi.mulSingle τ (Matrix.of g)) z (mulSingle_mem_KC hz)
      (fun τ' => entryDiff_mulSingle τ τ' z) x y).differentiableWithinAt

end KC

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical

theorem fact_diff {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z : E} {D : D7} {m n : ℕ}
    (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ)
    {k : E → D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ} {u : E → D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ}
    (hk : ∀ τ, k z τ ∈ GlobalTheory.Dec.KC (ε τ)) (hu : ∀ τ, IsUnit (u z τ))
    (dk : ∀ τ, EntryDiff (fun w => k w τ) z) (du : ∀ τ, EntryDiff (fun w => u w τ) z) (x y : PolF D m n) :
    DifferentiableAt ℂ (fun w => fockL x (fact ε x₁ x₂ x₃ (k w) (u w) y)) z := by
  simp only [fact, LinearMap.smul_apply, map_smul, smul_eq_mul, AlgHom.toLinearMap_apply]
  refine DifferentiableAt.mul ?_ (CoeffDiff.fock (CoeffDiff.aeval (fun v => ?_) y) x)
  · unfold fchar
    refine diff_prod _ fun τ _ => ?_
    have h := det_ne (hk τ).1
    rw [← detPlus_mul_detMinus (hk τ)] at h
    exact ((((dk τ).affine _ _).zpow_det (left_ne_zero_of_mul h) _).mul
      (((dk τ).affine _ _).zpow_det (right_ne_zero_of_mul h) _)).mul ((du τ).zpow_det (det_ne (hu τ)) _)
  · intro d
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
    refine DifferentiableAt.fun_sum fun a _ => DifferentiableAt.fun_sum fun b _ =>
      DifferentiableAt.mul ?_ (differentiableAt_const _)
    split_ifs
    · exact (dk _ _ _).mul ((du _).inv (hu _) _ _)
    · exact ((dk _).inv (hk _).1 _ _).mul (du _ _ _)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem main : ∀ (D : D7) (m n : ℕ) (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ),
    IsHolFam ε fockL (factK n ε x₁ x₂ x₃) ∧ IsHolFam (fun _ => allPos n) fockL (factU (n := n) ε x₁ x₂ x₃) := by
  intro D m n ε x₁ x₂ x₃
  obtain ⟨h1, hm, ha⟩ := GlobalTheory.T.fockPolynomialAction_one_mul_adjoint D m n ε x₁ x₂ x₃
  have hU : ∀ τ, IsUnit ((1 : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) τ) := fun _ => isUnit_one
  have hK : ∀ τ, (1 : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) τ ∈ GlobalTheory.Dec.KC (ε τ) := fun _ => one_mem_KC
  constructor
  · refine isHolFam_of fockL_aniso ?_ (fun a b ha' hb => ?_) (fun a ha' x y => ?_) (fun a z hz da x y => ?_)
    · rw [← h1, factK]
      congr 1
      funext τ
      simp
    · rw [factK, factK, factK, ← hm _ _ _ _ (fun τ => invT_mem_KC (ha' τ)) (fun τ => invT_mem_KC (hb τ)) hU hU,
        mul_one]
      congr 1
      funext τ
      simp [Matrix.mul_inv_rev]
    · rw [factK, factK, ha _ _ (fun τ => invT_mem_KC (ha' τ)) hU]
      have e1 : (fun τ => (((a τ)⁻¹)ᵀ)ᴴ) = fun τ => (((a τ)ᴴ)⁻¹)ᵀ := by
        funext τ
        rw [← Matrix.conjTranspose_nonsing_inv]
        ext i j
        simp
      have e2 : (fun τ => ((1 : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) τ)ᴴ) = 1 := by
        funext τ
        simp
      rw [e1, e2]
    · exact fact_diff ε x₁ x₂ x₃ (k := fun w τ => ((a w τ)⁻¹)ᵀ) (u := fun _ => 1)
        (fun τ => invT_mem_KC (hz τ)) hU (fun τ => ((da τ).inv (hz τ).1).transpose)
        (fun τ => EntryDiff.const _) x y
  · refine isHolFam_of fockL_aniso h1 (fun a b ha' hb => ?_) (fun a ha' x y => ?_) (fun a z hz da x y => ?_)
    · rw [factU, factU, factU, ← hm _ _ _ _ hK hK (fun τ => (ha' τ).1) (fun τ => (hb τ).1), mul_one]
    · rw [factU, factU, ha _ _ hK (fun τ => (ha' τ).1)]
      have e2 : (fun τ => ((1 : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) τ)ᴴ) = 1 := by
        funext τ
        simp
      rw [e2]
    · exact fact_diff ε x₁ x₂ x₃ (k := fun _ => 1) (u := a) hK (fun τ => (hz τ).1)
        (fun τ => EntryDiff.const _) da x y

end GlobalTheory.FockHol

end
