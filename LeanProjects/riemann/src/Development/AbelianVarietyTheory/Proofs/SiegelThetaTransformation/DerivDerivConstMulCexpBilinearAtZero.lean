import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpace
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.HeatTerm

noncomputable section

theorem diffAt_det {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {N : ℕ}
    (A : X → Matrix (Fin N) (Fin N) ℂ) (x : X)
    (h : ∀ i j, DifferentiableAt ℂ (fun y => A y i j) x) :
    DifferentiableAt ℂ (fun y => (A y).det) x := by
  simp only [Matrix.det_apply']
  refine DifferentiableAt.fun_sum fun σ _ => ?_
  refine DifferentiableAt.const_mul ?_ _
  exact (HasFDerivAt.finsetProd (fun i _ => (h (σ i) i).hasFDerivAt)).differentiableAt

theorem diffAt_inv {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {N : ℕ}
    (A : X → Matrix (Fin N) (Fin N) ℂ) (x : X)
    (h : ∀ i j, DifferentiableAt ℂ (fun y => A y i j) x) (h0 : (A x).det ≠ 0) (i j : Fin N) :
    DifferentiableAt ℂ (fun y => (A y)⁻¹ i j) x := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_apply]
  refine ((diffAt_det A x h).fun_inv h0).fun_mul (diffAt_det _ x fun a b => ?_)
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact differentiableAt_const _
  · exact h a b

def loc {n N : ℕ} (C D Z : Matrix (Fin N) (Fin N) ℂ) (z z' : Matrix (Fin n) (Fin N) ℂ) : ℂ :=
  ((C * Z + D).det ^ n * cexp (2 * Real.pi * I * ∑ k, z' k ⬝ᵥ ((C * Z + D)⁻¹ * C) *ᵥ z k))⁻¹

theorem det_one_add {N : ℕ} (S : Matrix (Fin N) (Fin N) ℂ) (a b : Fin N) (s : ℂ) :
    (1 + S * Matrix.single a b s).det = 1 + s * S b a := by
  have : S * Matrix.single a b s =
      replicateCol Unit (fun i => S i a * s) * replicateRow Unit (Pi.single b (1 : ℂ)) := by
    ext i j
    by_cases hj : j = b
    · subst hj; simp [Matrix.mul_apply, Matrix.single_apply]
    · simp [Matrix.mul_apply, Matrix.single_apply, hj, Ne.symm hj]
  rw [this, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [mul_comm]

theorem inv_one_add {N : ℕ} (S : Matrix (Fin N) (Fin N) ℂ) (a b : Fin N) (s : ℂ)
    (h : 1 + s * S b a ≠ 0) :
    (1 + S * Matrix.single a b s)⁻¹ = 1 - (s / (1 + s * S b a)) • (S * Matrix.single a b 1) := by
  apply Matrix.inv_eq_right_inv
  have h1 : Matrix.single a b s = s • Matrix.single a b (1 : ℂ) := by simp
  have h2 : S * Matrix.single a b (1 : ℂ) * (S * Matrix.single a b 1) =
      S b a • (S * Matrix.single a b 1) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.single a b 1),
      Matrix.single_mul_mul_single, ← Matrix.mul_smul]
    simp
  rw [h1, Matrix.mul_smul]
  generalize S * Matrix.single a b (1 : ℂ) = P at h2
  rw [add_mul, mul_sub, mul_sub, one_mul, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, h2]
  have : s / (1 + s * S b a) + s * (s / (1 + s * S b a) * S b a) = s := by field_simp
  rw [smul_smul, smul_smul, sub_add_sub_comm, ← add_smul, mul_assoc, this]
  simp

theorem quad_single {N : ℕ} (S : Matrix (Fin N) (Fin N) ℂ) (a b : Fin N) (u v : Fin N → ℂ) :
    u ⬝ᵥ (S * Matrix.single a b 1 * S) *ᵥ v = (u ᵥ* S) a * (S *ᵥ v) b := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.single_mulVec]
  simp [dotProduct, Function.update_apply]

theorem loc_Z {n N : ℕ} (C D Z : Matrix (Fin N) (Fin N) ℂ) (z z' : Matrix (Fin n) (Fin N) ℂ)
    (h : (C * Z + D).det ≠ 0) (a b : Fin N) :
    HasDerivAt (fun s : ℂ => loc C D (Z + Matrix.single a b s) z z')
      ((-(n : ℂ) * ((C * Z + D)⁻¹ * C) b a + 2 * Real.pi * I *
        ∑ k, (z' k ᵥ* ((C * Z + D)⁻¹ * C)) a * (((C * Z + D)⁻¹ * C) *ᵥ z k) b) *
        loc C D Z z z') 0 := by
  set M := C * Z + D with hM
  set S := M⁻¹ * C with hS
  have hu : IsUnit M.det := Ne.isUnit h
  have hfac : ∀ s, C * (Z + Matrix.single a b s) + D = M * (1 + S * Matrix.single a b s) := by
    intro s
    rw [Matrix.mul_add M, mul_one, hS, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hu, one_mul, hM, Matrix.mul_add]
    abel
  set q := ∑ k, z' k ⬝ᵥ S *ᵥ z k with hq
  set r := ∑ k, (z' k ᵥ* S) a * (S *ᵥ z k) b with hr
  set c := S b a with hc
  have hl : HasDerivAt (fun s : ℂ => 1 + s * c) c 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const c).const_add 1
  have hev : ∀ᶠ s in 𝓝 (0 : ℂ), 1 + s * c ≠ 0 :=
    hl.continuousAt.eventually_ne (by simp)
  have heq : (fun s : ℂ => loc C D (Z + Matrix.single a b s) z z') =ᶠ[𝓝 0]
      fun s => ((M.det * (1 + s * c)) ^ n *
        cexp (2 * Real.pi * I * (q - s / (1 + s * c) * r)))⁻¹ := by
    filter_upwards [hev] with s hs
    rw [loc, hfac, Matrix.det_mul, det_one_add, Matrix.mul_inv_rev, inv_one_add _ _ _ _ hs,
      Matrix.mul_assoc, ← hS, sub_mul, one_mul, Matrix.smul_mul]
    simp only [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
      quad_single, Finset.sum_sub_distrib, smul_eq_mul, ← Finset.mul_sum]
    rfl
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq
  have h1 := (hl.const_mul M.det).fun_pow n
  have h2 := (((((hasDerivAt_id (0 : ℂ)).fun_div hl (by simp)).mul_const r).const_sub q).const_mul
    (2 * Real.pi * I)).cexp
  have h3 := (h1.fun_mul h2).fun_inv (by simp [h])
  refine HasDerivAt.congr_deriv h3 ?_
  have he := Complex.exp_ne_zero (2 * Real.pi * I * q)
  rw [loc, ← hM, ← hS, ← hq]
  simp only [id, zero_mul, add_zero, mul_one, zero_div, sub_zero, one_mul, one_pow, div_one]
  rcases n with _ | n
  · simp
    field_simp
  · simp only [Nat.add_sub_cancel]
    field_simp
    ring

theorem quad_add {n N : ℕ} (S : Matrix (Fin N) (Fin N) ℂ) (z z' : Matrix (Fin n) (Fin N) ℂ)
    (k : Fin n) (a b : Fin N) (s t : ℂ) :
    ∑ j, (z' + Matrix.single k b t) j ⬝ᵥ S *ᵥ (z + Matrix.single k a s) j =
      ∑ j, z' j ⬝ᵥ S *ᵥ z j + s * (z' k ᵥ* S) a + t * ((S *ᵥ z k) b + s * S b a) := by
  have h : ∀ (j : Fin n) (a : Fin N) (s : ℂ) (w : Matrix (Fin n) (Fin N) ℂ),
      (w + Matrix.single k a s) j = w j + if j = k then Pi.single a s else 0 := by
    intro j a s w
    ext i
    by_cases hj : j = k
    · subst hj; simp [Matrix.single_apply, Pi.single_apply, eq_comm]
    · simp [Matrix.single_apply, hj, Ne.symm hj]
  have h2 : ∀ j, (z' + Matrix.single k b t) j ⬝ᵥ S *ᵥ (z + Matrix.single k a s) j =
      z' j ⬝ᵥ S *ᵥ z j +
        if j = k then s * (z' k ᵥ* S) a + t * ((S *ᵥ z k) b + s * S b a) else 0 := by
    intro j
    rw [h, h]
    by_cases hj : j = k
    · subst hj
      simp only [if_true, Matrix.mulVec_add, add_dotProduct, dotProduct_add, single_dotProduct]
      rw [Matrix.dotProduct_mulVec _ _ (Pi.single a s), dotProduct_single]
      simp [Matrix.mulVec_single]
      ring
    · simp [hj]
  simp only [h2, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem deriv_deriv_const_mul_cexp_bilinear_at_zero (K w q u v c : ℂ) :
    deriv (fun s : ℂ => deriv (fun t : ℂ =>
      K * cexp (w * (q + s * u + t * (v + s * c)))) 0) 0 =
      (w * c + w * w * (u * v)) * (K * cexp (w * q)) := by
  have h1 : ∀ s : ℂ, deriv (fun t : ℂ => K * cexp (w * (q + s * u + t * (v + s * c)))) 0 =
      K * (cexp (w * (q + s * u)) * (w * (v + s * c))) := by
    intro s
    have := ((((((hasDerivAt_id (0 : ℂ)).mul_const (v + s * c)).const_add (q + s * u)).const_mul
      w).cexp).const_mul K).deriv
    simpa using this
  simp only [h1]
  have h2 := (((((hasDerivAt_id (0 : ℂ)).mul_const u).const_add q).const_mul w).cexp)
  have h3 := (((hasDerivAt_id (0 : ℂ)).mul_const c).const_add v).const_mul w
  have := ((h2.fun_mul h3).const_mul K).deriv
  simp only [id] at this
  rw [this]
  simp
  ring

theorem loc_heat {n N : ℕ} (C D Z : Matrix (Fin N) (Fin N) ℂ) (z z' : Matrix (Fin n) (Fin N) ℂ)
    (h : (C * Z + D).det ≠ 0) (a b : Fin N) (K : ℂ) :
    2 * Real.pi * I * deriv (fun s : ℂ => K * loc C D (Z + Matrix.single a b s) z z') 0 =
      ∑ k, deriv (fun s : ℂ => deriv (fun t : ℂ =>
        K * loc C D Z (z + Matrix.single k a s) (z' + Matrix.single k b t)) 0) 0 := by
  rw [((loc_Z C D Z z z' h a b).const_mul K).deriv]
  have h1 : ∀ (w w' : Matrix (Fin n) (Fin N) ℂ), K * loc C D Z w w' =
      (K * ((C * Z + D).det ^ n)⁻¹) *
        cexp (-(2 * Real.pi * I) * ∑ k, w' k ⬝ᵥ ((C * Z + D)⁻¹ * C) *ᵥ w k) := by
    intro w w'
    rw [loc, mul_inv, ← Complex.exp_neg, neg_mul, ← mul_assoc K]
  simp only [h1, quad_add, deriv_deriv_const_mul_cexp_bilinear_at_zero]
  rw [← h1, ← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  generalize (∑ k, (z' k ᵥ* ((C * Z + D)⁻¹ * C)) a * (((C * Z + D)⁻¹ * C) *ᵥ z k) b) = r
  simp
  ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}

omit [NumberField E] [IsCMField E] in
theorem hFac_inv (γ : M2 E N) (Z : CM Ψ N N) (z z' : CM Ψ n N) :
    (hFac Ψ γ Z z z')⁻¹ = ∏ τ : Ψ,
      loc (γ.toBlocks₂₁.map τ.1) (γ.toBlocks₂₂.map τ.1) (Z τ) (z τ) (z' τ) := by
  rw [hFac, ← Finset.prod_inv_distrib]
  rfl

open Classical in
omit [NumberField E] [IsCMField E] in
theorem hFac_inv_at (γ : M2 E N) (Z : CM Ψ N N) (z z' : CM Ψ n N) (τ : Ψ)
    (W : Matrix (Fin N) (Fin N) ℂ) (w w' : Matrix (Fin n) (Fin N) ℂ) :
    (hFac Ψ γ (fun σ => Z σ + if σ = τ then W else 0) (fun σ => z σ + if σ = τ then w else 0)
      (fun σ => z' σ + if σ = τ then w' else 0))⁻¹ =
    (∏ σ ∈ Finset.univ.erase τ,
      loc (γ.toBlocks₂₁.map σ.1) (γ.toBlocks₂₂.map σ.1) (Z σ) (z σ) (z' σ)) *
      loc (γ.toBlocks₂₁.map τ.1) (γ.toBlocks₂₂.map τ.1) (Z τ + W) (z τ + w) (z' τ + w') := by
  rw [hFac_inv, ← Finset.prod_erase_mul _ _ (Finset.mem_univ τ)]
  congr 1
  · refine Finset.prod_congr rfl fun σ hσ => ?_
    simp [(Finset.mem_erase.1 hσ).1]
  · simp

omit [NumberField E] [IsCMField E] in
theorem isHeat_of_det (γ : M2 E N) (h : ∀ Z ∈ Hn Ψ N, ∀ τ, (hDen Ψ γ Z τ).det ≠ 0) :
    IsHeat Ψ (fun Z (z z' : CM Ψ n N) => (hFac Ψ γ Z z z')⁻¹) := by
  classical
  refine ⟨fun p hp => DifferentiableAt.differentiableWithinAt ?_, fun Z hZ z z' τ a b => ?_⟩
  · suffices hs : ∀ τ : Ψ, DifferentiableAt ℂ (fun y : CF Ψ N N × CF Ψ n N × CF Ψ n N =>
        loc (n := n) (γ.toBlocks₂₁.map τ.1) (γ.toBlocks₂₂.map τ.1) (y.1 τ) (y.2.1 τ) (y.2.2 τ)) p by
      refine ((HasFDerivAt.finsetProd (u := Finset.univ)
        (fun τ _ => (hs τ).hasFDerivAt)).differentiableAt).congr_of_eventuallyEq ?_
      exact Filter.Eventually.of_forall fun y => hFac_inv Ψ γ _ _ _
    intro τ
    have hd := h _ hp τ
    have hM : ∀ i j, DifferentiableAt ℂ (fun y : CF Ψ N N × CF Ψ n N × CF Ψ n N =>
        hDen Ψ γ y.1 τ i j) p := by
      intro i j
      show DifferentiableAt ℂ (fun y : CF Ψ N N × CF Ψ n N × CF Ψ n N =>
        ∑ l, γ.toBlocks₂₁.map τ.1 i l * y.1 τ l j + γ.toBlocks₂₂.map τ.1 i j) p
      fun_prop
    have h1 := diffAt_det _ p hM
    have h2 := diffAt_inv _ p hM hd
    refine DifferentiableAt.fun_inv ((h1.fun_pow n).fun_mul (DifferentiableAt.cexp ?_))
      (mul_ne_zero (pow_ne_zero _ hd) (Complex.exp_ne_zero _))
    refine DifferentiableAt.const_mul (DifferentiableAt.fun_sum fun k _ => ?_) _
    simp only [dotProduct, Matrix.mulVec, Matrix.mul_apply]
    refine DifferentiableAt.fun_sum fun i _ => DifferentiableAt.fun_mul (by fun_prop) ?_
    refine DifferentiableAt.fun_sum fun j _ => DifferentiableAt.fun_mul ?_ (by fun_prop)
    exact DifferentiableAt.fun_sum fun l _ => (h2 i l).mul_const _
  · have e1 := fun s : ℂ => hFac_inv_at Ψ γ Z z z' τ (Matrix.single a b s) 0 0
    have e2 := fun (k : Fin n) (s t : ℂ) =>
      hFac_inv_at Ψ γ Z z z' τ 0 (Matrix.single k a s) (Matrix.single k b t)
    simp only [ite_self, add_zero] at e1 e2
    simp only [e1, e2]
    exact loc_heat _ _ _ _ _ (h Z hZ τ) a b _

end

end GlobalTheory.SW.HeatTerm

theorem GlobalTheory.SW.isHeat_hFac_inv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) (n N : ℕ), ∀ γ ∈ UU E N, IsHeat Ψ (fun Z (z z' : CM Ψ n N) => (hFac Ψ γ Z z z')⁻¹) :=
  fun E _ _ _ Ψ _ N γ hγ => GlobalTheory.SW.HeatTerm.isHeat_of_det Ψ γ
    fun Z hZ τ => (((GlobalTheory.SW.unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ).1 τ).1
