import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ExtremalFactsProofA

noncomputable section

open MvPolynomial NumberField ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

namespace GlobalTheory.AlgWtF.DDHw

section Extremal

variable (K : Type) [Field K]

theorem rowAct_X (r n : ℕ) (M : Matrix (Fin r) (Fin r) K) (v : Fin r × Fin n) :
    Formalism.GradedWeylDivisibility.rowAct K M (X v) = ∑ b : Fin r, C (M v.1 b) * X (b, v.2) := by
  simp [Formalism.GradedWeylDivisibility.rowAct]

theorem rowAct_lpMinor (n : ℕ) (M : Matrix (Fin n) (Fin n) K) (hM : ∀ i j, i < j → M i j = 0)
    (hd : ∀ i, M i i = 1) (s : ℕ) (hs : s ≤ n) :
    Formalism.GradedWeylDivisibility.rowAct K (n := n) M (Formalism.GradedWeylDivisibility.lpMinor K s hs hs) = Formalism.GradedWeylDivisibility.lpMinor K s hs hs := by
  unfold Formalism.GradedWeylDivisibility.lpMinor
  rw [AlgHom.map_det, AlgHom.mapMatrix_apply]
  have hmat : (Matrix.of fun p q : Fin s =>
      (X (Fin.castLE hs p, Fin.castLE hs q) : MvPolynomial (Fin n × Fin n) K)).map
        (Formalism.GradedWeylDivisibility.rowAct K (n := n) M) =
      (Matrix.of fun p b : Fin s => (C (M (Fin.castLE hs p) (Fin.castLE hs b)) :
        MvPolynomial (Fin n × Fin n) K)) *
      Matrix.of fun p q : Fin s => (X (Fin.castLE hs p, Fin.castLE hs q) : MvPolynomial (Fin n × Fin n) K) := by
    ext p q
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply]
    rw [rowAct_X]
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map (Fin.castLEEmb hs))), Finset.sum_map]
    · rfl
    · intro b _ hb
      have hbs : s ≤ b.val := by
        by_contra hlt
        apply hb
        exact Finset.mem_map.mpr ⟨⟨b.val, by omega⟩, Finset.mem_univ _, Fin.ext (by simp)⟩
      simp only
      rw [hM _ _ (by rw [Fin.lt_def]; simp; omega), map_zero, zero_mul]
  have hL : (Matrix.of fun p b : Fin s => (C (M (Fin.castLE hs p) (Fin.castLE hs b)) :
        MvPolynomial (Fin n × Fin n) K)).IsLowerTriangular := by
    intro i j hij
    simp only [Matrix.of_apply]
    rw [hM _ _ (by rw [Fin.lt_def]; simpa using hij), map_zero]
  rw [hmat, Matrix.det_mul, Matrix.det_of_isLowerTriangular _ hL]
  simp [hd]

theorem rowAct_hw (n : ℕ) (M : Matrix (Fin n) (Fin n) K) (hM : ∀ i j, i < j → M i j = 0)
    (hd : ∀ i, M i i = 1) (ν : Fin n → ℕ) :
    Formalism.GradedWeylDivisibility.rowAct K (n := n) M (Formalism.GradedWeylDivisibility.hw K le_rfl ν) = Formalism.GradedWeylDivisibility.hw K le_rfl ν := by
  unfold Formalism.GradedWeylDivisibility.hw
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, rowAct_lpMinor K n M hM hd]

theorem det_unitri (n : ℕ) (g : GL (Fin n) K) (hl : ∀ i j, j < i → g i j = 0) (hd : ∀ i, g i i = 1) :
    Matrix.GeneralLinearGroup.det g = 1 := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular]
  · simp [hd]
  · intro i j hij
    exact hl i j hij

theorem sqAct_unitri (n : ℕ) (mu : DomWeight n) (g : GL (Fin n) K) (hl : ∀ i j, j < i → g i j = 0)
    (hd : ∀ i, g i i = 1) : sqAct K n mu g (extremal K n mu) = extremal K n mu := by
  unfold sqAct detPow extremal
  rw [det_unitri K n g hl hd, one_zpow, Units.val_one, one_smul]
  apply rowAct_hw
  · intro i j hij
    simp only [Matrix.transpose_apply]
    exact hl j i hij
  · intro i
    simp only [Matrix.transpose_apply]
    exact hd i

theorem sqAct_diag (n : ℕ) (mu : DomWeight n) (t : Fin n → Kˣ) :
    sqAct K n mu (diagGL K n t) (extremal K n mu) = ((∏ j, t j ^ mu.w j : Kˣ) : K) • extremal K n mu := by
  unfold sqAct detPow extremal
  have hdiag : ((diagGL K n t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose =
      Matrix.diagonal fun a => (t a : K) := by
    simp [diagGL]
  rw [hdiag, Formalism.GradedWeylDivisibility.rowActDiagWeight K n n _ _ _
    (Formalism.GradedWeylDivisibility.hwRowWeight K n n le_rfl mu.natW (PI.WGB.natW_anti_A mu)), smul_smul]
  congr 1
  have hdet : Matrix.GeneralLinearGroup.det (diagGL K n t) = ∏ a, t a := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, diagGL, Matrix.det_diagonal]
  have hrow : ∀ a : Fin n, Formalism.GradedWeylDivisibility.rowNu (r := n) mu.natW a = mu.natW a := by
    intro a
    simp [Formalism.GradedWeylDivisibility.rowNu]
  simp only [hrow, hdet]
  have key : (∏ a, t a) ^ mu.detShift * ∏ a, t a ^ ((mu.natW a : ℕ) : ℤ) = ∏ a, t a ^ mu.w a := by
    rw [← Finset.prod_zpow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← zpow_add, add_comm, PI.WGB.natW_add_A]
  rw [← key, Units.val_mul, Units.coe_prod]
  simp [zpow_natCast]

theorem sqAct_mul (n : ℕ) (mu : DomWeight n) (g h : GL (Fin n) K) (f : MvPolynomial (Fin n × Fin n) K) :
    sqAct K n mu (g * h) f = sqAct K n mu g (sqAct K n mu h f) := by
  have hm : Formalism.GradedWeylDivisibility.rowAct K (n := n) ((g * h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ f =
      Formalism.GradedWeylDivisibility.rowAct K (n := n) (g : Matrix (Fin n) (Fin n) K)ᵀ
        (Formalism.GradedWeylDivisibility.rowAct K (n := n) (h : Matrix (Fin n) (Fin n) K)ᵀ f) := by
    have := congrArg (fun φ => φ f) (Formalism.GradedWeylDivisibility.rowActMul K n n ((g : Matrix (Fin n) (Fin n) K)ᵀ)
      ((h : Matrix (Fin n) (Fin n) K)ᵀ))
    simp only [AlgHom.comp_apply] at this
    rw [this, Units.val_mul, Matrix.transpose_mul]
  unfold sqAct
  rw [hm, map_smul, smul_smul]
  congr 1
  simp only [detPow, map_mul, mul_zpow, Units.val_mul]

theorem sqAct_upper (n : ℕ) (mu : DomWeight n) (B : GL (Fin n) K)
    (hB : (B : Matrix (Fin n) (Fin n) K).BlockTriangular id) :
    sqAct K n mu B (extremal K n mu) = (∏ i, (B : Matrix (Fin n) (Fin n) K) i i ^ mu.w i) • extremal K n mu := by
  have hdet : (B : Matrix (Fin n) (Fin n) K).det = ∏ i, (B : Matrix (Fin n) (Fin n) K) i i :=
    Matrix.det_of_isUpperTriangular hB
  have hne0 : (B : Matrix (Fin n) (Fin n) K).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det B).ne_zero
  have hne : ∀ i, (B : Matrix (Fin n) (Fin n) K) i i ≠ 0 := by
    rw [hdet] at hne0
    exact fun i => (Finset.prod_ne_zero_iff.1 hne0) i (Finset.mem_univ i)
  set t : Fin n → Kˣ := fun i => Units.mk0 _ (hne i) with ht
  set U : GL (Fin n) K := (diagGL K n t)⁻¹ * B with hU
  have hBU : B = diagGL K n t * U := by rw [hU, mul_inv_cancel_left]
  have hUe : ∀ i j, (U : Matrix (Fin n) (Fin n) K) i j = ((t i)⁻¹ : Kˣ) * (B : Matrix (Fin n) (Fin n) K) i j := by
    intro i j
    have : ((diagGL K n t)⁻¹ : GL (Fin n) K).val = Matrix.diagonal fun a => (((t a)⁻¹ : Kˣ) : K) := rfl
    rw [hU, Units.val_mul, this, Matrix.diagonal_mul]
  conv_lhs => rw [hBU]
  rw [sqAct_mul, sqAct_unitri K n mu U (fun i j hij => by rw [hUe, hB hij, mul_zero])
    (fun i => by rw [hUe, ht, Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel₀ (hne i)]), sqAct_diag]
  congr 1
  rw [Units.coe_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Units.val_zpow_eq_zpow_val, ht, Units.val_mk0]

end Extremal

section Poly

variable {ι : Type} [Fintype ι] {n : ℕ} {K : Type} [Field K]

def univ : Pol K ι n →ₐ[K] MvPolynomial (ι × Fin n × Fin n) (MvPolynomial (ι × Fin n × Fin n) K) :=
  aeval fun v => ∑ b : Fin n, C (X (v.1, b, v.2.1)) * X (v.1, b, v.2.2)

theorem univ_map (M : ι → Matrix (Fin n) (Fin n) K) (F : Pol K ι n) :
    MvPolynomial.map (eval fun y : ι × Fin n × Fin n => M y.1 y.2.1 y.2.2) (univ F) =
      Formalism.GradedWeylDivisibility.blockAct K (fun τ => (M τ)ᵀ) F := by
  have h : (MvPolynomial.map (eval fun y : ι × Fin n × Fin n => M y.1 y.2.1 y.2.2)).comp
      (univ (K := K) (ι := ι) (n := n)).toRingHom = (Formalism.GradedWeylDivisibility.blockAct K (n := n) fun τ => (M τ)ᵀ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [univ, Formalism.GradedWeylDivisibility.blockAct]
    · intro v
      simp [univ, Formalism.GradedWeylDivisibility.blockAct, Matrix.transpose_apply]
  exact congrArg (fun f : Pol K ι n →+* Pol K ι n => f F) h

def cf (ℓ : Pol K ι n →ₗ[K] K)
    (Q : MvPolynomial (ι × Fin n × Fin n) (MvPolynomial (ι × Fin n × Fin n) K)) : MvPolynomial (ι × Fin n × Fin n) K :=
  ∑ m ∈ Q.support, coeff m Q * C (ℓ (monomial m 1))

theorem cf_eval (ℓ : Pol K ι n →ₗ[K] K) (y : ι × Fin n × Fin n → K)
    (Q : MvPolynomial (ι × Fin n × Fin n) (MvPolynomial (ι × Fin n × Fin n) K)) :
    eval y (cf ℓ Q) = ℓ (MvPolynomial.map (eval y) Q) := by
  conv_rhs => rw [Q.as_sum]
  rw [map_sum, map_sum, cf, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.map_monomial, eval_mul, eval_C,
    show monomial m (eval y (coeff m Q)) = eval y (coeff m Q) • (monomial m 1 : Pol K ι n) by
      rw [smul_monomial, smul_eq_mul, mul_one], map_smul, smul_eq_mul]

def coord (lam : ι → DomWeight n) (i : VVIdx lam) : Pol K ι n →ₗ[K] K :=
  (LinearMap.exists_extend ((bVV K lam).coord i)).choose

theorem coord_spec (lam : ι → DomWeight n) (i : VVIdx lam) (F : VV K lam) :
    coord lam i (F : Pol K ι n) = (bVV K lam).repr F i := by
  have h := (LinearMap.exists_extend ((bVV K lam).coord i)).choose_spec
  have := LinearMap.congr_fun h F
  simpa [coord, Module.Basis.coord_apply] using this

def coef (lam : ι → DomWeight n) (i j : VVIdx lam) : MvPolynomial (ι × Fin n × Fin n) K :=
  cf (coord lam i) (univ (bVVfun K lam j))

theorem coef_eval (lam : ι → DomWeight n) (M : ι → Matrix (Fin n) (Fin n) K) (i j : VVIdx lam) :
    eval (fun y : ι × Fin n × Fin n => M y.1 y.2.1 y.2.2) (coef lam i j) =
      coord lam i (Formalism.GradedWeylDivisibility.blockAct K (fun τ => (M τ)ᵀ) (bVVfun K lam j)) := by
  rw [coef, cf_eval, univ_map]

theorem eval_aeval' {σ ρ : Type} (f : σ → MvPolynomial ρ K) (d : ρ → K) (P : MvPolynomial σ K) :
    eval d (aeval f P) = eval (fun x => eval d (f x)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p x hp => simp only [map_mul, hp, aeval_X, eval_X]

end Poly

section Alg

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι] {K : Type} [Field K]

abbrev cL (L : Type) [Field L] [NumberField L] [IsCMField L] : L →+* L := (IsCMField.complexConj L : L →+* L)

theorem cL_cL (x : L) : cL L (cL L x) = x := IsCMField.complexConj_apply_apply L x

def detP (σ : L →+* K) : MvPolynomial ((L →+* K) × Fin n × Fin n) K :=
  (Matrix.of fun a b => (X (σ, a, b) : MvPolynomial ((L →+* K) × Fin n × Fin n) K)).det

theorem eval_genericDeterminant (σ : L →+* K) (y : (L →+* K) × Fin n × Fin n → K) :
    eval y (detP (n := n) σ) = (Matrix.of fun a b => y (σ, a, b)).det := by
  rw [detP, RingHom.map_det]
  congr 1
  ext a b
  simp

theorem det_conj (σ : L →+* K) (γ₀ : GL (Fin n) L) (hγ : γ₀ ∈ GQ0 L n) :
    (σ.comp (cL L)) (γ₀ : Matrix (Fin n) (Fin n) L).det = (σ (γ₀ : Matrix (Fin n) (Fin n) L).det)⁻¹ := by
  have h1 : ((γ₀ : Matrix (Fin n) (Fin n) L) * conjT (cL L) γ₀).det = 1 := by
    rw [show (γ₀ : Matrix (Fin n) (Fin n) L) * conjT (cL L) γ₀ = 1 from hγ, Matrix.det_one]
  have h2 : ((γ₀ : Matrix (Fin n) (Fin n) L).map (cL L)).det = (cL L) (γ₀ : Matrix (Fin n) (Fin n) L).det := by
    rw [RingHom.map_det]
    rfl
  rw [Matrix.det_mul, conjT, Matrix.det_transpose, h2] at h1
  apply eq_inv_of_mul_eq_one_right
  rw [RingHom.comp_apply, ← map_mul, h1, map_one]

def twP (emb : ι → L →+* K) (lam : ι → DomWeight n) : MvPolynomial ((L →+* K) × Fin n × Fin n) K :=
  ∏ τ, if 0 ≤ (lam τ).detShift then detP (emb τ) ^ (lam τ).detShift.toNat
    else detP ((emb τ).comp (cL L)) ^ (-(lam τ).detShift).toNat

def pt (γ₀ : Matrix (Fin n) (Fin n) L) : (L →+* K) × Fin n × Fin n → K := fun p => p.1 (γ₀ p.2.1 p.2.2)

theorem detTwistPolynomial_eval_point (emb : ι → L →+* K) (lam : ι → DomWeight n) (γ₀ : GL (Fin n) L) (hγ : γ₀ ∈ GQ0 L n) :
    eval (pt (γ₀ : Matrix (Fin n) (Fin n) L)) (twP emb lam) = detTwK lam (embGLF emb γ₀) := by
  simp only [twP, detTwK, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hσ : ∀ σ : L →+* K, eval (pt (γ₀ : Matrix (Fin n) (Fin n) L)) (detP σ) = σ (γ₀ : Matrix (Fin n) (Fin n) L).det := by
    intro σ
    rw [eval_genericDeterminant, RingHom.map_det]
    rfl
  have hd : ((Matrix.GeneralLinearGroup.det (embGLF emb γ₀ τ) : Kˣ) : K) = emb τ (γ₀ : Matrix (Fin n) (Fin n) L).det := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
    rfl
  rw [detPow, Units.val_zpow_eq_zpow_val, hd]
  split_ifs with h
  · rw [map_pow, hσ, ← zpow_natCast, Int.toNat_of_nonneg h]
  · rw [map_pow, hσ, det_conj _ _ hγ, ← zpow_natCast, Int.toNat_of_nonneg (by omega), inv_zpow', neg_neg]

def tenPF (emb : ι → L →+* K) (lam : ι → DomWeight n) (i j : VVIdx lam) : MvPolynomial ((L →+* K) × Fin n × Fin n) K :=
  twP emb lam * aeval (fun y : ι × Fin n × Fin n => (X (emb y.1, y.2.1, y.2.2) : MvPolynomial _ K)) (coef (K := K) lam i j)

theorem tenPF_eval (emb : ι → L →+* K) (lam : ι → DomWeight n) (i j : VVIdx lam) (y : (L →+* K) × Fin n × Fin n → K) :
    eval y (tenPF emb lam i j) = eval y (twP emb lam) *
      coord lam i (Formalism.GradedWeylDivisibility.blockAct K (fun τ => (Matrix.of fun a b => y (emb τ, a, b))ᵀ) (bVVfun K lam j)) := by
  rw [tenPF, eval_mul, eval_aeval', ← coef_eval]
  simp

theorem tenRepF_toMatrix (emb : ι → L →+* K) (lam : ι → DomWeight n) (γ : GQ L n) (γ₀ : GL (Fin n) L)
    (hm : (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom)) :
    LinearMap.toMatrix (bVV K lam) (bVV K lam) (tenRepF emb lam γ) =
      fun i j => MvPolynomial.eval (fun p => p.1 ((γ₀ : Matrix _ _ L) p.2.1 p.2.2)) (tenPF emb lam i j) := by
  obtain rfl := ratHom_eq_of_match γ γ₀ hm
  ext i j
  rw [LinearMap.toMatrix_apply, ← coord_spec, show (fun p : (L →+* K) × Fin n × Fin n =>
    p.1 (((ratHom γ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2)) = pt (ratHom γ : Matrix (Fin n) (Fin n) L) from rfl,
    tenPF_eval, detTwistPolynomial_eval_point _ _ _ (ratHom_mem γ)]
  simp only [tenRepF, MonoidHom.comp_apply, rhoK, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_restrict_apply, bVV_coe,
    actP, trAct, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul, smul_eq_mul]
  congr 2

end Alg

section HW

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι] {K : Type} [Field K]

def bDD (lam : ι → DomWeight n) [DecidableEq (VVIdx lam)] :
    Module.Basis (VVIdx lam) K (Module.Dual K (Module.Dual K (VV K lam))) :=
  (bVV K lam).dualBasis.dualBasis

theorem dd_toMatrix (emb : ι → L →+* K) (lam : ι → DomWeight n) [DecidableEq (VVIdx lam)] (γ : GQ L n) :
    LinearMap.toMatrix (bDD lam) (bDD lam) ((wtRepF emb lam).dual γ) =
      LinearMap.toMatrix (bVV K lam) (bVV K lam) (tenRepF emb lam γ) := by
  ext i j
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, bDD, Module.Basis.dualBasis_repr]
  simp only [wtRepF, Representation.dual_apply, Module.Dual.transpose_apply, inv_inv, LinearMap.comp_apply,
    Module.Basis.dualBasis_apply, Module.Basis.dualBasis_repr]

def hwV (lam : ι → DomWeight n) : VV K lam :=
  ⟨ten fun τ => extremal K n (lam τ), Submodule.subset_span ⟨fun τ => extremal K n (lam τ),
    fun τ => Formalism.GradedWeylDivisibility.hwMem K n n le_rfl _ (PI.WGB.natW_anti_A (lam τ)), rfl⟩⟩

theorem hwV_ne (lam : ι → DomWeight n) : hwV (K := K) lam ≠ 0 := by
  intro h
  have h' : (ten fun τ => extremal K n (lam τ) : Pol K ι n) = 0 := congrArg Subtype.val h
  rw [ten, Finset.prod_eq_zero_iff] at h'
  obtain ⟨τ, _, hτ⟩ := h'
  have hinj : Function.Injective (Formalism.GradedWeylDivisibility.blockEmb K (k := n) (n := n) τ) :=
    MvPolynomial.rename_injective _ fun a b hab => by simpa using hab
  exact Formalism.GradedWeylDivisibility.hwNe K n n le_rfl _ ((map_eq_zero_iff _ hinj).1 hτ)

theorem blockAct_ten (M : ι → Matrix (Fin n) (Fin n) K) (f : ι → MvPolynomial (Fin n × Fin n) K) :
    Formalism.GradedWeylDivisibility.blockAct K M (ten f) = ten fun τ => Formalism.GradedWeylDivisibility.rowAct K (M τ) (f τ) := by
  simp only [ten, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  exact (Formalism.GradedWeylDivisibility.blockActTensor K K ι n n M).1 τ (f τ)

theorem rowAct_one (f : MvPolynomial (Fin n × Fin n) K) : Formalism.GradedWeylDivisibility.rowAct K (1 : Matrix (Fin n) (Fin n) K) f = f := by
  have : Formalism.GradedWeylDivisibility.rowAct K (n := n) (1 : Matrix (Fin n) (Fin n) K) = AlgHom.id K _ := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [Formalism.GradedWeylDivisibility.rowAct, aeval_X, Matrix.one_apply, AlgHom.id_apply]
    rw [Finset.sum_eq_single v.1]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  rw [this]
  rfl

theorem ten_smul (c : ι → K) (f : ι → MvPolynomial (Fin n × Fin n) K) :
    ten (fun τ => c τ • f τ) = (∏ τ, c τ) • ten f := by
  simp only [ten, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.algHom_C, Finset.prod_mul_distrib, map_prod,
    MvPolynomial.algebraMap_eq]

theorem evPtF_self (c : L →+* L) (τ : L →+* K) (B : GL (Fin n) K) :
    (Matrix.of fun a b => Formalism.L2.NX.evPtF c τ B (τ, a, b)) = (B : Matrix (Fin n) (Fin n) K) := by
  ext a b
  simp [Formalism.L2.NX.evPtF]

theorem evPtF_conj (c : L →+* L) (τ : L →+* K) (B : GL (Fin n) K) (h : τ.comp c ≠ τ) :
    (Matrix.of fun a b => Formalism.L2.NX.evPtF c τ B (τ.comp c, a, b)) = ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ := by
  ext a b
  simp [Formalism.L2.NX.evPtF, h]

theorem evPtF_other (c : L →+* L) (τ σ : L →+* K) (B : GL (Fin n) K) (h1 : σ ≠ τ) (h2 : σ ≠ τ.comp c) :
    (Matrix.of fun a b => Formalism.L2.NX.evPtF c τ B (σ, a, b)) = (1 : Matrix (Fin n) (Fin n) K) := by
  ext a b
  simp [Formalism.L2.NX.evPtF, h1, h2, Matrix.one_apply]

theorem detTwistPolynomial_eval_embeddingPoint (emb : ι → L →+* K) (hd : CMDist emb) (lam : ι → DomWeight n) (τ₀ : ι) (B : GL (Fin n) K) :
    MvPolynomial.eval (Formalism.L2.NX.evPtF (cL L) (emb τ₀) B) (twP emb lam) = detPow K n B (lam τ₀).detShift := by
  obtain ⟨hinj, hcm⟩ := hd
  have hc : ∀ τ, (emb τ).comp (cL L) ≠ emb τ₀ := fun τ h' => hcm τ₀ τ h'.symm
  have hc' : ∀ τ, τ ≠ τ₀ → (emb τ).comp (cL L) ≠ (emb τ₀).comp (cL L) := by
    intro τ hτ h'
    apply hτ
    apply hinj
    ext x
    have := congrArg (fun f : L →+* K => f (cL L x)) h'
    simpa [cL_cL] using this
  simp only [twP, map_prod]
  rw [Finset.prod_eq_single τ₀]
  · split_ifs with he
    · rw [map_pow, eval_genericDeterminant, evPtF_self, detPow, Units.val_zpow_eq_zpow_val,
        Matrix.GeneralLinearGroup.val_det_apply, ← zpow_natCast, Int.toNat_of_nonneg he]
    · rw [map_pow, eval_genericDeterminant, evPtF_conj _ _ _ (hc τ₀), Matrix.det_transpose,
        ← Matrix.GeneralLinearGroup.val_det_apply, map_inv, Units.val_inv_eq_inv_val, detPow,
        Units.val_zpow_eq_zpow_val, ← zpow_natCast, Int.toNat_of_nonneg (by omega), inv_zpow', neg_neg]
  · intro τ _ hτ
    have h1 : emb τ ≠ emb τ₀ := fun h' => hτ (hinj h')
    split_ifs
    · rw [map_pow, eval_genericDeterminant, evPtF_other _ _ _ _ h1 (hcm τ τ₀), Matrix.det_one, one_pow]
    · rw [map_pow, eval_genericDeterminant, evPtF_other _ _ _ _ (hc τ) (hc' τ hτ), Matrix.det_one, one_pow]
  · intro h'
    exact absurd (Finset.mem_univ τ₀) h'

end HW

section Main

theorem dd_hwAt : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K]
    (emb : ι → L →+* K) (lam : ι → DomWeight n), GlobalTheory.AlgWtF.CMDist emb → ∀ τ₀ : ι,
      Formalism.L2.NX.HWAtF (IsCMField.complexConj L : L →+* L) (GlobalTheory.AlgWtF.wtRepF emb lam).dual (emb τ₀) (lam τ₀).w := by
  intro L _ _ _ n ι _ K _ emb lam hd τ₀
  classical
  have hinj := hd.1
  have hcm := hd.2
  refine ⟨VVIdx lam, inferInstance, inferInstance, bDD lam, tenPF emb lam,
    fun γ γ₀ hm => by rw [dd_toMatrix]; exact tenRepF_toMatrix emb lam γ γ₀ hm,
    ⇑((bVV K lam).repr (hwV (K := K) lam)), ?_, ?_⟩
  · intro hv
    apply hwV_ne (K := K) lam
    apply (bVV K lam).repr.injective
    rw [map_zero]
    exact Finsupp.ext fun i => congrFun hv i
  · intro B hB
    set c : K := detPow K n B (lam τ₀).detShift with hc
    have hc0 : c ≠ 0 := by
      rw [hc, detPow]
      exact Units.ne_zero _
    set P : K := ∏ i, (B : Matrix (Fin n) (Fin n) K) i i ^ (lam τ₀).w i with hP
    have hM : (fun τ => (Matrix.of fun a b => Formalism.L2.NX.evPtF (cL L) (emb τ₀) B (emb τ, a, b))ᵀ) =
        fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) K)ᵀ else 1 := by
      funext τ
      split_ifs with hτ
      · rw [hτ, evPtF_self]
      · rw [evPtF_other _ _ _ _ (fun h' => hτ (hinj h')) (hcm τ τ₀), Matrix.transpose_one]
    have hrow : ∀ τ, Formalism.GradedWeylDivisibility.rowAct K (n := n) (if τ = τ₀ then (B : Matrix (Fin n) (Fin n) K)ᵀ else 1)
        (extremal K n (lam τ)) = (if τ = τ₀ then c⁻¹ * P else 1) • extremal K n (lam τ) := by
      intro τ
      split_ifs with hτ
      · subst hτ
        have h2 := sqAct_upper K n (lam τ) B hB
        unfold sqAct at h2
        rw [← hc, ← hP] at h2
        rw [mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      · rw [rowAct_one, one_smul]
    have hact : Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) K)ᵀ else 1)
        ((hwV (K := K) lam : VV K lam) : Pol K ι n) = (c⁻¹ * P) • ((hwV (K := K) lam : VV K lam) : Pol K ι n) := by
      show Formalism.GradedWeylDivisibility.blockAct K _ (ten fun τ => extremal K n (lam τ)) = _ • ten fun τ => extremal K n (lam τ)
      rw [blockAct_ten]
      simp only [hrow]
      rw [ten_smul]
      congr 1
      simp
    have hsum : (∑ j, ((bVV K lam).repr (hwV (K := K) lam) j) • bVVfun K lam j) = ((hwV (K := K) lam : VV K lam) : Pol K ι n) := by
      have := congrArg Subtype.val ((bVV K lam).sum_repr (hwV lam))
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul, bVV_coe] at this
      exact this
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, tenPF_eval, detTwistPolynomial_eval_embeddingPoint emb hd lam τ₀ B, hM,
      Pi.smul_apply, smul_eq_mul]
    rw [← hc]
    have hlin : ∑ j, c * coord lam i (Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) K)ᵀ else 1)
        (bVVfun K lam j)) * (bVV K lam).repr (hwV (K := K) lam) j =
        c * coord lam i (Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) K)ᵀ else 1)
          (∑ j, ((bVV K lam).repr (hwV (K := K) lam) j) • bVVfun K lam j)) := by
      rw [map_sum, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, map_smul, smul_eq_mul]
      ring
    rw [hlin, hsum, hact, map_smul, smul_eq_mul, coord_spec, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]

end Main

end GlobalTheory.AlgWtF.DDHw
