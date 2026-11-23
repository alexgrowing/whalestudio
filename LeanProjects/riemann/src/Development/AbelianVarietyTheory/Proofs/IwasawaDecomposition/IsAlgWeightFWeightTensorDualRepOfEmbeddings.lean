import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.AlgWtF

open Formalism.L2.DIV
open scoped Matrix

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K : Type} [Field K]

theorem awf_eval_aeval {σ₁ σ₂ : Type} (f : σ₁ → MvPolynomial σ₂ K) (d : σ₂ → K) (P : MvPolynomial σ₁ K) :
    MvPolynomial.eval d (MvPolynomial.aeval f P) = MvPolynomial.eval (fun x => MvPolynomial.eval d (f x)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p x hp => simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval_X]

def awfPt (γ₀ : Matrix (Fin n) (Fin n) L) : (L →+* K) × Fin n × Fin n → K := fun p => p.1 (γ₀ p.2.1 p.2.2)

def awfLin {κ : Type} [Fintype κ] (e : Module.Basis κ ℚ L) (p : (L →+* K) × Fin n × Fin n) :
    MvPolynomial (κ × Fin n × Fin n) K :=
  ∑ k : κ, MvPolynomial.C (p.1 (e k)) * MvPolynomial.X (k, p.2.1, p.2.2)

theorem awf_emb_eq {κ : Type} [Fintype κ] (e : Module.Basis κ ℚ L) (σ : L →+* K) (x : L) :
    σ x = ∑ k : κ, σ (e k) * ((e.repr x k : ℚ) : K) := by
  conv_lhs => rw [← e.sum_repr x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Rat.smul_def, map_mul, map_ratCast, mul_comm]

theorem isAlgWeightF_of_embPoly {W : Type} [AddCommGroup W] [Module K W] (ρ : Representation K (GQ L n) W)
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K W)
    (Q : ι → ι → MvPolynomial ((L →+* K) × Fin n × Fin n) K)
    (hQ : ∀ γ : GQ L n, LinearMap.toMatrix b b (ρ γ) =
      fun i j => MvPolynomial.eval (awfPt ((ratHom γ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) (Q i j)) :
    NX.IsAlgWeightF L n K ρ := by
  let e := Module.finBasis ℚ L
  refine ⟨Module.Finite.of_basis b, ι, inferInstance, inferInstance, b, _, inferInstance, e,
    fun i j => MvPolynomial.aeval (awfLin e) (Q i j), ?_⟩
  intro γ γ₀ hm
  obtain rfl := ratHom_eq_of_match γ γ₀ hm
  rw [hQ γ]
  ext i j
  rw [awf_eval_aeval]
  refine congrArg (fun f => MvPolynomial.eval f (Q i j)) (funext fun p => ?_)
  simp only [awfLin, awfPt, map_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  exact awf_emb_eq e p.1 _

end Gen

section Poly

variable {ι : Type} [Fintype ι] {n : ℕ} {K : Type} [Field K]

def awfUniv : Pol K ι n →ₐ[K] MvPolynomial (ι × Fin n × Fin n) (MvPolynomial (ι × Fin n × Fin n) K) :=
  MvPolynomial.aeval fun v => ∑ b : Fin n, MvPolynomial.C (MvPolynomial.X (v.1, b, v.2.1)) * MvPolynomial.X (v.1, b, v.2.2)

theorem awfUniv_map (M : ι → Matrix (Fin n) (Fin n) K) (F : Pol K ι n) :
    MvPolynomial.map (MvPolynomial.eval fun y : ι × Fin n × Fin n => M y.1 y.2.1 y.2.2) (awfUniv F) =
      Formalism.GradedWeylDivisibility.blockAct K (fun τ => (M τ)ᵀ) F := by
  have h : (MvPolynomial.map (MvPolynomial.eval fun y : ι × Fin n × Fin n => M y.1 y.2.1 y.2.2)).comp
      (awfUniv (K := K) (ι := ι) (n := n)).toRingHom = (Formalism.GradedWeylDivisibility.blockAct K (n := n) fun τ => (M τ)ᵀ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [awfUniv, Formalism.GradedWeylDivisibility.blockAct]
    · intro v
      simp [awfUniv, Formalism.GradedWeylDivisibility.blockAct, Matrix.transpose_apply]
  exact congrArg (fun f : Pol K ι n →+* Pol K ι n => f F) h

def awfCf (ℓ : Pol K ι n →ₗ[K] K)
    (Q : MvPolynomial (ι × Fin n × Fin n) (MvPolynomial (ι × Fin n × Fin n) K)) : MvPolynomial (ι × Fin n × Fin n) K :=
  ∑ m ∈ Q.support, MvPolynomial.coeff m Q * MvPolynomial.C (ℓ (MvPolynomial.monomial m 1))

theorem awfCf_eval (ℓ : Pol K ι n →ₗ[K] K) (y : ι × Fin n × Fin n → K)
    (Q : MvPolynomial (ι × Fin n × Fin n) (MvPolynomial (ι × Fin n × Fin n) K)) :
    MvPolynomial.eval y (awfCf ℓ Q) = ℓ (MvPolynomial.map (MvPolynomial.eval y) Q) := by
  conv_rhs => rw [Q.as_sum]
  rw [map_sum, map_sum, awfCf, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.map_monomial, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    show MvPolynomial.monomial m (MvPolynomial.eval y (MvPolynomial.coeff m Q)) =
        MvPolynomial.eval y (MvPolynomial.coeff m Q) • (MvPolynomial.monomial m 1 : Pol K ι n) by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], map_smul, smul_eq_mul]

def awfCoord (lam : ι → DomWeight n) (i : VVIdx lam) : Pol K ι n →ₗ[K] K :=
  (LinearMap.exists_extend ((bVV K lam).coord i)).choose

theorem awfCoord_spec (lam : ι → DomWeight n) (i : VVIdx lam) (F : VV K lam) :
    awfCoord lam i (F : Pol K ι n) = (bVV K lam).repr F i := by
  have h := (LinearMap.exists_extend ((bVV K lam).coord i)).choose_spec
  have := LinearMap.congr_fun h F
  simpa [awfCoord, Module.Basis.coord_apply] using this

def awfCoef (lam : ι → DomWeight n) (i j : VVIdx lam) : MvPolynomial (ι × Fin n × Fin n) K :=
  awfCf (awfCoord lam i) (awfUniv (bVVfun K lam j))

theorem awfCoef_eval (lam : ι → DomWeight n) (M : ι → Matrix (Fin n) (Fin n) K) (i j : VVIdx lam) :
    MvPolynomial.eval (fun y : ι × Fin n × Fin n => M y.1 y.2.1 y.2.2) (awfCoef lam i j) =
      awfCoord lam i (Formalism.GradedWeylDivisibility.blockAct K (fun τ => (M τ)ᵀ) (bVVfun K lam j)) := by
  rw [awfCoef, awfCf_eval, awfUniv_map]

end Poly

section Alg

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι] {K : Type} [Field K]

def awfDetP (σ : L →+* K) : MvPolynomial ((L →+* K) × Fin n × Fin n) K :=
  (Matrix.of fun a b => (MvPolynomial.X (σ, a, b) : MvPolynomial ((L →+* K) × Fin n × Fin n) K)).det

theorem awfDetP_eval (σ : L →+* K) (γ₀ : Matrix (Fin n) (Fin n) L) :
    MvPolynomial.eval (awfPt γ₀) (awfDetP σ) = σ γ₀.det := by
  rw [awfDetP, RingHom.map_det, RingHom.map_det]
  congr 1
  ext a b
  simp [awfPt]

theorem awf_det_conj (σ : L →+* K) (γ₀ : GL (Fin n) L) (hγ : γ₀ ∈ GQ0 L n) :
    (σ.comp (IsCMField.complexConj L : L →+* L)) (γ₀ : Matrix (Fin n) (Fin n) L).det =
      (σ (γ₀ : Matrix (Fin n) (Fin n) L).det)⁻¹ := by
  have h1 : ((γ₀ : Matrix (Fin n) (Fin n) L) * conjT (IsCMField.complexConj L : L →+* L) γ₀).det = 1 := by
    rw [show (γ₀ : Matrix (Fin n) (Fin n) L) * conjT (IsCMField.complexConj L : L →+* L) γ₀ = 1 from hγ,
      Matrix.det_one]
  have h2 : ((γ₀ : Matrix (Fin n) (Fin n) L).map (IsCMField.complexConj L : L →+* L)).det =
      (IsCMField.complexConj L : L →+* L) (γ₀ : Matrix (Fin n) (Fin n) L).det := by
    rw [RingHom.map_det]
    rfl
  rw [Matrix.det_mul, conjT, Matrix.det_transpose, h2] at h1
  apply eq_inv_of_mul_eq_one_right
  rw [RingHom.comp_apply, ← map_mul, h1, map_one]

theorem awf_inv_entry (γ₀ : GL (Fin n) L) (hγ : γ₀ ∈ GQ0 L n) (k l : Fin n) :
    ((γ₀⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) k l =
      (IsCMField.complexConj L : L →+* L) ((γ₀ : Matrix (Fin n) (Fin n) L) l k) := by
  have h1 : ((γ₀⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      conjT (IsCMField.complexConj L : L →+* L) (γ₀ : Matrix (Fin n) (Fin n) L) :=
    Units.inv_eq_of_mul_eq_one_right hγ
  rw [h1]
  rfl

def awfTwP (emb : ι → L →+* K) (lam : ι → DomWeight n) : MvPolynomial ((L →+* K) × Fin n × Fin n) K :=
  ∏ τ, if 0 ≤ (lam τ).detShift then awfDetP (emb τ) ^ (lam τ).detShift.toNat
    else awfDetP ((emb τ).comp (IsCMField.complexConj L : L →+* L)) ^ (-(lam τ).detShift).toNat

theorem awfTwP_eval (emb : ι → L →+* K) (lam : ι → DomWeight n) (γ₀ : GL (Fin n) L) (hγ : γ₀ ∈ GQ0 L n) :
    MvPolynomial.eval (awfPt (γ₀ : Matrix (Fin n) (Fin n) L)) (awfTwP emb lam) = detTwK lam (embGLF emb γ₀) := by
  simp only [awfTwP, detTwK, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hd : ((Matrix.GeneralLinearGroup.det (embGLF emb γ₀ τ) : Kˣ) : K) = emb τ (γ₀ : Matrix (Fin n) (Fin n) L).det := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
    rfl
  rw [detPow, Units.val_zpow_eq_zpow_val, hd]
  split_ifs with h
  · rw [map_pow, awfDetP_eval, ← zpow_natCast, Int.toNat_of_nonneg h]
  · rw [map_pow, awfDetP_eval, awf_det_conj _ _ hγ, ← zpow_natCast, Int.toNat_of_nonneg (by omega), inv_zpow', neg_neg]

def awfTenP (emb : ι → L →+* K) (lam : ι → DomWeight n) (i j : VVIdx lam) :
    MvPolynomial ((L →+* K) × Fin n × Fin n) K :=
  awfTwP emb lam * MvPolynomial.aeval
    (fun y : ι × Fin n × Fin n => (MvPolynomial.X (emb y.1, y.2.1, y.2.2) : MvPolynomial ((L →+* K) × Fin n × Fin n) K))
    (awfCoef (K := K) lam i j)

theorem awfTenP_eval (emb : ι → L →+* K) (lam : ι → DomWeight n) (i j : VVIdx lam) (y : (L →+* K) × Fin n × Fin n → K) :
    MvPolynomial.eval y (awfTenP emb lam i j) = MvPolynomial.eval y (awfTwP emb lam) *
      awfCoord lam i (Formalism.GradedWeylDivisibility.blockAct K (fun τ => (Matrix.of fun a b => y (emb τ, a, b))ᵀ) (bVVfun K lam j)) := by
  rw [awfTenP, MvPolynomial.eval_mul, awf_eval_aeval, ← awfCoef_eval]
  simp

theorem tenRepF_toMatrix (emb : ι → L →+* K) (lam : ι → DomWeight n) (γ : GQ L n) :
    LinearMap.toMatrix (bVV K lam) (bVV K lam) (tenRepF emb lam γ) =
      fun i j => MvPolynomial.eval (awfPt ((ratHom γ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) (awfTenP emb lam i j) := by
  classical
  ext i j
  rw [LinearMap.toMatrix_apply, ← awfCoord_spec, awfTenP_eval, awfTwP_eval _ _ _ (ratHom_mem γ)]
  simp only [tenRepF, MonoidHom.comp_apply, rhoK, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_restrict_apply, bVV_coe,
    actP, trAct, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul, smul_eq_mul]
  congr 2

end Alg

section Dual

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι] {K : Type} [Field K]

open Classical in

theorem wtRepF_toMatrix (emb : ι → L →+* K) (lam : ι → DomWeight n) (γ : GQ L n) :
    LinearMap.toMatrix (bVV K lam).dualBasis (bVV K lam).dualBasis (wtRepF emb lam γ) =
      fun i j => MvPolynomial.eval (awfPt ((ratHom γ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))
        (MvPolynomial.rename (fun p : (L →+* K) × Fin n × Fin n =>
          (p.1.comp (IsCMField.complexConj L : L →+* L), p.2.2, p.2.1)) (awfTenP emb lam j i)) := by
  have e : LinearMap.toMatrix (bVV K lam).dualBasis (bVV K lam).dualBasis (wtRepF emb lam γ) =
      (LinearMap.toMatrix (bVV K lam) (bVV K lam) (tenRepF emb lam γ⁻¹))ᵀ := by
    rw [wtRepF, Representation.dual_apply, LinearMap.toMatrix_transpose]
  rw [e, tenRepF_toMatrix]
  ext i j
  show MvPolynomial.eval (awfPt ((ratHom γ⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) (awfTenP emb lam j i) = _
  rw [MvPolynomial.eval_rename]
  refine congrArg (fun f => MvPolynomial.eval f (awfTenP emb lam j i)) (funext fun p => ?_)
  simp only [Function.comp_apply, awfPt, RingHom.comp_apply, map_inv]
  rw [awf_inv_entry _ (ratHom_mem γ)]

end Dual

theorem wtRepF_alg : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K]
    (emb : ι → L →+* K) (lam : ι → DomWeight n), NX.IsAlgWeightF L n K (GlobalTheory.AlgWtF.wtRepF emb lam) := by
  intro L _ _ _ n ι _ K _ emb lam
  classical
  exact isAlgWeightF_of_embPoly _ (bVV K lam).dualBasis _ (wtRepF_toMatrix emb lam)

end GlobalTheory.AlgWtF
