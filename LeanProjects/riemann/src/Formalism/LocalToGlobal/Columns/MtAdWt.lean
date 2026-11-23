import Mathlib
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightDualExistence.IncludeInjective
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightDualExistence.AlgDualCore
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ExtremalFactsProofA
import Formalism.LocalToGlobal.Columns.CoefModB
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AlgWtDualUniq
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AlgWtHwUnq

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP MvPolynomial

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

section MtwRat

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

abbrev mtwInc : GL (Fin n) L →* GL (Fin n) (AL L) :=
  Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L)

theorem mtwInc_injective : Function.Injective (mtwInc (L := L) (n := n)) := by
  have hf : Function.Injective (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) := by
    first
      | exact RingHom.injective _
      | exact Algebra.TensorProduct.includeLeft_injective (RingHom.injective _)
      | exact Algebra.TensorProduct.includeLeft_injective (S := L) (RingHom.injective (algebraMap _ _))
  intro a b h
  apply Units.ext
  ext i j
  have hij := congrArg (fun g : GL (Fin n) (AL L) => (g : Matrix (Fin n) (Fin n) (AL L)) i j) h
  first
    | exact hf hij
    | exact hf (by simpa using hij)

theorem mtw_mem (γ : GQ L n) : ((γ : GAf L n) : GL (Fin n) (AL L)) ∈ (GQ0 L n).map mtwInc := by
  first
    | exact Subgroup.mem_subgroupOf.1 γ.2
    | exact γ.2

def mtwRatFun (γ : GQ L n) : GL (Fin n) L := (Subgroup.mem_map.1 (mtw_mem γ)).choose

theorem mtwRatFun_mem (γ : GQ L n) : mtwRatFun γ ∈ GQ0 L n :=
  (Subgroup.mem_map.1 (mtw_mem γ)).choose_spec.1

theorem mtwInc_mtwRatFun (γ : GQ L n) : mtwInc (mtwRatFun γ) = ((γ : GAf L n) : GL (Fin n) (AL L)) :=
  (Subgroup.mem_map.1 (mtw_mem γ)).choose_spec.2

def mtwRat : GQ L n →* GL (Fin n) L where
  toFun := mtwRatFun
  map_one' := mtwInc_injective (by rw [mtwInc_mtwRatFun, map_one]; rfl)
  map_mul' γ δ := mtwInc_injective (by rw [map_mul, mtwInc_mtwRatFun, mtwInc_mtwRatFun, mtwInc_mtwRatFun]; rfl)

theorem mtwRat_mem (γ : GQ L n) : mtwRat γ ∈ GQ0 L n :=
  mtwRatFun_mem γ

theorem mtwRat_eq_of_match (γ : GQ L n) (γ₀ : GL (Fin n) L)
    (h : (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom)) : γ₀ = mtwRat γ := by
  apply mtwInc_injective
  rw [show mtwRat γ = mtwRatFun γ from rfl, mtwInc_mtwRatFun]
  first
    | exact Units.ext h.symm
    | (apply Units.ext; rw [h]; rfl)
    | (apply Units.ext; ext i j; simp [h])

end MtwRat

section Reps

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι]

def mtwEmb (emb : ι → L →+* ℂ) : GL (Fin n) L →* (ι → GL (Fin n) ℂ) :=
  MonoidHom.pi fun τ => Matrix.GeneralLinearGroup.map (emb τ)

def mtwInvTr : (ι → GL (Fin n) ℂ) →* (ι → GL (Fin n) ℂ) where
  toFun g τ := inside₂ ℂ n (g τ)
  map_one' := by
    funext τ
    apply Units.ext
    simp [inside₂]
  map_mul' g h := by
    funext τ
    apply Units.ext
    simp [inside₂, Matrix.transpose_mul]

def mtwConj (emb : ι → L →+* ℂ) : ι → L →+* ℂ := fun τ => ComplexEmbedding.conjugate (emb τ)

def tenRep (emb : ι → L →+* ℂ) (lam : ι → DomWeight n) : Representation ℂ (GQ L n) (VV ℂ lam) :=
  (rhoK lam).comp ((mtwEmb emb).comp mtwRat)

def mtRep (emb : ι → L →+* ℂ) (lam : ι → DomWeight n) : Representation ℂ (GQ L n) (VV ℂ lam) :=
  (rhoK lam).comp (mtwInvTr.comp ((mtwEmb emb).comp mtwRat))

private theorem embedding_complexConj_eq_conjugate (φ : L →+* ℂ) (x : L) :
    φ ((IsCMField.complexConj L : L →+* L) x) = ComplexEmbedding.conjugate φ x := by
  first
    | exact (IsCMField.complexEmbedding_complexConj φ x).trans (ComplexEmbedding.conjugate_coe_eq φ x).symm
    | (rw [ComplexEmbedding.conjugate_coe_eq]; exact IsCMField.complexEmbedding_complexConj φ x)
    | simp [ComplexEmbedding.conjugate_coe_eq]

theorem mtwInvTr_emb (emb : ι → L →+* ℂ) (γ₀ : GL (Fin n) L) (hγ : γ₀ ∈ GQ0 L n) :
    mtwInvTr (mtwEmb emb γ₀) = mtwEmb (mtwConj emb) γ₀ := by
  have hinv : ((γ₀⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      ReciprocityTheory.Aut.conjT (IsCMField.complexConj L : L →+* L) γ₀ :=
    Units.inv_eq_of_mul_eq_one_right hγ
  funext τ
  apply Units.ext
  ext a b
  have e1 : ((mtwInvTr (mtwEmb emb γ₀) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) a b =
      emb τ (((γ₀⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) b a) := rfl
  have e2 : ((mtwEmb (mtwConj emb) γ₀ τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) a b =
      ComplexEmbedding.conjugate (emb τ) ((γ₀ : Matrix (Fin n) (Fin n) L) a b) := rfl
  rw [e1, e2, hinv]
  simp only [ReciprocityTheory.Aut.conjT, Matrix.transpose_apply, Matrix.map_apply]
  exact embedding_complexConj_eq_conjugate (emb τ) _

theorem mtRep_eq_tenRep (emb : ι → L →+* ℂ) (lam : ι → DomWeight n) :
    mtRep emb lam = tenRep (mtwConj emb) lam := by
  apply MonoidHom.ext
  intro γ
  simp only [mtRep, tenRep, MonoidHom.comp_apply]
  rw [mtwInvTr_emb emb _ (mtwRat_mem γ)]

end Reps

section Poly

variable {ι : Type} [Fintype ι] {n : ℕ}

def mtwUniv : Pol ℂ ι n →ₐ[ℂ] MvPolynomial (ι × Fin n × Fin n) (MvPolynomial (ι × Fin n × Fin n) ℂ) :=
  aeval fun v => ∑ b : Fin n, C (X (v.1, b, v.2.1)) * X (v.1, b, v.2.2)

theorem mtwUniv_map (M : ι → Matrix (Fin n) (Fin n) ℂ) (F : Pol ℂ ι n) :
    MvPolynomial.map (eval fun y : ι × Fin n × Fin n => M y.1 y.2.1 y.2.2) (mtwUniv F) =
      Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => (M τ)ᵀ) F := by
  induction F using MvPolynomial.induction_on
  · simp [mtwUniv, Formalism.GradedWeylDivisibility.blockAct, MvPolynomial.algebraMap_apply]
  · rename_i p q hp hq
    simp only [map_add, hp, hq]
  · rename_i p v hp
    have hX : MvPolynomial.map (eval fun y : ι × Fin n × Fin n => M y.1 y.2.1 y.2.2) (mtwUniv (X v)) =
        Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => (M τ)ᵀ) (X v) := by
      simp [mtwUniv, Formalism.GradedWeylDivisibility.blockAct, Matrix.transpose_apply]
    simp only [map_mul, hp, hX]

def mtwCf (ℓ : Pol ℂ ι n →ₗ[ℂ] ℂ)
    (Q : MvPolynomial (ι × Fin n × Fin n) (MvPolynomial (ι × Fin n × Fin n) ℂ)) : MvPolynomial (ι × Fin n × Fin n) ℂ :=
  ∑ m ∈ Q.support, coeff m Q * C (ℓ (monomial m 1))

theorem mtwCf_eval (ℓ : Pol ℂ ι n →ₗ[ℂ] ℂ) (y : ι × Fin n × Fin n → ℂ)
    (Q : MvPolynomial (ι × Fin n × Fin n) (MvPolynomial (ι × Fin n × Fin n) ℂ)) :
    eval y (mtwCf ℓ Q) = ℓ (MvPolynomial.map (eval y) Q) := by
  conv_rhs => rw [Q.as_sum]
  simp only [mtwCf, map_sum, MvPolynomial.map_monomial, map_mul, MvPolynomial.eval_C]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hm : (monomial m (eval y (coeff m Q)) : MvPolynomial (ι × Fin n × Fin n) ℂ) =
      eval y (coeff m Q) • monomial m 1 := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hm, LinearMap.map_smul, smul_eq_mul]

def mtwCoord (lam : ι → DomWeight n) (i : VVIdx lam) : Pol ℂ ι n →ₗ[ℂ] ℂ :=
  (LinearMap.exists_extend ((bVV ℂ lam).coord i)).choose

theorem mtwCoord_spec (lam : ι → DomWeight n) (i : VVIdx lam) (F : VV ℂ lam) :
    mtwCoord lam i (F : Pol ℂ ι n) = (bVV ℂ lam).repr F i := by
  have h := LinearMap.congr_fun (LinearMap.exists_extend ((bVV ℂ lam).coord i)).choose_spec F
  rw [LinearMap.comp_apply, Module.Basis.coord_apply] at h
  exact h

def mtwCoef (lam : ι → DomWeight n) (i j : VVIdx lam) : MvPolynomial (ι × Fin n × Fin n) ℂ :=
  mtwCf (mtwCoord lam i) (mtwUniv (bVVfun ℂ lam j))

theorem mtwCoef_eval (lam : ι → DomWeight n) (M : ι → Matrix (Fin n) (Fin n) ℂ) (i j : VVIdx lam) :
    eval (fun y : ι × Fin n × Fin n => M y.1 y.2.1 y.2.2) (mtwCoef lam i j) =
      mtwCoord lam i (Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => (M τ)ᵀ) (bVVfun ℂ lam j)) := by
  unfold mtwCoef
  rw [mtwCf_eval, mtwUniv_map]

theorem mtw_eval_aeval {σ ρ : Type} (f : σ → MvPolynomial ρ ℂ) (d : ρ → ℂ) (P : MvPolynomial σ ℂ) :
    eval d (aeval f P) = eval (fun x => eval d (f x)) P := by
  induction P using MvPolynomial.induction_on
  · simp [MvPolynomial.algebraMap_eq]
  · rename_i p q hp hq
    simp only [map_add, hp, hq]
  · rename_i p v hp
    simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval_X]

end Poly

section Alg

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι]

def mtwDetP (σ : L →+* ℂ) : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ :=
  (Matrix.of fun a b => (X (σ, a, b) : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ)).det

theorem detPolynomial_eval (σ : L →+* ℂ) (y : (L →+* ℂ) × Fin n × Fin n → ℂ) :
    eval y (mtwDetP σ) = (Matrix.of fun a b => y (σ, a, b)).det := by
  unfold mtwDetP
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp [RingHom.mapMatrix_apply]

theorem mtw_det_conj (σ : L →+* ℂ) (γ₀ : GL (Fin n) L) (hγ : γ₀ ∈ GQ0 L n) :
    ComplexEmbedding.conjugate σ (γ₀ : Matrix (Fin n) (Fin n) L).det = (σ (γ₀ : Matrix (Fin n) (Fin n) L).det)⁻¹ := by
  have hu : (γ₀ : Matrix (Fin n) (Fin n) L) * ReciprocityTheory.Aut.conjT (IsCMField.complexConj L : L →+* L) γ₀ = 1 := hγ
  have hd := congrArg Matrix.det hu
  rw [Matrix.det_mul, Matrix.det_one, ReciprocityTheory.Aut.conjT, Matrix.det_transpose] at hd
  have hm : ((γ₀ : Matrix (Fin n) (Fin n) L).map (IsCMField.complexConj L : L →+* L)).det =
      (IsCMField.complexConj L : L →+* L) (γ₀ : Matrix (Fin n) (Fin n) L).det := (RingHom.map_det _ _).symm
  rw [hm] at hd
  have hs := congrArg σ hd
  rw [map_mul, map_one, embedding_complexConj_eq_conjugate] at hs
  exact eq_inv_of_mul_eq_one_right hs

def mtwTwP (emb : ι → L →+* ℂ) (lam : ι → DomWeight n) : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ :=
  ∏ τ, if 0 ≤ (lam τ).detShift then mtwDetP (emb τ) ^ (lam τ).detShift.toNat
    else mtwDetP (ComplexEmbedding.conjugate (emb τ)) ^ (-(lam τ).detShift).toNat

def mtwPt (γ₀ : Matrix (Fin n) (Fin n) L) : (L →+* ℂ) × Fin n × Fin n → ℂ := fun p => p.1 (γ₀ p.2.1 p.2.2)

theorem twistPolynomial_eval (emb : ι → L →+* ℂ) (lam : ι → DomWeight n) (γ₀ : GL (Fin n) L) (hγ : γ₀ ∈ GQ0 L n) :
    eval (mtwPt (γ₀ : Matrix (Fin n) (Fin n) L)) (mtwTwP emb lam) = detTwK lam (mtwEmb emb γ₀) := by
  have hdet : ∀ σ : L →+* ℂ, eval (mtwPt (γ₀ : Matrix (Fin n) (Fin n) L)) (mtwDetP σ) =
      σ (γ₀ : Matrix (Fin n) (Fin n) L).det := by
    intro σ
    rw [detPolynomial_eval, RingHom.map_det]
    rfl
  unfold mtwTwP detTwK
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hP : detPow ℂ n (mtwEmb emb γ₀ τ) (lam τ).detShift =
      (emb τ (γ₀ : Matrix (Fin n) (Fin n) L).det) ^ (lam τ).detShift := by
    show (((Matrix.GeneralLinearGroup.det (mtwEmb emb γ₀ τ)) ^ (lam τ).detShift : ℂˣ) : ℂ) = _
    rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
    rfl
  rw [hP]
  split_ifs with h
  · rw [map_pow, hdet, ← zpow_natCast, Int.toNat_of_nonneg h]
  · rw [map_pow, hdet, mtw_det_conj (emb τ) γ₀ hγ, ← zpow_natCast, Int.toNat_of_nonneg (by omega), inv_zpow',
      neg_neg]

def tenP (emb : ι → L →+* ℂ) (lam : ι → DomWeight n) (i j : VVIdx lam) : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ :=
  mtwTwP emb lam * aeval (fun y : ι × Fin n × Fin n => (X (emb y.1, y.2.1, y.2.2) : MvPolynomial _ ℂ)) (mtwCoef lam i j)

theorem eval_tensorCoeff (emb : ι → L →+* ℂ) (lam : ι → DomWeight n) (i j : VVIdx lam) (y : (L →+* ℂ) × Fin n × Fin n → ℂ) :
    eval y (tenP emb lam i j) = eval y (mtwTwP emb lam) *
      mtwCoord lam i (Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => (Matrix.of fun a b => y (emb τ, a, b))ᵀ) (bVVfun ℂ lam j)) := by
  have key := mtwCoef_eval lam (fun τ => Matrix.of fun a b => y (emb τ, a, b)) i j
  simp only [Matrix.of_apply] at key
  simp only [tenP, map_mul, mtw_eval_aeval, MvPolynomial.eval_X, key]

theorem tenRep_toMatrix (emb : ι → L →+* ℂ) (lam : ι → DomWeight n) (γ : GQ L n) (γ₀ : GL (Fin n) L)
    (hm : (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom)) :
    LinearMap.toMatrix (bVV ℂ lam) (bVV ℂ lam) (tenRep emb lam γ) =
      fun i j => MvPolynomial.eval (fun p => p.1 ((γ₀ : Matrix _ _ L) p.2.1 p.2.2)) (tenP emb lam i j) := by
  have h0 := mtwRat_eq_of_match γ γ₀ hm
  subst h0
  have hb : ∀ j, ((bVV ℂ lam j : VV ℂ lam) : Pol ℂ ι n) = bVVfun ℂ lam j := by
    intro j
    first
      | simp only [bVV, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply, Module.Basis.span_apply]
      | simp [bVV]
      | rfl
  have htw : MvPolynomial.eval (fun p : (L →+* ℂ) × Fin n × Fin n => p.1 (((mtwRat γ : GL (Fin n) L) :
      Matrix (Fin n) (Fin n) L) p.2.1 p.2.2)) (mtwTwP emb lam) = detTwK lam (mtwEmb emb (mtwRat γ)) :=
    twistPolynomial_eval emb lam _ (mtwRat_mem γ)
  ext i j
  rw [LinearMap.toMatrix_apply, eval_tensorCoeff, htw, ← mtwCoord_spec]
  show mtwCoord lam i (actP lam (mtwEmb emb (mtwRat γ)) ((bVV ℂ lam j : VV ℂ lam) : Pol ℂ ι n)) = _
  rw [hb, actP, LinearMap.smul_apply, LinearMap.map_smul, smul_eq_mul]
  rfl

theorem tenRep_alg (emb : ι → L →+* ℂ) (lam : ι → DomWeight n) : IsAlgWeight L n (tenRep emb lam) := by
  refine ⟨?_, VVIdx lam, inferInstance, inferInstance, bVV ℂ lam, tenP emb lam,
    fun γ γ₀ hm => tenRep_toMatrix emb lam γ γ₀ hm⟩
  first
    | exact FiniteDimensional.of_fintype_basis (bVV ℂ lam)
    | exact Module.Finite.of_basis (bVV ℂ lam)
    | infer_instance

theorem mtRep_alg (emb : ι → L →+* ℂ) (lam : ι → DomWeight n) : IsAlgWeight L n (mtRep emb lam) := by
  rw [mtRep_eq_tenRep]
  exact tenRep_alg _ _

def TenIrr (emb : ι → L →+* ℂ) (lam : ι → DomWeight n) : Prop := (mtRep emb lam).IsIrreducible

def mtWt (emb : ι → L →+* ℂ) (lam : ι → DomWeight n) (h : TenIrr emb lam) : NG.AlgWt L n where
  W := VV ℂ lam
  ρ := mtRep emb lam
  alg := mtRep_alg emb lam
  irr := h

end Alg

section HW

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι]

theorem mtwConj_conj (emb : ι → L →+* ℂ) : mtwConj (mtwConj emb) = emb := by
  funext τ
  first
    | exact ComplexEmbedding.conjugate_conjugate (emb τ)
    | simp [mtwConj]

theorem tenRep_eq_mtRep (emb : ι → L →+* ℂ) (lam : ι → DomWeight n) : tenRep emb lam = mtRep (mtwConj emb) lam := by
  rw [mtRep_eq_tenRep, mtwConj_conj]

def tenWt (emb : ι → L →+* ℂ) (lam : ι → DomWeight n) (h : TenIrr (mtwConj emb) lam) : NG.AlgWt L n where
  W := VV ℂ lam
  ρ := tenRep emb lam
  alg := tenRep_alg emb lam
  irr := by
    rw [tenRep_eq_mtRep]
    exact h

def mtwHw (lam : ι → DomWeight n) : VV ℂ lam :=
  ⟨ten fun τ => extremal ℂ n (lam τ), Submodule.subset_span ⟨fun τ => extremal ℂ n (lam τ),
    fun τ => Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl _ (PI.WGB.natW_anti_A (lam τ)), rfl⟩⟩

private theorem lpMinor_complex_eq (s r m : ℕ) (hr : s ≤ r) (hm : s ≤ m) :
    Formalism.GradedWeylDivisibility.lpMinor ℂ (r := r) (n := m) s hr hm ≠ 0 := by
  have hinj : Function.Injective (fun v : Fin s × Fin s => (Fin.castLE hr v.1, Fin.castLE hm v.2)) := by
    intro a b h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Fin.castLE_injective hr h.1) (Fin.castLE_injective hm h.2)
  have hX : Matrix.det (Matrix.mvPolynomialX (Fin s) (Fin s) ℂ) ≠ 0 := by
    first
      | exact Matrix.det_mvPolynomialX_ne_zero (Fin s) ℂ
      | exact Matrix.det_mvPolynomialX_ne_zero ℂ
      | (intro h
         have h5 := congrArg (MvPolynomial.eval fun v : Fin s × Fin s => (1 : Matrix (Fin s) (Fin s) ℂ) v.1 v.2) h
         rw [RingHom.map_det, map_zero] at h5
         have hm : (MvPolynomial.eval fun v : Fin s × Fin s => (1 : Matrix (Fin s) (Fin s) ℂ) v.1 v.2).mapMatrix
             (Matrix.mvPolynomialX (Fin s) (Fin s) ℂ) = 1 := by
           ext i j
           simp [Matrix.mvPolynomialX]
         rw [hm, Matrix.det_one] at h5
         exact one_ne_zero h5)
  have he : Formalism.GradedWeylDivisibility.lpMinor ℂ (r := r) (n := m) s hr hm =
      rename (fun v : Fin s × Fin s => (Fin.castLE hr v.1, Fin.castLE hm v.2))
        (Matrix.det (Matrix.mvPolynomialX (Fin s) (Fin s) ℂ)) := by
    rw [AlgHom.map_det]
    unfold Formalism.GradedWeylDivisibility.lpMinor
    congr 1
    ext p q
    simp [Matrix.mvPolynomialX]
  rw [he]
  intro h0
  exact hX ((MvPolynomial.rename_injective _ hinj) (h0.trans (map_zero _).symm))

private theorem hw_complex_eq (m : ℕ) (ν : Fin m → ℕ) : Formalism.GradedWeylDivisibility.hw ℂ (r := m) (le_refl m) ν ≠ 0 := by
  unfold Formalism.GradedWeylDivisibility.hw
  rw [Finset.prod_ne_zero_iff]
  intro s _
  exact pow_ne_zero _ (lpMinor_complex_eq _ _ _ _ _)

theorem mtwHw_ne (lam : ι → DomWeight n) : mtwHw lam ≠ 0 := by
  intro h
  have h1 : ((mtwHw lam : VV ℂ lam) : Pol ℂ ι n) = 0 := by
    rw [h]
    rfl
  have h2 : ten (fun τ => extremal ℂ n (lam τ)) ≠ 0 := by
    unfold ten
    rw [Finset.prod_ne_zero_iff]
    intro τ _
    have hinj : Function.Injective (fun v : Fin n × Fin n => (τ, v)) := fun a b hab => (Prod.mk.inj hab).2
    intro h3
    have h4 : extremal ℂ n (lam τ) = 0 := (MvPolynomial.rename_injective _ hinj) (h3.trans (map_zero _).symm)
    exact hw_complex_eq n _ h4
  exact h2 h1

theorem mtw_blockAct_ten (M : ι → Matrix (Fin n) (Fin n) ℂ) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    Formalism.GradedWeylDivisibility.blockAct ℂ M (ten f) = ten fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (M τ) (f τ) := by
  simp only [ten, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h : (Formalism.GradedWeylDivisibility.blockAct ℂ M).comp (Formalism.GradedWeylDivisibility.blockEmb ℂ τ) =
      (Formalism.GradedWeylDivisibility.blockEmb ℂ τ).comp (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (M τ)) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [Formalism.GradedWeylDivisibility.blockAct, Formalism.GradedWeylDivisibility.blockEmb, Formalism.GradedWeylDivisibility.rowAct]
  exact DFunLike.congr_fun h (f τ)

theorem mtw_rowAct_one (f : MvPolynomial (Fin n × Fin n) ℂ) : Formalism.GradedWeylDivisibility.rowAct ℂ (1 : Matrix (Fin n) (Fin n) ℂ) f = f := by
  have h : Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (1 : Matrix (Fin n) (Fin n) ℂ) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X, AlgHom.id_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single v.1]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  rw [h, AlgHom.id_apply]

theorem mtw_sqAct_mul (mu : DomWeight n) (g h : GL (Fin n) ℂ) (f : MvPolynomial (Fin n × Fin n) ℂ) :
    sqAct ℂ n mu (g * h) f = sqAct ℂ n mu g (sqAct ℂ n mu h f) := by
  have hrow : ∀ (A B : Matrix (Fin n) (Fin n) ℂ) (p : MvPolynomial (Fin n × Fin n) ℂ),
      Formalism.GradedWeylDivisibility.rowAct ℂ A (Formalism.GradedWeylDivisibility.rowAct ℂ B p) = Formalism.GradedWeylDivisibility.rowAct ℂ (B * A) p := by
    intro A B p
    have hc : (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) A).comp (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) B) =
        Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (B * A) := by
      apply MvPolynomial.algHom_ext
      intro v
      simp only [AlgHom.comp_apply, Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X, map_sum, map_mul,
        MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, Matrix.mul_apply, Finset.mul_sum,
        Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
      ring
    exact DFunLike.congr_fun hc p
  have hdet : ∀ (a b : GL (Fin n) ℂ) (c : ℤ), detPow ℂ n (a * b) c = detPow ℂ n a c * detPow ℂ n b c := by
    intro a b c
    simp only [detPow, map_mul, mul_zpow, Units.val_mul]
  simp only [sqAct, hdet, map_smul, smul_smul, hrow, Units.val_mul, Matrix.transpose_mul]

theorem mtw_sqAct_upper (mu : DomWeight n) (B : GL (Fin n) ℂ) (hB : (B : Matrix (Fin n) (Fin n) ℂ).BlockTriangular id) :
    sqAct ℂ n mu B (extremal ℂ n mu) = (∏ i, (B : Matrix (Fin n) (Fin n) ℂ) i i ^ mu.w i) • extremal ℂ n mu := by
  have hdet : (B : Matrix (Fin n) (Fin n) ℂ).det = ∏ i, (B : Matrix (Fin n) (Fin n) ℂ) i i :=
    Matrix.det_of_isUpperTriangular hB
  have hne0 : (B : Matrix (Fin n) (Fin n) ℂ).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det B).ne_zero
  have hne : ∀ i, (B : Matrix (Fin n) (Fin n) ℂ) i i ≠ 0 := by
    rw [hdet] at hne0
    exact fun i => (Finset.prod_ne_zero_iff.1 hne0) i (Finset.mem_univ i)
  set t : Fin n → ℂˣ := fun i => Units.mk0 _ (hne i) with ht
  set U : GL (Fin n) ℂ := (diagGL ℂ n t)⁻¹ * B with hU
  have hBU : B = diagGL ℂ n t * U := by rw [hU, mul_inv_cancel_left]
  have hUe : ∀ i j, (U : Matrix (Fin n) (Fin n) ℂ) i j = ((t i)⁻¹ : ℂˣ) * (B : Matrix (Fin n) (Fin n) ℂ) i j := by
    intro i j
    have : ((diagGL ℂ n t)⁻¹ : GL (Fin n) ℂ).val = Matrix.diagonal fun a => (((t a)⁻¹ : ℂˣ) : ℂ) := rfl
    rw [hU, Units.val_mul, this, Matrix.diagonal_mul]
  have hF := PI.WGB.extremalFacts_proof_A n mu
  conv_lhs => rw [hBU]
  rw [mtw_sqAct_mul, hF.1 U (fun i j hij => by rw [hUe, hB hij, mul_zero])
    (fun i => by rw [hUe, ht, Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel₀ (hne i)]), hF.2.1 t]
  congr 1
  rw [Units.coe_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Units.val_zpow_eq_zpow_val, ht, Units.val_mk0]

theorem mtw_evPt_self (τ : L →+* ℂ) (B : GL (Fin n) ℂ) :
    (Matrix.of fun a b => NG.evPt τ B (τ, a, b)) = (B : Matrix (Fin n) (Fin n) ℂ) := by
  ext a b
  simp [NG.evPt]

theorem mtw_evPt_conj (τ : L →+* ℂ) (B : GL (Fin n) ℂ) (h : ComplexEmbedding.conjugate τ ≠ τ) :
    (Matrix.of fun a b => NG.evPt τ B (ComplexEmbedding.conjugate τ, a, b)) = ((B⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ := by
  first
    | (ext a b; simp [NG.evPt, h])
    | (ext a b; simp [NG.evPt, h, Matrix.transpose_apply])

theorem mtw_evPt_other (τ σ : L →+* ℂ) (B : GL (Fin n) ℂ) (h1 : σ ≠ τ) (h2 : σ ≠ ComplexEmbedding.conjugate τ) :
    (Matrix.of fun a b => NG.evPt τ B (σ, a, b)) = (1 : Matrix (Fin n) (Fin n) ℂ) := by
  first
    | (ext a b; simp [NG.evPt, h1, h2]; rfl)
    | (ext a b; simp [NG.evPt, h1, h2]; rw [Matrix.one_apply])
    | (ext a b; simp [NG.evPt, h1, h2, Matrix.one_apply])

end HW

section HW2

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι]

theorem mtw_ten_smul (c : ι → ℂ) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    ten (fun τ => c τ • f τ) = (∏ τ, c τ) • ten f := by
  simp only [ten, Algebra.smul_def, map_mul, AlgHom.commutes, Finset.prod_mul_distrib, map_prod]

theorem twistPolynomial_eval_point (emb : ι → L →+* ℂ) (hinj : Function.Injective emb)
    (hcm : ∀ τ τ', emb τ ≠ ComplexEmbedding.conjugate (emb τ')) (lam : ι → DomWeight n) (τ₀ : ι) (B : GL (Fin n) ℂ) :
    MvPolynomial.eval (NG.evPt (emb τ₀) B) (mtwTwP emb lam) = detPow ℂ n B (lam τ₀).detShift := by
  unfold mtwTwP
  rw [map_prod, Finset.prod_eq_single τ₀]
  · have hc0 : ComplexEmbedding.conjugate (emb τ₀) ≠ emb τ₀ := fun h => hcm τ₀ τ₀ h.symm
    have hP : detPow ℂ n B (lam τ₀).detShift = (B : Matrix (Fin n) (Fin n) ℂ).det ^ (lam τ₀).detShift := by
      show (((Matrix.GeneralLinearGroup.det B) ^ (lam τ₀).detShift : ℂˣ) : ℂ) = _
      rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]
    have hdi : ((B⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det = (B : Matrix (Fin n) (Fin n) ℂ).det⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    rw [hP]
    split_ifs with h
    · rw [map_pow, detPolynomial_eval, mtw_evPt_self, ← zpow_natCast, Int.toNat_of_nonneg h]
    · rw [map_pow, detPolynomial_eval, mtw_evPt_conj (emb τ₀) B hc0, Matrix.det_transpose, hdi, ← zpow_natCast,
        Int.toNat_of_nonneg (by omega), inv_zpow', neg_neg]
  · intro τ _ hτ
    have h1 : emb τ ≠ emb τ₀ := fun h => hτ (hinj h)
    have h2 : emb τ ≠ ComplexEmbedding.conjugate (emb τ₀) := hcm τ τ₀
    have h3 : ComplexEmbedding.conjugate (emb τ) ≠ emb τ₀ := fun h => hcm τ₀ τ h.symm
    have h4 : ComplexEmbedding.conjugate (emb τ) ≠ ComplexEmbedding.conjugate (emb τ₀) := fun h =>
      h1 (by simpa using congrArg ComplexEmbedding.conjugate h)
    split_ifs
    · rw [map_pow, detPolynomial_eval, mtw_evPt_other (emb τ₀) (emb τ) B h1 h2, Matrix.det_one, one_pow]
    · rw [map_pow, detPolynomial_eval, mtw_evPt_other (emb τ₀) _ B h3 h4, Matrix.det_one, one_pow]
  · intro h
    exact absurd (Finset.mem_univ τ₀) h

theorem tenWt_hwAt (emb : ι → L →+* ℂ) (hinj : Function.Injective emb)
    (hcm : ∀ τ τ', emb τ ≠ ComplexEmbedding.conjugate (emb τ')) (lam : ι → DomWeight n)
    (h : TenIrr (mtwConj emb) lam) (τ₀ : ι) : (tenWt emb lam h).HWAt (emb τ₀) (lam τ₀).w := by
  classical
  refine ⟨VVIdx lam, inferInstance, inferInstance, bVV ℂ lam, tenP emb lam,
    fun γ γ₀ hm => tenRep_toMatrix emb lam γ γ₀ hm, ⇑((bVV ℂ lam).repr (mtwHw lam)), ?_, ?_⟩
  · intro hv
    apply mtwHw_ne lam
    apply (bVV ℂ lam).repr.injective
    rw [map_zero]
    exact Finsupp.ext fun i => congrFun hv i
  · intro B hB
    set c : ℂ := detPow ℂ n B (lam τ₀).detShift with hc
    have hc0 : c ≠ 0 := by
      rw [hc, detPow]
      exact Units.ne_zero _
    set P : ℂ := ∏ i, (B : Matrix (Fin n) (Fin n) ℂ) i i ^ (lam τ₀).w i with hP
    have hM : (fun τ => (Matrix.of fun a b => NG.evPt (emb τ₀) B (emb τ, a, b))ᵀ) =
        fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) ℂ)ᵀ else 1 := by
      funext τ
      split_ifs with hτ
      · rw [hτ, mtw_evPt_self]
      · rw [mtw_evPt_other _ _ _ (fun h' => hτ (hinj h')) (hcm τ τ₀), Matrix.transpose_one]
    have hrow : ∀ τ, Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (if τ = τ₀ then (B : Matrix (Fin n) (Fin n) ℂ)ᵀ else 1)
        (extremal ℂ n (lam τ)) = (if τ = τ₀ then c⁻¹ * P else 1) • extremal ℂ n (lam τ) := by
      intro τ
      split_ifs with hτ
      · subst hτ
        have h2 := mtw_sqAct_upper (lam τ) B hB
        unfold sqAct at h2
        rw [← hc, ← hP] at h2
        rw [mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      · rw [mtw_rowAct_one, one_smul]
    have hact : Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) ℂ)ᵀ else 1)
        (mtwHw lam : Pol ℂ ι n) = (c⁻¹ * P) • (mtwHw lam : Pol ℂ ι n) := by
      show Formalism.GradedWeylDivisibility.blockAct ℂ _ (ten fun τ => extremal ℂ n (lam τ)) = _ • ten fun τ => extremal ℂ n (lam τ)
      rw [mtw_blockAct_ten]
      simp only [hrow]
      rw [mtw_ten_smul]
      congr 1
      simp
    have hsum : (∑ j, ((bVV ℂ lam).repr (mtwHw lam) j) • bVVfun ℂ lam j) = (mtwHw lam : Pol ℂ ι n) := by
      have := congrArg Subtype.val ((bVV ℂ lam).sum_repr (mtwHw lam))
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul, bVV_coe] at this
      exact this
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, eval_tensorCoeff, twistPolynomial_eval_point emb hinj hcm lam τ₀ B, hM,
      Pi.smul_apply, smul_eq_mul]
    rw [← hc]
    have hlin : ∑ j, c * mtwCoord lam i (Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) ℂ)ᵀ else 1)
        (bVVfun ℂ lam j)) * (bVV ℂ lam).repr (mtwHw lam) j =
        c * mtwCoord lam i (Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) ℂ)ᵀ else 1)
          (∑ j, ((bVV ℂ lam).repr (mtwHw lam) j) • bVVfun ℂ lam j)) := by
      rw [map_sum, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, map_smul, smul_eq_mul]
      ring
    rw [hlin, hsum, hact, map_smul, smul_eq_mul, mtwCoord_spec, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]

end HW2

section Dual

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι]

theorem mtw_hwAt_of_iso {a b : NG.AlgWt L n} (hab : a.Iso b) {τ : L →+* ℂ} {lam : Fin n → ℤ} (h : a.HWAt τ lam) :
    b.HWAt τ lam := by
  obtain ⟨T, hT⟩ := hab
  delta NG.AlgWt.HWAt at h ⊢
  obtain ⟨ι', i1, i2, bb, P, hP, hrest⟩ := h
  refine ⟨ι', i1, i2, bb.map T, P, fun γ γ₀ hm => ?_, hrest⟩
  rw [← hP γ γ₀ hm]
  ext i j
  simp [LinearMap.toMatrix_apply, ← hT]

theorem mtWt_isDual (emb : ι → L →+* ℂ) (lam : ι → DomWeight n) (h : TenIrr emb lam) (h' : TenIrr (mtwConj emb) lam) :
    (mtWt emb lam h).IsDual (tenWt emb lam h') := by
  refine ⟨pairBK lam, ?_, fun γ x y => ?_⟩
  · intro h0
    apply mtwHw_ne lam
    exact (pairingBNondegenerate_holds ℂ ι n lam).1 (mtwHw lam) fun y => by rw [h0]; rfl
  · show pairBK lam (mtRep emb lam γ x) (tenRep emb lam γ y) = pairBK lam x y
    exact (pairBK_apply lam _ _).trans ((pairingBInvariantK_holds ℂ ι n lam (mtwEmb emb (mtwRat γ)) (x : VV ℂ lam).1
      (y : VV ℂ lam).1).trans (pairBK_apply lam x y).symm)

theorem mtWt_hw_dual (emb : ι → L →+* ℂ) (hinj : Function.Injective emb)
    (hcm : ∀ τ τ', emb τ ≠ ComplexEmbedding.conjugate (emb τ')) (lam : ι → DomWeight n) (h : TenIrr emb lam)
    (h' : TenIrr (mtwConj emb) lam) (τ : ι) (a : NG.AlgWt L n) (lam0 : Fin n → ℤ)
    (hd : (mtWt emb lam h).IsDual a) (hw : a.HWAt (emb τ) lam0) : lam0 = (lam τ).w := by
  have hiso : a.Iso (tenWt emb lam h') := algebraic_weight_dual_unique L n _ a _ hd (mtWt_isDual emb lam h h')
  exact algebraic_weight_highest_unique L n _ (emb τ) lam0 (lam τ).w (mtw_hwAt_of_iso hiso hw) (tenWt_hwAt emb hinj hcm lam h' τ)

end Dual

end Formalism.L2.Col
