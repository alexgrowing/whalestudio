import Formalism.LocalToGlobal.GlobalTheory.GL6.AdelicFunctionRightTranslateDiamond

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open NumberField IsDedekindDomain Formalism.UG Classical Matrix Formalism.BasicNotions Formalism.L2.Forms
open scoped TensorProduct

section Ext

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def localAdeleSingle (v : HeightOneSpectrum (𝓞 F)) : v.adicCompletion F →ₗ[F] FiniteAdeleRing (𝓞 F) F where
  toFun x := (RestrictedProduct.single (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v x :
    FiniteAdeleRing (𝓞 F) F)
  map_add' x y := by
    apply RestrictedProduct.ext
    intro w
    change Pi.single v (x + y) w = Pi.single v x w + Pi.single v y w
    rw [Pi.single_add]; rfl
  map_smul' c x := by
    apply RestrictedProduct.ext
    intro w
    change Pi.single v (c • x) w = (algebraMap F (w.adicCompletion F) c) * Pi.single v x w
    by_cases h : w = v
    · subst h; simp [Algebra.smul_def]
    · simp [Pi.single_eq_of_ne h]

theorem local_adele_single_same_place (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) : (localAdeleSingle v x) v = x := by
  show RestrictedProduct.single _ v x v = x
  simp

theorem local_adele_single_other_place (v w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v) (x : v.adicCompletion F) : (localAdeleSingle v x) w = 0 := by
  show RestrictedProduct.single _ v x w = 0
  exact RestrictedProduct.single_eq_of_ne _ _ h

theorem local_adele_single_mul (v : HeightOneSpectrum (𝓞 F)) (x y : v.adicCompletion F) :
    localAdeleSingle v (x * y) = localAdeleSingle v x * localAdeleSingle v y := by
  apply RestrictedProduct.ext
  intro w
  change Pi.single v (x * y) w = Pi.single v x w * Pi.single v y w
  by_cases h : w = v
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

def localExtensionTensor (v : HeightOneSpectrum (𝓞 F)) : E ⊗[F] v.adicCompletion F →ₗ[F] E ⊗[F] FiniteAdeleRing (𝓞 F) F :=
  TensorProduct.map LinearMap.id (localAdeleSingle v)

theorem local_extension_tensor_tmul (v : HeightOneSpectrum (𝓞 F)) (x : E) (y : v.adicCompletion F) :
    localExtensionTensor v (x ⊗ₜ y) = x ⊗ₜ localAdeleSingle v y := rfl

theorem proj_local_extension_same_place (v : HeightOneSpectrum (𝓞 F)) (t : E ⊗[F] v.adicCompletion F) :
    prV (E := E) v (localExtensionTensor v t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [local_extension_tensor_tmul]
    simp only [prV, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    congr 1
    exact local_adele_single_same_place v y
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem proj_local_extension_other_place (v w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v) (t : E ⊗[F] v.adicCompletion F) :
    prV (E := E) w (localExtensionTensor v t) = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [local_extension_tensor_tmul]
    simp only [prV, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    have : (evalV F w) (localAdeleSingle v y) = 0 := local_adele_single_other_place v w h y
    rw [this, TensorProduct.tmul_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]

theorem local_extension_tensor_mul (v : HeightOneSpectrum (𝓞 F)) (t t' : E ⊗[F] v.adicCompletion F) :
    localExtensionTensor v (t * t') = localExtensionTensor v t * localExtensionTensor v t' := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    induction t' using TensorProduct.induction_on with
    | zero => simp
    | tmul x' y' =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, local_extension_tensor_tmul, local_extension_tensor_tmul, local_extension_tensor_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        local_adele_single_mul]
    | add a b ha hb => rw [mul_add, map_add, map_add, ha, hb, mul_add]
  | add a b ha hb => rw [add_mul, map_add, map_add, ha, hb, add_mul]

theorem local_extension_mul_incl (v : HeightOneSpectrum (𝓞 F)) (t : E ⊗[F] v.adicCompletion F) (j : E) :
    localExtensionTensor v (t * inclE (F := F) (v.adicCompletion F) j) = localExtensionTensor v t * inclE (F := F) (FiniteAdeleRing (𝓞 F) F) j := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [inclE, Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      local_extension_tensor_tmul]
  | add a b ha hb => rw [add_mul, map_add, map_add, ha, hb, add_mul]

theorem local_extension_conj_comm (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (t : E ⊗[F] v.adicCompletion F) :
    sigR σ (FiniteAdeleRing (𝓞 F) F) (localExtensionTensor v t) = localExtensionTensor v (sigR σ (v.adicCompletion F) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, local_extension_tensor_tmul, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

section Mat

variable {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

def localIdempotent : E ⊗[F] FiniteAdeleRing (𝓞 F) F := localExtensionTensor v 1

def localExtensionMatrix (M : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
  M.map (localExtensionTensor v)

def localDiagMatrix (M : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
  (1 - localIdempotent (E := E) v) • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) + localExtensionMatrix v M

theorem local_idempotent_mul_extension (t : E ⊗[F] v.adicCompletion F) : localIdempotent (E := E) v * localExtensionTensor v t = localExtensionTensor v t := by
  rw [localIdempotent, ← local_extension_tensor_mul, one_mul]

theorem complement_idempotent_mul_extension (t : E ⊗[F] v.adicCompletion F) : (1 - localIdempotent (E := E) v) * localExtensionTensor v t = 0 := by
  rw [sub_mul, one_mul, local_idempotent_mul_extension, sub_self]

theorem complement_local_idempotent_idem : (1 - localIdempotent (E := E) v) * (1 - localIdempotent (E := E) v) = 1 - localIdempotent (E := E) v := by
  have h : localIdempotent (E := E) v * localIdempotent (E := E) v = localIdempotent (E := E) v := local_idempotent_mul_extension v 1
  rw [sub_mul, one_mul, mul_sub, mul_one, h, sub_self, sub_zero]

theorem local_extension_matrix_mul (M N : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) : localExtensionMatrix v M * localExtensionMatrix v N = localExtensionMatrix v (M * N) := by
  ext i j
  simp only [localExtensionMatrix, Matrix.mul_apply, Matrix.map_apply, map_sum, local_extension_tensor_mul]

theorem local_extension_matrix_mul_gram (M : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (J : Matrix (Fin n) (Fin n) E) :
    localExtensionMatrix v M * J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) = localExtensionMatrix v (M * J.map (inclE (F := F) (v.adicCompletion F))) := by
  ext i j
  simp only [localExtensionMatrix, Matrix.mul_apply, Matrix.map_apply, map_sum, local_extension_mul_incl]

theorem gram_mul_local_extension_matrix (M : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (J : Matrix (Fin n) (Fin n) E) :
    J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) * localExtensionMatrix v M = localExtensionMatrix v (J.map (inclE (F := F) (v.adicCompletion F)) * M) := by
  ext i j
  simp only [localExtensionMatrix, Matrix.mul_apply, Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, ← local_extension_mul_incl, mul_comm]

theorem complement_smul_local_extension_matrix (M : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) : (1 - localIdempotent (E := E) v) • localExtensionMatrix v M = 0 := by
  ext i j
  simp only [localExtensionMatrix, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, complement_idempotent_mul_extension, Matrix.zero_apply]

theorem local_extension_matrix_one : localExtensionMatrix (E := E) v (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) = localIdempotent (E := E) v • 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [localExtensionMatrix, localIdempotent]
  · simp [localExtensionMatrix, Matrix.one_apply_ne h]

theorem local_extension_matrix_map_gram (J : Matrix (Fin n) (Fin n) E) :
    localExtensionMatrix v (J.map (inclE (F := F) (v.adicCompletion F))) = localIdempotent (E := E) v • J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) := by
  ext i j
  simp only [localExtensionMatrix, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, localIdempotent]
  rw [← local_extension_mul_incl, one_mul]

theorem local_diag_matrix_mul (M N : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) : localDiagMatrix v M * localDiagMatrix v N = localDiagMatrix v (M * N) := by
  simp only [localDiagMatrix, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul,
    local_extension_matrix_mul, complement_smul_local_extension_matrix, complement_local_idempotent_idem, add_zero, zero_add]

theorem local_diag_matrix_one : localDiagMatrix (E := E) v (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) = 1 := by
  rw [localDiagMatrix, local_extension_matrix_one, ← add_smul, sub_add_cancel, one_smul]

def localExtensionGL (M : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
  ⟨localDiagMatrix v M, localDiagMatrix v ↑M⁻¹, by rw [local_diag_matrix_mul, Units.mul_inv, local_diag_matrix_one], by rw [local_diag_matrix_mul, Units.inv_mul, local_diag_matrix_one]⟩

theorem proj_local_idempotent_same_place : prV (E := E) v (localIdempotent (E := E) v) = 1 := proj_local_extension_same_place v 1

theorem proj_local_idempotent_other_place (w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v) : prV (E := E) w (localIdempotent (E := E) v) = 0 := proj_local_extension_other_place v w h 1

theorem local_extension_GL_same_place (M : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : bc (prV (E := E) v) (localExtensionGL v M) = M := by
  apply Units.ext
  ext i j
  by_cases h : i = j
  · subst h
    simp [bc, localExtensionGL, localDiagMatrix, localExtensionMatrix, proj_local_idempotent_same_place, proj_local_extension_same_place]
  · simp [bc, localExtensionGL, localDiagMatrix, localExtensionMatrix, proj_local_idempotent_same_place, proj_local_extension_same_place, Matrix.one_apply_ne h]

theorem local_extension_GL_other_place (w : HeightOneSpectrum (𝓞 F)) (hw : w ≠ v) (M : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
    bc (prV (E := E) w) (localExtensionGL v M) = 1 := by
  apply Units.ext
  ext i j
  by_cases h : i = j
  · subst h
    simp [bc, localExtensionGL, localDiagMatrix, localExtensionMatrix, proj_local_idempotent_other_place v w hw, proj_local_extension_other_place v w hw]
  · simp [bc, localExtensionGL, localDiagMatrix, localExtensionMatrix, proj_local_idempotent_other_place v w hw, proj_local_extension_other_place v w hw, Matrix.one_apply_ne h]

end Mat

section Unit

variable {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E)

theorem conj_local_idempotent : sigR σ (FiniteAdeleRing (𝓞 F) F) (localIdempotent (E := E) v) = localIdempotent (E := E) v := by
  rw [localIdempotent, local_extension_conj_comm, map_one]

theorem local_diag_matrix_conj_transpose (M : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) :
    cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (localDiagMatrix v M) = localDiagMatrix v (cT (sigR σ (v.adicCompletion F)) M) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [cT, localDiagMatrix, localExtensionMatrix, Matrix.transpose_apply, Matrix.map_apply, local_extension_conj_comm, conj_local_idempotent]
  · simp [cT, localDiagMatrix, localExtensionMatrix, Matrix.transpose_apply, Matrix.map_apply, local_extension_conj_comm, conj_local_idempotent, Matrix.one_apply_ne h,
      Matrix.one_apply_ne (Ne.symm h)]

theorem local_extension_GL_mem_unitary (J : Matrix (Fin n) (Fin n) E) (M : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hM : M ∈ UPts σ J (v.adicCompletion F)) : localExtensionGL v M ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := by
  have h : cT (sigR σ (v.adicCompletion F)) (M : Matrix (Fin n) (Fin n) _) * J.map (inclE (F := F) (v.adicCompletion F)) *
      (M : Matrix (Fin n) (Fin n) _) = J.map (inclE (F := F) (v.adicCompletion F)) := hM
  show cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (localDiagMatrix v (M : Matrix (Fin n) (Fin n) _)) *
      J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) * localDiagMatrix v (M : Matrix (Fin n) (Fin n) _) =
    J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))
  rw [local_diag_matrix_conj_transpose]
  simp only [localDiagMatrix, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, local_extension_matrix_mul_gram, gram_mul_local_extension_matrix,
    local_extension_matrix_mul, smul_smul, complement_local_idempotent_idem, complement_smul_local_extension_matrix, add_zero, zero_add]
  rw [h, local_extension_matrix_map_gram, ← add_smul, sub_add_cancel, one_smul]

end Unit

section Assemble

variable {n : ℕ} {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

def IsLocalDiamond (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) (k : ℤ) : Prop :=
  ∃ M : GL (Fin n) (E ⊗[F] v.adicCompletion F), M ∈ levelVL σ J v S.Lb ∧
    ∃ hg : M ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))),
      ∀ x, k • S.fT v hv ⟨(M : Matrix (Fin n) (Fin n) _) *ᵥ x.1, (hg x.1).1 x.2⟩ = S.fT v hv x

theorem is_diamond_of_local_diamond (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) (k : ℤ) (h : IsLocalDiamond S v hv k) : ∃ δ, Formalism.L2.Forms.IsDia S v hv k δ := by
  obtain ⟨M, hM, hg, hf⟩ := h
  have hU : M ∈ UPts σ J (v.adicCompletion F) := (Subgroup.mem_inf.1 hM).1
  refine ⟨⟨localExtensionGL v M, local_extension_GL_mem_unitary v σ J M hU⟩, fun v' hv' => local_extension_GL_other_place v v' hv' M, ?_, ?_⟩
  · dsimp only
    rw [local_extension_GL_same_place]; exact hM
  · dsimp only
    have e := local_extension_GL_same_place v M
    refine ⟨by rw [e]; exact hg, fun x => ?_⟩
    rw [← hf x]
    congr 2
    exact Subtype.ext (congrArg (fun N : GL (Fin n) (E ⊗[F] v.adicCompletion F) =>
      (N : Matrix (Fin n) (Fin n) _) *ᵥ x.1) e)

end Assemble

end Ext

section Tied

open Formalism.BasicNotions Formalism.L2.Forms

variable {D : D7} {u : D.what₂.Word}

def LocalDiamondElementsExist (Tf : FormsTied D u) : Prop :=
  ∀ i (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ), ∃ k : ℤ, (k : (D.mem u).A.Fv v) = a ∧
    IsLocalDiamond (Tf.cls i hi).lev (Tf.atT.eV v).1 (Tf.atT.eV v).2 k

theorem diamond_elements_of_local (Tf : FormsTied D u) (h : LocalDiamondElementsExist Tf) : DiamondElementsExist Tf := by
  intro i hi v a
  obtain ⟨k, hk, hl⟩ := h i hi v a
  exact ⟨k, hk, is_diamond_of_local_diamond _ _ _ k hl⟩

theorem diamond_mul_of_local_diamonds (Tf : FormsTied D u) (h : LocalDiamondElementsExist Tf) : Formalism.MainNotions.product_first_zeroth_parts.DiaMul D u :=
  diamond_mul_of_diamond_elements Tf (diamond_elements_of_local Tf h)

end Tied

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
