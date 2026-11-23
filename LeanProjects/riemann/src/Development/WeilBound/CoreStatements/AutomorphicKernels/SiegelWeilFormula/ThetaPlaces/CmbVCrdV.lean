import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.BasisReprMap

noncomputable section

open scoped TensorProduct Matrix HeckeCharacterZeroLocus.SiegelWeilU
open NumberField IsDedekindDomain Filter

namespace PositivityTheory.SiegelWeilFormula.ThetaDictR.PureC

open PositivityTheory.SiegelWeilFormula.ThetaDictR.PureA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem map_mul_alg {A B : Type} [CommRing A] [CommRing B] [Algebra F A] [Algebra F B] (f : A →ₐ[F] B) {p q r : ℕ}
    (M : Matrix (Fin p) (Fin q) A) (N : Matrix (Fin q) (Fin r) A) : (M * N).map f = M.map f * N.map f :=
  Matrix.map_mul (f := f.toRingHom)

variable (bs : Module.Basis (Fin 2) F E) {m n : ℕ} (u : GL (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E))
  (v : HeightOneSpectrum (𝓞 F))

def toMxV (Y : Fin n → Fin m → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) : Matrix (Fin m) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) :=
  Matrix.of fun a j => Y j a

abbrev Av : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) :=
  (((u⁻¹ : GL (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)).1)ᵀ).map (mapV v)

abbrev Bv : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) := ((u.1)ᵀ).map (mapV v)

theorem Av_mul_Bv : Av u v * Bv u v = 1 := by
  rw [Av, Bv, ← map_mul_alg, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem Bv_mul_Av : Bv u v * Av u v = 1 := by
  rw [Av, Bv, ← map_mul_alg, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

def crdV (N : Matrix (Fin m) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) : Fin m × Fin n × Fin 2 → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v :=
  fun k => (Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) bs).repr (N k.1 k.2.1) k.2.2

def cmbV (c : Fin m × Fin n × Fin 2 → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) : Matrix (Fin m) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) :=
  Matrix.of fun i j => ∑ kk, c (i, j, kk) • Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) bs kk

theorem cmbV_crdV (N : Matrix (Fin m) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) : cmbV bs v (crdV bs v N) = N := by
  ext i j
  exact (Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) bs).sum_repr (N i j)

theorem crdV_cmbV (c : Fin m × Fin n × Fin 2 → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) : crdV bs v (cmbV bs v c) = c := by
  funext k
  simp only [crdV, cmbV, Matrix.of_apply]
  rw [(Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) bs).repr_sum_self]

def eL : (Fin n → Fin m → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) ≃ₗ[HeckeCharacterZeroLocus.SiegelWeilU.Fv F v]
    (Fin m × Fin n × Fin 2 → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) where
  toFun Y := crdV bs v (toMxV v Y * Av u v)
  map_add' Y Y' := by
    funext k
    have : toMxV v (Y + Y') = toMxV v Y + toMxV v Y' := by ext; rfl
    simp only [this, Matrix.add_mul, crdV, Matrix.add_apply, map_add, Finsupp.add_apply, Pi.add_apply]
  map_smul' r Y := by
    funext k
    have : toMxV v (r • Y) = r • toMxV v Y := by ext; rfl
    simp only [this, Matrix.smul_mul, crdV, Matrix.smul_apply, map_smul, Finsupp.smul_apply, RingHom.id_apply,
      Pi.smul_apply]
  invFun c := fun j a => (cmbV bs v c * Bv u v) a j
  left_inv Y := by
    funext j a
    simp only [cmbV_crdV, Matrix.mul_assoc, Av_mul_Bv, Matrix.mul_one]
    rfl
  right_inv c := by
    have : toMxV v (fun j a => (cmbV bs v c * Bv u v) a j) = cmbV bs v c * Bv u v := by ext; rfl
    simp only [this, Matrix.mul_assoc, Bv_mul_Av, Matrix.mul_one, crdV_cmbV]

section Top

instance modTopV : IsModuleTopology (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) := ⟨rfl⟩

def eH : (Fin n → Fin m → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) ≃ₜ (Fin m × Fin n × Fin 2 → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) := by
  haveI : ContinuousAdd (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) _
  haveI : ContinuousSMul (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) :=
    IsModuleTopology.toContinuousSMul (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) _
  exact { toEquiv := (eL bs u v).toEquiv
          continuous_toFun := IsModuleTopology.continuous_of_linearMap (eL bs u v).toLinearMap
          continuous_invFun := IsModuleTopology.continuous_of_linearMap (eL bs u v).symm.toLinearMap }

theorem isSB_comp (φ : (Fin m × Fin n × Fin 2 → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) → ℂ)
    (hφ : IsLocallyConstant φ ∧ HasCompactSupport φ) :
    HeckeCharacterZeroLocus.SiegelWeilU.IsSB (fun Y : Fin n → Fin m → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E => φ (crdV bs v (toMxV v Y * Av u v))) :=
  ⟨hφ.1.comp_continuous (eH bs u v).continuous, hφ.2.comp_homeomorph (eH bs u v)⟩

end Top

theorem int_iff : ∀ᶠ v in cofinite, ∀ Y : Fin n → Fin m → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E,
    (∀ k, crdV bs v (toMxV v Y * Av u v) k ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F) ↔
      Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV bs v := by
  filter_upwards [ev_matmul_int bs ((u⁻¹ : GL (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)).1)ᵀ,
    ev_matmul_int bs (u.1)ᵀ] with v h1 h2
  intro Y
  have e1 : (∀ k, crdV bs v (toMxV v Y * Av u v) k ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F) ↔
      IntM bs v (toMxV v Y * Av u v) := ⟨fun h i j kk => h (i, j, kk), fun h k => h k.1 k.2.1 k.2.2⟩
  have e2 : Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV bs v ↔ IntM bs v (toMxV v Y) := ⟨fun h i j kk => h j i kk, fun h a i kk => h i a kk⟩
  rw [e1, e2]
  constructor
  · intro h
    have := h2 _ _ h
    rwa [Matrix.mul_assoc, ← Bv, Av_mul_Bv, Matrix.mul_one] at this
  · intro h
    exact h1 _ _ h

end PositivityTheory.SiegelWeilFormula.ThetaDictR.PureC

end
