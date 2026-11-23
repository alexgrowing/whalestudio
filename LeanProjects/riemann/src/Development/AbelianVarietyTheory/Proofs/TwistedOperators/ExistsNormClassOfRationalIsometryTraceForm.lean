import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section
namespace GlobalTheory.RatCls

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} (P : PPol σ n)

theorem lid_smul (c : F ⊗[F] E) (z : F ⊗[F] Fld P) :
    Algebra.TensorProduct.lid F (Fld P) (c • z) =
      Algebra.TensorProduct.lid F E c • Algebra.TensorProduct.lid F (Fld P) z := by
  rw [Algebra.smul_def, map_mul, Algebra.smul_def]
  congr 1
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    change Algebra.TensorProduct.lid F (Fld P) (Algebra.TensorProduct.map (AlgHom.id F F)
      (IsScalarTower.toAlgHom F E (Fld P)) (a ⊗ₜ e)) = _
    simp [Algebra.smul_def, IsScalarTower.algebraMap_apply F E (Fld P)]
  | add a b ha hb => simp only [map_add, ha, hb]

omit [Field E] in
theorem inclR_lid {A : Type} [Field A] [Algebra F A] (c : F ⊗[F] A) :
    inclR F (Algebra.TensorProduct.lid F A c) = c := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [inclR, Algebra.TensorProduct.lid_tmul]
    change (1 : F) ⊗ₜ[F] (a • e) = a ⊗ₜ e
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add a b ha hb => simp only [map_add, ha, hb]

omit [Field E] in
theorem lid_inclR {A : Type} [Field A] [Algebra F A] (a : A) :
    Algebra.TensorProduct.lid F A (inclR F a) = a := by
  simp [inclR]

def tensEquiv (φ : Fld P ≃ₗ[E] (Fin n → E)) : (F ⊗[F] Fld P) ≃ₗ[F ⊗[F] E] (Fin n → F ⊗[F] E) where
  toFun z i := inclR F (φ (Algebra.TensorProduct.lid F (Fld P) z) i)
  invFun w := (Algebra.TensorProduct.lid F (Fld P)).symm (φ.symm (fun i => Algebra.TensorProduct.lid F E (w i)))
  map_add' a b := by ext i; simp
  map_smul' c z := by
    ext i
    rw [lid_smul, φ.map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply]
    rw [inclR_lid]
  left_inv z := by
    simp only [lid_inclR]
    simp
  right_inv w := by
    ext i
    simp [inclR_lid]

theorem tensEquiv_apply (φ : Fld P ≃ₗ[E] (Fin n → E)) (z : F ⊗[F] Fld P) (i : Fin n) :
    tensEquiv P φ z i = inclR F (φ (Algebra.TensorProduct.lid F (Fld P) z) i) := rfl

end GlobalTheory.RatCls

noncomputable section
namespace GlobalTheory.RatCls

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} (P : PPol σ n)

theorem tensEquiv_tmul (φ : Fld P ≃ₗ[E] (Fin n → E)) (v : Fld P) :
    tensEquiv (F := F) P φ (1 ⊗ₜ v) = fun i => inclR F (φ v i) := by
  funext i; rw [tensEquiv_apply]; simp

theorem sigR_inclR (e : E) : sigR F σ (inclR F e) = inclR F (σ e) := by
  simp [sigR, inclR]

theorem hform_inclR (J : Matrix (Fin n) (Fin n) E) (a b : Fin n → E) :
    Formalism.UG.hform (sigR F σ) (JR F J) (fun i => inclR F (a i)) (fun i => inclR F (b i)) =
      inclR F (Formalism.UG.hform (σ : E →+* E) J a b) := by
  simp [Formalism.UG.hform, JR, map_sum, map_mul, sigR_inclR]

theorem trBase_tmul (w : Fld P) : trBase P F (1 ⊗ₜ w) = inclR F (Algebra.trace E (Fld P) w) := by
  simp [trBase, inclR]

end GlobalTheory.RatCls

noncomputable section
namespace GlobalTheory.RatCls

theorem hasCls_of_ratIsom : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (P : PPol σ n)
    (J : Matrix (Fin n) (Fin n) E) (φ : Fld P ≃ₗ[E] (Fin n → E)) (x : Fld P), x ≠ 0 → star' P x = x →
    (∀ y y', Formalism.UG.hform (σ : E →+* E) J (φ y') (φ y) = Algebra.trace E (Fld P) (x * y * star' P y')) →
    ∀ γ : GRat σ J, (∀ y, γ.1.1 *ᵥ φ y = φ (alpha P * y)) → ∃ q, HasCls P F J (diagH σ J F γ) q := by
  intro F E _ _ _ σ n P J φ x hx hs hφ γ hγ
  let Φ := tensEquiv (F := F) P φ
  let u : (F ⊗[F] Fld P)ˣ :=
    Units.map (Algebra.TensorProduct.lid F (Fld P)).symm.toAlgHom.toRingHom.toMonoidHom (Units.mk0 x hx)
  have hu : (u : F ⊗[F] Fld P) = 1 ⊗ₜ x := by simp [u]
  have hmem : u ∈ plusUnits P F := by
    change Units.map (sigR F (star' P)).toMonoidHom u = MonoidHom.id _ u
    ext
    simp [hu, sigR, hs]
  let xu : plusUnits P F := ⟨u, hmem⟩
  have pure : ∀ y : F ⊗[F] Fld P, ∃ v, y = 1 ⊗ₜ v := fun y =>
    ⟨Algebra.TensorProduct.lid F (Fld P) y, (inclR_lid y).symm⟩
  have hI : IsIsom P F J xu.1.1 Φ := by
    intro y y'
    obtain ⟨v, rfl⟩ := pure y
    obtain ⟨v', rfl⟩ := pure y'
    simp only [Φ, tensEquiv_tmul, hform_inclR, hφ]
    change _ = trBase P F (u.1 * 1 ⊗ₜ v * sigR F (star' P) (1 ⊗ₜ v'))
    rw [hu]
    simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      map_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one, trBase_tmul]
  refine ⟨QuotientGroup.mk xu, xu, Φ, hI, rfl, ?_⟩
  have ht : (torUnit (diagH (star' P) (one₁ P) F (alphaRat P))).1 = 1 ⊗ₜ alpha P := by
    show Matrix.det ((((alphaRat P).1 : GL (Fin 1) (Fld P)) : Matrix (Fin 1) (Fin 1) (Fld P)).map (inclR F)) = _
    rw [Matrix.det_fin_one]
    simp [alphaRat, inclR]
  apply Subtype.ext
  apply Units.ext
  show mulMat Φ (torUnit (diagH (star' P) (one₁ P) F (alphaRat P))).1 = (γ.1 : Matrix (Fin n) (Fin n) E).map (inclR F)
  rw [ht]
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro w
  obtain ⟨y, rfl⟩ := Φ.surjective w
  obtain ⟨v, rfl⟩ := pure y
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, mulMat_mulVec, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  simp only [Φ, tensEquiv_tmul]
  funext i
  rw [← hγ, RingHom.map_mulVec]
  rfl

end GlobalTheory.RatCls
