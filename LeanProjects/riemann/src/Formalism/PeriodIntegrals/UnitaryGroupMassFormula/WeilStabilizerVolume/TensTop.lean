import Mathlib
import Formalism.PeriodIntegrals.VolFromSW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension

noncomputable section

namespace PI.VolStabW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

instance secondCountable_tens [SecondCountableTopology R] :
    SecondCountableTopology (R ⊗[F] E) := by
  obtain ⟨ι, _, ⟨h⟩⟩ := exists_homeomorph_tens (F := F) (E := E) R
  exact h.isInducing.secondCountableTopology

instance borelSpace_tens : BorelSpace (R ⊗[F] E) := ⟨rfl⟩

instance borelSpace_herm (σ : E →ₐ[F] E) (n : ℕ) : BorelSpace (HermR R σ n) := ⟨rfl⟩

theorem continuous_norm_tens : Continuous (fun x : R ⊗[F] E => Algebra.norm R x) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R (R ⊗[F] E)
  let bE := Module.finBasis F E
  let b := Algebra.TensorProduct.basis R bE
  have he : (fun x : R ⊗[F] E => Algebra.norm R x) = fun x => (Algebra.leftMulMatrix b x).det := by
    funext x
    exact Algebra.norm_eq_matrix_det b x
  rw [he]
  apply Continuous.matrix_det
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have h1 : (fun x => Algebra.leftMulMatrix b x i j) =
      fun x => (b.coord i ∘ₗ LinearMap.mulRight R (b j)) x := by
    funext x
    simp [Algebra.leftMulMatrix_eq_repr_mul]
  rw [h1]
  exact IsModuleTopology.continuous_of_linearMap _

theorem isUnit_iff_norm_tens (x : R ⊗[F] E) : IsUnit x ↔ IsUnit (Algebra.norm R x) := by
  rw [Algebra.norm_apply, ← LinearMap.isUnit_iff_isUnit_det]
  constructor
  · intro hx
    exact hx.map (Algebra.lmul R (R ⊗[F] E))
  · intro h
    obtain ⟨y, hy⟩ := ((Module.End.isUnit_iff _).1 h).2 1
    exact ⟨⟨x, y, hy, by rw [mul_comm]; exact hy⟩, rfl⟩

theorem isOpen_units_tens (h : IsOpen {r : R | IsUnit r}) :
    IsOpen {x : R ⊗[F] E | IsUnit x} := by
  have e : {x : R ⊗[F] E | IsUnit x} = (fun x => Algebra.norm R x) ⁻¹' {r | IsUnit r} := by
    ext x
    exact isUnit_iff_norm_tens R x
  rw [e]
  exact h.preimage (continuous_norm_tens R)

theorem isOpen_isUnit_det (h : IsOpen {r : R | IsUnit r}) (n : ℕ) :
    IsOpen {S : Matrix (Fin n) (Fin n) (R ⊗[F] E) | IsUnit S.det} := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R (R ⊗[F] E)
  exact (isOpen_units_tens R h).preimage (Continuous.matrix_det continuous_id)

def hLin (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin M → R ⊗[F] E) :
    (Fin M → R ⊗[F] E) →ₗ[R ⊗[F] E] R ⊗[F] E where
  toFun := hR R σ J x
  map_add' y z := by
    simp only [hR, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem linIndep_of_isUnit_det (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) (h : IsUnit (gramR R σ J X).det) :
    LinearIndependent (R ⊗[F] E) X := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hG : (gramR R σ J X).mulVec c = 0 := by
    funext b
    have h1 := congrArg (hLin R σ J (X b)) hc
    rw [map_sum, map_zero] at h1
    simp only [map_smul, smul_eq_mul] at h1
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [← h1]
    exact Finset.sum_congr rfl fun a _ => by rw [mul_comm]; rfl
  have hc0 : c = 0 := by
    calc c = ((gramR R σ J X)⁻¹ * gramR R σ J X).mulVec c := by
          rw [Matrix.nonsing_inv_mul _ h, Matrix.one_mulVec]
      _ = (gramR R σ J X)⁻¹.mulVec ((gramR R σ J X).mulVec c) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = 0 := by rw [hG, Matrix.mulVec_zero]
  intro i
  exact congrFun hc0 i

variable [LocallyCompactSpace R] [T2Space R]

theorem continuous_hR (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Continuous (fun p : (Fin M → R ⊗[F] E) × (Fin M → R ⊗[F] E) => hR R σ J p.1 p.2) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R (R ⊗[F] E)
  have hsig : Continuous (sigR R σ) := by
    have e : ⇑(sigR R σ) = ⇑(LinearMap.baseChange R σ.toLinearMap) := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul r e => simp [sigR]
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [e]
    exact IsModuleTopology.continuous_of_linearMap _
  unfold hR Formalism.UG.hform
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact ((hsig.comp ((continuous_apply i).comp continuous_fst)).mul continuous_const).mul
    ((continuous_apply j).comp continuous_snd)

theorem continuous_gramR_apply (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (a b : Fin n) : Continuous (fun X : Fin n → Fin M → R ⊗[F] E => gramR R σ J X a b) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R (R ⊗[F] E)
  have hsig : Continuous (sigR R σ) := by
    have e : ⇑(sigR R σ) = ⇑(LinearMap.baseChange R σ.toLinearMap) := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul r e => simp [sigR]
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [e]
    exact IsModuleTopology.continuous_of_linearMap _
  unfold gramR hR Formalism.UG.hform
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact ((hsig.comp ((continuous_apply i).comp (continuous_apply a))).mul continuous_const).mul
    ((continuous_apply j).comp (continuous_apply b))

theorem continuous_gramR (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Continuous (fun X : Fin n → Fin M → R ⊗[F] E => gramR R σ J X) :=
  continuous_pi fun a => continuous_pi fun b => continuous_gramR_apply R σ J a b

theorem isClosed_HermR (σ : E →ₐ[F] E) (n : ℕ) :
    IsClosed (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have hsig : Continuous (sigR R σ) := by
    have e : ⇑(sigR R σ) = ⇑(LinearMap.baseChange R σ.toLinearMap) := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul r e => simp [sigR]
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [e]
    exact IsModuleTopology.continuous_of_linearMap _
  let b := Algebra.TensorProduct.basis R (Module.finBasis F E)
  haveI : T2Space (R ⊗[F] E) := T2Space.of_injective_continuous b.equivFun.injective
    (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap)
  show IsClosed {S : Matrix (Fin n) (Fin n) (R ⊗[F] E) | ∀ a b, sigR R σ (S b a) = S a b}
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun a => isClosed_iInter fun c => isClosed_eq
    (hsig.comp ((continuous_apply a).comp (continuous_apply c)))
    ((continuous_apply c).comp (continuous_apply a))

instance locallyCompact_herm (σ : E →ₐ[F] E) (n : ℕ) : LocallyCompactSpace (HermR R σ n) :=
  (isClosed_HermR R σ n).isClosedEmbedding_subtypeVal.locallyCompactSpace

end Gen

section CM

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sigma_invol [NumberField E] (σ : E →ₐ[F] E)
    (hσ : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [hσ τ (σ x), hσ τ x, star_star]

variable (R : Type) [CommRing R] [Algebra F R]

theorem sigR_invol (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (x : R ⊗[F] E) :
    sigR R σ (sigR R σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, hσ]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem gramR_mem (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, σ (J j i) = J i j)
    (X : Fin n → Fin M → R ⊗[F] E) : gramR R σ J X ∈ HermR R σ n := by
  have hsi : ∀ e, sigR R σ (inclR R e) = inclR R (σ e) := fun e => by simp [sigR, inclR]
  show ∀ a b, sigR R σ (gramR R σ J X b a) = gramR R σ J X a b
  intro a b
  simp only [gramR, hR, Formalism.UG.hform, JR, Matrix.map_apply, map_sum, map_mul, sigR_invol R σ hσ, hsi, hJ]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end CM

section Arch

variable (F : Type) [Field F] [NumberField F]

instance secondCountable_completion (v : InfinitePlace F) : SecondCountableTopology v.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding (v := v)).isEmbedding.isInducing.secondCountableTopology

instance secondCountable_Ainf : SecondCountableTopology (InfiniteAdeleRing F) :=
  inferInstanceAs (SecondCountableTopology ((v : InfinitePlace F) → v.Completion))

theorem isOpen_units_Ainf : IsOpen {x : InfiniteAdeleRing F | IsUnit x} := by
  have e : {x : InfiniteAdeleRing F | IsUnit x} =
      ⋂ v, (fun x : InfiniteAdeleRing F => x v) ⁻¹' {0}ᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff]
    exact (Pi.isUnit_iff (M := fun v : InfinitePlace F => v.Completion) (x := x)).trans
      (forall_congr' fun v => isUnit_iff_ne_zero)
  rw [e]
  exact isOpen_iInter_of_finite fun v => isOpen_compl_singleton.preimage (continuous_apply v)

end Arch

section Glue

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem isUnit_det_hermOf (σ : E →ₐ[F] E) {n : ℕ} (T : Matrix (Fin n) (Fin n) E)
    (hT : ∀ a b, σ (T b a) = T a b) (hdet : T.det ≠ 0) :
    IsUnit ((hermOf R σ T hT : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) := by
  show IsUnit (T.map (inclR R)).det
  have h := RingHom.map_det (inclR (F := F) (E := E) R) T
  rw [RingHom.mapMatrix_apply] at h
  rw [← h]
  exact (isUnit_iff_ne_zero.2 hdet).map _

def gramH (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (X : Fin n → Fin M → R ⊗[F] E) : HermR R σ n :=
  ⟨gramR R σ J X, gramR_mem R σ hσ J hJ X⟩

end Glue

section GlueTop

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [T2Space R]

theorem continuous_gramH (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, σ (J j i) = J i j) :
    Continuous (gramH (n := n) R σ hσ J hJ) :=
  (continuous_gramR R σ J).subtype_mk _

theorem isOpen_unitHerm (h : IsOpen {r : R | IsUnit r}) (σ : E →ₐ[F] E) (n : ℕ) :
    IsOpen {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} :=
  continuous_subtype_val.isOpen_preimage _ (isOpen_isUnit_det R h n)

end GlueTop

end PI.VolStabW
