import Mathlib
import Formalism.PeriodIntegrals.VolFromSW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension

noncomputable section

namespace PI.VolStabSW

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
  let b := Algebra.TensorProduct.basis R (Module.finBasis F E)
  have hc : Continuous (Algebra.leftMulMatrix b) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap
  have e : (fun x : R ⊗[F] E => Algebra.norm R x) = fun x => (Algebra.leftMulMatrix b x).det := by
    funext x
    exact Algebra.norm_eq_matrix_det b x
  rw [e]
  exact hc.matrix_det

theorem isUnit_iff_norm_tens (x : R ⊗[F] E) : IsUnit x ↔ IsUnit (Algebra.norm R x) := by
  constructor
  · intro h
    exact h.map (Algebra.norm R)
  · intro h
    rw [Algebra.norm_apply, ← LinearMap.isUnit_iff_isUnit_det] at h
    obtain ⟨u, hu⟩ := h
    have h1 : x * (↑u⁻¹ : Module.End R (R ⊗[F] E)) 1 = 1 := by
      have e := congrArg (fun f : Module.End R (R ⊗[F] E) => f 1) u.mul_inv
      simp only [Module.End.mul_apply, Module.End.one_apply] at e
      rw [hu] at e
      exact e
    exact ⟨⟨x, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

theorem isOpen_units_tens (h : IsOpen {r : R | IsUnit r}) :
    IsOpen {x : R ⊗[F] E | IsUnit x} := by
  have e : {x : R ⊗[F] E | IsUnit x} = (fun x => Algebra.norm R x) ⁻¹' {r : R | IsUnit r} := by
    ext x
    exact isUnit_iff_norm_tens R x
  rw [e]
  exact h.preimage (continuous_norm_tens (F := F) (E := E) R)

theorem isOpen_isUnit_det (h : IsOpen {r : R | IsUnit r}) (n : ℕ) :
    IsOpen {S : Matrix (Fin n) (Fin n) (R ⊗[F] E) | IsUnit S.det} := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R (R ⊗[F] E)
  exact (isOpen_units_tens R h).preimage (continuous_id.matrix_det)

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
  intro g hg
  have key : ∀ b, ∑ a, g a * gramR R σ J X b a = 0 := by
    intro b
    have e := congrArg (hLin R σ J (X b)) hg
    rw [map_sum, map_zero] at e
    simp only [map_smul, smul_eq_mul] at e
    exact e
  have hv : Matrix.mulVec (gramR R σ J X) g = 0 := by
    funext b
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [← key b]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  have hg0 : g = 0 := by
    calc g = Matrix.mulVec ((gramR R σ J X)⁻¹ * gramR R σ J X) g := by
          rw [Matrix.nonsing_inv_mul _ h, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  intro i
  simp [hg0]

variable [LocallyCompactSpace R] [T2Space R]

private theorem continuous_sigR_stabilizer_orbit_volume (σ : E →ₐ[F] E) : Continuous (sigR R σ) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have e : ⇑(sigR R σ) = ⇑(LinearMap.baseChange R σ.toLinearMap) := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [sigR, LinearMap.baseChange_tmul]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  rw [e]
  exact IsModuleTopology.continuous_of_linearMap _

theorem continuous_hR (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Continuous (fun p : (Fin M → R ⊗[F] E) × (Fin M → R ⊗[F] E) => hR R σ J p.1 p.2) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R (R ⊗[F] E)
  have hs := continuous_sigR_stabilizer_orbit_volume (F := F) (E := E) R σ
  unfold hR Formalism.UG.hform
  exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    ((hs.comp ((continuous_apply i).comp continuous_fst)).mul continuous_const).mul
      ((continuous_apply j).comp continuous_snd)

theorem continuous_gramR_apply (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (a b : Fin n) : Continuous (fun X : Fin n → Fin M → R ⊗[F] E => gramR R σ J X a b) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R (R ⊗[F] E)
  have hs := continuous_sigR_stabilizer_orbit_volume (F := F) (E := E) R σ
  show Continuous fun X : Fin n → Fin M → R ⊗[F] E => hR R σ J (X a) (X b)
  unfold hR Formalism.UG.hform
  exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    ((hs.comp ((continuous_apply i).comp (continuous_apply a))).mul continuous_const).mul
      ((continuous_apply j).comp (continuous_apply b))

theorem continuous_gramR (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Continuous (fun X : Fin n → Fin M → R ⊗[F] E => gramR R σ J X) := continuous_pi fun a => continuous_pi fun b => continuous_gramR_apply R σ J a b

theorem isClosed_HermR (σ : E →ₐ[F] E) (n : ℕ) :
    IsClosed (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : T2Space (R ⊗[F] E) :=
    T2Space.of_injective_continuous (Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun.injective
      (IsModuleTopology.continuous_of_linearMap
        (Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun.toLinearMap)
  have hs := continuous_sigR_stabilizer_orbit_volume (F := F) (E := E) R σ
  have e : (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
      ⋂ a, ⋂ b, {S | sigR R σ (S b a) = S a b} := by
    ext S
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  rw [e]
  exact isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_eq (hs.comp ((continuous_apply a).comp (continuous_apply b)))
      ((continuous_apply b).comp (continuous_apply a))

instance locallyCompact_herm (σ : E →ₐ[F] E) (n : ℕ) : LocallyCompactSpace (HermR R σ n) :=
  (isClosed_HermR R σ n).isClosedEmbedding_subtypeVal.locallyCompactSpace

end Gen

section CM

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sigma_invol [NumberField E] (σ : E →ₐ[F] E)
    (hσ : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  exact τ.injective (by rw [hσ τ, hσ τ, star_star])

variable (R : Type) [CommRing R] [Algebra F R]

theorem sigR_invol (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (x : R ⊗[F] E) :
    sigR R σ (sigR R σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, hσ]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem gramR_mem (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, σ (J j i) = J i j)
    (X : Fin n → Fin M → R ⊗[F] E) : gramR R σ J X ∈ HermR R σ n := by
  have hJR : ∀ p q, sigR R σ (JR R J q p) = JR R J p q := fun p q => by
    simp [JR, inclR, sigR, hJ]
  show ∀ a b, sigR R σ (gramR R σ J X b a) = gramR R σ J X a b
  intro a b
  simp only [gramR, hR, Formalism.UG.hform, map_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [sigR_invol R σ hσ, hJR]
  ring

end CM

section Arch

variable (F : Type) [Field F] [NumberField F]

instance secondCountable_completion (v : InfinitePlace F) : SecondCountableTopology v.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding (v := v)).isEmbedding.isInducing.secondCountableTopology

instance secondCountable_Ainf : SecondCountableTopology (InfiniteAdeleRing F) :=
  inferInstanceAs (SecondCountableTopology ((v : InfinitePlace F) → v.Completion))

theorem isOpen_units_Ainf : IsOpen {x : InfiniteAdeleRing F | IsUnit x} := by
  have e : {x : InfiniteAdeleRing F | IsUnit x} = ⋂ v, {x : InfiniteAdeleRing F | x v ≠ 0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact Pi.isUnit_iff.trans (forall_congr' fun v => isUnit_iff_ne_zero)
  rw [e]
  exact isOpen_iInter_of_finite fun v => isOpen_ne_fun (continuous_apply v) continuous_const

end Arch

section Glue

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem isUnit_det_hermOf (σ : E →ₐ[F] E) {n : ℕ} (T : Matrix (Fin n) (Fin n) E)
    (hT : ∀ a b, σ (T b a) = T a b) (hdet : T.det ≠ 0) :
    IsUnit ((hermOf R σ T hT : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) := by
  show IsUnit (T.map (inclR R)).det
  have e := RingHom.map_det (inclR (F := F) R) T
  rw [show (inclR (F := F) R).mapMatrix T = T.map (inclR R) from rfl] at e
  rw [← e]
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
    Continuous (gramH (n := n) R σ hσ J hJ) := (continuous_gramR R σ J).subtype_mk _

theorem isOpen_unitHerm (h : IsOpen {r : R | IsUnit r}) (σ : E →ₐ[F] E) (n : ℕ) :
    IsOpen {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} := (isOpen_isUnit_det R h n).preimage continuous_subtype_val

end GlueTop

end PI.VolStabSW
