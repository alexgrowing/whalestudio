import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.ShellP
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.NontrivialLocalCharacter.ExistsPsiVNeOne
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalInvariantNeighborhoods.MeasurePreservingOfAddEquiv
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalInvariantNeighborhoods.NhdsInv
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalInvariantNeighborhoods.SmallSub

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.SwLocFin

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc Filter Topology
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (v : HeightOneSpectrum (𝓞 F))

instance properSpace_Fv : ProperSpace (Fv F v) :=
  Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.2
    ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F)),
      Formalism.UG.P.glint_finite_residueField v⟩
instance locallyCompact_Fv : LocallyCompactSpace (Fv F v) := inferInstance
instance secondCountable_Fv : SecondCountableTopology (Fv F v) := inferInstance
instance isModuleTopology_A : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
instance isTopologicalRing_A : IsTopologicalRing (Fv F v ⊗[F] E) :=
  IsModuleTopology.isTopologicalRing (Fv F v) _
instance borel_A : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
instance borel_Herm (σ : E →ₐ[F] E) (n : ℕ) : BorelSpace (HermR (Fv F v) σ n) := ⟨rfl⟩
instance isTopAddGroup_Herm (σ : E →ₐ[F] E) (n : ℕ) : IsTopologicalAddGroup (HermR (Fv F v) σ n) := inferInstance

def crdL : (Fv F v ⊗[F] E) ≃L[Fv F v] (Fin (Module.finrank F E) → Fv F v) :=
  { (bA E v).equivFun with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap (bA E v).equivFun.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap (bA E v).equivFun.symm.toLinearMap }

instance t2Space_local_tensor_alt : T2Space (Fv F v ⊗[F] E) := (crdL v).toHomeomorph.isEmbedding.t2Space
instance locallyCompact_A : LocallyCompactSpace (Fv F v ⊗[F] E) :=
  (crdL v).toHomeomorph.isClosedEmbedding.locallyCompactSpace
instance secondCountable_A : SecondCountableTopology (Fv F v ⊗[F] E) :=
  (crdL v).toHomeomorph.isEmbedding.secondCountableTopology

theorem crd_add (a b : Fv F v ⊗[F] E) : crd v (a + b) = crd v a + crd v b := map_add _ _ _
theorem crd_neg (a : Fv F v ⊗[F] E) : crd v (-a) = -crd v a := map_neg _ _
theorem crd_smul (t : Fv F v) (a : Fv F v ⊗[F] E) : crd v (t • a) = t • crd v a := map_smul _ _ _
theorem crd_eq_zero {a : Fv F v ⊗[F] E} : crd v a = 0 ↔ a = 0 := (bA E v).equivFun.map_eq_zero_iff

def crdM (p q : ℕ) : (Fin p → Fin q → Fv F v ⊗[F] E) ≃ₜ (Fin p → Fin q → Fin (Module.finrank F E) → Fv F v) :=
  Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ => (crdL v).toHomeomorph

theorem crdM_apply (p q : ℕ) (x : Fin p → Fin q → Fv F v ⊗[F] E) : crdM v p q x = fun i j => crd v (x i j) := rfl

def crdV (n : ℕ) : (Fin n → Fv F v ⊗[F] E) ≃ₜ (Fin n → Fin (Module.finrank F E) → Fv F v) :=
  Homeomorph.piCongrRight fun _ => (crdL v).toHomeomorph

theorem crdV_apply (n : ℕ) (y : Fin n → Fv F v ⊗[F] E) : crdV v n y = fun i => crd v (y i) := rfl

variable {v}

theorem nA_nonneg (a : Fv F v ⊗[F] E) : 0 ≤ nA v a := norm_nonneg _
theorem nA_add_le (a b : Fv F v ⊗[F] E) : nA v (a + b) ≤ max (nA v a) (nA v b) := by
  unfold nA; rw [crd_add]; exact IsUltrametricDist.norm_add_le_max _ _
theorem nA_smul (t : Fv F v) (a : Fv F v ⊗[F] E) : nA v (t • a) = ‖t‖ * nA v a := by
  unfold nA; rw [crd_smul, norm_smul]
theorem nA_eq_zero {a : Fv F v ⊗[F] E} : nA v a = 0 ↔ a = 0 := by unfold nA; rw [norm_eq_zero, crd_eq_zero]
theorem nA_zero : nA v (0 : Fv F v ⊗[F] E) = 0 := nA_eq_zero.2 rfl
theorem crd_sum {ι : Type*} (s : Finset ι) (f : ι → Fv F v ⊗[F] E) : crd v (∑ i ∈ s, f i) = ∑ i ∈ s, crd v (f i) :=
  map_sum (bA E v).equivFun _ _
theorem nA_sum_le {ι : Type*} (s : Finset ι) (f : ι → Fv F v ⊗[F] E) : nA v (∑ i ∈ s, f i) ≤ ∑ i ∈ s, nA v (f i) := by
  unfold nA; rw [crd_sum]; exact norm_sum_le _ _

variable {p q : ℕ}

theorem nM_nonneg (x : Fin p → Fin q → Fv F v ⊗[F] E) : 0 ≤ nM v x := norm_nonneg _
theorem nM_eq (x : Fin p → Fin q → Fv F v ⊗[F] E) : nM v x = ‖crdM v p q x‖ := rfl
theorem crdM_add (x y : Fin p → Fin q → Fv F v ⊗[F] E) : crdM v p q (x + y) = crdM v p q x + crdM v p q y := by
  funext i j; simp [crdM_apply, crd_add]
theorem crdM_neg (x : Fin p → Fin q → Fv F v ⊗[F] E) : crdM v p q (-x) = -crdM v p q x := by
  funext i j; simp [crdM_apply, crd_neg]
theorem crdM_smul (t : Fv F v) (x : Fin p → Fin q → Fv F v ⊗[F] E) : crdM v p q (t • x) = t • crdM v p q x := by
  funext i j; simp [crdM_apply, crd_smul]
theorem crdM_zero : crdM v p q (0 : Fin p → Fin q → Fv F v ⊗[F] E) = 0 := by
  funext i j; simp [crdM_apply, crd_eq_zero]
theorem nM_add_le (x y : Fin p → Fin q → Fv F v ⊗[F] E) : nM v (x + y) ≤ max (nM v x) (nM v y) := by
  simp only [nM_eq, crdM_add]; exact IsUltrametricDist.norm_add_le_max _ _
theorem nM_neg (x : Fin p → Fin q → Fv F v ⊗[F] E) : nM v (-x) = nM v x := by simp only [nM_eq, crdM_neg, norm_neg]
theorem nM_smul (t : Fv F v) (x : Fin p → Fin q → Fv F v ⊗[F] E) : nM v (t • x) = ‖t‖ * nM v x := by
  simp only [nM_eq, crdM_smul, norm_smul]
theorem nM_eq_zero {x : Fin p → Fin q → Fv F v ⊗[F] E} : nM v x = 0 ↔ x = 0 := by
  rw [nM_eq, norm_eq_zero]
  constructor
  · intro h; exact (crdM v p q).injective (h.trans crdM_zero.symm)
  · rintro rfl; exact crdM_zero
theorem nM_zero : nM v (0 : Fin p → Fin q → Fv F v ⊗[F] E) = 0 := nM_eq_zero.2 rfl
theorem nA_le_nM (x : Fin p → Fin q → Fv F v ⊗[F] E) (i : Fin p) (j : Fin q) : nA v (x i j) ≤ nM v x := by
  have h1 : ‖crdM v p q x i‖ ≤ ‖crdM v p q x‖ := norm_le_pi_norm _ i
  have h2 : ‖crdM v p q x i j‖ ≤ ‖crdM v p q x i‖ := norm_le_pi_norm _ j
  exact h2.trans h1
theorem nM_le_iff {x : Fin p → Fin q → Fv F v ⊗[F] E} {r : ℝ} (hr : 0 ≤ r) :
    nM v x ≤ r ↔ ∀ i j, nA v (x i j) ≤ r := by
  rw [nM_eq, pi_norm_le_iff_of_nonneg hr]
  refine forall_congr' fun i => ?_
  rw [pi_norm_le_iff_of_nonneg hr]
  rfl

theorem nM_add_eq_of_lt {x y : Fin p → Fin q → Fv F v ⊗[F] E} (h : nM v y < nM v x) : nM v (x + y) = nM v x := by
  simp only [nM_eq, crdM_add] at h ⊢
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]
theorem continuous_nM : Continuous (nM v : (Fin p → Fin q → Fv F v ⊗[F] E) → ℝ) :=
  continuous_norm.comp (crdM v p q).continuous
theorem ballM_eq (r : ℝ) : {x : Fin p → Fin q → Fv F v ⊗[F] E | nM v x ≤ r} =
    crdM v p q ⁻¹' Metric.closedBall 0 r := by
  ext x; simp [nM_eq]
theorem isCompact_ballM (r : ℝ) : IsCompact {x : Fin p → Fin q → Fv F v ⊗[F] E | nM v x ≤ r} := by
  rw [ballM_eq, ← Homeomorph.image_symm]; exact (isCompact_closedBall _ _).image (crdM v p q).symm.continuous
theorem isOpen_ballM {r : ℝ} (hr : 0 < r) : IsOpen {x : Fin p → Fin q → Fv F v ⊗[F] E | nM v x ≤ r} := by
  rw [ballM_eq]; exact (IsUltrametricDist.isOpen_closedBall _ hr.ne').preimage (crdM v p q).continuous
theorem exists_ballM_subset {U : Set (Fin p → Fin q → Fv F v ⊗[F] E)} (hU : U ∈ 𝓝 0) :
    ∃ r > 0, {x | nM v x ≤ r} ⊆ U := by
  have h0 : crdM (E := E) v p q 0 = 0 := crdM_zero
  have : (crdM (E := E) v p q).symm ⁻¹' U ∈ 𝓝 (0 : Fin p → Fin q → Fin (Module.finrank F E) → Fv F v) := by
    apply (crdM (E := E) v p q).symm.continuous.continuousAt.preimage_mem_nhds
    have : (crdM (E := E) v p q).symm 0 = 0 := by rw [← h0, Homeomorph.symm_apply_apply]
    rw [this]; exact hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 this
  refine ⟨ε / 2, half_pos hε, fun x hx => ?_⟩
  have hx' : crdM v p q x ∈ Metric.ball 0 ε := by
    rw [mem_ball_zero_iff]; exact lt_of_le_of_lt hx (half_lt_self hε)
  have := hball hx'
  simpa using this
theorem exists_bound_nM {C : Set (Fin p → Fin q → Fv F v ⊗[F] E)} (hC : IsCompact C) :
    ∃ R, ∀ x ∈ C, nM v x ≤ R := by
  obtain ⟨R, hR⟩ := hC.exists_bound_of_continuousOn (continuous_nM (v := v)).continuousOn
  exact ⟨R, fun x hx => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hR x hx)⟩

variable {n : ℕ}

theorem nV_nonneg (y : Fin n → Fv F v ⊗[F] E) : 0 ≤ nV v y := norm_nonneg _
theorem nV_eq (y : Fin n → Fv F v ⊗[F] E) : nV v y = ‖crdV v n y‖ := rfl
theorem crdV_smul (t : Fv F v) (y : Fin n → Fv F v ⊗[F] E) : crdV v n (t • y) = t • crdV v n y := by
  funext i; simp [crdV_apply, crd_smul]
theorem crdV_zero : crdV v n (0 : Fin n → Fv F v ⊗[F] E) = 0 := by
  funext i; simp [crdV_apply, crd_eq_zero]
theorem nV_smul (t : Fv F v) (y : Fin n → Fv F v ⊗[F] E) : nV v (t • y) = ‖t‖ * nV v y := by
  simp only [nV_eq, crdV_smul, norm_smul]
theorem nA_le_nV (y : Fin n → Fv F v ⊗[F] E) (i : Fin n) : nA v (y i) ≤ nV v y := norm_le_pi_norm (crdV v n y) i
theorem nV_le_iff {y : Fin n → Fv F v ⊗[F] E} {r : ℝ} (hr : 0 ≤ r) : nV v y ≤ r ↔ ∀ i, nA v (y i) ≤ r := by
  rw [nV_eq, pi_norm_le_iff_of_nonneg hr]; rfl
theorem continuous_nV : Continuous (nV v : (Fin n → Fv F v ⊗[F] E) → ℝ) :=
  continuous_norm.comp (crdV v n).continuous
theorem exists_ballV_subset {U : Set (Fin n → Fv F v ⊗[F] E)} (hU : U ∈ 𝓝 0) : ∃ r > 0, {y | nV v y ≤ r} ⊆ U := by
  have h0 : crdV (E := E) v n 0 = 0 := crdV_zero
  have : (crdV (E := E) v n).symm ⁻¹' U ∈ 𝓝 (0 : Fin n → Fin (Module.finrank F E) → Fv F v) := by
    apply (crdV (E := E) v n).symm.continuous.continuousAt.preimage_mem_nhds
    have : (crdV (E := E) v n).symm 0 = 0 := by rw [← h0, Homeomorph.symm_apply_apply]
    rw [this]; exact hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 this
  refine ⟨ε / 2, half_pos hε, fun x hx => ?_⟩
  have hx' : crdV v n x ∈ Metric.ball 0 ε := by
    rw [mem_ball_zero_iff]; exact lt_of_le_of_lt hx (half_lt_self hε)
  have := hball hx'
  simpa using this
theorem exists_bound_nV {C : Set (Fin n → Fv F v ⊗[F] E)} (hC : IsCompact C) : ∃ R, ∀ y ∈ C, nV v y ≤ R := by
  obtain ⟨R, hR⟩ := hC.exists_bound_of_continuousOn (continuous_nV (v := v)).continuousOn
  exact ⟨R, fun x hx => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hR x hx)⟩

variable (v)

theorem crd_le_nA (a : Fv F v ⊗[F] E) (i : Fin (Module.finrank F E)) : ‖crd v a i‖ ≤ nA v a :=
  norm_le_pi_norm (crd v a) i

theorem sum_crd (a : Fv F v ⊗[F] E) : ∑ i, crd v a i • bA E v i = a := (bA E v).sum_equivFun a

theorem norm_comb_le {X : Type*} [SeminormedAddCommGroup X] [Module (Fv F v) X] [NormSMulClass (Fv F v) X]
    (a : Fv F v ⊗[F] E) (w : Fin (Module.finrank F E) → X) :
    ‖∑ i, crd v a i • w i‖ ≤ (∑ i, ‖w i‖) * nA v a := by
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (crd_le_nA v a i) (norm_nonneg _)

theorem exists_nA_mul : ∃ C, 0 ≤ C ∧ ∀ a b : Fv F v ⊗[F] E, nA v (a * b) ≤ C * nA v a * nA v b := by
  refine ⟨∑ i, ∑ j, nA v (bA E v i * bA E v j), Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    nA_nonneg _, fun a b => ?_⟩
  have hab : a * b = ∑ i, crd v a i • ∑ j, crd v b j • (bA E v i * bA E v j) := by
    conv_lhs => rw [← sum_crd v a, ← sum_crd v b]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm, mul_smul]
  rw [hab]
  have e : crd v (∑ i, crd v a i • ∑ j, crd v b j • (bA E v i * bA E v j)) =
      ∑ i, crd v a i • ∑ j, crd v b j • crd v (bA E v i * bA E v j) := by simp only [crd_sum, crd_smul]
  show ‖crd v _‖ ≤ _
  rw [e]
  calc _ ≤ (∑ i, ‖∑ j, crd v b j • crd v (bA E v i * bA E v j)‖) * nA v a :=
        norm_comb_le (X := Fin (Module.finrank F E) → Fv F v) v a _
    _ ≤ (∑ i, (∑ j, ‖crd v (bA E v i * bA E v j)‖) * nA v b) * nA v a := by
        exact mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun i _ =>
          norm_comb_le (X := Fin (Module.finrank F E) → Fv F v) v b _) (nA_nonneg a)
    _ = (∑ i, ∑ j, nA v (bA E v i * bA E v j)) * nA v a * nA v b := by
        rw [← Finset.sum_mul]; simp only [nA]; ring

theorem sigR_smul (σ : E →ₐ[F] E) (t : Fv F v) (a : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (t • a) = t • sigR (Fv F v) σ a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x e =>
    simp only [sigR, TensorProduct.smul_tmul', AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem exists_nA_sig (σ : E →ₐ[F] E) : ∃ C, 0 ≤ C ∧ ∀ a : Fv F v ⊗[F] E, nA v (sigR (Fv F v) σ a) ≤ C * nA v a := by
  refine ⟨∑ i, nA v (sigR (Fv F v) σ (bA E v i)), Finset.sum_nonneg fun i _ => nA_nonneg _, fun a => ?_⟩
  have : sigR (Fv F v) σ a = ∑ i, crd v a i • sigR (Fv F v) σ (bA E v i) := by
    conv_lhs => rw [← sum_crd v a]
    rw [map_sum]; simp only [sigR_smul]
  rw [this]; unfold nA; rw [crd_sum]; simp only [crd_smul]
  exact norm_comb_le v a _

theorem exists_trace_le : ∃ C, 0 ≤ C ∧ ∀ a : Fv F v ⊗[F] E,
    ‖Algebra.trace (Fv F v) (Fv F v ⊗[F] E) a‖ ≤ C * nA v a := by
  refine ⟨∑ i, ‖Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (bA E v i)‖, Finset.sum_nonneg fun i _ => norm_nonneg _,
    fun a => ?_⟩
  conv_lhs => rw [← sum_crd v a]
  rw [map_sum]; simp only [map_smul]
  exact norm_comb_le v a _

theorem trace_one_tmul (e : E) : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (1 ⊗ₜ e) =
    algebraMap F (Fv F v) (Algebra.trace F E e) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange]
  congr 1
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp [Algebra.coe_lmul_eq_mul, LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem crd_basis (i : Fin (Module.finrank F E)) : crd v (bA E v i) = Pi.single i 1 := by
  funext j
  simp [crd, Module.Basis.equivFun_apply, Module.Basis.repr_self, Finsupp.single_apply, Pi.single_apply, eq_comm]

theorem nA_basis_le (i : Fin (Module.finrank F E)) : nA v (bA E v i) ≤ 1 := by
  unfold nA; rw [crd_basis, pi_norm_le_iff_of_nonneg zero_le_one]
  intro j; by_cases h : j = i
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem exists_trace_ge : ∃ c, 0 < c ∧ ∀ a : Fv F v ⊗[F] E, ∃ a', nA v a' ≤ 1 ∧
    c * nA v a ≤ ‖Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (a' * a)‖ := by
  classical
  set b0 := Module.finBasis F E
  set G : Matrix (Fin (Module.finrank F E)) (Fin (Module.finrank F E)) (Fv F v) :=
    Matrix.of fun i k => Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (bA E v i * bA E v k) with hG
  have hGmap : G = (Algebra.traceMatrix F b0).map (algebraMap F (Fv F v)) := by
    refine Matrix.ext fun i k => ?_
    simp only [hG, Matrix.of_apply, Matrix.map_apply, Algebra.traceMatrix_apply, Algebra.traceForm_apply, bA,
      Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact trace_one_tmul (E := E) v _
  have hdet : IsUnit G.det := by
    have e : ((Algebra.traceMatrix F b0).map (algebraMap F (Fv F v))).det =
        algebraMap F (Fv F v) (Algebra.traceMatrix F b0).det := (RingHom.map_det _ _).symm
    rw [hGmap, e, isUnit_iff_ne_zero, Ne, map_eq_zero_iff _ (algebraMap F (Fv F v)).injective]
    exact Algebra.discr_not_zero_of_basis F b0
  set D : ℝ := ∑ k, ∑ i, ‖G⁻¹ k i‖ with hD
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨1 / (D + 1), by positivity, fun a => ?_⟩
  by_cases ha : nA v a = 0
  · exact ⟨0, by rw [nA_zero]; exact zero_le_one, by rw [ha, mul_zero]; exact norm_nonneg _⟩
  have hapos : 0 < nA v a := lt_of_le_of_ne (nA_nonneg a) (Ne.symm ha)
  by_contra hcon
  push Not at hcon
  have hlt : ∀ i, ‖Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (bA E v i * a)‖ < 1 / (D + 1) * nA v a :=
    fun i => hcon _ (nA_basis_le v i)

  have htr : ∀ i, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (bA E v i * a) = (G.mulVec (crd v a)) i := by
    intro i
    conv_lhs => rw [← sum_crd v a]
    rw [Finset.mul_sum, map_sum]
    simp only [mul_smul_comm, map_smul, Matrix.mulVec, dotProduct, hG, Matrix.of_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hinv : crd v a = G⁻¹.mulVec (G.mulVec (crd v a)) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  have hk : ∀ k, ‖crd v a k‖ ≤ D * (1 / (D + 1) * nA v a) := by
    intro k
    rw [hinv]
    simp only [Matrix.mulVec, dotProduct]
    refine (norm_sum_le _ _).trans ?_
    have : ∑ i, ‖G⁻¹ k i * (G.mulVec (crd v a)) i‖ ≤ (∑ i, ‖G⁻¹ k i‖) * (1 / (D + 1) * nA v a) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [norm_mul, ← htr]
      exact mul_le_mul_of_nonneg_left (hlt i).le (norm_nonneg _)
    refine this.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    rw [hD]
    exact Finset.single_le_sum (f := fun k => ∑ i, ‖G⁻¹ k i‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Finset.mem_univ k)
  have hle : nA v a ≤ D * (1 / (D + 1) * nA v a) := by
    unfold nA; exact (pi_norm_le_iff_of_nonneg (by positivity)).2 hk
  have : D * (1 / (D + 1) * nA v a) < nA v a := by
    rw [← mul_assoc, mul_one_div]
    have : D / (D + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
    calc D / (D + 1) * nA v a < 1 * nA v a := mul_lt_mul_of_pos_right this hapos
      _ = nA v a := one_mul _
  linarith

theorem exists_nM_mul (p q r : ℕ) : ∃ C, 0 ≤ C ∧ ∀ (x : Matrix (Fin p) (Fin q) (Fv F v ⊗[F] E))
    (y : Matrix (Fin q) (Fin r) (Fv F v ⊗[F] E)), nM v (x * y) ≤ C * nM v x * nM v y := by
  obtain ⟨C, hC0, hC⟩ := exists_nA_mul v (E := E)
  refine ⟨q * C, by positivity, fun x y => ?_⟩
  show nM v (fun i j => (x * y) i j) ≤ _
  refine (nM_le_iff (by have := nM_nonneg (v := v) x; have := nM_nonneg (v := v) y; positivity)).2 fun i j => ?_
  rw [Matrix.mul_apply]
  refine (nA_sum_le _ _).trans ?_
  calc ∑ k, nA v (x i k * y k j) ≤ ∑ _k : Fin q, C * nM v x * nM v y := Finset.sum_le_sum fun k _ =>
        (hC _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left (nA_le_nM x i k) hC0) (nA_le_nM y k j)
          (nA_nonneg _) (mul_nonneg hC0 (nM_nonneg x)))
    _ = q * C * nM v x * nM v y := by simp [Finset.sum_const, Finset.card_univ]; ring

theorem exists_nM_mulVec (p q : ℕ) : ∃ C, 0 ≤ C ∧ ∀ (x : Matrix (Fin p) (Fin q) (Fv F v ⊗[F] E))
    (y : Fin q → Fv F v ⊗[F] E), nV v (x.mulVec y) ≤ C * nM v x * nV v y := by
  obtain ⟨C, hC0, hC⟩ := exists_nA_mul v (E := E)
  refine ⟨q * C, by positivity, fun x y => ?_⟩
  rw [nV_le_iff (by have := nM_nonneg (v := v) x; have := nV_nonneg (v := v) y; positivity)]
  intro i
  simp only [Matrix.mulVec, dotProduct]
  refine (nA_sum_le _ _).trans ?_
  calc ∑ k, nA v (x i k * y k) ≤ ∑ _k : Fin q, C * nM v x * nV v y := Finset.sum_le_sum fun k _ =>
        (hC _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left (nA_le_nM x i k) hC0) (nA_le_nV y k)
          (nA_nonneg _) (mul_nonneg hC0 (nM_nonneg x)))
    _ = q * C * nM v x * nV v y := by simp [Finset.sum_const, Finset.card_univ]; ring

theorem exists_nM_sig (σ : E →ₐ[F] E) (p q : ℕ) : ∃ C, 0 ≤ C ∧ ∀ x : Matrix (Fin p) (Fin q) (Fv F v ⊗[F] E),
    nM v (x.map (sigR (Fv F v) σ)) ≤ C * nM v x := by
  obtain ⟨C, hC0, hC⟩ := exists_nA_sig v σ
  refine ⟨C, hC0, fun x => ?_⟩
  show nM v (fun i j => (x.map (sigR (Fv F v) σ)) i j) ≤ _
  refine (nM_le_iff (mul_nonneg hC0 (nM_nonneg x))).2 fun i j => ?_
  exact (hC _).trans (mul_le_mul_of_nonneg_left (nA_le_nM x i j) hC0)

def sigL (σ : E →ₐ[F] E) : (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fv F v ⊗[F] E) where
  toFun := sigR (Fv F v) σ
  map_add' := map_add _
  map_smul' := sigR_smul v σ

theorem continuous_sigR (σ : E →ₐ[F] E) : Continuous (sigR (Fv F v) σ) :=
  IsModuleTopology.continuous_of_linearMap (sigL v σ)

theorem isClosed_hermSet (σ : E →ₐ[F] E) (n : ℕ) :
    IsClosed ((HermR (Fv F v) σ n : AddSubgroup (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) :
      Set (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) := by
  have : ((HermR (Fv F v) σ n : AddSubgroup (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) :
      Set (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) =
      ⋂ a, ⋂ b, {S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | sigR (Fv F v) σ (S b a) = S a b} := by
    ext S; simp only [Set.mem_iInter, Set.mem_setOf_eq]; rfl
  rw [this]
  refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_eq ?_ ?_
  · exact (continuous_sigR v σ).comp ((continuous_apply a).comp (continuous_apply b))
  · exact (continuous_apply b).comp (continuous_apply a)

instance locallyCompact_Herm (σ : E →ₐ[F] E) (n : ℕ) : LocallyCompactSpace (HermR (Fv F v) σ n) :=
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → Fv F v ⊗[F] E))
  (isClosed_hermSet v σ n).locallyCompactSpace

theorem continuous_algNorm : Continuous (Algebra.norm (Fv F v) : Fv F v ⊗[F] E → Fv F v) := by
  classical
  have h : (Algebra.norm (Fv F v) : Fv F v ⊗[F] E → Fv F v) = fun a => (Algebra.leftMulMatrix (bA E v) a).det :=
    funext fun a => Algebra.norm_eq_matrix_det (bA E v) a
  rw [h]
  exact (IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix (bA E v)).toLinearMap).matrix_det

theorem isUnit_of_norm_ne_zero {a : Fv F v ⊗[F] E} (h : Algebra.norm (Fv F v) a ≠ 0) : IsUnit a := by
  rw [Algebra.norm_apply] at h
  have hu : IsUnit (Algebra.lmul (Fv F v) (Fv F v ⊗[F] E) a : Module.End (Fv F v) (Fv F v ⊗[F] E)) :=
    (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
  obtain ⟨b, hb⟩ := ((Module.End.isUnit_iff _).1 hu).2 1
  have hab : a * b = 1 := by simpa [Algebra.coe_lmul_eq_mul] using hb
  exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, rfl⟩

theorem exists_isUnit_det (n : ℕ) : ∃ r > 0, ∀ x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E),
    nM v x ≤ r → IsUnit (1 + x).det := by
  set f : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) → Fv F v := fun x => Algebra.norm (Fv F v) (1 + x).det
  have hf : Continuous f := (continuous_algNorm v).comp (continuous_const.add continuous_id).matrix_det
  have hU : {x | f x ≠ 0} ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :=
    (isOpen_ne_fun hf continuous_const).mem_nhds (by simp [f])
  obtain ⟨r, hr, hsub⟩ := exists_ballM_subset (v := v) (p := n) (q := n) hU
  exact ⟨r, hr, fun x hx => isUnit_of_norm_ne_zero v (hsub hx)⟩

theorem exists_norm_lt_one : ∃ ϖ : Fv F v, 0 < ‖ϖ‖ ∧ ‖ϖ‖ < 1 := exists_norm_lt_one' v

variable {v}

theorem continuous_psiV {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) : Continuous (psiV F ψ v) := continuous_psiV' hψ
theorem psiV_add (ψ : AddChar (AF F) ℂ) (x y : Fv F v) : psiV F ψ v (x + y) = psiV F ψ v x * psiV F ψ v y :=
  psiV_add' ψ x y
theorem psiV_zero (ψ : AddChar (AF F) ℂ) : psiV F ψ v 0 = 1 := psiV_zero' ψ
theorem norm_psiV {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (x : Fv F v) : ‖psiV F ψ v x‖ = 1 := norm_psiV' hψ x
theorem exists_psiV_ne_one {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) :
    ∃ y, psiV F ψ v y ≠ 1 := exists_psiV_ne_one' hcm hψ

theorem exists_psiV_small {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) :
    ∃ ε > 0, ∀ t : Fv F v, ‖t‖ ≤ ε → psiV F ψ v t = 1 :=
  OswLocFin.no_small_subgroups (psiV F ψ v) (continuous_psiV hψ) (psiV_add ψ) (psiV_zero ψ) (norm_psiV hψ)

theorem measurePreserving_of_addEquiv {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsAddHaarMeasure] (e : G ≃+ G) (he : Continuous e) (he' : Continuous e.symm)
    (B : Set G) (hB : IsCompact B) (hB' : (interior B).Nonempty) (heB : e ⁻¹' B = B) :
    MeasurePreserving e μ μ := OswLocFin.measurePreserving_of_addEquiv μ e he he' B hB hB' heB

theorem exists_nhds_invariant {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    {Φ : G → ℂ} (hΦ : IsSB Φ) : ∃ U ∈ 𝓝 (0 : G), ∀ Y, ∀ Z ∈ U, Φ (Y + Z) = Φ Y := OswLocFin.exists_nhds_invariant hΦ

end PositivityTheory.SiegelWeilFormula.SwLocFin
