import Mathlib
import GroundTheory.AutomorphicForms.UnitaryAdmissible.Scalar
import GroundTheory.AutomorphicForms.TensorProductTheorem.NonemptyAdelicDecomposition
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableCartan
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableLaplacian

namespace GroundTheory.Automorphic

namespace UnitaryAdmissible

open AutomorphicForm Module Set

attribute [local instance 100] LieRing.ofAssociativeRing

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
variable (U : Submodule ℂ (cuspForms K n))
  (hρ : ∀ X, ∀ φ ∈ U, (gkModuleCusp K n).ρ X φ ∈ U) (hσ : ∀ k, ∀ φ ∈ U, (gkModuleCusp K n).σ k φ ∈ U)
  (hτ : ∀ g, ∀ φ ∈ U, finRepCusp K n g φ ∈ U)

include hρ in

theorem uActionCusp_mem (u : UEnv K n) {φ : cuspForms K n}
    (hφ : φ ∈ U) : uActionCusp K n u φ ∈ U := by
  obtain ⟨t, rfl⟩ : ∃ t, UniversalEnvelopingAlgebra.mkAlgHom ℝ _ t = u :=
    RingCon.mkₐ_surjective (α := ℝ) (UniversalEnvelopingAlgebra.ringCon ℝ _) u
  induction t using TensorAlgebra.induction generalizing φ with
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes]
    exact Submodule.smul_of_tower_mem _ r hφ
  | ι X => exact hρ X φ hφ
  | mul a b ha hb =>
    rw [map_mul, map_mul, Module.End.mul_apply]
    exact ha (hb hφ)
  | add a b ha hb =>
    rw [map_add, map_add, LinearMap.add_apply]
    exact U.add_mem (ha hφ) (hb hφ)

theorem archTraceForm_AdLie (g : archGroup K n) (X Y : (isExpLieAlgebra K n).lieSubalgebra) :
    archTraceForm K n ((isExpLieAlgebra K n).AdLie g X) ((isExpLieAlgebra K n).AdLie g Y) =
      archTraceForm K n X Y := by
  rw [archTraceForm_apply, archTraceForm_apply]
  congr 1
  have hgi : (((g⁻¹ : archGroup K n) : (ArchMatrix K n)ˣ) : ArchMatrix K n) *
      (((g : archGroup K n) : (ArchMatrix K n)ˣ) : ArchMatrix K n) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    rfl
  have hgi' : mat (((g⁻¹ : archGroup K n) : (ArchMatrix K n)ˣ) : ArchMatrix K n) *
      mat (((g : archGroup K n) : (ArchMatrix K n)ˣ) : ArchMatrix K n) = 1 := by
    rw [← mat_mul, hgi, mat_one]
  set A := mat (((g : archGroup K n) : (ArchMatrix K n)ˣ) : ArchMatrix K n)
  set C := mat (((g⁻¹ : archGroup K n) : (ArchMatrix K n)ˣ) : ArchMatrix K n)
  change Matrix.trace (A * mat (X : ArchMatrix K n) * C * (A * mat (Y : ArchMatrix K n) * C)) =
    Matrix.trace (mat (X : ArchMatrix K n) * mat (Y : ArchMatrix K n))
  have e : A * mat (X : ArchMatrix K n) * C * (A * mat (Y : ArchMatrix K n) * C) =
      A * (mat (X : ArchMatrix K n) * mat (Y : ArchMatrix K n)) * C := by
    rw [show A * mat (X : ArchMatrix K n) * C * (A * mat (Y : ArchMatrix K n) * C) =
      A * mat (X : ArchMatrix K n) * (C * A) * mat (Y : ArchMatrix K n) * C by
        simp only [Matrix.mul_assoc], hgi', Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hgi', Matrix.one_mul]

theorem exists_uActionCusp_eq_smul (hirr : (cuspSubmodule K n U hρ hσ hτ).IsIrreducible) (u : UEnv K n)
    (hu : u ∈ (isExpLieAlgebra K n).centerU)
    (hcomm : ∀ k φ, archCompactRepCusp K n k (uActionCusp K n u φ) =
      uActionCusp K n u (archCompactRepCusp K n k φ)) :
    ∃ c : ℂ, ∀ φ ∈ U, uActionCusp K n u φ = c • φ := by
  set T : Module.End ℂ U := (uActionCusp K n u).restrict fun φ hφ => uActionCusp_mem U hρ u hφ
  obtain ⟨c, hc⟩ := exists_eq_smul_one (cuspSubmodule K n U hρ hσ hτ) hirr T
    (fun X => LinearMap.ext fun φ => Subtype.ext (by
      show uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ X) (uActionCusp K n u φ) =
        uActionCusp K n u (uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ X) φ)
      rw [← Module.End.mul_apply, ← map_mul, Subalgebra.mem_center_iff.1 hu, map_mul,
        Module.End.mul_apply]))
    (fun k => LinearMap.ext fun φ => Subtype.ext (hcomm k φ))
    (fun g => LinearMap.ext fun φ => Subtype.ext (by
      show finRepCusp K n g (uActionCusp K n u φ) = uActionCusp K n u (finRepCusp K n g φ)
      rw [uActionCusp_finRepCusp]))
    (fun v => by
      set S₀ := Submodule.span ℂ ((fun z => uActionCusp K n z (v : cuspForms K n)) ''
        ((isExpLieAlgebra K n).centerU : Set (UEnv K n))) with hS₀
      have hle : cuspForms K n ≤ archSmooth K n :=
        cuspForms_le_automorphicForms.trans automorphicForms_le_archSmooth
      have hinc : Function.Injective (Submodule.inclusion hle) :=
        Submodule.inclusion_injective _
      have hS₀fin : FiniteDimensional ℂ S₀ := by
        have hZ := (v : cuspForms K n).2.1.isZFinite
        have e : S₀.map (Submodule.inclusion hle) =
            Submodule.span ℂ ((fun z => uAction z (⟨(v : cuspForms K n), (v : cuspForms K n).2.1.isSmooth.1⟩ :
              archSmooth K n)) ''
              ((isExpLieAlgebra K n).centerU : Set (UEnv K n))) := by
          rw [hS₀, Submodule.map_span, Set.image_image]
          rfl
        have : FiniteDimensional ℂ (S₀.map (Submodule.inclusion hle)) := by
          rw [e]; exact hZ
        exact Module.Finite.equiv (Submodule.equivMapOfInjective _ hinc S₀).symm
      refine ⟨S₀.comap U.subtype, ?_, ?_, ?_⟩
      · have h1 : (S₀.comap U.subtype).map U.subtype ≤ S₀ :=
          Submodule.map_comap_le _ _
        have : FiniteDimensional ℂ ((S₀.comap U.subtype).map U.subtype) :=
          Submodule.finiteDimensional_of_le h1
        exact Module.Finite.equiv
          (Submodule.equivMapOfInjective _ U.injective_subtype _).symm
      · show (v : cuspForms K n) ∈ S₀
        refine Submodule.subset_span ⟨1, Subalgebra.one_mem _, ?_⟩
        show uActionCusp K n 1 (v : cuspForms K n) = v
        rw [map_one, Module.End.one_apply]
      · have key : ∀ x ∈ S₀, uActionCusp K n u x ∈ S₀ := by
          intro x hx
          induction hx using Submodule.span_induction with
          | mem x hx =>
            obtain ⟨z, hz, rfl⟩ := hx
            refine Submodule.subset_span ⟨u * z, Subalgebra.mul_mem _ hu hz, ?_⟩
            show uActionCusp K n (u * z) (v : cuspForms K n) = _
            rw [map_mul, Module.End.mul_apply]
          | zero => rw [map_zero]; exact S₀.zero_mem
          | add x y _ _ hx hy => rw [map_add]; exact S₀.add_mem hx hy
          | smul a x _ hx => rw [map_smul]; exact S₀.smul_mem a hx
        intro w hw
        exact key _ hw)
  refine ⟨c, fun φ hφ => ?_⟩
  have := congrArg (fun f : Module.End ℂ U => ((f ⟨φ, hφ⟩ : U) : cuspForms K n)) hc
  simpa [T] using this

theorem casimirOp_gkModuleCusp {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ (isExpLieAlgebra K n).lieSubalgebra) (ε : ι → ℝ) :
    casimirOp (gkModuleCusp K n) b ε = uActionCusp K n (casimir b ε) := by
  unfold casimirOp casimir
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_mul]
  rfl

theorem exists_casimir_eq_smul (hirr : (cuspSubmodule K n U hρ hσ hτ).IsIrreducible) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι ℝ (isExpLieAlgebra K n).lieSubalgebra) (ε : ι → ℝ)
    (hε : ∀ i, ε i * ε i = 1)
    (horth : ∀ i j, archTraceForm K n (b i) (b j) = if i = j then ε i else 0) :
    ∃ c : ℂ, ∀ φ ∈ U, uActionCusp K n (casimir b ε) φ = c • φ := by
  refine exists_uActionCusp_eq_smul U hρ hσ hτ hirr _
    (casimir_mem_center hε horth archTraceForm_symm archTraceForm_lie) fun k φ => ?_
  have := σ_mul_casimirOp (gkModuleCusp K n) hε horth archTraceForm_symm
    (fun k X Y => archTraceForm_AdLie (k : archGroup K n) X Y) k
  rw [casimirOp_gkModuleCusp] at this
  exact congrArg (fun f : Module.End ℂ (cuspForms K n) => f φ) this

theorem exists_lieActionCusp_eq_smul (hirr : (cuspSubmodule K n U hρ hσ hτ).IsIrreducible)
    (Z₀ : (isExpLieAlgebra K n).lieSubalgebra)
    (hZ : ∀ X : (isExpLieAlgebra K n).lieSubalgebra, ⁅Z₀, X⁆ = 0)
    (hAd : ∀ g : archGroup K n, (isExpLieAlgebra K n).Ad g ((isExpLieAlgebra K n).ofLie Z₀) =
      (isExpLieAlgebra K n).ofLie Z₀) :
    ∃ c : ℂ, ∀ φ ∈ U, lieActionCusp K n Z₀ φ = c • φ := by
  refine exists_uActionCusp_eq_smul U hρ hσ hτ hirr (UniversalEnvelopingAlgebra.ι ℝ Z₀)
    (mem_center_of_forall_ι_commute fun X => ?_) fun k φ => ?_
  · have e : ⁅UniversalEnvelopingAlgebra.ι ℝ X, UniversalEnvelopingAlgebra.ι ℝ Z₀⁆ = 0 := by
      rw [← LieHom.map_lie, ← lie_skew, hZ, neg_zero, map_zero]
    rw [Ring.lie_def, sub_eq_zero] at e
    exact e
  · have := (gkModuleCusp K n).map_ρ k ((isExpLieAlgebra K n).ofLie Z₀) φ
    rw [hAd] at this
    exact this

noncomputable def lapZ {d : ℕ} (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra K n).lieSubalgebra)
    (ε : Fin d → ℝ) (i : Fin d) : (isExpLieAlgebra K n).lieSubalgebra :=
  Real.sqrt (1 - ε i) • b i

theorem lapZ_mem {d : ℕ} (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra K n).lieSubalgebra)
    (ε : Fin d → ℝ) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hK : ∀ i, ε i = -1 → ∀ t : ℝ,
      (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie (b i)) ∈ archCompact K n)
    (i : Fin d) (t : ℝ) :
    (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie (lapZ b ε i)) ∈ archCompact K n := by
  rcases hε i with e | e
  · have h0 : lapZ b ε i = 0 := by simp [lapZ, e]
    rw [h0]
    have : (isExpLieAlgebra K n).ofLie (0 : (isExpLieAlgebra K n).lieSubalgebra) = 0 := rfl
    rw [this, smul_zero, IsExpLieAlgebra.expG_zero]
    exact (archCompact K n).one_mem
  · have := hK i e (t * Real.sqrt (1 - ε i))
    convert this using 2
    rw [mul_smul]
    rfl

theorem aeval_apply_eq_of_eqOn {V : Type*} [AddCommGroup V] [Module ℂ V] (A B : Module.End ℂ V)
    (W : Submodule ℂ V) (hA : ∀ w ∈ W, A w ∈ W) (hAB : ∀ w ∈ W, A w = B w) (q : Polynomial ℂ)
    {w : V} (hw : w ∈ W) : Polynomial.aeval A q w = Polynomial.aeval B q w := by
  have h1 := AutomorphicForm.map_aeval_apply_of_intertwine W.subtype (A := A.restrict hA) (B := A)
    (fun _ => rfl) q ⟨w, hw⟩
  have h2 := AutomorphicForm.map_aeval_apply_of_intertwine W.subtype (A := A.restrict hA) (B := B)
    (fun x => hAB x x.2) q ⟨w, hw⟩
  exact h1.symm.trans h2

theorem aeval_laplacian_eq_zero {d : ℕ}
    (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra K n).lieSubalgebra) (ε : Fin d → ℝ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (ω : ℂ) (hω : ∀ φ ∈ U, uActionCusp K n (casimir b ε) φ = ω • φ) (q : Polynomial ℂ) {φ : U}
    (hq : Polynomial.aeval (∑ i, (cuspSubmodule K n U hρ hσ hτ).gk.ρ (lapZ b ε i) *
      (cuspSubmodule K n U hρ hσ hτ).gk.ρ (lapZ b ε i)) q φ = 0) :
    Polynomial.aeval (uActionCusp K n (laplacianU K n b)) (q.comp (Polynomial.X - Polynomial.C ω))
      (φ : cuspForms K n) = 0 := by
  set M := (cuspSubmodule K n U hρ hσ hτ).gk
  set L := uActionCusp K n (laplacianU K n b)
  set B : Module.End ℂ (cuspForms K n) := ∑ i,
    uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ (lapZ b ε i)) *
      uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ (lapZ b ε i))
  have hsq : ∀ i, (1 - ε i) = Real.sqrt (1 - ε i) * Real.sqrt (1 - ε i) := fun i =>
    (Real.mul_self_sqrt (by rcases hε i with e | e <;> rw [e] <;> norm_num)).symm
  have hAB : ∀ ψ ∈ U, (L - ω • 1) ψ = B ψ := by
    intro ψ hψ
    have e1 : L ψ = ω • ψ + ∑ i, (1 - ε i) • uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ (b i))
          (uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ (b i)) ψ) := by
      show uActionCusp K n (laplacianU K n b) ψ = _
      rw [laplacianU_eq_casimir_add b ε, map_add, LinearMap.add_apply, hω _ hψ, map_sum,
        LinearMap.sum_apply]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, map_mul, LinearMap.smul_apply, Module.End.mul_apply]
    rw [LinearMap.sub_apply, e1, LinearMap.smul_apply, Module.End.one_apply, add_sub_cancel_left,
      LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Module.End.mul_apply]
    simp only [lapZ, map_smul, LinearMap.smul_apply]
    rw [LinearMap.map_smul_of_tower, smul_smul, ← hsq]
  have hAU : ∀ ψ ∈ U, (L - ω • 1) ψ ∈ U := by
    intro ψ hψ
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact U.sub_mem (uActionCusp_mem U hρ _ hψ) (U.smul_mem ω hψ)
  rw [Polynomial.aeval_comp]
  have e2 : Polynomial.aeval L (Polynomial.X - Polynomial.C ω) = L - ω • 1 := by
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
  rw [e2, aeval_apply_eq_of_eqOn (L - ω • 1) B U hAU hAB q φ.2]
  have h3 := AutomorphicForm.map_aeval_apply_of_intertwine U.subtype
    (A := ∑ i, M.ρ (lapZ b ε i) * M.ρ (lapZ b ε i)) (B := B) (fun x => by
      simp only [B, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
      rfl) q φ
  rw [Submodule.subtype_apply, Submodule.subtype_apply, hq] at h3
  exact h3.symm.trans rfl

end UnitaryAdmissible

end GroundTheory.Automorphic
