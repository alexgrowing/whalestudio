import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsAutomorphicFormOfBddSubmodule
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsBasisAlgModLaplacianOfTypesCentre
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteDimensionalInfKerAevalMonic

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.finiteDimensional_of_bdd_cuspidal :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (S : Submodule ℂ (archSmooth K n)), Bdd S → (∀ φ ∈ S, IsCuspidal φ.1) → FiniteDimensional ℂ S := by
  intro K _ _ n S hS hcusp
  classical
  have hle : cuspForms K n ≤ archSmooth K n :=
    cuspForms_le_automorphicForms.trans automorphicForms_le_archSmooth
  let j : cuspForms K n →ₗ[ℂ] archSmooth K n := Submodule.inclusion hle
  have hj : Function.Injective j := Submodule.inclusion_injective hle
  have hju : ∀ (u : UEnv K n) (ψ : cuspForms K n), j (uActionCusp K n u ψ) = uAction u (j ψ) :=
    fun u ψ => rfl
  have hjf : ∀ (h : AdelicGLn.FiniteAdelicGL K n) (ψ : cuspForms K n),
      j (finRepCusp K n h ψ) = rtFin h (j ψ) := fun h ψ => rfl
  obtain ⟨d, b, P, hPm, hP⟩ := UpperTheory.exists_basis_algMod_laplacian_of_types_centre K n S hS.types hS.centre
  set Z := UnitaryAdmissible.centralZ K n with hZdef
  have hZc : UniversalEnvelopingAlgebra.ι ℝ Z ∈ (isExpLieAlgebra K n).centerU := by
    apply mem_center_of_forall_ι_commute
    intro x
    have h1 := UnitaryAdmissible.lie_centralZ (K := K) (n := n) x
    have h2 : UniversalEnvelopingAlgebra.ι ℝ ⁅Z, x⁆ = UniversalEnvelopingAlgebra.ι ℝ Z * UniversalEnvelopingAlgebra.ι ℝ x - UniversalEnvelopingAlgebra.ι ℝ x * UniversalEnvelopingAlgebra.ι ℝ Z := by
      rw [LieHom.map_lie, Ring.lie_def]
    rw [h1, map_zero] at h2
    exact (sub_eq_zero.mp h2.symm).symm
  obtain ⟨Q, hQm, hQ⟩ := hS.centre _ hZc
  obtain ⟨L, hLo, hL⟩ := hS.level
  let U : Subgroup (AdelicGLn.integralFiniteGL K n) := L.subgroupOf _
  have hUo : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) := hLo.preimage continuous_subtype_val
  have hP'm : (Polynomial.X * P).Monic := Polynomial.monic_X.mul hPm
  have hP'd : 0 < (Polynomial.X * P).natDegree := by
    rw [Polynomial.Monic.natDegree_mul Polynomial.monic_X hPm, Polynomial.natDegree_X]
    omega
  let N : Submodule ℂ (cuspForms K n) :=
    LinearMap.ker (Polynomial.aeval (uActionCusp K n (laplacianU K n b)) (Polynomial.X * P)) ⊓
      ⨅ u : U, LinearMap.ker (finRepCusp K n ((u : AdelicGLn.integralFiniteGL K n) : AdelicGLn.FiniteAdelicGL K n) - LinearMap.id)
  have hmemN : ∀ ψ, ψ ∈ N ↔ Polynomial.aeval (uActionCusp K n (laplacianU K n b)) (Polynomial.X * P) ψ = 0 ∧
      ∀ u : U, finRepCusp K n ((u : AdelicGLn.integralFiniteGL K n) : AdelicGLn.FiniteAdelicGL K n) ψ = ψ := by
    intro ψ
    simp only [N, Submodule.mem_inf, LinearMap.mem_ker, Submodule.mem_iInf, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
  have hTA : ∀ m, uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ Z) (uActionCusp K n (laplacianU K n b) m) =
      uActionCusp K n (laplacianU K n b) (uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ Z) m) := by
    intro m
    have hc := (Subalgebra.mem_center_iff.mp hZc) (laplacianU K n b)
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hc]
  have hTf : ∀ (h : AdelicGLn.FiniteAdelicGL K n) m,
      uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ Z) (finRepCusp K n h m) =
        finRepCusp K n h (uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ Z) m) := by
    intro h m
    apply hj
    rw [hju, hjf, hjf, hju, uAction_rtFin]
  have hTN : ∀ x ∈ N, uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ Z) x ∈ N := by
    intro x hx
    rw [hmemN] at hx ⊢
    refine ⟨?_, fun u => ?_⟩
    · rw [← map_aeval_apply_of_intertwine _ hTA, hx.1, map_zero]
    · rw [← hTf, hx.2 u]
  have hE : ∀ c : ℂ, FiniteDimensional ℂ ↥(N ⊓ (uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ Z)).eigenspace c) := by
    intro c
    refine UnitaryAdmissible.finiteDimensional_of_eigen b _ hP'm hP'd c U hUo _ ?_
    intro φ hφ
    rw [Submodule.mem_inf, hmemN, Module.End.mem_eigenspace_iff] at hφ
    exact ⟨hφ.1.1, hφ.2, fun u hu => hφ.1.2 ⟨u, hu⟩⟩
  have hfin := UpperTheory.finiteDimensional_inf_ker_aeval_monic _ _ N hTN hE Q hQm
  refine Submodule.finiteDimensional_of_le (S₂ := (N ⊓ LinearMap.ker (Polynomial.aeval
    (uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ Z)) Q)).map j) ?_
  intro φ hφ
  have hφc : (φ : AdelicGLn.AdelicGL K n → ℂ) ∈ cuspForms K n :=
    ⟨UpperTheory.isAutomorphicForm_of_bdd_submodule K n S hS φ hφ, hcusp φ hφ⟩
  have hjψ : j ⟨φ.1, hφc⟩ = φ := rfl
  refine ⟨⟨φ.1, hφc⟩, ?_, hjψ⟩
  refine Submodule.mem_inf.mpr ⟨(hmemN _).mpr ⟨?_, fun u => ?_⟩, ?_⟩
  · apply hj
    rw [map_zero, map_aeval_apply_of_intertwine j (hju _), hjψ, map_mul, Polynomial.aeval_X,
      Module.End.mul_apply, (Submodule.mem_bot ℂ).mp (hP φ hφ), map_zero]
  · apply hj
    rw [hjf, hjψ]
    apply Subtype.ext
    funext g
    exact hL φ hφ _ (Subgroup.mem_subgroupOf.mp u.2) g
  · rw [LinearMap.mem_ker]
    apply hj
    rw [map_zero, map_aeval_apply_of_intertwine j (hju _), hjψ]
    exact (Submodule.mem_bot ℂ).mp (hQ φ hφ)
