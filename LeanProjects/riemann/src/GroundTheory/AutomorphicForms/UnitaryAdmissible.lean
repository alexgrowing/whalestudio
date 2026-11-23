import Mathlib
import GroundTheory.AutomorphicForms.UnitaryAdmissible.FiltrationCocycleLiftCriterion
import GroundTheory.AutomorphicForms.UnitaryAdmissible.Scalar
import GroundTheory.AutomorphicForms.UnitaryAdmissible.CuspScalar
import GroundTheory.AutomorphicForms.UnitaryAdmissible.CuspFinite

namespace GroundTheory.Automorphic

namespace UnitaryAdmissible

open AutomorphicForm Module Set GKTensor CompactRep

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem finiteDimensional_of_map_subtype_le {V : Type*} [AddCommGroup V] [Module ℂ V]
    {U : Submodule ℂ V} (R : Submodule ℂ U) {S : Submodule ℂ V} [FiniteDimensional ℂ S]
    (h : R.map U.subtype ≤ S) : FiniteDimensional ℂ R := by
  have : FiniteDimensional ℂ (R.map U.subtype) := Submodule.finiteDimensional_of_le h
  exact Module.Finite.equiv (Submodule.equivMapOfInjective _ U.injective_subtype R).symm

theorem isAdmissible_cuspSubmodule (U : Submodule ℂ (cuspForms K n))
    (hρ : ∀ X, ∀ φ ∈ U, (gkModuleCusp K n).ρ X φ ∈ U) (hσ : ∀ k, ∀ φ ∈ U, (gkModuleCusp K n).σ k φ ∈ U)
    (hτ : ∀ g, ∀ φ ∈ U, finRepCusp K n g φ ∈ U)
    (hirr : (cuspSubmodule K n U hρ hσ hτ).IsIrreducible) :
    (cuspSubmodule K n U hρ hσ hτ).IsAdmissible := by
  set Mx := cuspSubmodule K n U hρ hσ hτ with hMx

  refine ⟨fun v => ?_, fun H hHc hHo c hc => ?_⟩
  · obtain ⟨W, -, hW⟩ := AutomorphicForm.exists_openSubgroup_rightInvariant
      (v : cuspForms K n).2.1.isSmooth (v : cuspForms K n).2.1.isKFinite
    refine Subgroup.isOpen_mono (H₁ := W.toSubgroup) (fun u hu => ?_) W.isOpen
    show Mx.τ u v = v
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact hW g u hu

  obtain ⟨d, b, ε, hε, horth, hskew⟩ := exists_archCartanBasis (K := K) (n := n)
  have hε2 : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with e | e <;> rw [e] <;> norm_num
  have hK : ∀ i, ε i = -1 → ∀ t : ℝ,
      (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie (b i)) ∈ archCompact K n := by
    intro i hi t
    refine expG_mem_archCompact_of_skew _ ?_
    have h := hskew i hi
    rw [mem_archSkew] at h
    show Matrix.conjTranspose (t • mat (b i : ArchMatrix K n)) = -(t • mat (b i : ArchMatrix K n))
    rw [Matrix.conjTranspose_smul, star_trivial, h, smul_neg]

  obtain ⟨ω, hω⟩ := exists_casimir_eq_smul U hρ hσ hτ hirr b ε hε2 horth
  obtain ⟨lam, hlam⟩ := exists_lieActionCusp_eq_smul U hρ hσ hτ hirr (centralZ K n) lie_centralZ
    Ad_centralZ

  obtain ⟨q, hqm, hqd, hq⟩ :=
    exists_aeval_eq_zero_of_mem_isotypic Mx.gk (lapZ b ε) (lapZ_mem b ε hε hK) hc
  set P := q.comp (Polynomial.X - Polynomial.C ω) with hP
  have hPm : P.Monic :=
    hqm.comp (Polynomial.monic_X_sub_C ω) (by rw [Polynomial.natDegree_X_sub_C]; exact one_ne_zero)
  have hPd : 0 < P.natDegree := by
    rw [hP, Polynomial.natDegree_comp, Polynomial.natDegree_X_sub_C, mul_one]
    exact hqd

  set U₀ : Subgroup (AdelicGLn.integralFiniteGL K n) :=
    H.comap (AdelicGLn.integralFiniteGL K n).subtype with hU₀
  have hU₀o : IsOpen (U₀ : Set (AdelicGLn.integralFiniteGL K n)) :=
    hHo.preimage continuous_subtype_val

  set S : Submodule ℂ (cuspForms K n) :=
    LinearMap.ker (Polynomial.aeval (uActionCusp K n (laplacianU K n b)) P) ⊓
      LinearMap.ker (lieActionCusp K n (centralZ K n) - lam • 1) ⊓
        ⨅ u ∈ U₀, LinearMap.ker (finRepCusp K n (u : AdelicGLn.FiniteAdelicGL K n) - 1) with hS
  have hSfin : FiniteDimensional ℂ S := by
    refine finiteDimensional_of_eigen b P hPm hPd lam U₀ hU₀o S fun φ hφ => ?_
    rw [hS, Submodule.mem_inf, Submodule.mem_inf, Submodule.mem_iInf] at hφ
    obtain ⟨⟨h1, h2⟩, h3⟩ := hφ
    refine ⟨h1, ?_, fun u hu => ?_⟩
    · have := LinearMap.mem_ker.1 h2
      rwa [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at this
    · have := LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 (h3 u) hu)
      rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this

  refine finiteDimensional_of_map_subtype_le _ (S := S) ?_
  rintro _ ⟨v, ⟨w, rfl⟩, rfl⟩
  have hvc : (kProj Mx.gk.isKFinite hc (w : U) : Mx.gk.σ.asModule) ∈ c :=
    kProj_mem_component Mx.gk.isKFinite hc _
  rw [hS, Submodule.mem_inf, Submodule.mem_inf, Submodule.mem_iInf]
  refine ⟨⟨?_, ?_⟩, fun u => (Submodule.mem_iInf _).2 fun hu => ?_⟩
  · exact aeval_laplacian_eq_zero U hρ hσ hτ b ε hε ω hω q (hq _ hvc)
  · rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      sub_eq_zero]
    exact hlam _ (kProj Mx.gk.isKFinite hc (w : U)).2
  · rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    have hcomm : ∀ k, Mx.τ (u : AdelicGLn.FiniteAdelicGL K n) * Mx.gk.σ k =
        Mx.gk.σ k * Mx.τ (u : AdelicGLn.FiniteAdelicGL K n) := fun k => (Mx.comm_σ k _).symm
    have hfix : Mx.τ (u : AdelicGLn.FiniteAdelicGL K n) (kProj Mx.gk.isKFinite hc (w : U)) =
        kProj Mx.gk.isKFinite hc (w : U) := by
      rw [← kProj_comm Mx.gk.isKFinite hc hcomm]
      congr 1
      exact w.2 _ hu
    exact congrArg Subtype.val hfix

end UnitaryAdmissible

end GroundTheory.Automorphic
