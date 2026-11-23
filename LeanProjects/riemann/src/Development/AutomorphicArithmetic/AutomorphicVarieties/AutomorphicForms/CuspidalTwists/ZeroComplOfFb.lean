import Mathlib
import GroundTheory.AutomorphicForms.TensorProductTheorem.CuspidalRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalTwists.Reduce
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.SiegelHeight

noncomputable section

open NumberField GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

attribute [local instance 100] LieRing.ofAssociativeRing

namespace UpperTheory.V.TR.SS

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ}

theorem zeroCompl_of (hto : ∀ φ : Sm F a, IsCuspForm φ → φ.1 ∈ cuspForms F a)
    (hof : ∀ f ∈ cuspForms F a, ∃ h : f ∈ Sm F a, IsCuspForm ⟨f, h⟩)
    (hlie : ∃ e : Lie F a → (isExpLieAlgebra F a).lieSubalgebra, Function.Surjective e ∧
      ((e (oneL F a) : (isExpLieAlgebra F a).lieSubalgebra) : ArchMatrix F a) = 1 ∧
      ∀ (X : Lie F a) (φ : Sm F a) (h : φ.1 ∈ archSmooth F a),
        (lie F a X φ).1 = (uAction (UniversalEnvelopingAlgebra.ι ℝ (e X)) ⟨φ.1, h⟩).1)
    (hcpt : ∃ e : Kinf F a → archCompact F a, Function.Surjective e ∧
      ∀ k, infGL F a (Unitary.toUnits k) = infEmb F a (e k))
    (hfin : ∀ k, finGL F a k = finEmb F a k) : ZeroCompl F a := by
  obtain ⟨e, he, he1, hL⟩ := hlie
  obtain ⟨c, hc, hK⟩ := hcpt
  have hle : cuspForms F a ≤ Sm F a := fun f hf => (hof f hf).1
  let j : cuspForms F a →ₗ[ℂ] Sm F a := Submodule.inclusion hle
  have hj : Function.Injective j := Submodule.inclusion_injective _
  have a1 : ∀ X ψ, act (.lie X) (j ψ) = j ((gkModuleCusp F a).ρ (e X) ψ) := fun X ψ =>
    Subtype.ext (hL X (j ψ) ψ.2.1.isSmooth.1)
  have a2 : ∀ k ψ, act (.cpt k) (j ψ) = j ((gkModuleCusp F a).σ (c k) ψ) := fun k ψ =>
    Subtype.ext (funext fun g => congrArg (fun x => ψ.1 (g * x)) (hK k))
  have a3 : ∀ k ψ, act (.fin k) (j ψ) = j (finRepCusp F a k ψ) := fun k ψ =>
    Subtype.ext (funext fun g => congrArg (fun x => ψ.1 (g * x)) (hfin k))
  have hmap : ∀ W : Submodule ℂ (cuspForms F a), (∀ X, ∀ φ ∈ W, (gkModuleCusp F a).ρ X φ ∈ W) →
      (∀ k, ∀ φ ∈ W, (gkModuleCusp F a).σ k φ ∈ W) → (∀ g, ∀ φ ∈ W, finRepCusp F a g φ ∈ W) →
      IsStable (W.map j) := by
    rintro W h1 h2 h3 o _ ⟨ψ, hψ, rfl⟩
    cases o with
    | fin k => exact ⟨_, h3 k ψ hψ, (a3 k ψ).symm⟩
    | cpt k => exact ⟨_, h2 _ ψ hψ, (a2 k ψ).symm⟩
    | lie X => exact ⟨_, h1 _ ψ hψ, (a1 X ψ).symm⟩
  refine ⟨(centralCuspForms F a).map j, ?_, fun φ h1 h2 => ⟨⟨φ.1, hto φ h1⟩, fun s x => ?_, rfl⟩,
    hmap _ (fun X _ h => ρ_mem_centralCuspForms X h) (fun k _ h => σ_mem_centralCuspForms k h)
      fun g _ h => finRepCusp_mem_centralCuspForms g h, fun U hU hs => ?_⟩
  · rintro _ ⟨ψ, -, rfl⟩
    exact (hof ψ.1 ψ.2).2
  · have h3 : (gkModuleCusp F a).ρ (e (oneL F a)) ⟨φ.1, hto φ h1⟩ = 0 :=
      hj ((a1 _ _).symm.trans (h2.trans (map_zero j).symm))
    have h4 : UnitaryAdmissible.centralZ F a = UnitaryAdmissible.centralExp F a • e (oneL F a) := Subtype.ext (by
      rw [UnitaryAdmissible.coe_centralZ, Algebra.algebraMap_eq_smul_one, ← he1]; rfl)
    have h5 : lieActionCusp F a (UnitaryAdmissible.centralZ F a) ⟨φ.1, hto φ h1⟩ = (0 : ℂ) • ⟨φ.1, hto φ h1⟩ := by
      rw [h4, map_smul, zero_smul, LinearMap.smul_apply]
      exact (congrArg _ h3).trans (smul_zero _)
    have h6 := UnitaryAdmissible.apply_mul_centralSection h5 x s
    rw [Reduction.centralSection_mul_comm, h6]
    simp
  · have hU' : U ≤ LinearMap.range j := hU.trans LinearMap.map_le_range
    obtain ⟨D, d1, d2, d3, d4, d5, d6⟩ := exists_compl_centralCuspForms (U.comap j)
      ((Submodule.comap_mono hU).trans (Submodule.comap_map_eq_of_injective hj _).le)
      (fun X ψ h => by obtain ⟨X, rfl⟩ := he X; exact show j _ ∈ U from a1 X ψ ▸ hs _ _ h)
      (fun k ψ h => by obtain ⟨k, rfl⟩ := hc k; exact show j _ ∈ U from a2 k ψ ▸ hs _ _ h)
      (fun k ψ h => show j _ ∈ U from a3 k ψ ▸ hs _ _ h)
    have hUe : (U.comap j).map j = U := Submodule.map_comap_eq_self hU'
    refine ⟨D.map j, Submodule.map_mono d1, hmap D d2 d3 d4, ?_, ?_⟩
    · rw [← hUe, ← Submodule.map_inf j hj, d5, Submodule.map_bot]
    · rw [← hUe, ← Submodule.map_sup, d6]

theorem zeroCompl_of_fb (hto : ∀ φ : Sm F a, IsCuspForm φ → φ.1 ∈ cuspForms F a)
    (hof : ∀ f ∈ cuspForms F a, ∃ h : f ∈ Sm F a, IsCuspForm ⟨f, h⟩)
    (hlie : ∀ (X : Lie F a) (φ : Sm F a) (h : φ.1 ∈ archSmooth F a),
        (lie F a X φ).1 = (uAction (UniversalEnvelopingAlgebra.ι ℝ (Fb.lieEq F a X)) ⟨φ.1, h⟩).1)
    (hcpt : Fb.CptIff) : ZeroCompl F a := by
  refine zeroCompl_of hto hof ⟨Fb.lieEq F a, (Fb.lieEq F a).surjective, Fb.lieEq_oneL, hlie⟩
    ⟨fun k => ⟨Fb.grpEq F a (Unitary.toUnits k), (hcpt F a _).2 k.2⟩, fun k => ?_, fun k => (Fb.infEmb_grpEq _).symm⟩
    fun k => by rw [Fb.finEmb_eq]
  obtain ⟨y, hy⟩ := (Fb.grpEq F a).surjective k.1
  refine ⟨⟨y.val, (hcpt F a y).1 (hy ▸ k.2)⟩, Subtype.ext (Eq.trans (congrArg (Fb.grpEq F a) (show _ = y from Units.ext rfl)) hy)⟩

end UpperTheory.V.TR.SS
