import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChiDetSplitCentre
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfCommutingFiniteAlgebraJointEiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalEigenIntertwinersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompMemKinfEquivariantAutomorphicMapsStatement

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

namespace GlobalTheory.AutGrowth.KilledFin

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem cap_commute_Zalg (τ : E →+* ℂ) (u : ℂ) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    Commute (cap τ u) z :=
  commute_Zalg (fun X => GlobalTheory.SpehInfChar.cap_commute_act τ u (.lie X)) hz

theorem Zalg_commute {z z' : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) (hz' : z' ∈ Zalg E a) :
    Commute z z' := by
  have hle : Zalg E a ≤ Subalgebra.centralizer ℂ {z'} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨τ, u, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    exact (cap_commute_Zalg τ u hz').eq.symm
  have h := hle hz
  rw [Subalgebra.mem_centralizer_iff] at h
  exact (h z' rfl).symm

variable (φ : Sm E a) (L : Subgroup (GL (Fin a) (Af E)))

def postZ (z : Module.End ℂ (Sm E a)) (hz : z ∈ Zalg E a) : Module.End ℂ (mapsJ φ L) where
  toFun T := ⟨z ∘ₗ T.1, by
    have hT : T.1 ∈ maps L (spanK E a φ) (spanK_stable φ) ∧
        ∀ z ∈ Zalg E a, z φ = 0 → ∀ w, z (T.1 w) = 0 := T.2
    show _ ∧ _
    refine ⟨GlobalTheory.T.centre_comp_mem_kinfEquivariantAutomorphicMaps E a L (spanK E a φ) (spanK_stable φ) T.1 hT.1 z hz, fun z' hz' h0 w => ?_⟩
    show z' (z (T.1 w)) = 0
    rw [← Module.End.mul_apply, ← (Zalg_commute hz hz').eq, Module.End.mul_apply, hT.2 z' hz' h0 w, map_zero]⟩
  map_add' T T' := by ext; simp
  map_smul' c T := by ext; simp

@[simp] theorem postZ_apply (z : Module.End ℂ (Sm E a)) (hz : z ∈ Zalg E a) (T : mapsJ φ L) :
    (postZ φ L z hz T).1 = z ∘ₗ T.1 := rfl

def postZAlg : Zalg E a →ₐ[ℂ] Module.End ℂ (mapsJ φ L) where
  toFun z := postZ φ L z.1 z.2
  map_one' := by ext; simp
  map_mul' z z' := by ext; simp
  map_zero' := by ext; simp
  map_add' z z' := by ext; simp
  commutes' c := by ext; simp

end GlobalTheory.AutGrowth.KilledFin

namespace GlobalTheory.AutGrowth.KilledFin

theorem fd_adjoin_of_ker_le (M : Type) [AddCommGroup M] [Module ℂ M] (A : Type) [Ring A] [Algebra ℂ A]
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : A →ₐ[ℂ] Module.End ℂ M) (ev : A →ₗ[ℂ] V)
    (hev : FiniteDimensional ℂ (LinearMap.range ev)) (hker : LinearMap.ker ev ≤ LinearMap.ker ρ.toLinearMap)
    (S : Set (Module.End ℂ M)) (hS : S ⊆ ρ.range) : FiniteDimensional ℂ (Algebra.adjoin ℂ S) := by
  haveI : FiniteDimensional ℂ (A ⧸ LinearMap.ker ev) :=
    LinearEquiv.finiteDimensional (ev.quotKerEquivRange).symm
  have hR : FiniteDimensional ℂ (LinearMap.range ρ.toLinearMap) := by
    rw [← Submodule.range_liftQ (LinearMap.ker ev) ρ.toLinearMap hker]
    infer_instance
  have hle : Subalgebra.toSubmodule (Algebra.adjoin ℂ S) ≤ LinearMap.range ρ.toLinearMap := by
    intro x hx
    obtain ⟨y, rfl⟩ := Algebra.adjoin_le hS hx
    exact ⟨y, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.AutGrowth.KilledFin

namespace GlobalTheory.AutGrowth.KilledFin

theorem finiteDimensional_mapsJ : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E]
    [IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsAutForm φ → ∀ L : Subgroup (GL (Fin a) (Af E)),
    IsOpen (L : Set (GL (Fin a) (Af E))) → FiniteDimensional ℂ (mapsJ φ L) := by
  intro hP E _ _ _ a φ hφ L hL
  have hcap : ∀ (τ : E →+* ℂ) (u : ℂ), cap (a := a) τ u ∈ Zalg E a := fun τ u =>
    Algebra.subset_adjoin ⟨τ, u, rfl⟩
  let S : Set (Module.End ℂ (mapsJ φ L)) := {s | ∃ τ u, s = postZ φ L (cap τ u) (hcap τ u)}
  refine GlobalTheory.T.finiteDimensional_of_commuting_finiteAlgebra_jointEigen (mapsJ φ L) S ?_ ?_ ?_
  · rintro _ ⟨τ, u, rfl⟩ _ ⟨τ', u', rfl⟩
    refine LinearMap.ext fun T => Subtype.ext (LinearMap.ext fun w => ?_)
    show cap τ u (cap τ' u' (T.1 w)) = cap τ' u' (cap τ u (T.1 w))
    rw [← Module.End.mul_apply, (Zalg_commute (hcap τ u) (hcap τ' u')).eq, Module.End.mul_apply]
  · let ev : Zalg E a →ₗ[ℂ] Sm E a := (LinearMap.applyₗ φ).comp (Zalg E a).val.toLinearMap
    have hker : LinearMap.ker ev ≤ LinearMap.ker (postZAlg φ L).toLinearMap := by
      intro z hz
      rw [LinearMap.mem_ker] at hz ⊢
      refine LinearMap.ext fun T => Subtype.ext (LinearMap.ext fun w => ?_)
      have hT : T.1 ∈ maps L (spanK E a φ) (spanK_stable φ) ∧
          ∀ z ∈ Zalg E a, z φ = 0 → ∀ w, z (T.1 w) = 0 := T.2
      exact hT.2 z.1 z.2 hz w
    have hev : FiniteDimensional ℂ (LinearMap.range ev) := by
      have h1 : LinearMap.range ev ≤
          Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) := by
        rintro _ ⟨z, rfl⟩
        exact Submodule.subset_span ⟨z.1, z.2, rfl⟩
      haveI := hφ.zfin
      exact Submodule.finiteDimensional_of_le h1
    refine fd_adjoin_of_ker_le (mapsJ φ L) (Zalg E a) (Sm E a) (postZAlg φ L) ev hev hker S ?_
    rintro _ ⟨τ, u, rfl⟩
    exact ⟨⟨cap τ u, hcap τ u⟩, rfl⟩
  · intro c
    let J := ⨅ s ∈ S, LinearMap.ker (s - algebraMap ℂ (Module.End ℂ (mapsJ φ L)) (c s))
    let N : Submodule ℂ (spanK E a φ →ₗ[ℂ] Sm E a) := J.map (mapsJ φ L).subtype
    have hNle : N ≤ maps L (spanK E a φ) (spanK_stable φ) := by
      rintro _ ⟨T, _, rfl⟩
      have hT : T.1 ∈ maps L (spanK E a φ) (spanK_stable φ) ∧
          ∀ z ∈ Zalg E a, z φ = 0 → ∀ w, z (T.1 w) = 0 := T.2
      exact hT.1
    have hNe : ∀ T ∈ N, ∀ (τ : E →+* ℂ) (u : ℂ),
        cap τ u ∘ₗ T = c (postZ φ L (cap τ u) (hcap τ u)) • T := by
      rintro _ ⟨T, hT, rfl⟩ τ u
      have hT' : T ∈ ⨅ s ∈ S, LinearMap.ker (s - algebraMap ℂ (Module.End ℂ (mapsJ φ L)) (c s)) := hT
      have h := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hT' (postZ φ L (cap τ u) (hcap τ u))) ⟨τ, u, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Module.algebraMap_end_apply] at h
      exact congrArg Subtype.val h
    have hN : FiniteDimensional ℂ N :=
      GlobalTheory.T.finiteDimensional_eigen_intertwiners hP E a L hL (spanK E a φ) (spanK_stable φ) hφ.kfin
        (fun τ u => c (postZ φ L (cap τ u) (hcap τ u))) N hNle hNe
    exact LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective (mapsJ φ L).subtype Subtype.val_injective J).symm

end GlobalTheory.AutGrowth.KilledFin
