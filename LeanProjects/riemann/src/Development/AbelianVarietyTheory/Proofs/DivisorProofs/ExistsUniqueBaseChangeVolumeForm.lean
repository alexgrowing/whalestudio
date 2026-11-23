import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace AltBaseChange

section General

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
  {X W : Type} [AddCommGroup X] [Module R X] [AddCommGroup W] [Module R W] [Module R' W]
  [IsScalarTower R R' W] {j : X →ₗ[R] W} (hj : IsBaseChange R' j) (n : ℕ)

def bc (g : X [⋀^Fin n]→ₗ[R] R) : W [⋀^Fin n]→ₗ[R'] R' :=
  exteriorPower.alternatingMapLinearEquiv.symm
    ((TopForm.isBaseChange_exteriorPower hj n).toDual
      (exteriorPower.alternatingMapLinearEquiv g))

theorem bc_apply (g : X [⋀^Fin n]→ₗ[R] R) (v : Fin n → X) :
    bc hj n g (fun i => j (v i)) = algebraMap R R' (g v) := by
  unfold bc
  rw [← exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, LinearEquiv.apply_symm_apply,
    ← exteriorPowerMapOver_ιMulti (B := R'), IsBaseChange.toDual_comp_apply,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]

include hj in
theorem ext_tuples {ω₁ ω₂ : W [⋀^Fin n]→ₗ[R'] R'}
    (h : ∀ v : Fin n → X, ω₁ (fun i => j (v i)) = ω₂ (fun i => j (v i))) : ω₁ = ω₂ := by
  apply exteriorPower.alternatingMapLinearEquiv.injective
  apply (TopForm.isBaseChange_exteriorPower hj n).algHom_ext
  intro x
  have key : ((exteriorPower.alternatingMapLinearEquiv ω₁).restrictScalars R).comp
        (exteriorPowerMapOver R' n j) =
      ((exteriorPower.alternatingMapLinearEquiv ω₂).restrictScalars R).comp
        (exteriorPowerMapOver R' n j) := by
    apply exteriorPower.linearMap_ext
    ext v
    simp [h]
  exact LinearMap.congr_fun key x

theorem bc_smul (r : R) (g : X [⋀^Fin n]→ₗ[R] R) :
    bc hj n (r • g) = algebraMap R R' r • bc hj n g :=
  ext_tuples hj n fun v => by simp [bc_apply]

theorem mem_span_bc_of_free [Module.Free R X] [Module.Finite R X]
    (ω : W [⋀^Fin n]→ₗ[R'] R') : ω ∈ Submodule.span R' (Set.range (bc hj n)) := by
  obtain ⟨L, rfl⟩ := exteriorPower.alternatingMapLinearEquiv.symm.surjective ω
  have hD := (TopForm.isBaseChange_exteriorPower hj n).dual
  induction L using hD.inductionOn with
  | zero => simp
  | tmul m =>
    refine Submodule.subset_span ⟨exteriorPower.alternatingMapLinearEquiv.symm m, ?_⟩
    simp [bc]
  | smul s L h => rw [map_smul]; exact Submodule.smul_mem _ _ h
  | add a b ha hb => rw [map_add]; exact add_mem ha hb

end General

end AltBaseChange

end GlobalTheory

namespace GlobalTheory

namespace AltBaseChange

section Projective

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
  {M : Type} [AddCommGroup M] [Module R M] (n : ℕ)

theorem exists_smul_bc_eq [Module.Finite R M] [Module.Projective R M]
    (δ : M [⋀^Fin n]→ₗ[R] R) (hδ : Submodule.span R {δ} = ⊤)
    (ω : (R' ⊗[R] M) [⋀^Fin n]→ₗ[R'] R') :
    ω ∈ Submodule.span R' {bc (TensorProduct.isBaseChange R M R') n δ} := by
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' R M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hF := TensorProduct.isBaseChange R (Fin k → R) R'
  have hM := TensorProduct.isBaseChange R M R'
  have hfs (x : R' ⊗[R] M) : f.baseChange R' (s.baseChange R' x) = x := by
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hs, LinearMap.baseChange_id,
      LinearMap.id_apply]
  let Φ : ((R' ⊗[R] (Fin k → R)) [⋀^Fin n]→ₗ[R'] R') →ₗ[R'] ((R' ⊗[R] M) [⋀^Fin n]→ₗ[R'] R') :=
    { toFun := fun t => t.compLinearMap (s.baseChange R')
      map_add' := fun _ _ => by ext; simp
      map_smul' := fun _ _ => by ext; simp }
  have hω : Φ (ω.compLinearMap (f.baseChange R')) = ω := by
    ext v
    simp [Φ, hfs]
  have hη := mem_span_bc_of_free hF n (ω.compLinearMap (f.baseChange R'))
  rw [← hω]
  have hmap := Submodule.mem_map_of_mem (f := Φ) hη
  rw [Submodule.map_span] at hmap
  refine Submodule.span_le.mpr ?_ hmap
  rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
  have hg : g.compLinearMap s ∈ Submodule.span R {δ} := hδ ▸ Submodule.mem_top
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hg
  have : Φ (bc hF n g) = algebraMap R R' r • bc hM n δ := by
    rw [← bc_smul, hr]
    refine ext_tuples hM n fun v => ?_
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, AlternatingMap.compLinearMap_apply]
    rw [bc_apply hM n]
    have h1 : (fun i => s.baseChange R' (TensorProduct.mk R R' M 1 (v i))) =
        fun i => TensorProduct.mk R R' (Fin k → R) 1 (s (v i)) := by
      funext i
      simp
    rw [h1, bc_apply hF n]
    rfl
  rw [SetLike.mem_coe, this]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end Projective

end AltBaseChange

end GlobalTheory

namespace GlobalTheory

namespace AltBaseChange

theorem exists_unique_baseChange_generator : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (M : Type) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (N : Type) [AddCommGroup N] [Module R' N] (e : R' ⊗[R] M ≃ₗ[R'] N)
    (n : ℕ) (δ : M [⋀^Fin n]→ₗ[R] R), Submodule.span R {δ} = ⊤ →
    ∃! δ' : N [⋀^Fin n]→ₗ[R'] R', Submodule.span R' {δ'} = ⊤ ∧
      ∀ v : Fin n → M, δ' (fun i ↦ e (1 ⊗ₜ v i)) = algebraMap R R' (δ v) := by
  intro R R' _ _ _ M _ _ _ _ N _ _ e n δ hδ
  have hM := TensorProduct.isBaseChange R M R'
  let δ' : N [⋀^Fin n]→ₗ[R'] R' := (bc hM n δ).compLinearMap e.symm.toLinearMap
  have hval (v : Fin n → M) : δ' (fun i ↦ e (1 ⊗ₜ v i)) = algebraMap R R' (δ v) := by
    simp only [δ', AlternatingMap.compLinearMap_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    exact bc_apply hM n δ v
  refine ⟨δ', ⟨?_, hval⟩, ?_⟩
  · rw [Submodule.eq_top_iff']
    intro ω
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
      (exists_smul_bc_eq n δ hδ (ω.compLinearMap e.toLinearMap))
    refine Submodule.mem_span_singleton.mpr ⟨a, ?_⟩
    ext x
    have := congrArg (fun t => t (fun i => e.symm (x i))) ha
    simpa [δ'] using this
  · rintro y ⟨-, hy⟩
    have key : y.compLinearMap e.toLinearMap = bc hM n δ := by
      refine ext_tuples hM n fun v => ?_
      simp only [AlternatingMap.compLinearMap_apply, LinearEquiv.coe_coe]
      rw [bc_apply hM n]
      exact hy v
    ext x
    have := congrArg (fun t => t (fun i => e.symm (x i))) key
    simpa [δ'] using this

end AltBaseChange

end GlobalTheory
