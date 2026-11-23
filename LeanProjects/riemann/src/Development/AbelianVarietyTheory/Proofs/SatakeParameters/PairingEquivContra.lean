import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable
open NumberField IsDedekindDomain ValuativeRel Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InvPairing

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def pairMap (π : Representation ℂ G V) {π' : Representation ℂ G W} (hπ' : IsSmooth π')
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hB : ∀ g a b, B (π g a) (π' g b) = B a b) :
    π'.IntertwiningMap (contra π) where
  toLinearMap :=
    { toFun := fun b => ⟨B.flip b, mem_smoothPart_of_nhds (Filter.mem_of_superset
        ((hπ' b).mem_nhds (by simp)) fun g hg => by
          have hg' : π' g b = b := hg
          ext a
          show B (π g⁻¹ a) b = B a b
          have h := hB g (π g⁻¹ a) b
          rw [hg'] at h
          rw [← h, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply])⟩
      map_add' := fun b c => Subtype.ext (by simp)
      map_smul' := fun c b => Subtype.ext (by simp) }
  isIntertwining' g := by
    refine LinearMap.ext fun b => Subtype.ext (LinearMap.ext fun a => ?_)
    show B a (π' g b) = B (π g⁻¹ a) b
    have h := hB g (π g⁻¹ a) b
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
    exact h

theorem pairMap_apply (π : Representation ℂ G V) {π' : Representation ℂ G W} (hπ' : IsSmooth π')
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hB : ∀ g a b, B (π g a) (π' g b) = B a b) (a : V) (b : W) :
    ((pairMap π hπ' B hB b : smoothPart π.dual) : Module.Dual ℂ V) a = B a b := rfl

theorem eq_zero_of_pairMap (π : Representation ℂ G V) {π' : Representation ℂ G W} (hπ' : IsSmooth π')
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hB : ∀ g a b, B (π g a) (π' g b) = B a b)
    (h : ∀ b, pairMap π hπ' B hB b = 0) : B = 0 :=
  LinearMap.ext fun a => LinearMap.ext fun b => by
    have := congrArg (fun l : smoothPart π.dual => (l : Module.Dual ℂ V) a) (h b)
    simpa [pairMap_apply] using this

theorem pairMap_bijective (π : Representation ℂ G V) {π' : Representation ℂ G W} (hπ' : IsSmooth π')
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hB : ∀ g a b, B (π g a) (π' g b) = B a b) (hB0 : B ≠ 0)
    (hirr' : π'.IsIrreducible) (hirr : (contra π).IsIrreducible) :
    Function.Bijective (pairMap π hπ' B hB) := by
  set f := pairMap π hπ' B hB with hf
  constructor
  · let S : Subrepresentation π' :=
      { toSubmodule := LinearMap.ker f.toLinearMap
        apply_mem_toSubmodule := fun g v hv => by
          simp only [LinearMap.mem_ker] at hv ⊢
          have := LinearMap.congr_fun (f.isIntertwining' g) v
          simp only [LinearMap.comp_apply] at this
          rw [this, hv, map_zero] }
    rcases hirr'.eq_bot_or_eq_top S with hS | hS
    · intro x y hxy
      have : x - y ∈ S.toSubmodule := by
        show f.toLinearMap (x - y) = 0
        rw [map_sub]; exact sub_eq_zero.2 hxy
      rw [hS] at this
      exact sub_eq_zero.1 ((Submodule.mem_bot ℂ).1 this)
    · exfalso
      refine hB0 (eq_zero_of_pairMap π hπ' B hB fun b => ?_)
      have : b ∈ S.toSubmodule := by rw [hS]; exact Submodule.mem_top
      exact this
  · let R : Subrepresentation (contra π) :=
      { toSubmodule := LinearMap.range f.toLinearMap
        apply_mem_toSubmodule := fun g v hv => by
          obtain ⟨w, rfl⟩ := hv
          refine ⟨π' g w, ?_⟩
          have := LinearMap.congr_fun (f.isIntertwining' g) w
          simpa only [LinearMap.comp_apply] using this }
    rcases hirr.eq_bot_or_eq_top R with hR | hR
    · exfalso
      refine hB0 (eq_zero_of_pairMap π hπ' B hB fun b => ?_)
      have : f b ∈ R.toSubmodule := ⟨b, rfl⟩
      rw [hR] at this
      exact (Submodule.mem_bot ℂ).1 this
    · intro l
      have : l ∈ R.toSubmodule := by rw [hR]; exact Submodule.mem_top
      obtain ⟨b, hb⟩ := this
      exact ⟨b, hb⟩

end GlobalTheory.InvPairing
