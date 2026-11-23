import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ScalarOnInertiaProp

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

namespace UpperTheory.TNZ

namespace UnramifiedTwist

theorem charpoly_smul_one {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (c : ℂ) :
    (c • (1 : Module.End ℂ V)).charpoly = (X - C c) ^ Module.finrank ℂ V := by
  have h1 := LinearMap.charpoly_sub_smul (c • (1 : Module.End ℂ V)) c
  rw [sub_self, LinearMap.charpoly_zero] at h1
  calc (c • (1 : Module.End ℂ V)).charpoly
      = ((c • (1 : Module.End ℂ V)).charpoly.comp (X + C c)).comp (X - C c) := by
        rw [Polynomial.comp_assoc]; simp
    _ = (X - C c) ^ Module.finrank ℂ V := by rw [← h1, Polynomial.X_pow_comp]

theorem diagEnd_const (c : ℂ) :
    diagEnd (fun _ : Fin 1 => c) = c • (1 : Module.End ℂ (Fin 1 → ℂ)) :=
  LinearMap.ext fun v => funext fun i => by simp

end UnramifiedTwist

open UnramifiedTwist in
theorem step_unrTwist : UnramifiedTwistProp := by
  intro E Ω _ _ _ _ _ A w h u ψ hψ hu
  obtain ⟨n, a, rfl⟩ := WD.exists_rep u
  rw [WD.unr_mk] at hu
  obtain ⟨hN, hI⟩ := hu
  simp only [WD.lpOfChar, WD.lpChar_mk, WD.monodromyZero_ofWeilDeligneRepClass_iff, WD.charPol_mk, WD.lpDim_mk]
  refine ⟨?_, fun t => ?_⟩
  · rw [WDRep.tensor_N, hN, WDRep.ofChars_N]
    simp
  · rw [WDRep.tensor_ρ, hI t, WDRep.ofChars_ρ, diagEnd_const, TensorProduct.map_smul_right,
      TensorProduct.map_one, charpoly_smul_one, Module.finrank_tensorProduct]
    simp

end UpperTheory.TNZ
