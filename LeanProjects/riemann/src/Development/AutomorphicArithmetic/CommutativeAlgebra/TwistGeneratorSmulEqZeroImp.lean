import Mathlib
import Development.EtaleCohomology.EtaleSheaves.DerivUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistModuleFreeAndGeneratorSummandStatement
open CategoryTheory AlgebraicGeometry GlobalTheory.EtC

theorem UpperTheory.twist_generator_smul_eq_zero_imp :
    ∀ (q : ℕ) [NeZero q] (i : ℤ) (C : CommRingCat.{0}) [Nontrivial C] (ζ : Prim q C) (c : ULift.{1} (ZMod q)), c • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj C) = 0 → c = 0 := by
  intro q _ i C _ ζ c h
  obtain ⟨f, hf⟩ := (GlobalTheory.T.tateTwistModule_free_and_generator_summand q i C).2 ζ
  have h' : c • (Submodule.Quotient.mk (Finsupp.single ζ 1) :
      (Prim q C →₀ ULift.{1} (ZMod q)) ⧸ twRel q i C) = 0 := h
  have h2 := congrArg f h'
  rw [map_smul, hf, map_zero] at h2
  simpa using h2
