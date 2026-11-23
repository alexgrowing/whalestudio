import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PurityFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnnihilatorQuotientSmulTopOfFree
open IsLocalRing

namespace GlobalTheory.AnnRegSeq

theorem free_of_free_quotient_map (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing A] [Algebra R A] [Module.Finite R A] (f : R) (hf : f ∈ maximalIdeal R)
    (reg : IsSMulRegular A f)
    (hfree : Module.Free (R ⧸ Ideal.span {f}) (A ⧸ (Ideal.span {f}).map (algebraMap R A))) :
    Module.Free R A := by
  set I : Ideal R := Ideal.span {f}
  have hsub : I • (⊤ : Submodule R A) = (I.map (algebraMap R A)).restrictScalars R :=
    Ideal.smul_top_eq_map I
  let e0 : (A ⧸ I • (⊤ : Submodule R A)) ≃ₗ[R] (A ⧸ I.map (algebraMap R A)) :=
    (Submodule.quotEquivOfEq _ _ hsub).trans
      (Submodule.Quotient.restrictScalarsEquiv R (I.map (algebraMap R A)))
  let e : (A ⧸ I • (⊤ : Submodule R A)) ≃ₗ[R ⧸ I] (A ⧸ I.map (algebraMap R A)) :=
    { e0.toAddEquiv with
      map_smul' := by
        intro c x
        obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        show e0 (Ideal.Quotient.mk I c • Submodule.Quotient.mk x) = Ideal.Quotient.mk I c • e0 (Submodule.Quotient.mk x)
        rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul, algebraMap_smul, map_smul] }
  haveI := hfree
  haveI : Module.Free (R ⧸ I) (A ⧸ I • (⊤ : Submodule R A)) := Module.Free.of_equiv e.symm
  exact free_of_free_quotient hf reg

end GlobalTheory.AnnRegSeq
