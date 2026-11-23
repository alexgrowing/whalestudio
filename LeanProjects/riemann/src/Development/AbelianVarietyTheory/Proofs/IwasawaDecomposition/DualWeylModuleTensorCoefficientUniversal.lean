import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqBotOrTopOfTensor
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.CoefIrred

theorem vv_universal :
    ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (V : Type) [AddCommGroup V] [Module ℂ V] (F : MultilinearMap ℂ (fun v => nablaSq ℂ n (lam v)) V), ∃! f : Formalism.L2.DIV.VV ℂ lam →ₗ[ℂ] V, ∀ u, f (GlobalTheory.CoefIrred.tenMul (K := ℂ) lam u) = F u := by
  intro ι _ n lam V _ _ F
  have hB : ∀ i, Formalism.L2.DIV.bVV ℂ lam i = tenMul lam (fun τ => ssBasis ℂ (lam τ) (i τ)) := by
    intro i
    apply Subtype.ext
    rw [Formalism.L2.DIV.bVV_coe, tenMul_coe, Formalism.L2.DIV.bVVfun]
    simp only [ssBasis_coe]
  refine ⟨(Formalism.L2.DIV.bVV ℂ lam).constr ℂ (fun i => F (fun τ => ssBasis ℂ (lam τ) (i τ))), ?_, ?_⟩
  · intro u
    have := Module.Basis.ext_multilinear (f := ((Formalism.L2.DIV.bVV ℂ lam).constr ℂ
      (fun i => F (fun τ => ssBasis ℂ (lam τ) (i τ)))).compMultilinearMap (tenMul lam)) (g := F)
      (fun τ => ssBasis ℂ (lam τ)) (fun v => by
        simp only [LinearMap.compMultilinearMap_apply, ← hB, Module.Basis.constr_basis])
    exact congrArg (fun m => m u) this
  · intro g hg
    apply (Formalism.L2.DIV.bVV ℂ lam).ext
    intro i
    rw [Module.Basis.constr_basis, hB, hg]

end GlobalTheory.CoefIrred
