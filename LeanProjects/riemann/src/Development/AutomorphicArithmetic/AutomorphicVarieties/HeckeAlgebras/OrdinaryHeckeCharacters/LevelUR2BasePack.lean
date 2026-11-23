import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.V.Hi.levelUR2BasePack :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V₀ : s.Lev) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V₀.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (D : ℕ) (wt : Pa.WtVars (Pa.locOf r) O n D) (A : Type) [CommRing A] [Algebra O A] (e : Pa.abelian₂ O Empty D ≃ₐ[O] A) (lam : A →ₐ[O] B.B), (∀ k, residue O (wt.c k) * (r.psib (wt.v k) (wt.i k) (wt.γ k) : ResidueField O) = 1) → (∀ k, lam (e (MvPowerSeries.X (.inr k))) = algebraMap O B.B (wt.c k) * (B.u.ψ (wt.v k) (wt.i k) (wt.γ k) : B.B) - 1) → ∀ (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Free A M] (μ : B.B →+* Module.End A M), (∀ a y, μ (lam a) y = a • y) → RingHom.ker μ = J → ∃ (b : Pa.TWBase (Pa.pairOf B.u) J Empty D) (eb : M ≃+ b.M), b.wt = wt ∧ ∀ t y, eb (μ t y) = t • eb y := by
  intro l _ L Ω _ _ _ _ _ _ s V₀ O _ _ _ n r B J D wt A _ _ e lam hres hlam M _ _ _ _ μ hμ hker
  letI mB : Module B.B M := Module.compHom M μ
  letI mL : Module (Pa.abelian₂ O Empty D) M := Module.compHom M (e : Pa.abelian₂ O Empty D →+* A)
  have hsm : ∀ (a : Pa.abelian₂ O Empty D) (m : M), a • m = (lam.comp e.toAlgHom) a • m := by
    intro a m
    exact (hμ (e a) m).symm
  haveI : Nontrivial A := e.injective.nontrivial
  let bL := (Module.Free.chooseBasis A M).mapCoeffs e.symm.toRingEquiv (fun c x => by
    show e (e.symm c) • x = c • x
    rw [AlgEquiv.apply_symm_apply])
  haveI : Module.Free (Pa.abelian₂ O Empty D) M := Module.Free.of_basis bL
  haveI : Module.Finite (Pa.abelian₂ O Empty D) M := Module.Finite.of_basis bL
  have hann : Module.annihilator B.B M = J := by
    rw [← hker]
    ext b
    rw [Module.mem_annihilator, RingHom.mem_ker]
    constructor
    · intro hb
      ext m
      exact hb m
    · intro hb m
      show μ b m = 0
      rw [hb]
      rfl
  exact ⟨Pa.TWBase.mk wt hres (lam.comp e.toAlgHom) (fun k => hlam k) M hsm inferInstance inferInstance
    (fun p _ => by rw [hann]), AddEquiv.refl M, rfl, fun t y => rfl⟩
