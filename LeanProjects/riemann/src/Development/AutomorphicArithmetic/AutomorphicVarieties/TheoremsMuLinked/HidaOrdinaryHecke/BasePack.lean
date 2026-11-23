import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.V.Th.AnnihilatorQuotientFinite.basePack :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V₀ : s.Lev) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V₀.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (D : ℕ) (wt : Pa.WtVars (Pa.locOf r) O n D) (A : Type) [CommRing A] [Algebra O A] (e : Pa.abelian₂ O Empty D ≃ₐ[O] A) (lam : A →ₐ[O] B.B), (∀ k, residue O (wt.c k) * (r.psib (wt.v k) (wt.i k) (wt.γ k) : ResidueField O) = 1) → (∀ k, lam (e (MvPowerSeries.X (.inr k))) = algebraMap O B.B (wt.c k) * (B.u.ψ (wt.v k) (wt.i k) (wt.γ k) : B.B) - 1) → ∀ (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Free A M] (μ : B.B →+* Module.End A M), (∀ a y, μ (lam a) y = a • y) → RingHom.ker μ = J → ∃ (b : Pa.TWBase (Pa.pairOf B.u) J Empty D) (eb : M ≃+ b.M), b.wt = wt ∧ (∀ t y, eb (μ t y) = t • eb y) ∧ ∀ (x : B.B →ₐ[O] O) y, eb y ∈ Th.wtSub b x ↔ y ∈ (RingHom.ker (x.comp lam) • ⊤ : Submodule A M) := by
  intro l _ L Ω _ _ _ _ _ _ s V₀ O _ _ _ n r B J D wt A _ _ e lam hres hw M _ _ _ _ μ hμ hker
  letI mB : Module B.B M := Module.compHom M μ
  letI mL : Module (Pa.abelian₂ O Empty D) M := Module.compHom M e.toRingEquiv.toRingHom
  have hB : ∀ (t : B.B) (y : M), t • y = μ t y := fun _ _ => rfl
  have hL : ∀ (a : Pa.abelian₂ O Empty D) (y : M), a • y = e a • y := fun _ _ => rfl
  have bs : Module.Basis (Module.Free.ChooseBasisIndex A M) (Pa.abelian₂ O Empty D) M :=
    (Module.Free.chooseBasis A M).mapCoeffs e.symm.toRingEquiv (fun c x => by
      rw [hL]; simp)
  have hann : Module.annihilator B.B M = J := by
    rw [← hker]
    ext t
    rw [Module.mem_annihilator, RingHom.mem_ker]
    constructor
    · intro h
      ext y
      exact h y
    · intro h y
      rw [hB, h]; rfl
  refine ⟨{ wt := wt, wt_res := hres, lam := lam.comp e.toAlgHom, segmentWeightExponent := hw, M := M,
            smul_lam := fun a m => ?_, free := Module.Free.of_basis bs, fin := Module.Finite.of_basis bs,
            supp := fun p _ => by rw [hann] }, AddEquiv.refl M, rfl, fun t y => rfl, fun x y => ?_⟩
  · rw [hL, hB]
    exact (hμ _ _).symm
  · change y ∈ (RingHom.ker (x.comp (lam.comp e.toAlgHom)) • ⊤ : Submodule (Pa.abelian₂ O Empty D) M) ↔ _
    constructor
    · intro h
      refine Submodule.smul_induction_on h (fun a ha m _ => ?_) fun _ _ => add_mem
      exact Submodule.smul_mem_smul (r := e a) ha Submodule.mem_top
    · intro h
      refine Submodule.smul_induction_on h (fun a ha m _ => ?_) fun _ _ => add_mem
      obtain ⟨a, rfl⟩ := e.surjective a
      exact Submodule.smul_mem_smul (r := a) (n := m) ha Submodule.mem_top
