import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.V.hasFixed_of_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ G V} {τ : Representation ℂ G W} (e : ρ.Equiv τ) {U : Subgroup G}
    (h : UpperTheory.V.Af.HasFixed τ U) : UpperTheory.V.Af.HasFixed ρ U := by
  obtain ⟨v, hv, hU⟩ := h
  refine ⟨e.symm.toLinearEquiv v, by simpa using hv, fun u hu => ?_⟩
  have h1 := LinearMap.congr_fun (e.symm.isIntertwining' u) v
  simp only [LinearMap.comp_apply, hU u hu] at h1
  exact h1.symm

private theorem UpperTheory.V.hasFixed_of_nu {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (x : IrrGL k) (s : ℂ) (U : Subgroup (GL (Fin x.1) k))
    (hU : U ≤ GlobalTheory.SplitWeil.KO k (Fin x.1)) (h : UpperTheory.V.Af.HasFixed (x.nu s).rep U) :
    UpperTheory.V.Af.HasFixed x.rep U := by
  obtain ⟨v, hv, h1⟩ := UpperTheory.V.hasFixed_of_equiv (x.twEquiv _ _) h
  refine ⟨v, hv, fun u hu => ?_⟩
  have h2 := h1 u hu
  rwa [GlobalTheory.SmGL.twist_apply, detChar_of_mem_KO (GlobalTheory.SmGL.isUnram_absPow k s) (hU hu), Units.val_one,
    one_smul] at h2

theorem UpperTheory.hasFixed_of_algNorm_fixed_ne_bot :
    ∀ (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (n : ℕ) (σ : GlobalTheory.CuspRep.SmIrr (GL (Fin n) (w.adicCompletion F)))
    (U : Subgroup (GL (Fin n) (w.adicCompletion F))), U ≤ GlobalTheory.SplitWeil.KO (w.adicCompletion F) (Fin n) →
    GlobalTheory.PRep.fixed (algNorm σ).rep U ≠ ⊥ → UpperTheory.V.Af.HasFixed σ.ρ U := by
  intro F _ _ w n σ U hU h
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h
  refine UpperTheory.V.hasFixed_of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred) ?_
  refine UpperTheory.V.hasFixed_of_nu (IrrGL.of σ.ρ σ.smooth σ.irred) (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) U hU ⟨v, hv0, ?_⟩
  exact fun u hu => (hv ⟨u, hu⟩).trans (by simp)
