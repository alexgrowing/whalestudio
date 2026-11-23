import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.GoodSet
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.ConjFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.ConjEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfUnramifiedOfInertiaDegEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Ga.spread :
    ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω], Unr L → ∀ E B : Set (G L Ω), IsClosed E → IsClosed B → (∀ c : G (maximalRealSubfield L) Ω, IsConjEl c → ∀ s s' : G L Ω, s'.restrictScalars (maximalRealSubfield L) = c * s.restrictScalars (maximalRealSubfield L) * c⁻¹ → s' ∈ E → s ∈ E) → ∀ (P : Set (Plc L)) (M : ℕ), M ≠ 0 → (∀ w, IsSplitAt w → (M : 𝓞 L) ∉ w.asIdeal → (∃ s, Ga.FrobAt w s ∧ s ∉ B) → ∃ w' ∈ P, w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) → (∀ᶠ w in Filter.cofinite, w ∈ P → ∀ s, Ga.FrobAt w s → s ∈ E) → Bᶜ ⊆ E := by
  intro L Ω _ _ _ _ _ _ hU E B hE hB hconj P M hM hsplit hev
  classical
  obtain ⟨c, hc⟩ := Ga.conjEx L Ω
  have hbad : {w : Plc L | ¬ (w ∈ P → ∀ s, Ga.FrobAt w s → s ∈ E)}.Finite :=
    Filter.eventually_cofinite.mp hev
  let T : Set (HeightOneSpectrum (𝓞 L)) :=
    ⋃ w ∈ {w : Plc L | ¬ (w ∈ P → ∀ s, Ga.FrobAt w s → s ∈ E)},
      {v | HeightOneSpectrum.under (𝓞 (Lp L)) w = HeightOneSpectrum.under (𝓞 (Lp L)) v}
  have hT : T.Finite := by
    refine hbad.biUnion fun w _ => ?_
    have hfin := IsDedekindDomain.primesOver_finite
      (HeightOneSpectrum.under (𝓞 (Lp L)) w).asIdeal (𝓞 L)
    refine (hfin.preimage (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
    intro v hv
    refine ⟨v.isPrime, ⟨?_⟩⟩
    rw [hv]
    rfl
  have hMne : ((M : 𝓞 L) : 𝓞 L) ≠ 0 := by exact_mod_cast hM
  have hMfin : {v : HeightOneSpectrum (𝓞 L) | (M : 𝓞 L) ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {(M : 𝓞 L)}) ?_).subset ?_
    · rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hMne
    · intro v hv
      exact Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hv)
  have hS : ({v : HeightOneSpectrum (𝓞 L) | (M : 𝓞 L) ∈ v.asIdeal} ∪ T).Finite := hMfin.union hT
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := L) (Ω := Ω)
    GlobalTheory.Published.chebotarevDegreeOne' hS
  intro σ hσB
  have hcl := hD.open_subset_closure_inter hB.isOpen_compl hσB
  refine closure_minimal ?_ hE hcl
  rintro τ ⟨hτB, v, hvS, hdeg, A, hA, hfr⟩
  have hFrob : Ga.FrobAt v τ := ⟨A, hA, hfr⟩
  have hMv : (M : 𝓞 L) ∉ v.asIdeal := fun h => hvS (Or.inl h)
  have hspl : IsSplitAt v := UpperTheory.isSplitAt_of_unramified_of_inertiaDeg_eq_one L v (hU v) hdeg
  obtain ⟨w', hw'P, hw'⟩ := hsplit v hspl hMv ⟨τ, hFrob, hτB⟩
  have hgood : ∀ s, Ga.FrobAt w' s → s ∈ E := by
    by_contra hcon
    exact hvS (Or.inr (Set.mem_biUnion (x := w') (fun h => hcon (h hw'P)) hw'))
  rcases Ga.conjFrob L Ω c hc v w' hw' τ hFrob with h1 | ⟨s', hs', hres⟩
  · exact hgood τ h1
  · exact hconj c hc τ s' hres (hgood s' hs')
