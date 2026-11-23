import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.LevShrink
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CuspSupportOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDiscriminantIdentityStatement
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.ReproOf
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.IsoEq
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL

open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.LFun UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp

open PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.Rs MeasureTheory

private theorem expV_cusp {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} (π : CuspSub E N)
    {r : ℕ} (hr : 0 < r) (hrN : r < N) : ExpV r π.V = ∅ := by
  refine Set.eq_empty_of_forall_notMem ?_
  rintro c ⟨φ, hφ, F₀, ⟨μ, 𝓕, hμ, h𝓕, e⟩, F, hF, hF0, -⟩
  have h0 : F₀ = 0 := by
    funext g
    have hc := (π.cusp φ hφ).2
    have h := @hc r hr hrN (_root_.borel _) ⟨rfl⟩ μ 𝓕 hμ h𝓕 g
    rw [e]
    simpa [PositivityTheory.Affgl.CT.ct] using h
  subst h0
  refine hF0 ((Submodule.mem_bot ℂ).1 ((Submodule.span_le (p := ⊥)).2 ?_ hF))
  rintro _ ⟨t, rfl⟩
  exact (Submodule.mem_bot ℂ).2 rfl

private theorem iso_of_isoV {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} {π π' : CuspSub E N}
    {V : Submodule ℂ (Sm E N)} (h : IsoV π.V V) (h' : IsoV π'.V V) : π.Iso π' := by
  obtain ⟨T₁, e₁⟩ := h
  obtain ⟨T₂, e₂⟩ := h'
  refine ⟨T₁.trans T₂.symm, fun o φ => ?_⟩
  have a := e₁ o φ (π.op o φ) rfl
  have b := e₂ o (T₂.symm (T₁ φ)) (π'.op o (T₂.symm (T₁ φ))) rfl
  rw [LinearEquiv.apply_symm_apply] at b
  simp only [LinearEquiv.trans_apply]
  rw [LinearEquiv.symm_apply_eq]
  exact Subtype.ext (a.trans b.symm)

private theorem isDiscrete_of_norm' {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} {π : CuspSub E N}
    (hn : GlobalTheory.DiscSpec.IsNormalised π) : IsDiscrete π.V :=
  isDiscrete_of_cuspSub π fun φ hφ => by
    obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL.of_invariant (π.cusp φ hφ) (hn φ hφ)
    exact GlobalTheory.DiscChar.isSqInt_of_bounded (hn φ hφ) (C := C) fun g => by simpa using hC g

private theorem cuspFin_of (hF : FinDisc) : CuspFin := by
  intro E _ _ _ N hN K W R hK hW
  letI : MeasurableSpace (GA E N) := _root_.borel _
  haveI : BorelSpace (GA E N) := ⟨rfl⟩
  let μ : Measure (GA E N) := Measure.haar
  obtain ⟨V₀, hV₀⟩ := hF E N μ K W R 1 hK hW one_pos (PositivityTheory.Rg.BcB.CG.reproEx_holds E N μ K W R hK hW)
  have hex : ∀ π : {π : CuspSub E N | GlobalTheory.DiscSpec.IsNormalised π ∧ HasType K W π.V ∧ InfBdd R π.V},
      ∃ V' ∈ V₀, IsoV π.1.V V' := fun π =>
    hV₀ _ (isDiscrete_of_norm' π.2.1) π.2.2.1 π.2.2.2 fun r hr hrN c hc => by
      rw [expV_cusp π.1 hr hrN] at hc
      exact hc.elim
  choose f hf hfi using hex
  let g : {π : CuspSub E N | GlobalTheory.DiscSpec.IsNormalised π ∧ HasType K W π.V ∧ InfBdd R π.V} → V₀ :=
    fun π => ⟨f π, hf π⟩
  have hg : Function.Injective g := fun a b hab => by
    have e : f a = f b := congrArg Subtype.val hab
    have h := iso_of_isoV (hfi a) (e ▸ hfi b)
    exact Subtype.ext ((UpperTheory.ConvolutionTheory.Dp.isoEq E N _ _).1 h)
  haveI := Finite.of_injective g hg
  exact Set.toFinite _

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp.cuspFin :
    CuspFin :=
  cuspFin_of GlobalTheory.T.finite_discriminant_identity
