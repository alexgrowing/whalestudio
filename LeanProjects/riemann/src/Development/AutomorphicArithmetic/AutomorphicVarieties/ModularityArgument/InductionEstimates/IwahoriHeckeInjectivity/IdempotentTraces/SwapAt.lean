import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.HeckeInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.GalLoc
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.TwUnitary
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ConjCarries
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SInfIff
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SSatIff
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExCusp
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.AdUnique
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.InfinitesimalCharacterPullback.HasInfCharPullSub
import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSGalAdEx

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

open Formalism.L2.Host.CT UpperTheory.V.FieldIso in
private theorem swap_one {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ} {μ : Measure (G1 E n)}
    [μ.IsHaarMeasure] (σ : E ≃+* E) (θ : Twist μ) (hθ : UpperTheory.ConvolutionTheory.K.IsGal σ θ) {V V' : Submodule ℂ (L2 μ)}
    (hV : IsSummand μ V) (e : V'.map (θ.U : L2 μ →ₗ[ℂ] L2 μ) = V) :
    (∀ (τ : E →+* ℂ) m, SInf μ V τ m ↔ SInf μ V' (τ.comp σ.toRingHom) m) ∧
      ∀ w B, SSat μ V (plMap σ w) B → SSat μ V' w B := by
  obtain ⟨π, hπ, -⟩ := Dp.exCusp E n μ V hV
  obtain ⟨s, hs⟩ := UpperTheory.CBC.SGalAdEx_holds E σ
  have h1 := UpperTheory.ConvolutionTheory.K.adUnique E σ s.toRingHom hs.1 hs.2.1
  have h2 := UpperTheory.ConvolutionTheory.K.adUnique E σ (adm σ) (continuous_adm σ) (adm_algebraMap σ)
  have hc : Dp.Carries μ (pullSub σ π) V' := by
    refine (Dp.conjCarries E n μ θ σ s hs (fun g => by rw [h1]; exact hθ g) π _ V' ?_).2 (e ▸ hπ)
    rw [h1, ← h2]
    ext f
    constructor
    · rintro ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
      exact ⟨φ.1, ⟨φ, hφ, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
      exact ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
  refine ⟨fun τ m => ?_, fun w B hB => ?_⟩
  · rw [Dp.sInfIff E n μ π V hπ, Dp.sInfIff E n μ _ V' hc]
    exact (hasInfChar_pullSub σ π τ m).symm
  · obtain ⟨B', rfl, h⟩ := (Dp.sSatIff E n μ π V hπ _ _).1 hB
    exact (Dp.sSatIff E n μ _ V' hc _ _).2 ⟨B', rfl, hasSat_pullSub σ h⟩

open Formalism.L2.Host.CT in
private theorem under_plMap {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E ≃ₐ[F] E) (w : Pl E) : (plMap σ.toRingEquiv w).under (𝓞 F) = w.under (𝓞 F) := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  have e : RingOfIntegers.mapRingEquiv σ.toRingEquiv (algebraMap (𝓞 F) (𝓞 E) x) = algebraMap (𝓞 F) (𝓞 E) x :=
    RingOfIntegers.ext (σ.commutes x)
  have := mem_plMap σ.toRingEquiv w (algebraMap (𝓞 F) (𝓞 E) x)
  rw [e] at this
  exact this

open Formalism.L2.Host.CT in
private theorem exists_plMap {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
    {w w' : Pl E} (h : w.under (𝓞 F) = w'.under (𝓞 F)) : ∃ g : E ≃ₐ[F] E, plMap g.toRingEquiv w = w' := by
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 F) (𝓞 E) (E ≃ₐ[F] E) w.asIdeal w'.asIdeal
    (congrArg HeightOneSpectrum.asIdeal h)
  refine ⟨g, HeightOneSpectrum.ext ?_⟩
  rw [hg, asIdeal_plMap]
  rfl

open Formalism.L2.Host.CT in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.swapAt :
    SwapAt := by
  intro F E _ _ _ _ _ _ _ _ σ h2 hσ τ₁ τ₂ θ hp hθ e₁ e₂
  have s₁ : IsSummand (BW.mu1 E 2) τ₁ := ⟨hp.irr₁.le, hp.irr₁.closed, hp.irr₁.inv, hp.irr₁.ne, hp.irr₁.irr⟩
  have s₂ : IsSummand (BW.mu1 E 2) τ₂ := ⟨hp.irr₂.le, hp.irr₂.closed, hp.irr₂.inv, hp.irr₂.ne, hp.irr₂.irr⟩
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 := (IsGalois.card_aut_eq_finrank F E).trans h2
  have hall : ∀ g : E ≃ₐ[F] E, g = 1 ∨ g = σ := by
    obtain ⟨y, hy, hu⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
    have hs : σ ≠ 1 := by
      rintro rfl
      exact hy (by simpa using hσ y)
    intro g
    by_cases hg : g = 1
    · exact Or.inl hg
    · exact Or.inr ((hu g hg).trans (hu σ hs).symm)
  have hinv : σ.toRingEquiv.symm = σ.toRingEquiv := by
    rcases hall σ⁻¹ with h | h
    · rw [inv_eq_one.1 h]; rfl
    · exact congrArg AlgEquiv.toRingEquiv h
  have hpp : ∀ w, plMap σ.toRingEquiv (plMap σ.toRingEquiv w) = w := fun w => by
    have := plMap_symm_plMap σ.toRingEquiv w
    rwa [hinv] at this
  refine ⟨(swap_one σ.toRingEquiv θ hθ s₂ e₁).1, fun w w' hw hc B => ?_⟩
  have e : w' = plMap σ.toRingEquiv w := by
    rcases hc with hc | hc
    · obtain ⟨g, hg⟩ := exists_plMap hw
      rcases hall g with rfl | rfl
      · exact absurd (hg ▸ HeightOneSpectrum.ext (Ideal.ext fun x => Iff.rfl)) hc
      · exact hg.symm
    · have := (UpperTheory.ConvolutionTheory.T.places F E (h2 ▸ Nat.prime_two)).2.2.2.1 _ hc
      exact congrArg Subtype.val (this ⟨plMap σ.toRingEquiv w, ⟨(congrArg HeightOneSpectrum.asIdeal (under_plMap σ w)).symm⟩⟩ ⟨w', ⟨congrArg HeightOneSpectrum.asIdeal hw⟩⟩)
  subst e
  refine ⟨fun h => (swap_one σ.toRingEquiv θ hθ s₂ e₁).2 _ B (by rwa [hpp]), (swap_one σ.toRingEquiv θ hθ s₁ e₂).2 w B⟩
