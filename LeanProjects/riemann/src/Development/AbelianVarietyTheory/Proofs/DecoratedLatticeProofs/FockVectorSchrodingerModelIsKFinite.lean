import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumDoubledOfSchrodingerFormulasStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFockVectorOfSchrodingerMemFockSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardCartanInvolutionCommuteCompactStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanParametersAddCharUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerThetaEqSchwartzBruhatStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ShiftedAdditiveCharacterArchimedeanParameters
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerFunctionLinearThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCartanInvStandardInvolutionDoubledGram
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousStandardUnitaryChartAndSymm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousLeviBlock
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockVectorFiniteUnderCompactCommutingCartan
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IterPLin
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.StdUnn.KFin

theorem fock_kfinite : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 → ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω → ∀ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l → ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∀ Φ : schwartzA θ V.rank n, Φ.1 ∈ fockA θ V n l s → FiniteDimensional ℂ (Submodule.span ℂ {Ψ : schwartzA θ V.rank n | ∃ k ∈ K D n, Ψ = ω k Φ}) := by
  intro D n V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω l hl s hs Φ hΦ
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  have hAr : A.rank = n := rfl
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, hlam, hψeq, hchart, hdat, htr⟩ :=
    GlobalTheory.T.exists_weilDatum_doubled_of_schrodingerFormulas D A V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω
  obtain ⟨lam', hlam', -, l', hl', habs⟩ := GlobalTheory.StdUnn.shift_char_realPar D ψ₀ hstd θ hθ μ' hsk
  have hll : lam' = lam := (algebraMap D.host.F D.host.E).injective (hlam'.trans hlam.symm)
  subst hll
  have hl'' : HasRealPar ψ θ l' := hψeq ▸ hl'
  have hleq : l = l' := GlobalTheory.T.archimedean_parameters_addChar_unique D ψ θ hθ l l' hl hl''
  subst hleq
  obtain ⟨-, hsurj, -⟩ := GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat D ψ₀ hstd θ hθ A V μ 𝓕 hμ
  obtain ⟨f, hf, hfΦ⟩ := hsurj Φ.1 Φ.2
  obtain ⟨s', hstd', hcomm⟩ := GlobalTheory.T.exists_standardCartanInvolution_commute_compact D A μ' hsk κ hchart θ hθ
  have hfock : IsFockVec ψ₀ θ (dblSp A) V s' s f :=
    GlobalTheory.T.isFockVector_of_schrodinger_mem_fockSpace D ψ₀ hstd θ hθ A V μ 𝓕 hμ μ' hsk s' s hstd' hs l habs f hf (hfΦ ▸ hΦ)

  have hcont := GlobalTheory.StdUnn.chart_continuous D A μ' hsk κ hchart
  let K' : Subgroup (GA D (dblSp A)) := (K D A.rank).comap κ.toMonoidHom
  have hK' : IsCompact (K' : Set (GA D (dblSp A))) := by
    have h1 : (K' : Set (GA D (dblSp A))) = κ.symm '' (K D A.rank : Set (G D A.rank)) := by
      ext g
      simp only [K', Subgroup.coe_comap, Set.mem_preimage, SetLike.mem_coe, MulEquiv.coe_toMonoidHom]
      constructor
      · intro hg; exact ⟨κ g, hg, κ.symm_apply_apply g⟩
      · rintro ⟨k, hk, rfl⟩; simpa using hk
    rw [h1]
    exact (GlobalTheory.StdUnn.HeightExists.isCompact_K).image hcont.2
  have hkf : GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.IsKFinVec omh K' f :=
    GlobalTheory.Core.Rk.IP.isKFinVec_of_isFockVec D ψ₀ θ (dblSp A) V 1 χ⁻¹ omh s' s hdat hθ
      (GlobalTheory.CartStd.isCartanInv_stdInv D A μ' hsk s' hstd') hs K' hK' (fun k hk τ => hcomm k hk τ) f hfock
  haveI : FiniteDimensional ℂ (Submodule.span ℂ {g : WO (dblSp A) V → ℂ | ∃ k ∈ K', g = omh (k, 1) f}) := hkf

  let T := Formalism.IndefR.Eqv.thetaSubO ψ₀ (dblSp A) V
  let L : T →ₗ[ℂ] (Mx D V.rank A.rank → ℂ) :=
    { toFun := fun g => sch ψ₀ A V μ 𝓕 g.1
      map_add' := fun g h => (GlobalTheory.StdUnn.sch_linear D ψ₀ hstd A V μ 𝓕 hμ g.1 h.1 g.2 h.2 1).2.2.1
      map_smul' := fun c g => (GlobalTheory.StdUnn.sch_linear D ψ₀ hstd A V μ 𝓕 hμ g.1 g.1 g.2 g.2 c).2.2.2 }
  let W : Submodule ℂ T := Submodule.span ℂ {g : T | ∃ k ∈ K', g.1 = omh (k, 1) f}
  have hWmap : W.map T.subtype ≤ Submodule.span ℂ {g : WO (dblSp A) V → ℂ | ∃ k ∈ K', g = omh (k, 1) f} := by
    rw [Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨g, ⟨k, hk, hg⟩, rfl⟩
    exact ⟨k, hk, hg⟩
  haveI : FiniteDimensional ℂ (W.map T.subtype) := Submodule.finiteDimensional_of_le hWmap
  haveI : FiniteDimensional ℂ W :=
    LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective T.subtype Subtype.val_injective W).symm
  have hWL : FiniteDimensional ℂ (W.map L) := Module.Finite.map W L
  set S := Submodule.span ℂ {Ψ : schwartzA θ V.rank n | ∃ k ∈ K D n, Ψ = ω k Φ} with hSdef
  have hSmap : S.map (schwartzA θ V.rank n).subtype ≤ W.map L := by
    rw [hSdef, Submodule.map_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨Ψ, ⟨k, hk, rfl⟩, rfl⟩
    have hth : IsThetaFunO ψ₀ (dblSp A) V (omh (κ.symm k, 1) f) := hdat.om_pres _ f hf
    refine ⟨⟨_, hth⟩, Submodule.subset_span ⟨κ.symm k, ?_, rfl⟩, ?_⟩
    · show κ (κ.symm k) ∈ K D A.rank
      rw [show κ (κ.symm k) = k from κ.apply_symm_apply k]
      exact hk
    · have := htr (κ.symm k) f hf Φ hfΦ.symm
      rw [show κ (κ.symm k) = k from κ.apply_symm_apply k] at this
      exact this.symm
  haveI : FiniteDimensional ℂ (S.map (schwartzA θ V.rank n).subtype) := @Submodule.finiteDimensional_of_le _ _ _ _ _ _ _ hWL hSmap
  exact Module.Finite.equiv (Submodule.equivMapOfInjective (schwartzA θ V.rank n).subtype Subtype.val_injective S).symm

end GlobalTheory.StdUnn.KFin
