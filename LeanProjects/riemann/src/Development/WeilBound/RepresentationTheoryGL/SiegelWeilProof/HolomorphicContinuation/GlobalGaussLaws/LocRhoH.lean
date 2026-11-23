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

namespace PositivityTheory.Rg.Sw.Glob.RhoH

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

theorem orbit_cont : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ →
    ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 →
    ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω → ∀ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l →
    ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) →
    ∀ Φ : schwartzA θ V.rank n, Φ.1 ∈ fockA θ V n l s → ∀ Λ : schwartzA θ V.rank n →ₗ[ℂ] ℂ,
      ContinuousOn (fun g : G D n => Λ (ω g Φ)) (K D n : Set (G D n)) := by
  intro D n V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω l hl s hs Φ hΦ Λ
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, hlam, hψeq, hchart, hdat, htr⟩ :=
    GlobalTheory.T.exists_weilDatum_doubled_of_schrodingerFormulas D A V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω
  obtain ⟨lam', hlam', -, l', hl', habs⟩ := GlobalTheory.StdUnn.shift_char_realPar D ψ₀ hstd θ hθ μ' hsk
  have hll : lam' = lam := (algebraMap D.host.F D.host.E).injective (hlam'.trans hlam.symm)
  subst hll
  have hl'' : HasRealPar ψ θ l' := hψeq ▸ hl'
  have hleq : l = l' := GlobalTheory.T.archimedean_parameters_addChar_unique D ψ θ hθ l l' hl hl''
  subst hleq
  obtain ⟨hschS, hsurj, -⟩ := GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat D ψ₀ hstd θ hθ A V μ 𝓕 hμ
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
  let Vf : Submodule ℂ (WO (dblSp A) V → ℂ) := Submodule.span ℂ {g | ∃ k ∈ K', g = omh (k, 1) f}
  have : FiniteDimensional ℂ Vf := hkf
  have hVth : ∀ v ∈ Vf, IsThetaFunO ψ₀ (dblSp A) V v := by
    intro v hv
    have hle : Vf ≤ Formalism.IndefR.Eqv.thetaSubO ψ₀ (dblSp A) V := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨k, -, rfl⟩
      exact hdat.om_pres _ f hf
    exact hle hv

  let Sv : Vf →ₗ[ℂ] schwartzA θ V.rank n :=
    { toFun := fun v => ⟨sch ψ₀ A V μ 𝓕 v.1, hschS v.1 (hVth v.1 v.2)⟩
      map_add' := fun v w => Subtype.ext
        (GlobalTheory.StdUnn.sch_linear D ψ₀ hstd A V μ 𝓕 hμ v.1 w.1 (hVth v.1 v.2) (hVth w.1 w.2) 1).2.2.1
      map_smul' := fun c v => Subtype.ext
        (GlobalTheory.StdUnn.sch_linear D ψ₀ hstd A V μ 𝓕 hμ v.1 v.1 (hVth v.1 v.2) (hVth v.1 v.2) c).2.2.2 }
  have hΛc : Continuous (Λ ∘ₗ Sv) := LinearMap.continuous_of_finiteDimensional _

  have hmemK : ∀ g : G D A.rank, g ∈ K D A.rank → κ.symm g ∈ K' := by
    intro g hg
    show κ (κ.symm g) ∈ K D A.rank
    rw [κ.apply_symm_apply]
    exact hg
  let o : Set.Elem (((K D n : Subgroup (G D n)) : Set (G D n))) → Vf := fun g =>
    ⟨omh (κ.symm g.1, 1) f, Submodule.subset_span ⟨κ.symm g.1, hmemK g.1 g.2, rfl⟩⟩
  have hκs : Continuous (fun g : G D n => κ.symm g) := hcont.2
  have hval : Continuous (fun g : Set.Elem (((K D n : Subgroup (G D n)) : Set (G D n))) => (g.1 : G D n)) :=
    continuous_subtype_val
  have ho : Continuous o := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_pi fun w => ?_
    exact (hdat.om_cont f hf w).comp ((hκs.comp hval).prodMk continuous_const)
  have heq : ∀ g : Set.Elem (((K D n : Subgroup (G D n)) : Set (G D n))), Λ (ω g.1 Φ) = (Λ ∘ₗ Sv) (o g) := by
    intro g
    simp only [LinearMap.coe_comp, Function.comp_apply]
    congr 1
    apply Subtype.ext
    have := htr (κ.symm g.1) f hf Φ hfΦ.symm
    rw [show κ (κ.symm g.1) = g.1 from κ.apply_symm_apply g.1] at this
    exact this
  rw [continuousOn_iff_continuous_domRestrict]
  have : (Set.domRestrict (K D n : Set (G D n)) fun g => Λ (ω g Φ)) = (Λ ∘ₗ Sv) ∘ o := funext heq
  rw [this]
  exact hΛc.comp ho

end PositivityTheory.Rg.Sw.Glob.RhoH
