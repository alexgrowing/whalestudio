import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ResidueVanishing.ContinuousInvariantCoefficients
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteUnitaryQuotientCompactFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartMemRationalIffStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsHeckeCharRestrictionEtaInvStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKillingImpliesVanishing

noncomputable section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Eis
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.Kplug

theorem dblInt_eq_fd {D : D7} (A : HSp D) {μ : (AE D)ˣ →* Circle} (hμ : IsHeckeChar D μ) (m : Measure (GA D A))
    [m.IsHaarMeasure] {E : GA D (dblSp A) → ℂ} {f₁ f₂ : GA D A → ℂ} (hE : Continuous E)
    (hEi : LeftInv (GQ (dblSp A)) E) (h₁ : Continuous f₁) (h₁i : LeftInv (GQ A) f₁) (h₂ : Continuous f₂)
    (h₂i : LeftInv (GQ A) f₂) {X K : Set (GA D A)} (hX : IsFundamentalDomain (GQ A) X m) (hK : IsCompact K)
    (hXK : X ⊆ K) :
    dblInt A μ m E f₁ f₂ = ∫ g in X ×ˢ X, dblIntegrand A μ E f₁ f₂ g ∂m.prod m := by
  have hi := leftInv_dblIntegrand hμ hEi h₁i h₂i
  have hc := continuous_dblIntegrand hμ hE h₁ h₂
  have hint : IntegrableOn (dblIntegrand A μ E f₁ f₂) (X ×ˢ X) (m.prod m) :=
    (hc.continuousOn.integrableOn_compact (hK.prod hK)).mono_set (Set.prod_mono hXK hXK)
  exact (((dblConv_iff hi hc.measurable hX).2 hint).dblInt_eq hX).2

theorem theta_continuation : K4 := by
  intro D ψ θ A cA a hA W χ omh hW ν 𝓨 hν μ hμ κ hκ omS hT p m hm u hu hui hKi F hF hFi hX
  obtain ⟨-, X, K, hXm, hXf, hKc, hXK⟩ := GlobalTheory.T.definite_unitary_quotient_compact_fundamentalDomain D A hA.sig hA.pos m hm
  have hχ := (GlobalTheory.T.isHeckeChar_restrictionEta_inv D χ W.rank hW.hecT hW.resT).1
  obtain ⟨hκc, -⟩ := GlobalTheory.T.continuous_standardUnitaryChart_and_symm D A μ hμ κ hκ
  have hG' := GlobalTheory.T.standardUnitaryChart_mem_rational_iff D A μ hμ κ hκ
  have hcu : Continuous fun g => conj (u g) := Complex.continuous_conj.comp hu
  have hcui : LeftInv (GQ A) fun g => conj (u g) := fun γ hγ g => by simp only [hui γ hγ g]
  set w : GA D A × GA D A → ℂ := dblIntegrand A χ⁻¹ (fun _ => 1) (fun g => conj (u g)) (fun g => conj (u g)) with hw_def
  have hw : Continuous w := continuous_dblIntegrand hχ continuous_const hcu hcu
  have hsplit : ∀ (E : GA D (dblSp A) → ℂ) x,
      dblIntegrand A χ⁻¹ E (fun g => conj (u g)) (fun g => conj (u g)) x = E (io A x) * w x := fun E x => by
    simp only [hw_def, dblIntegrand]; ring
  classical
  let c : GA D A × GA D A → G D A.rank := fun x => if x ∈ K ×ˢ K then κ (io A x * p) else 1
  have hKK : IsCompact (K ×ˢ K) := hKc.prod hKc
  have hXX : X ×ˢ X ⊆ K ×ˢ K := Set.prod_mono hXK hXK
  have hcK : ∀ x ∈ X ×ˢ X, c x = κ (io A x * p) := fun x hx => if_pos (hXX hx)
  have hc0 : Continuous fun x : GA D A × GA D A => κ (io A x * p) :=
    hκc.comp ((continuous_io A).mul continuous_const)
  have hcm : Measurable c := Measurable.ite hKK.isClosed.measurableSet hc0.measurable measurable_const
  have hcr : IsCompact (closure (Set.range c)) := by
    refine ((hKK.image hc0).union (isCompact_singleton (x := (1 : G D A.rank)))).closure_of_subset ?_
    rintro _ ⟨x, rfl⟩
    by_cases h : x ∈ K ×ˢ K
    · exact Or.inl ⟨x, h, (if_pos h).symm⟩
    · exact Or.inr (if_neg h)
  have : IsFiniteMeasure ((m.prod m).restrict (X ×ˢ X)) :=
    isFiniteMeasure_restrict.2 ((measure_mono hXX).trans_lt hKK.measure_lt_top).ne
  have hwi : Integrable w ((m.prod m).restrict (X ×ˢ X)) :=
    (hw.continuousOn.integrableOn_compact hKK).mono_set hXX
  have hXXm : MeasurableSet (X ×ˢ X) := hXm.prod hXm
  have hE : Continuous fun g : GA D (dblSp A) => F (κ (g * p)) :=
    hF.comp (hκc.comp (continuous_id.mul continuous_const))
  have hEi : LeftInv (GQ (dblSp A)) fun g => F (κ (g * p)) := fun γ hγ g => by
    simp only [mul_assoc, map_mul]
    exact hFi _ ((hG' γ).1 hγ) _
  have key := hX (GA D A × GA D A) ((m.prod m).restrict (X ×ˢ X)) c hcm hcr w hwi ?_
  · rw [dblInt_eq_fd A hχ m hE hEi hcu hcui hcu hcui hXf hKc hXK, ← key]
    refine setIntegral_congr_fun hXXm fun x hx => ?_
    simp only [hsplit, hcK x hx]
  · intro Ψ h
    obtain ⟨f, hf, he⟩ := theta_kernel_identity D ψ θ hA.inf A W χ omh hW ν 𝓨 hν κ omS hT p Ψ
    have hk := hKi f hf h
    have hkc : Continuous fun g => thetaKO omh g h f := (hW.om_cont f hf 0).comp (Continuous.prodMk_left h)
    have hki : LeftInv (GQ (dblSp A)) fun g => thetaKO omh g h f := fun γ hγ g =>
      GlobalTheory.Core.Rk.Aniso.thetaKernel_rationalSource_invariant hW hf hγ g h
    rw [dblInt_eq_fd A hχ m hkc hki hcu hcui hcu hcui hXf hKc hXK] at hk
    rw [← hk]
    refine setIntegral_congr_fun hXXm fun x hx => ?_
    simp only [hsplit, hcK x hx, he]

end PositivityTheory.Rg.Rsw.Kplug

end
