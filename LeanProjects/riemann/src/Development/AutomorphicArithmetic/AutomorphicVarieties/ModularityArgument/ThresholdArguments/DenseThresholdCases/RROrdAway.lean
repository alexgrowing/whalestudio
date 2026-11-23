import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.OrdAway
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.LocalConditionCharacters.CharPolSupp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.OrdPlain
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocCompR
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TJacqOfU

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open private UpperTheory.V.Sd.OrdinaryAwayPlaces.rep_retr UpperTheory.V.Sd.OrdinaryAwayPlaces.map_dc UpperTheory.V.Sd.OrdinaryAwayPlaces.exists_ps UpperTheory.V.Sd.OrdinaryAwayPlaces.charPol_lpTw UpperTheory.V.Sd.OrdinaryAwayPlaces.diag_of_wd UpperTheory.V.Sd.OrdinaryAwayPlaces.iwahori_level_zero_eq from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.OrdAway
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Hi
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win UpperTheory.Gal.SV
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.V.Z.Win.RR.ordAway_of_alt (hX : ExRS) (hGd : GdOf) :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Sd.OrdAway := by
  intro PH F Ω _ _ _ _ _ _ l _ ι ξ s c m a π r H A hA
  have P := PH.toClassicalTheorems
  obtain ⟨p1, p2, p3, p4⟩ := UpperTheory.V.Base.places F Ω l A
  have triv : (∀ g ∈ Ine (F := F) A, r g = 1) → Ine (F := F) A ≤ ξ.ker → IsDiagOn r (Ine (F := F) A) ![1, ξ] :=
    fun h1 h2 => ⟨1, fun g hg => by
      have h3 : ξ g = 1 := h2 hg
      rw [h1 g hg]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h3]⟩
  by_cases hT : A = ⊤
  · rw [(p2 hT).1] at triv ⊢
    exact triv (fun g hg => by rw [Subgroup.mem_bot.1 hg, map_one]) bot_le
  obtain ⟨w, h⟩ := p1 hT
  have hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal := fun e => hA ((p3 w h).2 e)
  obtain ⟨χ, hχ⟩ := H.pol
  obtain ⟨-, wt, HT, -, -, hall⟩ := hX F Ω l ι 2 one_le_two π χ H.reg hχ
  have hG := hall r H.cont H.att
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := _root_.UpperTheory.V.Af.local_comp_real_of_printed_results P F 2 π w
  by_cases hc : c w = 0
  · obtain ⟨v, hv, hf⟩ := H.sph w hc
    obtain ⟨T, hT, hTv⟩ := UpperTheory.V.Sd.OrdinaryAwayPlaces.rep_retr σ.ρ σ.irred (π.locRep w) (hiso σ hσ).2 v hv
    obtain ⟨B, hB⟩ := (_root_.UpperTheory.V.Af.satake_local_of_printed_results P F 2 w σ).1 ⟨T v, hTv, fun u hu => by rw [← hT, hf u (UpperTheory.V.Sd.OrdinaryAwayPlaces.iwahori_level_zero_eq w ▸ hu)]⟩
    have hB' : π.HasSat w B := ((_root_.UpperTheory.V.Af.satake_local_of_printed_results P F 2 w σ).2 _ π.finPart (hiso σ hσ) B).2 hB
    exact triv (hG.frob w hl B hB' A h).1
      ((H.ram w A h).2 (Or.inl hc))
  obtain ⟨lam, ⟨v, hv, hf, hU⟩, hlam⟩ := H.away w hc hl
  have hl0 : lam ≠ 0 := by
    rintro rfl
    simp at hlam
  obtain ⟨T, hT, hTv⟩ := UpperTheory.V.Sd.OrdinaryAwayPlaces.rep_retr σ.ρ σ.irred (π.locRep w) (hiso σ hσ).2 v hv
  obtain ⟨μ₁, μ₂, L, hL, hμ, -, hlaw⟩ := _root_.UpperTheory.V.Sd.jacqOfU_alt P F w σ (c w) (Units.mk0 lam hl0) hc
    ⟨T v, hTv, fun u hu => by rw [← hT, hf u hu], by
      rw [Uop, ← UpperTheory.V.Sd.OrdinaryAwayPlaces.map_dc σ.ρ (π.locRep w) T hT hTv, ← Uop, hU, map_smul, Units.val_mk0]⟩
  obtain ⟨ψ, hψ, hs, hψ0⟩ := UpperTheory.V.Sd.OrdinaryAwayPlaces.exists_ps σ.smooth σ.irred μ₁ μ₂ L hL hlaw
  obtain ⟨rc, hrc⟩ := recTExists F Ω A w h
  have hpl := (Birth.ordPlain F Ω l ι ξ s c m a π r H w σ hσ).elim id fun ⟨B, hB⟩ => hG.plain w B hB σ hσ
  have hx := (((hG.loc w σ hσ hpl).1 A h rc hrc).1 hl).isWDOf (hGd F Ω A w h rc hrc 2 σ hpl)
  refine UpperTheory.V.Sd.OrdinaryAwayPlaces.diag_of_wd hl ι r ξ hx (fun g => ?_) (fun g hg => ?_)
    fun e => ((H.ram w A h).1 e).elim hc hl
  · obtain ⟨b, hb, ε, hL⟩ := toV' hrc
    obtain ⟨e1, e2⟩ := RR.ps_cls hL σ ψ hψ hs
    rw [e1, UpperTheory.V.Sd.OrdinaryAwayPlaces.charPol_lpTw]
    have h1 := e2 (ineIncl h g)
    have h2 : valuation (w.adicCompletion F) (b (ineIncl h g) : w.adicCompletion F) = 1 :=
      ord_eq_zero_iff.1 (by rw [hb.ord_eq, deg_ineIncl, neg_zero])
    have : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    rw [Fin.prod_univ_two, hψ0 _ h2, hμ _ ((isEquiv (valuation (w.adicCompletion F))
      (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ)))).eq_one_iff_eq_one.1 h2)] at h1
    exact ⟨_, h1⟩
  · have h1 := DFunLike.congr_fun H.det g
    have h2 : cycZ F Ω l g = 1 := p4 hA hg
    simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.zpow_apply, cycBar, h2, map_one, one_zpow,
      one_mul] at h1
    exact congrArg Units.val h1
end
