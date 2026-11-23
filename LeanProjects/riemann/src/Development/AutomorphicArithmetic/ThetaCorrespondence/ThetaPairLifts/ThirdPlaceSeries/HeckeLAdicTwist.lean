import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGaloisCharacterOfAlgebraic
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeLAdicParameterAbove
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CgEqOfCharStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocParTwistAbsPow
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeilDeligneRankOneEqLocalStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventuallyUnr
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.GalPin
open Neutral.B1 GlobalTheory.HeckeGal GlobalTheory.TripleGal GlobalTheory.Pst GlobalTheory.CuspRep Formalism.BasicNotions.Loc
theorem heckeLAdicTwist_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.HeckeLAdicCharacterAbove → _root_.GlobalTheory.Published.HeckeLAdicParameterAboveAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (i : D.nd.Loc) (χ : D.naut.CG 1) (s : ℝ), (∀ τ : D.host.E →+* ℂ, ∀ z ∈ D.naut.infG χ τ, ∃ k : ℤ, z + (s : ℂ) = (k : ℂ)) → ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i)), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ ∧ (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG χ w) s) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG χ w) s ∧ ∀ τ, InducesW D.nd i τ w → (D.naut.jumpsW i ρ τ).map (fun n : ℤ => (n : ℂ)) = (D.naut.infG χ ((D.naut.iotaQC i).toRingHom.comp τ)).map (fun z => -(z + (s : ℂ))) := by
  intro hF hGA hCh hPa hL D P i χ s hint
  have := host_isCMField D.host
  set ψ : HChar D.host.E := (P.chr.e1 χ).1 with hψ
  set ν := GlobalTheory.HeckeGal.Model.absPow D.host.E s
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow D.host.E s
  have hinf : ∀ τ, D.naut.infG χ τ = {expo ψ τ} := fun τ => by
    rw [P.cg.inf, CGu.infChar, _root_.GlobalTheory.T.cusp_rep_one_eq_of_character_choice hF hL D P χ, CG.infChar_ofChar]
  have hexpo : ∀ τ, expo (ψ * ν) τ = expo ψ τ + s := fun τ => by
    have h := (CG.hasInfChar_ofChar ψ τ).twist ν
    rw [CG.twist_ofChar, Multiset.map_singleton] at h
    have := h.infChar_eq
    rw [CG.infChar_ofChar] at this
    rw [← (GlobalTheory.T.heckeChar_exponent_of_infinityType _ ν).2.1 s hν τ]
    simpa using this
  have hint' : ∀ τ, ∃ k : ℤ, expo (ψ * ν) τ = k := fun τ => by
    obtain ⟨k, hk⟩ := hint τ (expo ψ τ) (by rw [hinf]; exact Multiset.mem_singleton_self _)
    exact ⟨k, by rw [hexpo, hk]⟩
  choose n hn using hint'
  have hAlg : IsAlgPos (ψ * ν) n := GlobalTheory.T.isAlgebraicHeckeCharOfWeight_of_integer_expo D.host.E (ψ * ν) n hn
  obtain ⟨art, ha⟩ := hGA D.host.E D.nd.Om
  obtain ⟨μ, hμc, hμ⟩ := ha.exists_isLAdicOf (D.naut.iotaQC i) hAlg
  have hpar : ∀ (w : PlE D.host) (u : ℝ), P.T.e w (D.naut.lpTw (D.naut.locG χ w) u) =
      (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar ψ) (D.nd.plOm.2 w)).lpTw u := fun w u => by
    rw [P.T.tw, P.cg.loc, ← _root_.GlobalTheory.T.cusp_rep_one_eq_of_character_choice hF hL D P χ]
    rfl
  have htw : ∀ w : PlE D.host, _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar (ψ * ν)) (D.nd.plOm.2 w) =
      (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar ψ) (D.nd.plOm.2 w)).lpTw s := fun w => by
    rw [← CG.twist_ofChar]
    exact _root_.GlobalTheory.HeightCounting.Blocks.local_parameter_twist_abs_pow hL hF _ hν _
  refine ⟨rk1 μ, ?_, fun w hw => ?_, fun w hw => ?_⟩
  · show Continuous fun g => ((rk1 μ g : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i)))
    exact (continuous_pi fun _ => Units.continuous_val.comp hμc).matrix_diagonal
  · have hl : (((D.nd.l i : ℕ)) : 𝓞 D.host.E) ∉ w.asIdeal := hw
    rw [(P.wdOf i 1 (rk1 μ) w).1]
    refine (P.T.e w).injective ?_
    rw [P.wd.away _ _ (rk1 μ) w hl, _root_.GlobalTheory.T.weil_deligne_rank_one_local_param' hL D.host.E D.nd.Om _ _ art ha _ n μ hμc hμ _ w (D.nd.plOm.2 w) hl, htw, hpar]
  · have hab := fun (O : Type) [CommRing O] [Algebra ℤ_[D.nd.l i] O] [TopologicalSpace O]
        (Bw : LocBridge (D.nd.l i) D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O) (hj : Induces Bw) =>
      (GlobalTheory.Published.heckeLAdicCharacterAbove_iff.1 hCh) D.host.E D.nd.Om (D.nd.l i) (D.loc _) (D.locA _) ⟨D.locT _⟩
        (D.naut.iotaQC i) art ha (ψ * ν) n μ hAlg hμc hμ w (D.nd.plOm.1 w) (D.nd.plOm.2 w) O Bw hj
    obtain ⟨hdR, hJ⟩ := GlobalTheory.T.deRham_jumps_of_continuous_lAdic_char D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) μ hμc
      (fun τ => {-n ((D.naut.iotaQC i).toRingHom.comp τ)}) w hw
      (fun O _ _ _ Bw hj => ⟨(hab O Bw hj).1, (hab O Bw hj).2.2.2⟩)
    refine ⟨(P.wdOf i 1 (rk1 μ) w).2.2.2.1.2 hdR, ?_, fun τ hτ => ?_⟩
    · rw [(P.wdOf i 1 (rk1 μ) w).1]
      refine (P.T.e w).injective ?_
      obtain ⟨LL, Bw, hj, he⟩ := P.wd.above _ _ (rk1 μ) w hw
      have hc : IsComp (ψ * ν) w ((ψ * ν).loc w) := ⟨ParLaws.isSmoothChar_loc _ w, fun x => rfl⟩
      rw [he, hpar, ← htw, hPa D.host.E D.nd.Om (D.nd.l i) (D.loc _) (D.locA _) ⟨D.locT _⟩ (D.naut.iotaQC i) art ha
        (ψ * ν) n μ hAlg hμc hμ w (D.nd.plOm.1 w) (D.nd.plOm.2 w) _ Bw hj _ hc _
        (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w)), _root_.GlobalTheory.CuspRep.ParLaws.local_parameter_of_hecke_character_eq_reciprocity]
      rfl
    · rw [(P.wdOf i 1 (rk1 μ) w).2.2.2.2 τ, hJ τ hτ, hinf, Multiset.map_singleton, Multiset.map_singleton,
        Int.cast_neg, ← hn, hexpo]
end GlobalTheory.GalPin
end
