import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActOOneResGCompl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralHilbert90FiniteIdelesTrivialWhereTrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationOfMemNotMemSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNsmulActO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryGroupCharacterOfHeckeChar
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMatrixOfIsLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt)

noncomputable section

namespace GlobalTheory.ProductIdeleModulus

theorem exists_under_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) : ∃ Q : HeightOneSpectrum (𝓞 E), Q.under (𝓞 F) = v := by
  have hker : RingHom.ker (algebraMap (𝓞 F) (𝓞 E)) ≤ v.asIdeal := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]
    exact bot_le
  haveI := v.isMaximal
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral v.asIdeal hker
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQc, ← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]
  refine ⟨⟨Q, hQ.isPrime, hQ0⟩, ?_⟩
  ext1
  exact hQc

theorem valuation_eq_one_iff {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (x : w.adicCompletion E) :
    ValuativeRel.valuation (w.adicCompletion E) x = 1 ↔ Valued.v x = 1 := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).eq_one_iff_eq_one

theorem norm_comp_le_one {D : D7} {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} (hΦ : GlobalTheory.IdemSupport.Comp D Φ)
    {z : AE D} (hz : finPart D z ∈ intAE D) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    Valued.v (GlobalTheory.AdeleBaseChange.locMap D.host.F Q
      ((Algebra.norm (AF D.host.F) z).2 (Q.under (𝓞 D.host.F)))) ≤ 1 := by
  have hm : finPart D (z * cA D z) ∈ intAE D := by
    rw [map_mul]
    exact GlobalTheory.SplitLatBasis.mul_mem_intAE D hz (GlobalTheory.IdemSupport.finPart_cA_mem hz)
  have h := (hΦ.int _).1 hm Q
  rw [← GlobalTheory.SplitDetCharacter.algebraMap_norm, hΦ.base] at h
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h

theorem absFin_eq_one_of_int {D : D7} (x : (AE D)ˣ) (h1 : finPart D (x : AE D) ∈ intAE D)
    (h2 : finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D) : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D x = 1 := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin
  refine (finprod_congr fun v => ?_).trans finprod_one
  obtain ⟨Q, rfl⟩ := exists_under_eq (E := D.host.E) v
  have a1 := norm_comp_le_one hΦ h1 Q
  have a2 := norm_comp_le_one hΦ h2 Q
  have hn : Algebra.norm (AF D.host.F) (x : AE D) * Algebra.norm (AF D.host.F) ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hprod : Valued.v (GlobalTheory.AdeleBaseChange.locMap D.host.F Q
        ((Algebra.norm (AF D.host.F) (x : AE D)).2 (Q.under (𝓞 D.host.F)))) *
      Valued.v (GlobalTheory.AdeleBaseChange.locMap D.host.F Q
        ((Algebra.norm (AF D.host.F) ((x⁻¹ : (AE D)ˣ) : AE D)).2 (Q.under (𝓞 D.host.F)))) = 1 := by
    rw [← map_mul, ← map_mul]
    have : (Algebra.norm (AF D.host.F) (x : AE D)).2 (Q.under (𝓞 D.host.F)) *
        (Algebra.norm (AF D.host.F) ((x⁻¹ : (AE D)ˣ) : AE D)).2 (Q.under (𝓞 D.host.F)) = 1 := by
      have := congrArg (fun a : AF D.host.F => a.2 (Q.under (𝓞 D.host.F))) hn
      exact this
    rw [this, map_one, map_one]
  have hv1 : Valued.v (GlobalTheory.AdeleBaseChange.locMap D.host.F Q
      ((Algebra.norm (AF D.host.F) (x : AE D)).2 (Q.under (𝓞 D.host.F)))) = 1 :=
    le_antisymm a1 (hprod.symm.le.trans (mul_le_of_le_one_right' a2))
  have hv := (GlobalTheory.TwU.IntegralHilbert90Unramified.locMap_val_eq_one_iff Q _).1 hv1
  have e : ((GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.normV D (Q.under (𝓞 D.host.F)) x : (Fv D.host.F (Q.under (𝓞 D.host.F)))ˣ) :
      Fv D.host.F (Q.under (𝓞 D.host.F))) = (Algebra.norm (AF D.host.F) (x : AE D)).2 (Q.under (𝓞 D.host.F)) := rfl
  simp [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV, e, hv]

end GlobalTheory.ProductIdeleModulus

namespace GlobalTheory.TopLevelInv

theorem absFin_prod_locIdele_unit : ∀ {D : D7} (P : Finset (Pl D.host.E)) (y : ∀ w : P, (Kw w.1)ˣ),
    (∀ w, valuation (Kw w.1) (y w : Kw w.1) = 1) →
    GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (∏ w : P, GlobalTheory.LFun.locIdele D.host.F w.1 (y w)) = 1 := by
  intro D P y hy
  have hone : ∀ w : P, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (GlobalTheory.LFun.locIdele D.host.F w.1 (y w)) = 1 := by
    intro w
    have hv : Valued.v ((y w : Kw w.1)) = 1 := (GlobalTheory.ProductIdeleModulus.valuation_eq_one_iff w.1 _).1 (hy w)
    refine GlobalTheory.ProductIdeleModulus.absFin_eq_one_of_int _ ((GlobalTheory.LFun.EulerTie.locIdele_int_iff w.1 (y w)).2 hv.le) ?_
    rw [← map_inv]
    refine (GlobalTheory.LFun.EulerTie.locIdele_int_iff w.1 (y w)⁻¹).2 ?_
    rw [Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]
  refine Finset.prod_induction _ (fun z => GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D z = 1)
    (fun a b ha hb => by rw [GlobalTheory.SplitLinear.absFin_mul, ha, hb, one_mul]) ?_ (fun w _ => hone w)
  simp [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]

end GlobalTheory.TopLevelInv

end
