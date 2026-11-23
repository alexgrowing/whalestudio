import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSplitPrimeAvoiding
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelPrimeSplitsCompletelyInCmField
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducible

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.GoodPlace

theorem ncard_primesOver_eq_two {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) {p : ℕ} (hp : p.Prime)
    (h : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E)
    (v : HeightOneSpectrum (𝓞 F)) (hpv : (p : 𝓞 F) ∈ v.asIdeal) :
    (v.asIdeal.primesOver (𝓞 E)).ncard = 2 := by
  classical
  haveI := v.isMaximal
  have hs := Ideal.sum_ramification_inertia (𝓞 E) F E (p := v.asIdeal) v.ne_bot
  rw [h2] at hs
  rw [← hs, ← IsDedekindDomain.coe_primesOverFinset v.ne_bot, Set.ncard_coe_finset, Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot] at hq
  haveI := hq.1
  haveI := hq.2
  have hpq : (p : 𝓞 E) ∈ q := by
    simpa using (Ideal.mem_of_liesOver q v.asIdeal (p : 𝓞 F)).1 hpv
  have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≤ q := Ideal.map_le_iff_le_comap.2 (Ideal.LiesOver.over (P := q) (p := v.asIdeal)).le
  have he : v.asIdeal.ramificationIdx' q = 1 := by
    by_contra hne1
    have h3 := (Ideal.ramificationIdx'_ne_one_iff hle).1 hne1
    have h4 := h3 (Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) hpv)
    rw [map_natCast] at h4
    exact (GlobalTheory.LocSplit.split_prime hp h q hpq).1 h4
  have hcF := (GlobalTheory.ColClassCompare.unram_card_of_split (F := F) (E := E) hp h v.asIdeal hpv).2
  have hcE := (GlobalTheory.ColClassCompare.unram_card_of_split (F := E) (E := E) hp h q hpq).2
  have hf : v.asIdeal.inertiaDeg' q = 1 := by
    have hcomap : Ideal.comap (algebraMap (𝓞 F) (𝓞 E)) q = v.asIdeal := (Ideal.LiesOver.over (P := q) (p := v.asIdeal)).symm
    rw [Ideal.inertiaDeg', dif_pos hcomap]
    letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
    have hfin : Module.Finite (𝓞 F ⧸ v.asIdeal) (𝓞 E ⧸ q) := inferInstance
    have := Module.natCard_eq_pow_finrank (K := 𝓞 F ⧸ v.asIdeal) (V := 𝓞 E ⧸ q)
    rw [hcF, hcE] at this
    exact (Nat.pow_right_injective hp.two_le (by simpa using this.symm))
  rw [he, hf]

end GlobalTheory.GoodPlace

namespace GlobalTheory.GoodPlace

theorem exists_good_place : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (P₀ : Finset (HeightOneSpectrum (𝓞 D.host.F))), ∃ v₁ : HeightOneSpectrum (𝓞 D.host.F), v₁ ∉ P₀ ∧
      SplitsFully D.host.E v₁ ∧ (∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ v₁) ∧
      Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v₁) := by
  intro D T L sc G μ₀ _ t P₀
  classical
  set S : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
    P₀ ∪ (locPl G t).image (fun w => w.under (𝓞 D.host.F)) with hS
  have hn : D.host.QS ≠ 0 := D.host.QS_pos.ne'
  have hq : D.host.q ≠ 0 := D.host.hyp.1.ne_zero
  have hd : D.host.d ≠ 0 := D.host.hyp.2.1.ne_zero
  have hm : D.host.QS * D.host.q * D.host.d ≠ 0 := by positivity
  obtain ⟨p, hp, hlt, hc⟩ := Nat.exists_prime_gt_modEq_one (∑ u ∈ S, Ideal.absNorm u.asIdeal) hm
  obtain ⟨h1, -, -⟩ := GlobalTheory.HostSplit.split_completely_of_modEq_one D.R D.host p hp hc
  have h : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E := by
    rw [← GlobalTheory.HostSplit.ncard_placesOver _ hp]
    exact h1
  obtain ⟨v, hv⟩ := GlobalTheory.SplitChoice.exists_place_over D.host.F hp
  have hnot : ∀ u ∈ S, u ≠ v := by
    intro u hu e
    refine GlobalTheory.SplitChoice.natCast_notMem_of_absNorm_lt u hp ?_ (e ▸ hv)
    have := Finset.single_le_sum (f := fun u : HeightOneSpectrum (𝓞 D.host.F) => Ideal.absNorm u.asIdeal)
      (fun _ _ => Nat.zero_le _) hu
    omega
  refine ⟨v, fun hv0 => hnot v (Finset.mem_union_left _ hv0) rfl, ?_,
    fun w hw e => hnot _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hw)) e, ?_⟩
  · have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible
    have hle : Ideal.span {(p : ℤ)} ≤ v.asIdeal.under ℤ := by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
      simpa using hv
    have hunder : v.asIdeal.under ℤ = Ideal.span {(p : ℤ)} :=
      (hmax.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top hle).symm
    unfold SplitsFully
    rw [hunder]
    exact h
  · rw [GlobalTheory.AdelicU.nonempty_split_iff (GlobalTheory.AdelicU.isCMExt_host D)]
    exact ncard_primesOver_eq_two (GlobalTheory.AdelicU.isCMExt_host D).2.2.1 hp h v hv

end GlobalTheory.GoodPlace
