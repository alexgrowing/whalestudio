import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleCMBaseDataOfSquareTupleStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitCompletelyAuxiliaryPlaceOutsideFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasArchimedeanCharExponentsConjOfHasInfExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTauEOverRealPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowOfRestrictsToQuadratiStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridHeckeCharactersExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUnramifiedAtCofinitelyManyPlacesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUnramifiedPlaceOfUnramifiedOnePrimeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyAlgHomCompletionOfSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUnramifiedAbovePlaceOfTrivialUnitsStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.TripleBaseChars

theorem exists_placeIdem (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : ∃ ε, IsPlaceIdem D v ε :=
  ⟨_, GlobalTheory.AdelicU.singleFin v 1, rfl, GlobalTheory.AdelicU.evalV_singleFin_self v 1,
    fun _ h => GlobalTheory.AdelicU.evalV_singleFin_ne h 1⟩

theorem exists_good_place (D : D7) (P₀ : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    ∃ v₁ : HeightOneSpectrum (𝓞 D.host.F), v₁ ∉ P₀ ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SplitsFully D.host.E v₁ ∧
      Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v₁) := by
  classical
  have hn : D.host.QS ≠ 0 := D.host.QS_pos.ne'
  have hq : D.host.q ≠ 0 := D.host.hyp.1.ne_zero
  have hd : D.host.d ≠ 0 := D.host.hyp.2.1.ne_zero
  have hm : D.host.QS * D.host.q * D.host.d ≠ 0 := by positivity
  obtain ⟨p, hp, hlt, hc⟩ := Nat.exists_prime_gt_modEq_one (∑ u ∈ P₀, Ideal.absNorm u.asIdeal) hm
  obtain ⟨h1, -, -⟩ := GlobalTheory.HostSplit.split_completely_of_modEq_one D.R D.host p hp hc
  have h : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E := by
    rw [← GlobalTheory.HostSplit.ncard_placesOver _ hp]
    exact h1
  obtain ⟨v, hv⟩ := GlobalTheory.SplitChoice.exists_place_over D.host.F hp
  have hnot : ∀ u ∈ P₀, u ≠ v := by
    intro u hu e
    refine GlobalTheory.SplitChoice.natCast_notMem_of_absNorm_lt u hp ?_ (e ▸ hv)
    have := Finset.single_le_sum (f := fun u : HeightOneSpectrum (𝓞 D.host.F) => Ideal.absNorm u.asIdeal)
      (fun _ _ => Nat.zero_le _) hu
    omega
  refine ⟨v, fun hv0 => hnot v hv0 rfl, ?_, ?_⟩
  · have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible
    have hle : Ideal.span {(p : ℤ)} ≤ v.asIdeal.under ℤ := by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
      simpa using hv
    have hunder : v.asIdeal.under ℤ = Ideal.span {(p : ℤ)} :=
      (hmax.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top hle).symm
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SplitsFully
    rw [hunder]
    exact h
  · rw [GlobalTheory.AdelicU.nonempty_split_iff (GlobalTheory.AdelicU.isCMExt_host D)]
    exact GlobalTheory.GoodPlace.ncard_primesOver_eq_two (GlobalTheory.AdelicU.isCMExt_host D).2.2.1 hp h v hv

theorem exists_base_chars : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (W W₁ X : HSp D) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ ωA : WRep W X, IsWeil ψ true W X β (β / α) ωA →
    ∃ (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E),
      Bs.ψ = ψ ∧ Xc.α = α ∧ Xc.β = β ∧ Bs.IsGood D.sp.cm.sig ∧ Xc.IsGood Bs W.rank W₁.rank ∧
      (∀ w, ∃ τ, ∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧
      ∀ w, ((W.rank + W₁.rank : ℕ) : ℤ) < Bs.mα w - Bs.mβ w := by
  classical
  intro D ψ W W₁ X α β hT ωA hW
  have hψ : IsStdChar D ψ (-1) := hW.std
  choose τf hτf using fun w : InfinitePlace D.host.F => GlobalTheory.ConjTypeOverReal.exists_conj_tauE_over D w
  choose a b ha hb hab using hT.gap
  obtain ⟨mα, hmα, emα⟩ := GlobalTheory.ConjInfExp.hasExp_conj_of_hasInfExp α a ha τf hτf
  obtain ⟨mβ, hmβ, emβ⟩ := GlobalTheory.ConjInfExp.hasExp_conj_of_hasInfExp β b hb τf hτf
  have hν : IsHeckeChar D (α / β) := GlobalTheory.HeckeCharsOfSquare.isHeckeChar_div hT.hecA hT.hecB
  have hνr : ResEta D (α / β) 0 :=
    GlobalTheory.HeckeCharsOfSquare.resEta_of_mod (GlobalTheory.HeckeCharsOfSquare.resEta_div hT.resA hT.resB) (by
      have h := hT.even
      rw [hT.rank] at h
      obtain ⟨k, hk⟩ := h
      omega)
  have hfin : {w : HeightOneSpectrum (𝓞 D.host.E) | ¬ GlobalTheory.LFun.UnrAt α w ∨ ¬ GlobalTheory.LFun.UnrAt β w}.Finite :=
    ((GlobalTheory.T.heckeChar_unramified_at_cofinitely_many_places D α hT.hecA).union (GlobalTheory.T.heckeChar_unramified_at_cofinitely_many_places D β hT.hecB)).subset (fun w hw => hw)
  set S₀ : Finset (HeightOneSpectrum (𝓞 D.host.F)) := hfin.toFinset.image (fun w => w.under (𝓞 D.host.F)) with hS₀
  have hS : ∀ v ∈ S₀, ∃ ε, IsPlaceIdem D v ε ∧ ¬ GlobalTheory.WeilParts.NonSplitAt D v ε ∧
      ¬ GlobalTheory.WeilParts.UnramAt ε (α / β) ∧ ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F) := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hv
    rw [Set.Finite.mem_toFinset] at hw
    obtain ⟨ε, hε⟩ := exists_placeIdem D (w.under (𝓞 D.host.F))
    rcases hT.ram _ ε hε with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · exfalso
      rcases hw with hw | hw
      · exact hw (GlobalTheory.T.heckeChar_unramified_above_place_of_trivial_units D α _ ε hε h1 w rfl)
      · exact hw (GlobalTheory.T.heckeChar_unramified_above_place_of_trivial_units D β _ ε hε h2 w rfl)
    · exact ⟨ε, hε, h1, h2, h3⟩
  have hbad : ∀ w : HeightOneSpectrum (𝓞 D.host.E), (¬ GlobalTheory.LFun.UnrAt α w ∨ ¬ GlobalTheory.LFun.UnrAt β w) →
      w.under (𝓞 D.host.F) ∈ S₀ := fun w hw =>
    Finset.mem_image.2 ⟨w, (Set.Finite.mem_toFinset hfin).2 hw, rfl⟩
  obtain ⟨v₁, hv₁, hsp, ⟨τ₁⟩⟩ := exists_good_place D S₀
  have hemb : ∀ v : S₀, Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v) := fun v => by
    obtain ⟨ε, hε, hns, -, -⟩ := hS v.1 v.2
    exact GlobalTheory.T.nonempty_algHom_completion_of_split_place D v.1 ε hε hns
  let Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E :=
    { ψ := ψ, emb := fun w => ⟨(starRingEnd ℂ).comp (tauE D (τf w)), hτf w⟩, mα := mα, mβ := mβ, P := S₀,
      τ := fun v => (hemb v).some, v₁ := v₁, τ₁ := τ₁ }
  let Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E := ⟨α, β, S₀, ∅⟩
  have hT' : Xc.T = S₀ := by simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars.T, Xc]
  refine ⟨Bs, Xc, rfl, rfl, rfl, ?_, ?_, fun w => ⟨τf w, fun x => rfl⟩, fun w => ?_⟩
  · refine { cm := GlobalTheory.AdelicU.isCMExt_host D
             galois := D.host.hostE_isGalois
             unram := GlobalTheory.InertOfConj.unram D
             std := GlobalTheory.BaseGoodPlace.isStd_of_isStdChar hψ
             inert := ?_
             psiP := ?_ }
    · intro v w hw
      have hns : ¬ Formalism.MainNotions.KudlaSiegelWeil.Split D v := by
        rintro ⟨w1, w2, hne, h1, h2⟩
        apply hne
        have key : ∀ u : HeightOneSpectrum (𝓞 D.host.E), Formalism.MainNotions.KudlaSiegelWeil.Over D u v → u = w := fun u hu => by
          have hle : w.asIdeal ≤ u.asIdeal := by
            rw [← hw]
            exact Ideal.map_le_iff_le_comap.2 (le_of_eq hu.symm)
          exact HeightOneSpectrum.ext (w.isMaximal.eq_of_le u.isPrime.ne_top hle).symm
        rw [key w1 h1, key w2 h2]
      obtain ⟨h2, h3, hd, -⟩ := Formalism.MainNotions.KudlaSiegelWeil.inert_conditions_hold D v hns
      exact ⟨h2, h3, GlobalTheory.BaseGoodPlace.psiUnr_of_not_le hψ v hd⟩
    · intro v hv
      obtain ⟨ε, -, -, -, hd⟩ := hS v hv
      exact GlobalTheory.BaseGoodPlace.psiUnr_of_not_le hψ v (fun hle => hd (Ideal.dvd_iff_le.2 hle))
  · refine ⟨hT.hecA, hT.hecB, GlobalTheory.T.restrictsToQuadraticSignPow_of_restrictsToQuadraticCharPow _ _ D.sp.cm.deg2 _ _ hT.resA, GlobalTheory.T.restrictsToQuadraticSignPow_of_restrictsToQuadraticCharPow _ _ D.sp.cm.deg2 _ _ hT.resB,
      hmα, hmβ, Finset.disjoint_empty_right _, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hT']
    · intro w hw
      rw [hT'] at hw
      obtain ⟨ε, hε, -, hnu, -⟩ := hS _ hw
      exact fun hu => hnu (GlobalTheory.T.heckeChar_unramified_place_of_unramified_one_prime D (α / β) hν hνr _ ε hε w rfl hu)
    · intro w hw
      by_contra h
      exact hw (show w.under (𝓞 D.host.F) ∈ ((Xc.T : Finset _) : Set _) by
        rw [hT']; exact Finset.mem_coe.2 (hbad w (Or.inl h)))
    · intro w hw
      by_contra h
      exact hw (show w.under (𝓞 D.host.F) ∈ ((Xc.T : Finset _) : Set _) by
        rw [hT']; exact Finset.mem_coe.2 (hbad w (Or.inr h)))
    · exact ⟨by rw [hT']; exact hv₁, hsp⟩
  · have h1 := emα w
    have h2 := emβ w
    have h3 := hab (τf w)
    rw [hT.rank] at h3
    have : (((W.rank + W₁.rank : ℕ) : ℤ) : ℚ) < ((mα w - mβ w : ℤ) : ℚ) := by
      push_cast at h1 h2 h3 ⊢
      rw [h1, h2]
      linarith
    exact_mod_cast this

end GlobalTheory.TripleBaseChars

end
