import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.FamSat
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.LiftSum
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V.Published PositivityTheory.RgJS UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.T Filter

private theorem above_finite {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {S : Set (HeightOneSpectrum (𝓞 F))} (hS : S.Finite) :
    {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) ∈ S}.Finite := by
  refine Set.Finite.preimage' (f := fun w : HeightOneSpectrum (𝓞 E) => w.under (𝓞 F)) hS fun v _ => ?_
  have h := Ideal.finite_factors (R := 𝓞 E) (I := v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)))
    (by
      intro h
      exact v.ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h))
  refine h.subset fun w hw => ?_
  have e : w.under (𝓞 F) = v := hw
  rw [Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← e]
  exact le_rfl

theorem UpperTheory.ConvolutionTheory.T.famParts :
    UpperTheory.ConvolutionTheory.T.FamParts := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hl n hn hL Λ t h
  classical
  simp only [OffAll, OffFam, not_forall, not_and_or, not_not] at h
  obtain ⟨S, hS, h⟩ := h
  have hT := above_finite (E := E) hS
  rcases h with ⟨b, hb⟩ | ⟨b, Λ', t', hb, h⟩
  · obtain ⟨P, hP⟩ := famSat E n b _ hT Λ t hb
    refine ⟨Fin b.r, inferInstance, b.d, P, b.pos, by simpa using b.two, ?_⟩
    exact hT.eventually_cofinite_notMem.mono hP
  · have ht : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∉ S → t w = bcSat t' w := by
      intro w hw
      by_contra hc
      apply h
      right
      exact ⟨w, hw, hc⟩
    obtain ⟨π, hπ⟩ := famSat F n b S hS Λ' t' hb
    have hlt : ∀ i, b.d i < n := by
      intro i
      haveI : Nontrivial (Fin b.r) := Fin.nontrivial_iff_two_le.2 b.two
      obtain ⟨j, hj⟩ := exists_ne i
      refine lt_of_lt_of_eq ?_ b.sum
      exact Finset.single_lt_sum hj (Finset.mem_univ _) (Finset.mem_univ _) (b.pos j) fun k _ _ => Nat.zero_le _
    choose κ fκ m P hm hne hP using fun i => hL (b.d i) (b.pos i) (hlt i) (π i)
    have hsum := R.liftSum F E hl (Fin b.r) κ b.d (fun a => m a.1 a.2) π (fun a => P a.1 a.2) hP
    refine ⟨Σ i, κ i, inferInstance, fun a => m a.1 a.2, fun a => P a.1 a.2, fun a => hm a.1 a.2, ?_, ?_⟩
    · refine b.two.trans ?_
      have := Fintype.card_le_of_surjective (Sigma.fst : (Σ i, κ i) → Fin b.r) fun i => ⟨⟨i, (hne i).some⟩, rfl⟩
      simpa using this
    · have hN := (places F E hl).2.2.2.2.1
      filter_upwards [hsum, hT.eventually_cofinite_notMem] with w hw hwS
      obtain ⟨B, ⟨B1, hB1, e1⟩, hB'⟩ := hw (resDeg F w) (hN w)
      obtain ⟨C, ⟨C1, hC1, e2⟩, e⟩ := hπ _ hwS
      have e3 : B = C := by
        rw [e1, e2]
        exact Finset.sum_congr rfl fun i _ => (hB1 i).unique (hC1 i)
      refine ⟨_, hB', ?_⟩
      rw [ht w hwS, bcSat, e, e3, Multiset.map_map, Multiset.map_map]
      exact Multiset.map_congr rfl fun a _ => by simp
