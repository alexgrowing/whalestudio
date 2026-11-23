import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsShaDict
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsGsEquiv
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsLocal
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsRep
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDualPf
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsBidual
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SelmerGroupDualExact

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion GroundTheory.ProfCoh GroundTheory.Global CategoryTheory

namespace PositivityTheory.Lit1.PTN

abbrev toFS (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] : FiniteSubfield :=
  ⟨K, inferInstance⟩

section
attribute [local instance 2000] Rep.hV2
theorem finite_dualRep' {G : Type} [Group G] (D A : Rep.{0} (ULift.{0} ℤ) G) [Finite D] [Finite A] :
    Finite (dualRep D A) := inferInstance
end

set_option maxHeartbeats 0 in
theorem shaDictFS : ShaDictFS := by
  intro K _ _ l _ r hl hr ζ hζ inv hinv S hS Av hAv μ hμ M _ _ _ _ _ ρ hρ
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero r (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨e, he⟩ := gsEquiv_toGS' K (S : Set (HeightOneSpectrum (𝓞 K)))
  obtain ⟨ιs, ev, hevc, hev⟩ := localCmp' K S Av hAv e he
  obtain ⟨A, hAd, eM, hM⟩ := repCmp e ρ hρ
  have hc' : ContAction (twDual μ ρ) :=
    GlobalTheory.CompanionTheory.GalDual.contAction_twDual K (AlgebraicClosure ℚ) l r M S Av μ ρ hρ hμ
  obtain ⟨eD, hD, -⟩ := dualCmp' (toFS K) S hr ζ hζ hS e he μ hμ ρ A eM hM
  have hSN : ∀ v : HeightOneSpectrum (𝓞 K), ((l ^ r : ℕ) : 𝓞 K) ∈ v.asIdeal →
      v ∈ (S : Set (HeightOneSpectrum (𝓞 K))) := by
    intro v hv
    rw [Nat.cast_pow] at hv
    exact Finset.mem_coe.2 (hS v (v.isPrime.mem_of_pow_mem r hv))
  have hK : Odd (l ^ r) ∨ IsTotallyComplex K :=
    hl.imp (fun h => ((Fact.out : l.Prime).odd_of_ne_two h).pow) id
  have hDZ : Nonempty (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r) ≃+ ZMod (l ^ r)) :=
    nonempty_addEquiv_gsRoots_of_mem (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) hSN
  haveI : Finite (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) := Finite.of_equiv _ hDZ.some.symm.toEquiv
  haveI hFA : Finite A := Finite.of_equiv M eM.toEquiv
  have htor : ∀ m : A, (l ^ r) • m = 0 := fun m => by
    obtain ⟨x, rfl⟩ := eM.surjective m
    rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod (l ^ r)), ZMod.natCast_self, zero_smul,
      map_zero]
  have htor1 : ∀ f : dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A, (l ^ r) • f = 0 :=
    nsmul_dualRep_eq_zero (fun d => nsmul_gsRoots (K := (toFS K)) _ _ d)
  haveI hDd : IsDiscreteRep (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A) :=
    isDiscreteRep_dualRep _ _
  haveI hF1 : Finite (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A) := finite_dualRep' _ _
  haveI hDDd : IsDiscreteRep (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A)) := isDiscreteRep_dualRep _ _
  obtain ⟨eB, hB⟩ := bidualCmp (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A (l ^ r) hDZ htor
  have hM'' : ∀ g m, (eM.trans eB) (ρ g m) = (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r))
      (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A)).ρ (e g) ((eM.trans eB) m) := by
    intro g m
    simp only [AddEquiv.trans_apply, hM, hB]
  have X1 : Nonempty (Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av) ≃+ ptSha (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs) (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A) 1) :=
    (shaIso_of_rep K S Av e ιs ev hevc hev (twDual μ ρ) hc' (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A) eD hD).1
  have X2 : Nonempty (Sha2 ρ (locFam S Av) (continuous_locFam S Av) ≃+ ptSha (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs) (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A)) 2) :=
    (shaIso_of_rep K S Av e ιs ev hevc hev ρ hρ (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A)) (eM.trans eB) hM'').2
  have X3 : Nonempty (Sha1 ρ (locFam S Av) (continuous_locFam S Av) ≃+ ptSha (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs) A 1) :=
    (shaIso_of_rep K S Av e ιs ev hevc hev ρ hρ A eM hM).1
  have X4 : Nonempty (Sha2 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av) ≃+ ptSha (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs) (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A) 2) :=
    (shaIso_of_rep K S Av e ιs ev hevc hev (twDual μ ρ) hc' (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A) eD hD).2
  refine ⟨⟨(toFS K), (S : Set (HeightOneSpectrum (𝓞 K))), inferInstance, ιs, l ^ r, inferInstance, hSN, hK, (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A), hDd, hF1, htor1, ?_, ?_⟩,
    ⟨(toFS K), (S : Set (HeightOneSpectrum (𝓞 K))), inferInstance, ιs, l ^ r, inferInstance, hSN, hK, A, hAd, hFA, htor, ?_, ?_⟩⟩
  · exact X1
  · exact X2
  · exact X3
  · exact X4

theorem shaCmpFS' : ShaCmpFS := shaCmpFS_of_dict shaDictFS

end PositivityTheory.Lit1.PTN
