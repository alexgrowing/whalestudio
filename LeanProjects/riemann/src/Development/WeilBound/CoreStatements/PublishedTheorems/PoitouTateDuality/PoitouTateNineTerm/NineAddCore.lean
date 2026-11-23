import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsNineAdd
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsDataEx
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.TateDualityDegreeZeroMiddle
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.TateDualityDegreeOneMiddle
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.TateDualityDegreeTwoMiddle
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.TateDualityDegreeZeroLeft
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.TateDualityDegreeOneLeft
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.DegreeTwoCohomologyComparisonLeft
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDualQZ
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PfContActionTwDualC
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.LocTr0B
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.LocTr1C
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.LocTr2
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PoitouTateNineTerm.NineAddOfFound3

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual
  GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

set_option maxHeartbeats 8000000 in
theorem nineAdd_core (Kf : FiniteSubfield)
    [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)] {l r : ℕ} [Fact l.Prime] (hl : l ≠ 2 ∨ IsTotallyComplex Kf.1) (hr : 0 < r)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (l ^ r))
    (inv : InvFam Kf.1 (AlgebraicClosure ℚ) l r) (hinv : PositivityTheory.PoitouTateConclusion.InvNormalised ζ inv)
    (S : Finset (HeightOneSpectrum (𝓞 Kf.1))) (hS : ContainsAbove S l) (Av : S → ValuationSubring (AlgebraicClosure ℚ))
    (hAv : ∀ v, IsPlaceOver (Av v) v.1)
    (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) →* (ZMod (l ^ r))ˣ)
    (hμ : μ.comp (toGS (AlgebraicClosure ℚ) _) = cycMod Kf.1 (AlgebraicClosure ℚ) l r)
    (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) M)
    (hρ : ContAction ρ) (d : FoundData Kf S l r ζ Av μ M ρ) :
    NineAdd (loc0 S Av ρ) (tr0 S Av μ (invAt S Av μ hμ inv) ρ) (loc1 S Av ρ)
      (tr1 S Av μ (invAt S Av μ hμ inv) ρ hρ) (loc2 S Av ρ) (tr2 S Av μ (invAt S Av μ hμ inv) ρ) := by
  haveI := d.isDiscrete
  haveI : Finite d.A := Finite.of_equiv M d.eM.toEquiv
  haveI hDd : IsDiscreteRep (dualRep (gsRoots (K := Kf) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A) := isDiscreteRep_dualRep _ _
  haveI hDv : ∀ v : S, IsDiscreteRep (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom
      (dualRep (gsRoots (K := Kf) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A)) :=
    fun v => isDiscreteRep_res_dualRep_of_finite _ _ _
  have hρ' : ContAction (twDual μ ρ) := contAction_twDual_C S μ hμ ρ hρ
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero r (Fact.out : l.Prime).ne_zero⟩
  have hSN : ∀ v : HeightOneSpectrum (𝓞 Kf.1), (((l ^ r : ℕ) : ℕ) : 𝓞 Kf.1) ∈ v.asIdeal →
      v ∈ (S : Set (HeightOneSpectrum (𝓞 Kf.1))) := by
    intro v hv
    rw [Nat.cast_pow] at hv
    exact Finset.mem_coe.2 (hS v (v.isPrime.mem_of_pow_mem r hv))
  have hK : Odd (l ^ r) ∨ IsTotallyComplex Kf.1 := by
    rcases hl with h | h
    · exact Or.inl ((Fact.out : l.Prime).odd_of_ne_two h).pow
    · exact Or.inr h
  have hMt : ∀ m : d.A, (l ^ r) • m = 0 := by
    intro m
    rw [← d.eM.apply_symm_apply m, ← map_nsmul, nsmul_eq_zero_of_zmod, map_zero]
  have F9 :=
    poitouTate_nineTerm_gs (K := Kf) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs hSN hK d.A hMt
  have hM0 := tate_duality_degree_zero_middle Kf S ζ Av μ ρ d hρ
  have hM1 := tate_duality_degree_one_middle Kf S ζ Av μ ρ d hρ
  have hM2 := tate_duality_degree_two_middle Kf S ζ Av μ ρ d hρ
  have hD0 := tate_duality_degree_zero_left Kf S ζ Av μ ρ d hρ'
  have hD1 := tate_duality_degree_one_left Kf S ζ Av μ ρ d hρ'
  have hD2 := degree_two_cohomology_comparison_left Kf S ζ Av μ ρ d hρ'
  exact nineAdd_of_found3 (N := l ^ r) S (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs) (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A (gsLocalInvRootsQZ (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs (l ^ r)) _ _
    F9
    (fun k => resH0 ρ (locFam S Av k)) (fun k => resH1 ρ (locFam S Av k) (continuous_locFam S Av k))
    (fun k => resH2 ρ (locFam S Av k) (continuous_locFam S Av k))
    (fun k => resH0 (twDual μ ρ) (locFam S Av k))
    (fun k => resH1 (twDual μ ρ) (locFam S Av k) (continuous_locFam S Av k))
    (fun k => resH2 (twDual μ ρ) (locFam S Av k) (continuous_locFam S Av k))
    (fun k a b => invAt S Av μ hμ inv k (cupH0H2TwistedDual μ ρ (locFam S Av k) a b))
    (fun k a b => invAt S Av μ hμ inv k (cupH1H1TwistedDual μ ρ (locFam S Av k) (hρ.comp' (continuous_locFam S Av k)) b a))
    (fun k a b => invAt S Av μ hμ inv k (cup20 μ ρ (locFam S Av k) a b))
    (loc0 S Av ρ) (tr0 S Av μ (invAt S Av μ hμ inv) ρ) (loc1 S Av ρ)
    (tr1 S Av μ (invAt S Av μ hμ inv) ρ hρ) (loc2 S Av ρ) (tr2 S Av μ (invAt S Av μ hμ inv) ρ)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun x y => poitouTateNineTerm_transgressionZero_apply S Av μ (invAt S Av μ hμ inv) ρ x y)
    (fun x y => poitouTateNineTerm_transgressionOne_apply S Av μ (invAt S Av μ hμ inv) ρ hρ x y)
    (fun x y => poitouTateNineTerm_transgressionTwo_apply S Av μ (invAt S Av μ hμ inv) ρ x y)
    hM0 hM1 hM2 hD0 hD1 hD2
    (fun Ev Fv c c' k a b => locTr0_B Kf S hr ζ hζ inv hinv hS Av hAv μ hμ ρ hρ d k (Ev k) (c k) (Fv k) (c' k) a b)
    (fun Ev Fv c c' k a b => locTr1_C Kf S hr ζ hζ inv hinv hS Av hAv μ hμ ρ hρ d k (Ev k) (c k) (Fv k) (c' k) a b)
    (fun Ev Fv c c' k a b => locTr2' Kf S hr ζ hζ inv hinv hS Av hAv μ hμ ρ hρ d k (Ev k) (c k) (Fv k) (c' k) a b)

end PositivityTheory.Lit1.PTN
