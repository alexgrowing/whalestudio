import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDefs
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateNineTermGs
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PfInvMatchNsmulB
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsInvGen

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual
  GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

set_option maxHeartbeats 800000 in
theorem invCmp' (Kf : FiniteSubfield) [NumberField Kf.1] [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)]
    (S : Set (HeightOneSpectrum (𝓞 Kf.1))) [Fintype S] {l r : ℕ} [Fact l.Prime] (hr : 0 < r)
    (hS : ∀ v : HeightOneSpectrum (𝓞 Kf.1), ((l : ℕ) : 𝓞 Kf.1) ∈ v.asIdeal → v ∈ S)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (l ^ r))
    (inv : InvFam Kf.1 (AlgebraicClosure ℚ) l r) (hinv : InvNormalised ζ inv)
    (ιs : ∀ v : S, AlgebraicClosure ℚ →ₐ[Kf.1]
      AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))
    (v : S) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : IsPlaceOver A v.1)
    (ev : (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[
        (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)) ≃* Dec (F := Kf.1) A)
    (hev : ∀ σ x, ιs v (((ev σ : Dec (F := Kf.1) A) : G Kf.1 (AlgebraicClosure ℚ)) x) = σ (ιs v x))
    (hevc : Continuous ev) (z : Z2 (muLoc Kf.1 l r A))
    (x : cocycles (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S (l ^ r))) 2)
    (hzx : ∀ s : Fin 2 → (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[
        (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)),
      ((((Additive.toMul (cochainOf _ (cocycleι _ 2 x) s) :
          rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) :
          (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) :
          maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S) : AlgebraicClosure ℚ) =
        ζ ^ (z.1 (ev (s 0), ev (s 1))).val) :
    zmodToQZ (l ^ r) (inv A (Submodule.Quotient.mk z)) =
      - gsLocalInvRootsQZ S ιs (l ^ r) v (cohomologyπ _ 2 x) := by
  have key := @invMatch_gen' Kf ‹_› ‹_› S ‹_› l r ‹_› hr hS ζ hζ inv hinv ιs v A hA ev hev
  have hm0 := key.choose_spec.choose_spec.1
  have hz0 := key.choose_spec.choose_spec.2.1
  have hx0 := key.choose_spec.choose_spec.2.2
  have : NeZero (l ^ r) := ⟨pow_ne_zero r (Fact.out : l.Prime).ne_zero⟩
  have hbij := (hinv A v.1 hA).1
  have hz : (Submodule.Quotient.mk z : H2 (muLoc Kf.1 l r A)) =
      (inv A (Submodule.Quotient.mk z)).val • Submodule.Quotient.mk key.choose := by
    apply hbij.1
    rw [map_nsmul, hz0, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  have hx := @invMatch_nsmul_B Kf ‹_› ‹_› S ‹_› l r ‹_› hr hS ζ hζ inv hinv ιs v A hA ev hev hevc
    z key.choose x key.choose_spec.choose hzx hm0 _ hz
  have E := (congrArg (gsLocalInvRootsQZ S ιs (l ^ r) v) hx).trans
    ((map_nsmul (gsLocalInvRootsQZ S ιs (l ^ r) v) _ _).trans
      (congrArg ((inv A (Submodule.Quotient.mk z)).val • ·) hx0))
  have e3 := zmodToQZ_eq_nsmul (inv A (Submodule.Quotient.mk z))
  exact e3.trans ((neg_neg _).symm.trans (congrArg Neg.neg ((smul_neg _ _).symm.trans E.symm)))

end PositivityTheory.Lit1.PTN
