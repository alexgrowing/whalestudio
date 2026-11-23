import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PluckerCoord
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinCkOnFlagPair
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPairIff
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPlainPolyPairNum
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinRootPolyNum
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinDivDiffExpansion
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberExpansionIndependence
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.VerticalDivisorsCommuteStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelValueIndependentStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelRootIndependentStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem ck_rootNum_eq_pairNum_on_flagPair : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ d : ℕ, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V), SameGeneric O x E E' → ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d → fnField O (joinCoord x z) = fnField O x → ∀ EB E'B : ChartBundle O (mseg (joinCoord x z)) N V, IsPull O x z E EB → IsPull O x z E' E'B → ∀ (w w' : Module.Basis (Fin N) Ω V) (b b' : Fin N → K ⊕ K' → ℤ) (f g : Fin N → MRing (Sum.elim ι ι') O), IsFlagPair ϖ (joinCoord x z) EB E'B w w' b b' f g → (∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d N E E' k L Q = ∑ μ ∈ Q.support, Q.coeff μ * pairNum (pointIdeal O (joinCoord x z)) b b' f g (psumExpansion N k) (classList (fun j => pullDeg (K' := K') (L j)) μ)) ∧ (∀ (c : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsSymmetric → G.IsHomogeneous c → c ≤ d → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d - c) → ∀ a : O, a ≠ 0 → rootNum O x d N E G L Q a = ∑ μ ∈ Q.support, Q.coeff μ * cycEval (fun W => classNum b G (classList (fun j => pullDeg (K' := K') (L j)) μ) W) (divCycle (pointIdeal O (joinCoord x z)) (C a))) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x ϖ hϖ d hW N V _ _ E E' hEE' K' _ _ ι' _ z hm hb EB E'B hp hp'
    w w' b b' f g hfp
  have hprime : (mcIdeal O x).IsPrime := hW.2.1.1
  obtain ⟨-, hB⟩ := (BundleExamples.isModelOver_iff O _ d).mp hm
  have hB' : IsModelOver (pointIdeal O (joinCoord x z)) d := hB
  haveI hprimeB : (pointIdeal O (joinCoord x z)).IsPrime := hm.2.1.1
  have hI := IntNumIsFieldIntersection.full (IsLocalRing.ResidueField O) (K ⊕ K') (Sum.elim ι ι')
  refine ⟨fun k hk1 hk2 q L Q hQ => ?_, fun c G hsym hG hc q L Q hQ a ha => ?_⟩
  · obtain ⟨φ, -, -, hd, hd', hf, hg⟩ :=
      ((FlagPairCharacterisation.proof O Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) N V EB E'B ϖ hϖ
        hB'.multiProj).1 w w' b b' f g).mp hfp
    let F₀ : FlagModel O x d N E E' :=
      { K' := K', ι' := ι', z := z, model := hm, birat := hb, EB := EB, E'B := E'B,
        pull := hp, pull' := hp', flag := φ }
    have hne : Nonempty (FlagModel O x d N E E') := ⟨F₀⟩
    have hv : F₀.value O (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs)
        (psum (Fin N) ℤ k) L L (fun _ => 1) (fun _ => 1) Q =
        GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O
          (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs)
          (pointIdeal O (joinCoord x z)) d
          (Fin.append b fun l => pullDeg (K' := K') (L l))
          (Fin.append b' fun l => pullDeg (K' := K') (L l))
          (Fin.append f fun _ => 1) (Fin.append g fun _ => 1)
          (rename (Fin.castAdd q) (psum (Fin N) ℤ k) * rename (Fin.natAdd N) Q) := by
      show GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O _ _ d (Fin.append φ.deg _)
        (Fin.append φ.deg' _) (Fin.append φ.f fun _ => rename (liftVar ι') (1 : MRing ι O))
        (Fin.append φ.g fun _ => rename (liftVar ι') (1 : MRing ι O)) _ = _
      rw [hd, hd', hf, hg, map_one]
      rfl
    unfold ck
    rw [dif_pos hne]
    refine (GlobalTheory.T.flag_model_value_independent O Ω K ι x d N V E E' hW hEE'
      (Classical.choice hne) F₀ _ _ (ChernClassOnFlagPair.fieldNum_spec _ _) hI (psum (Fin N) ℤ k)
      (psum_isSymmetric _ _ k) q L L (fun _ => 1) (fun _ => 1)
      (fun l => ChernClassOnFlagPair.isVertDiv_one hprime _ (sub_self _)) k Q hk2
      (isHomogeneous_psum N k) hQ).trans ?_
    refine hv.trans ((plainPolynomialPairNumber.proof O (K ⊕ K') (Sum.elim ι ι')
      (pointIdeal O (joinCoord x z)) d N b b' f g k (psum (Fin N) ℤ k)
      (isHomogeneous_psum N k) hk2 q _ Q hQ).trans ?_)
    refine Finset.sum_congr rfl fun μ hμ => ?_
    have hlen : (classList (fun j => pullDeg (K' := K') (L j)) μ).length + k = d + 1 := by
      have h := hQ (mem_support_iff.mp hμ)
      rw [ChernClassOnFlagPair.length_classList, Finsupp.degree_eq_weight_one]
      have : Finsupp.weight (fun _ => 1) μ = Finsupp.weight 1 μ := rfl
      omega
    rw [PairNumberExpansionIndependence.proof GlobalTheory.T.vertical_divisors_commute O ϖ hϖ (K ⊕ K') (Sum.elim ι ι')
      (pointIdeal O (joinCoord x z)) d hB' N b b' f g hfp.vertical k (psum (Fin N) ℤ k)
      (isHomogeneous_psum N k) _ (psumExpansion N k)
      (dividedDifferenceExpansion.proof N k _ (isHomogeneous_psum N k)) (isPairExpansion_psum N k)
      _ hlen]
  · have hsame : SameGeneric O x E E := fun s _ =>
      ⟨fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩,
        fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩⟩
    obtain ⟨φ, -, -, hd, -, -, -⟩ :=
      ((FlagPairCharacterisation.proof O Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) N V EB EB ϖ hϖ
        hB'.multiProj).1 w w b b _ _).mp (ChernClassOnFlagPair.isFlagPair_self hfp.flag)
    let F₀ : FlagModel O x d N E E :=
      { K' := K', ι' := ι', z := z, model := hm, birat := hb, EB := EB, E'B := EB,
        pull := hp, pull' := hp, flag := φ }
    have hne : Nonempty (FlagModel O x d N E E) := ⟨F₀⟩
    unfold rootNum
    rw [dif_pos hne]
    refine (GlobalTheory.T.flag_model_root_independent O Ω K ι x d N V E E hW hsame
      (Classical.choice hne) F₀ _ _ (ChernClassOnFlagPair.fieldNum_spec _ _) hI c G hsym hG hc q L Q hQ a
      ha).trans ?_
    have h6 := RootPolynomialNumber.proof O (K ⊕ K') (Sum.elim ι ι') (pointIdeal O (joinCoord x z)) d N b
      c G hG hc q (fun j => pullDeg (K' := K') (L j)) Q hQ a
    rw [← hd] at h6 ⊢
    exact h6

end GlobalTheory.CompanionTheory.Ar.Num
