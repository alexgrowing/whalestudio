import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVerticalDivisorJoinPullback
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagFrameBaseExtensionStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_pull_flagpair

theorem joinCoord_eq {K K' : Type} {ι : K → Type} {ι' : K' → Type} {Ω : Type} [Field Ω]
    (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) : joinCoord x z = joinCoords x z := by
  funext p
  rcases p with ⟨k | k, i⟩ <;> rfl

theorem pullDeg_sub {K K' : Type} (b b' : K → ℤ) :
    pullDeg (K' := K') b - pullDeg (K' := K') b' = joinDeg (K' := K') (b - b') := by
  funext s
  rcases s with k | k <;> simp [pullDeg, joinDeg]

theorem pointIdeal_algebraMap {K : Type} {ι : K → Type} (O : Type) [CommRing O] {Ω Ω₁ : Type}
    [Field Ω] [Field Ω₁] [Algebra O Ω] [Algebra O Ω₁] [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁]
    (x : (Σ k, ι k) → Ω) :
    pointIdeal O (fun p => algebraMap Ω Ω₁ (x p)) = pointIdeal O x := by
  have key : ∀ f : MRing ι O, pointConeMap O (fun p => algebraMap Ω Ω₁ (x p)) f =
      MvPolynomial.map (algebraMap Ω Ω₁) (pointConeMap O x f) := by
    intro f
    simp only [pointConeMap]
    induction f using MvPolynomial.induction_on with
    | C a => simp [IsScalarTower.algebraMap_apply O Ω Ω₁]
    | add p q hp hq => simp [hp, hq]
    | mul_X p v hp => simp [hp]
  ext f
  simp only [pointIdeal, RingHom.mem_ker, key]
  exact map_eq_zero_iff _ (MvPolynomial.map_injective _ (algebraMap Ω Ω₁).injective)

theorem vertical_join (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    {Ω : Type} [Field Ω] [Algebra O Ω]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K' : Type} [Fintype K'] [DecidableEq K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (b b' : K → ℤ) (f g : MRing ι O)
    (h : IsVerticalDivisor (pointIdeal O x) ϖ (b - b') f g) :
    IsVerticalDivisor (pointIdeal O (joinCoord x z)) ϖ
      (pullDeg (K' := K') b - pullDeg (K' := K') b') (rename (liftVar ι') f) (rename (liftVar ι') g) := by
  rw [joinCoord_eq, pullDeg_sub]
  exact VerticalDivisorJoinPullback.proof O ϖ Ω K ι K' ι' x z (b - b') f g h

theorem aeval_join {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
    {K K' : Type} {ι : K → Type} {ι' : K' → Type}
    (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (f : MRing ι O) :
    aeval (joinCoord x z) (rename (liftVar ι') f) = aeval x f := by
  rw [aeval_rename]
  rfl

theorem repr_bc {Ω Ω₁ : Type} [Field Ω] [Field Ω₁] [Algebra Ω Ω₁] {N : ℕ}
    {V : Type} [AddCommGroup V] [Module Ω V]
    {V₁ : Type} [AddCommGroup V₁] [Module Ω₁ V₁] [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁]
    (bc : V →ₗ[Ω] V₁) (w : Module.Basis (Fin N) Ω V) (w₁ : Module.Basis (Fin N) Ω₁ V₁)
    (hw : ∀ i, w₁ i = bc (w i)) (v : V) (j : Fin N) :
    w₁.repr (bc v) j = algebraMap Ω Ω₁ (w.repr v j) := by
  have h : bc v = ∑ i, algebraMap Ω Ω₁ (w.repr v i) • w₁ i := by
    conv_lhs => rw [← w.sum_repr v, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hw, algebraMap_smul]
  rw [h, w₁.repr_sum_self]

end PositivityTheory.Xgn.A_pull_flagpair

open PositivityTheory.Xgn.A_pull_flagpair in
theorem PositivityTheory.Xgn.t_pull_flagpair : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V) (w w' : Module.Basis (Fin N) Ω V) (b b' : Fin N → K → ℤ) (f g : Fin N → MRing ι O), IsFlagPair ϖ x E E' w w' b b' f g → (∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) (EB E'B : ChartBundle O (mseg (joinCoord x z)) N V), IsPull O x z E EB → IsPull O x z E' E'B → IsFlagPair ϖ (joinCoord x z) EB E'B w w' (fun i => pullDeg (K' := K') (b i)) (fun i => pullDeg (K' := K') (b' i)) (fun i => rename (liftVar ι') (f i)) (fun i => rename (liftVar ι') (g i))) ∧ ∀ (Ω₁ : Type) [Field Ω₁] [Algebra O Ω₁] [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁] (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω₁) (V₁ : Type) [AddCommGroup V₁] [Module Ω₁ V₁] [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁] (bc : V →ₗ[Ω] V₁) (w₁ w₁' : Module.Basis (Fin N) Ω₁ V₁), (∀ i, w₁ i = bc (w i)) → (∀ i, w₁' i = bc (w' i)) → ∀ EB E'B : ChartBundle O (mseg (bcCoord x z)) N V₁, IsPullBC O x z bc E EB → IsPullBC O x z bc E' E'B → IsFlagPair ϖ (bcCoord x z) EB E'B w₁ w₁' (fun i => pullDeg (K' := K') (b i)) (fun i => pullDeg (K' := K') (b' i)) (fun i => rename (liftVar ι') (f i)) (fun i => rename (liftVar ι') (g i)) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x ϖ N V _ _ E E' w w' b b' f g h
  obtain ⟨h1, h1'⟩ := GlobalTheory.T.flag_frame_base_extension O Ω K ι x N V E w b h.flag
  obtain ⟨h2, h2'⟩ := GlobalTheory.T.flag_frame_base_extension O Ω K ι x N V E' w' b' h.flag'
  refine ⟨?_, ?_⟩
  · intro K' _ _ ι' _ z EB E'B hE hE'
    refine ⟨h1 K' ι' z EB hE, h2 K' ι' z E'B hE', h.sameFlag, fun i => ?_, fun i => ?_⟩
    · exact vertical_join O ϖ x z _ _ _ _ (h.vertical i)
    · rw [aeval_join, aeval_join]
      exact h.generic i
  · intro Ω₁ _ _ _ _ K' _ _ ι' _ z V₁ _ _ _ _ bc w₁ w₁' hw hw' EB E'B hE hE'
    refine ⟨h1' Ω₁ K' ι' z V₁ bc w₁ hw EB hE, h2' Ω₁ K' ι' z V₁ bc w₁' hw' E'B hE',
      fun i j hij => ?_, fun i => ?_, fun i => ?_⟩
    · rw [hw', repr_bc bc w w₁ hw, h.sameFlag i j hij, map_zero]
    · refine vertical_join O ϖ _ z _ _ _ _ ?_
      rw [pointIdeal_algebraMap]
      exact h.vertical i
    · unfold bcCoord
      have e : ∀ p : MRing ι O, aeval (fun q => algebraMap Ω Ω₁ (x q)) p =
          algebraMap Ω Ω₁ (aeval x p) := fun p => aeval_algebraMap_apply Ω₁ x p
      rw [aeval_join, aeval_join, hw', repr_bc bc w w₁ hw, e, e, h.generic i, map_mul]
