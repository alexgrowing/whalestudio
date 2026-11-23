import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PluckerCoord
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericFlagDifferenceStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericBundleChainStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericFlagComparisonStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleBaseExtensionUniqueStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PairCocycleStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.Cocycle

section Generic

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω]
  [Algebra O Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {x : (Σ k, ι k) → Ω} {N : ℕ} {V : Type} [AddCommGroup V] [Module Ω V]

theorem sameGeneric_self (E : ChartBundle O (mseg x) N V) : SameGeneric O x E E :=
  fun _ _ => ⟨fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩,
    fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩⟩

theorem sameGeneric_flip {E E' : ChartBundle O (mseg x) N V} (h : SameGeneric O x E E') :
    SameGeneric O x E' E :=
  fun s hs => ⟨(h s hs).2, (h s hs).1⟩

theorem sameGeneric_comp {E E' E'' : ChartBundle O (mseg x) N V} (h : SameGeneric O x E E')
    (h' : SameGeneric O x E' E'') : SameGeneric O x E E'' := by
  have step : ∀ {A B C : ChartBundle O (mseg x) N V} (s : ∀ k, ι k),
      (∀ v ∈ A.lat s, ∃ c : O, c ≠ 0 ∧ algebraMap O Ω c • v ∈ B.lat s) →
      (∀ v ∈ B.lat s, ∃ c : O, c ≠ 0 ∧ algebraMap O Ω c • v ∈ C.lat s) →
      ∀ v ∈ A.lat s, ∃ c : O, c ≠ 0 ∧ algebraMap O Ω c • v ∈ C.lat s := by
    intro A B C s hAB hBC v hv
    obtain ⟨c, hc, hcv⟩ := hAB v hv
    obtain ⟨c', hc', hcv'⟩ := hBC _ hcv
    exact ⟨c' * c, mul_ne_zero hc' hc, by rwa [map_mul, mul_smul]⟩
  exact fun s hs => ⟨step s (h s hs).1 (h' s hs).1, step s (h' s hs).2 (h s hs).2⟩

end Generic

theorem length_classList {K : Type} {q m : ℕ} (cls : Fin q → K → ℤ) {Q : MvPolynomial (Fin q) ℤ}
    (hQ : Q.IsHomogeneous m) {μ : Fin q →₀ ℕ} (hμ : μ ∈ Q.support) :
    (classList cls μ).length = m := by
  have h := hQ (mem_support_iff.1 hμ)
  rw [classList, Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset, ← h]
  simp [Finsupp.weight_apply, Finsupp.sum]

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.Ba.Statement.{0,0,0} O Ω ι := by
  intro O _ _ _ Ω _ _ K _ ι _
  classical
  intro x d N V _ _ E E' E'' hM h1 h2 k hk1 hk2 q L Q hQ
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have h13 : SameGeneric O x E E'' := sameGeneric_comp h1 h2
  obtain ⟨K', _, _, ι', _, z, EB, w, b, hMB, hbir, hEB⟩ :=
    GlobalTheory.T.same_generic_bundle_chain O Ω K ι x d hM N 2 V ![E, E', E''] (by
      intro j
      fin_cases j
      · exact sameGeneric_self E
      · exact h1
      · exact h13)
  have hM' : IsModelOver (pointIdeal O (joinCoord x z)) d :=
    ((GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples.isModelOver_iff O _ d).1 hMB).2
  have p0 : IsPull O x z E (EB 0) := (hEB 0).1
  have p1 : IsPull O x z E' (EB 1) := (hEB 1).1
  have p2 : IsPull O x z E'' (EB 2) := (hEB 2).1
  have fr : ∀ j, IsFlagFrame (joinCoord x z) (EB j) w (b j) := fun j => (hEB j).2
  have tri : ∀ i j : Fin N, i < j → w.repr (w i) j = 0 := by
    intro i j hij
    simp [Module.Basis.repr_self, Finsupp.single_apply, ne_of_lt hij]
  have pair : ∀ i j, SameGeneric O (joinCoord x z) (EB i) (EB j) →
      SameGenericFibre ϖ (EB i) (EB j) ∧ ∃ f g : Fin N → MRing (Sum.elim ι ι') O,
        IsFlagPair ϖ (joinCoord x z) (EB i) (EB j) w w (b i) (b j) f g := fun i j hs =>
    GlobalTheory.T.same_generic_flag_comparison O Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) ϖ hϖ d hM' N V (EB i) (EB j) hs
      w w (b i) (b j) (fr i) (fr j) tri
  have s01 := (GlobalTheory.T.chart_bundle_base_extension_unique O Ω K ι x N V E E' K' ι' z (EB 0) (EB 1) p0 p1).2.1 h1
  have s12 := (GlobalTheory.T.chart_bundle_base_extension_unique O Ω K ι x N V E' E'' K' ι' z (EB 1) (EB 2) p1 p2).2.1 h2
  have s02 := (GlobalTheory.T.chart_bundle_base_extension_unique O Ω K ι x N V E E'' K' ι' z (EB 0) (EB 2) p0 p2).2.1 h13
  obtain ⟨g01, f01, d01, c01⟩ := pair 0 1 s01
  obtain ⟨g12, f12, d12, c12⟩ := pair 1 2 s12
  obtain ⟨-, f02, d02, c02⟩ := pair 0 2 s02
  obtain ⟨-, f10, d10, c10⟩ := pair 1 0 (sameGeneric_flip s01)
  have num : ∀ {A B : ChartBundle O (mseg x) N V} (i j : Fin 3) (f g : Fin N → MRing (Sum.elim ι ι') O),
      SameGeneric O x A B → IsPull O x z A (EB i) → IsPull O x z B (EB j) →
      IsFlagPair ϖ (joinCoord x z) (EB i) (EB j) w w (b i) (b j) f g →
      ck O x d N A B k L Q = ∑ μ ∈ Q.support, Q.coeff μ *
        pairNum (pointIdeal O (joinCoord x z)) (b i) (b j) f g (psumExpansion N k)
          (classList (fun j => pullDeg (K' := K') (L j)) μ) := by
    intro A B i j f g hs pi pj hf
    exact (GlobalTheory.T.same_generic_flag_difference O Ω K ι x ϖ hϖ d hM N V A B hs K' ι' z hMB hbir (EB i) (EB j) pi pj
      w w (b i) (b j) f g hf).1 k hk1 hk2 q L Q hQ
  have coc := fun μ (hμ : μ ∈ Q.support) =>
    GlobalTheory.T.pair_cocycle O ϖ hϖ Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) d hM' N V (EB 0) (EB 1) (EB 2)
      g01 g12 w w w (b 0) (b 1) (b 2) f01 d01 f12 d12 f02 d02 c01 c12 c02 k (psumExpansion N k)
      (psumExpansion N k) (psumExpansion N k) (isPairExpansion_psum N k) (isPairExpansion_psum N k)
      (isPairExpansion_psum N k) (classList (fun j => pullDeg (K' := K') (L j)) μ)
      (by rw [length_classList _ hQ hμ]; omega)
  refine ⟨?_, ?_⟩
  · rw [num 0 2 f02 d02 h13 p0 p2 c02, num 0 1 f01 d01 h1 p0 p1 c01,
      num 1 2 f12 d12 h2 p1 p2 c12, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [(coc μ hμ).1, mul_add]
  · rw [num 1 0 f10 d10 (sameGeneric_flip h1) p1 p0 c10, num 0 1 f01 d01 h1 p0 p1 c01,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [(coc μ hμ).2 f10 d10 (psumExpansion N k) c10 (isPairExpansion_psum N k), mul_neg]

end GlobalTheory.CompanionTheory.Ar.Num.Cocycle
