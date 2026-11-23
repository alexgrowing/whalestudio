import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DvrBundleStatementAStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DvrBundleStatementBStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleProductStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.QuotIsoCk

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d N N₁ : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (E E' : ChartBundle O (mseg x) N V) (F F' : ChartBundle O (mseg x) N₁ V₁), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → SameGeneric O x E E' → SameGeneric O x F F' → QuotIso O x E E' F F' → ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d N E E' k L Q = ck O x d N₁ F F' k L Q := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d N N₁ V _ _ V₁ _ _ E E' F F' hM hE hF hQ k hk1 hk2 q L Q hQh
  obtain ⟨P, hP⟩ := hQ
  obtain ⟨S, hS⟩ := (GlobalTheory.T.chart_bundle_product O Ω K ι x).1 N N₁ V V₁ E F
  have hSP : SameGeneric O x S P := by
    intro s hs
    obtain ⟨h1, h2, h3, h4⟩ := hP s hs
    refine ⟨?_, ?_⟩
    · rintro ⟨v, w⟩ hvw
      rw [hS s hs, AddSubgroup.mem_prod] at hvw
      obtain ⟨c, hc, hcv⟩ := (hE s hs).1 v hvw.1
      obtain ⟨c', hc', hcw⟩ := (hF s hs).1 w hvw.2
      refine ⟨c * c', mul_ne_zero hc hc', ?_⟩
      have a1 := P.stable s (algebraMap O Ω c') (Subalgebra.algebraMap_mem _ _) _ ((h1 _).2 hcv)
      have a2 := P.stable s (algebraMap O Ω c) (Subalgebra.algebraMap_mem _ _) _ ((h3 _).2 hcw)
      have a3 := (P.lat s).add_mem a1 a2
      convert a3 using 1
      ext
      · simp [smul_smul, mul_comm]
      · simp [smul_smul]
    · rintro ⟨v, w⟩ hvw
      refine ⟨1, one_ne_zero, ?_⟩
      rw [hS s hs, AddSubgroup.mem_prod]
      simp only [map_one, one_smul]
      exact ⟨(h2 v).1 ⟨w, hvw⟩, (h4 w).1 ⟨v, hvw⟩⟩
  have hrefE : SameGeneric O x E E := fun s _ =>
    ⟨fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩, fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩⟩
  have hrefF : SameGeneric O x F F := fun s _ =>
    ⟨fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩, fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩⟩
  have zE := (GlobalTheory.T.dvr_bundle_statement_a O Ω K ι x d N V E E E hM hrefE hrefE k hk1 hk2 q L Q hQh).2
  have zF := (GlobalTheory.T.dvr_bundle_statement_a O Ω K ι x d N₁ V₁ F F F hM hrefF hrefF k hk1 hk2 q L Q hQh).2
  have s1 : IsSubQuot O x S (LinearMap.inl Ω V V₁) (LinearMap.snd Ω V V₁) E F := by
    refine ⟨LinearMap.inl_injective, LinearMap.snd_surjective, LinearMap.range_inl Ω V V₁,
      fun s hs => ⟨?_, ?_⟩⟩
    · ext v
      rw [hS s hs]
      simp [AddSubgroup.mem_prod]
    · ext w
      rw [hS s hs, AddSubgroup.mem_map]
      constructor
      · intro hw
        exact ⟨(0, w), AddSubgroup.mem_prod.2 ⟨zero_mem _, hw⟩, rfl⟩
      · rintro ⟨⟨v, w'⟩, h, rfl⟩
        exact (AddSubgroup.mem_prod.1 h).2
  have s2 : IsSubQuot O x P (LinearMap.inl Ω V V₁) (LinearMap.snd Ω V V₁) E' F := by
    refine ⟨LinearMap.inl_injective, LinearMap.snd_surjective, LinearMap.range_inl Ω V V₁,
      fun s hs => ⟨?_, ?_⟩⟩
    · ext v
      exact ((hP s hs).1 v).symm
    · ext w
      rw [AddSubgroup.mem_map, ← (hP s hs).2.2.2 w]
      constructor
      · rintro ⟨v, h⟩
        exact ⟨(v, w), h, rfl⟩
      · rintro ⟨⟨v, w'⟩, h, rfl⟩
        exact ⟨v, h⟩
  have s3 : IsSubQuot O x S (LinearMap.inr Ω V V₁) (LinearMap.fst Ω V V₁) F E := by
    refine ⟨LinearMap.inr_injective, LinearMap.fst_surjective, LinearMap.range_inr Ω V V₁,
      fun s hs => ⟨?_, ?_⟩⟩
    · ext v
      rw [hS s hs]
      simp [AddSubgroup.mem_prod]
    · ext v
      rw [hS s hs, AddSubgroup.mem_map]
      constructor
      · intro hv
        exact ⟨(v, 0), AddSubgroup.mem_prod.2 ⟨hv, zero_mem _⟩, rfl⟩
      · rintro ⟨⟨v', w⟩, h, rfl⟩
        exact (AddSubgroup.mem_prod.1 h).1
  have s4 : IsSubQuot O x P (LinearMap.inr Ω V V₁) (LinearMap.fst Ω V V₁) F' E := by
    refine ⟨LinearMap.inr_injective, LinearMap.fst_surjective, LinearMap.range_inr Ω V V₁,
      fun s hs => ⟨?_, ?_⟩⟩
    · ext w
      exact ((hP s hs).2.2.1 w).symm
    · ext v
      rw [AddSubgroup.mem_map, ← (hP s hs).2.1 v]
      constructor
      · rintro ⟨w, h⟩
        exact ⟨(v, w), h, rfl⟩
      · rintro ⟨⟨v', w⟩, h, rfl⟩
        exact ⟨w, h⟩
  have e1 := GlobalTheory.T.dvr_bundle_statement_b O Ω K ι x d (N + N₁) N N₁ (V × V₁) V V₁ S P _ _ E E' F F hM hSP s1 s2
    k hk1 hk2 q L Q hQh
  have e2 := GlobalTheory.T.dvr_bundle_statement_b O Ω K ι x d (N + N₁) N₁ N (V × V₁) V₁ V S P _ _ F F' E E hM hSP s3 s4
    k hk1 hk2 q L Q hQh
  omega

end GlobalTheory.CompanionTheory.Ar.Num.QuotIsoCk
