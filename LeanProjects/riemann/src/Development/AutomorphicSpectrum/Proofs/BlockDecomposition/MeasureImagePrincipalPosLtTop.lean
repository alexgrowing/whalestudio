import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsTemperedCoeff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenIsCompactPrincipal

open GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.PrincipalCongruence

theorem measure_image_principal_pos_lt_top :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (N : ℕ) (ϖ : k) (m : ℕ), ϖ ≠ 0 → ValuativeRel.valuation k (ϖ) < 1 →
      (∀ x : k, ValuativeRel.valuation k (x) < 1 →
        ValuativeRel.valuation k (x) ≤ ValuativeRel.valuation k (ϖ)) → 1 ≤ m →
      ∀ [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)] (μ : MeasureTheory.Measure (AdGL k N)),
        μ.IsHaarMeasure →
        0 < μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) ''
          {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k
            ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
              ValuativeRel.valuation k (ϖ ^ m)}) ∧
        μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) ''
          {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k
            ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
              ValuativeRel.valuation k (ϖ ^ m)}) < ⊤ := by
  intro k _ _ _ _ N ϖ m h0 h1 _ hm _ _ μ hμ
  have ht0 : ϖ ^ m ≠ 0 := pow_ne_zero m h0
  have ht1 : ValuativeRel.valuation k (ϖ ^ m) < 1 := by
    rw [map_pow]
    exact pow_lt_one' h1 (by omega)
  obtain ⟨hopen, hcomp⟩ := isOpen_isCompact_principal k N (ϖ ^ m) ht0 ht1
  have hone : (1 : GL (Fin N) k) ∈ {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k
      ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
        ValuativeRel.valuation k (ϖ ^ m)} := by
    intro i j
    simp
  refine ⟨?_, ?_⟩
  · have himg : IsOpenMap (QuotientGroup.mk : GL (Fin N) k → AdGL k N) :=
      QuotientGroup.isOpenMap_coe
    exact (himg _ hopen).measure_pos μ ⟨_, Set.mem_image_of_mem _ hone⟩
  · exact (hcomp.image QuotientGroup.continuous_mk).measure_lt_top

end GlobalTheory.CompanionTheory.PrincipalCongruence
