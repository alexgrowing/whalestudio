import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAdeleCharEqCompMulTotallyReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingClassGroupOfConductorNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModFMulPosPrincipal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSectionIntegralFiniteIdeleUpToUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModFFiniteIdeleUpToExtension
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option autoImplicit false

namespace GlobalTheory

theorem normSq_embedding_eq_abs_norm_of_imagQuad {K : Type} [Field K] [NumberField K] (d : ℕ)
    (δ : K) (io : K →+* ℂ) (hK : Module.finrank ℚ K = 2) (hd : 0 < d) (hδ : δ ^ 2 = -(d : K))
    (x : K) : Complex.normSq (io x) = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  classical
  have hnoreal : ∀ w : InfinitePlace K, ¬ InfinitePlace.IsReal w := by
    intro w hw
    have h := InfinitePlace.conjugate_embedding_eq_of_isReal hw
    have h1 : w.embedding δ ^ 2 = -(d : ℂ) := by rw [← map_pow, hδ]; simp
    have h2 : (starRingEnd ℂ) (w.embedding δ) = w.embedding δ := by
      have := congrArg (fun f : K →+* ℂ => f δ) h
      simpa [ComplexEmbedding.conjugate_coe_eq] using this
    obtain ⟨r, hr⟩ : ∃ r : ℝ, w.embedding δ = r :=
      ⟨(w.embedding δ).re, (Complex.conj_eq_iff_re.mp h2).symm⟩
    rw [hr] at h1
    have h3 : (r ^ 2 : ℝ) = -(d : ℝ) := by exact_mod_cast h1
    have h4 : (0 : ℝ) < d := Nat.cast_pos.mpr hd
    nlinarith [sq_nonneg r]
  have hR : InfinitePlace.nrRealPlaces K = 0 :=
    Fintype.card_eq_zero_iff.mpr ⟨fun w => hnoreal w.1 w.2⟩
  have hC : InfinitePlace.nrComplexPlaces K = 1 := by
    have := InfinitePlace.card_add_two_mul_card_eq_rank K; omega
  have hcard : Fintype.card (InfinitePlace K) = 1 := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, hR, hC]
  have huniv : (Finset.univ : Finset (InfinitePlace K)) = {InfinitePlace.mk io} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    exact ⟨Finset.mem_univ _, fun w _ => Fintype.card_le_one_iff.mp hcard.le w _⟩
  have h := InfinitePlace.prod_eq_abs_norm x
  rw [huniv, Finset.prod_singleton,
    (InfinitePlace.not_isReal_iff_isComplex.mp (hnoreal _)).mult_eq_two,
    InfinitePlace.apply] at h
  rw [Complex.normSq_eq_norm_sq, h]
  push_cast
  rfl

end GlobalTheory
