import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceRingFractionEmbeddingStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.XiSize

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations

variable (R : Subring ℂ) [IsDiscreteValuationRing R]

theorem ord_nonneg {y : FractionRing R} (hy : y ≠ 0)
    (h : (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R) y ≤ 1) : 0 ≤ ord_vw R y := by
  unfold ord_vw
  have h0 : (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R) y ≠ 0 := by simpa using hy
  have e := WithZero.exp_log h0
  rw [← e, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
  omega

theorem ord_inv (y : FractionRing R) : ord_vw R y⁻¹ = - ord_vw R y := by
  unfold ord_vw
  rw [map_inv₀, WithZero.log_inv]

theorem ord_nonneg_of_mem {y : FractionRing R} (hy : y ≠ 0) (r : R) (hr : algebraMap R (FractionRing R) r = y) :
    0 ≤ ord_vw R y := by
  refine ord_nonneg R hy ?_
  rw [← hr]
  exact (IsDiscreteValuationRing.maximalIdeal R).valuation_le_one r

theorem xi_size : GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (d : ℕ)
    (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (R : Subring ℂ) [IsDiscreteValuationRing R],
    GlobalTheory.LatModel.IsPlaceRing E l lam R → ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (ξ : E) (e₀ : ℤˣ), ξ ∈ GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.polPos φ e₀ (GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.latMod (condQ 𝔣 Q) y) →
      GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.GenAt l (GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.polMod (GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.latMod (condQ 𝔣 Q) y)) ξ →
      ξ ≠ 0 ∧ ∀ σ : E →+* FractionRing R, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (σ ξ) ≤ 0 := by
  intro hPM E _ _ _ I _ d φ hFD 𝔣 h𝔣 l _ Q hQ hQl y hy lam R _ hR j hj ξ e₀ hξ hgen
  obtain ⟨-, -, hUn, -, -, -, hCM, -⟩ := hFD
  obtain ⟨hne, hint, -⟩ := (hPM E hUn I φ hCM e₀).2 𝔣 Q h𝔣 hQ l Fact.out hQl y hy ξ hξ hgen
  refine ⟨hne, fun σ => ?_⟩
  have hl : l.Prime := Fact.out
  have hσ : σ ξ ≠ 0 := (map_ne_zero σ).2 hne
  obtain ⟨n, hn, hI⟩ := hint (j.comp σ)
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hl.one_lt.ne' ((Nat.coprime_zero_left l).1 hn)
  have hnd : ¬ l ∣ n := (Nat.Prime.coprime_iff_not_dvd hl).1 hn.symm

  have e1 : (n : ℂ) * ((j.comp σ) ξ)⁻¹ = j ((n : FractionRing R) * (σ ξ)⁻¹) := by
    simp [map_inv₀]
  have hIR : IsIntegral R ((n : FractionRing R) * (σ ξ)⁻¹) := by
    obtain ⟨p, hp, hev⟩ := hI
    refine ⟨p.map (Int.castRingHom R), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    apply j.injective
    rw [Polynomial.hom_eval₂, ← e1, map_zero]
    have hs : j.comp ((algebraMap R (FractionRing R)).comp (Int.castRingHom R)) = algebraMap ℤ ℂ := Subsingleton.elim _ _
    rw [hs]
    exact hev
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hIR

  have hq : (((1 / n : ℚ)) : ℂ) ∈ R := hR.2.2.1 _ (by
    rw [one_div, padicValRat.inv, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnd]; simp)
  set u : R := ⟨_, hq⟩
  have hun : u * (n : R) = 1 := by
    apply Subtype.ext
    have : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
    simp [u]
    field_simp
  have e2 : algebraMap R (FractionRing R) (u * r) = (σ ξ)⁻¹ := by
    rw [map_mul, hr, ← _root_.mul_assoc, ← map_natCast (algebraMap R (FractionRing R)), ← map_mul, hun, map_one, _root_.one_mul]
  have h1 : ord_vw R (σ ξ) ≤ 0 := by
    have := ord_nonneg_of_mem R (inv_ne_zero hσ) _ e2
    rw [ord_inv] at this
    omega
  have hl0 : (l : FractionRing R) ≠ 0 := by
    rw [← map_natCast (algebraMap R (FractionRing R))]
    refine (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 ?_
    intro h
    have := congrArg Subtype.val h
    simp [hl.ne_zero] at this
  have h2 : 0 ≤ ord_vw R (l : FractionRing R) :=
    ord_nonneg_of_mem R hl0 (l : R) (map_natCast _ _)
  unfold val_vp
  rw [if_neg hσ]
  have h3 : ((ord_vw R (σ ξ) : ℚ) / (ord_vw R (l : FractionRing R) : ℚ)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h1) (by exact_mod_cast h2)
  exact_mod_cast h3

end GlobalTheory.XiSize
