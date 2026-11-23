import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOfRegularAtCodimOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

set_option autoImplicit false

namespace GlobalTheory.CxOffSupp

open GlobalTheory.Cartier

theorem offSupp_of_mult_vertical : ∀ (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp (𝓞 F)) (e : ℕ),
    IsArithVar p e → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ (D : GlobalTheory.Cartier.CartierDiv X),
    (∀ z, D.mult z ≠ 0 → (p z).asIdeal ≠ ⊥) → ∀ (σ : 𝓞 F →+* ℂ) (y : CxPts p σ), y ∈ GlobalTheory.Cartier.offSupp p σ D := by
  intro F _ _ X _ _ p e _ hN D hD σ y
  rw [GlobalTheory.Cartier.mem_offSupp]

  have hinj : Function.Injective σ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have hk : RingHom.ker σ = ⊥ := by
      apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
      ext n
      simp only [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot, algebraMap_int_eq, eq_intCast,
        map_intCast, Int.cast_eq_zero]
    have : a ∈ RingHom.ker σ := ha
    rw [hk] at this
    exact this
  have hpx : (p (under y)).asIdeal = ⊥ := by
    have e1 : p (under y) = (spMap σ) (IsLocalRing.closedPoint ℂ) := by
      rw [← y.2]; rfl
    rw [e1]
    show (PrimeSpectrum.comap σ (IsLocalRing.closedPoint ℂ)).asIdeal = ⊥
    rw [PrimeSpectrum.comap_asIdeal]
    ext a
    simp only [Ideal.mem_comap, IsLocalRing.closedPoint, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      isUnit_iff_ne_zero, not_not, Ideal.mem_bot]
    exact ⟨fun h => hinj (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩
  obtain ⟨g, hg⟩ := D.exists_isEqn (under y)
  rw [hg.mem_supp_iff, not_not]
  obtain ⟨U, hxU, hU⟩ := hg.exists_nhds
  have hz : ∀ z : X, z ⤳ under y → IsDiscreteValuationRing (X.presheaf.stalk z) →
      UnitAt z (g : X.functionField) := by
    intro z hzx hdvr
    have hgz := hU z (hzx.mem_open U.isOpen hxU)
    have hc : Order.coheight z = 1 := by
      have h1 := ringKrullDim_stalk_eq_coheight z
      rw [IsDiscreteValuationRing.ringKrullDim_eq_one] at h1
      exact_mod_cast h1.symm
    have hm : D.mult z = 0 := by
      by_contra hne
      apply hD z hne
      have h2 : p z ⤳ p (under y) := hzx.map p.continuous
      have h3 : (p z).asIdeal ≤ (p (under y)).asIdeal := (PrimeSpectrum.le_iff_specializes _ _).2 h2
      rw [hpx] at h3
      exact le_bot_iff.mp h3
    rw [hgz.mult_eq, Scheme.ord_eq_iff hc g.ne_zero, ofAdd_zero] at hm
    have : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hc.le
    change Ring.ordFrac (X.presheaf.stalk z) (g : X.functionField) = 1 at hm
    rcases ValuationRing.isInteger_or_isInteger (X.presheaf.stalk z) (g : X.functionField) with
      ⟨a, ha⟩ | ⟨a, ha⟩
    · refine ⟨a, ?_, ha⟩
      rw [Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing (K := X.functionField), ha, hm]
    · have hu : UnitAt z (g : X.functionField)⁻¹ := by
        refine ⟨a, ?_, ha⟩
        rw [Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing (K := X.functionField), ha,
          map_inv₀, hm, inv_one]
      simpa using hu.inv
  have hNc : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) := fun x => (hN x).2
  exact (unitAt_iff g.ne_zero).2
    ⟨GlobalTheory.Hartogs.regAt_of_forall_dvr X hNc _ _ fun z h1 h2 => (hz z h1 h2).regAt,
     GlobalTheory.Hartogs.regAt_of_forall_dvr X hNc _ _ fun z h1 h2 => (hz z h1 h2).inv.regAt⟩

end GlobalTheory.CxOffSupp
