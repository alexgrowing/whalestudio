import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticHeightTensorAdditiveOnCurves
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeLinearRootSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.DualRef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsDualBundle
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechPic
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CoverNorm GlobalTheory.ArDegIndep.TieOther

namespace GlobalTheory

theorem fibre_over_prime_of_finite_field_action : ∀ (F : Type) [Field F] [NumberField F] (X Z : Scheme.{0}) (q : X ⟶ Sp (𝓞 F)) (i : Z ⟶ X) [IsIntegral Z]
    (κ : Type) [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)],
    ∃ v : HeightOneSpectrum (𝓞 F), ((ringChar κ : ℕ) : 𝓞 F) ∈ v.asIdeal ∧ ∀ z : Z, (q (i z)).asIdeal = v.asIdeal := by
  intro F _ _ X Z q i _ κ _ _ _
  set p : ℕ := ringChar κ with hpdef
  have hp : p ≠ 0 := CharP.char_ne_zero_of_finite κ p
  have hpF : ((p : ℕ) : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 hp
  have hp0 : ((p : ℕ) : Γ(Z, ⊤)) = 0 := by
    rw [← map_natCast (algebraMap κ Γ(Z, ⊤)), hpdef, ringChar.Nat.cast_ringChar, map_zero]
  have e : i ≫ q = Z.toSpecΓ ≫
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 F))).inv ≫ (i ≫ q).appTop) := by
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.comp_id]
  have key : ∀ z : Z, ((p : ℕ) : 𝓞 F) ∈ (q (i z)).asIdeal := by
    intro z
    have hz : q (i z) = (Z.toSpecΓ ≫
        Spec.map ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 F))).inv ≫ (i ≫ q).appTop)) z := by
      rw [← e]; rfl
    rw [hz]
    show _ ∈ Ideal.comap _ _
    rw [Ideal.mem_comap, map_natCast, hp0]
    exact zero_mem _
  have hne : ∀ z : Z, (q (i z)).asIdeal ≠ ⊥ := fun z h => hpF (by
    have := key z
    rw [h] at this
    exact (Submodule.mem_bot _).1 this)
  let η : Z := genericPoint Z
  have hmax : (q (i η)).asIdeal.IsMaximal := (q (i η)).isPrime.isMaximal (hne η)
  refine ⟨⟨(q (i η)).asIdeal, (q (i η)).isPrime, hne η⟩, key η, fun z => ?_⟩
  have hsp : η ⤳ z := (genericPoint_spec Z).specializes (Set.mem_univ z)
  have hsp' : (q (i η)) ⤳ (q (i z)) := (hsp.map i.continuous).map q.continuous
  have hle : (q (i η)).asIdeal ≤ (q (i z)).asIdeal := (PrimeSpectrum.le_iff_specializes _ _).2 hsp'
  exact (hmax.eq_of_le (q (i z)).isPrime.ne_top hle).symm

end GlobalTheory
