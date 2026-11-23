import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormalThetaSumShiftPeriodDiv

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts

theorem isFShift_iff {O : Type} [CommRing O] [StarRing O] (A : AnArc O) (k : ℕ) [NeZero k] (α : A.X)
    (th : (Fin A.gB → ℂ) → ℂ) (la : A.La) (z : A.V) (F : ℂ⸨X⸩)
    (hd : (k : ℤ) ∣ A.be la.y α := by apply_assumption) :
    IsFShift A k α th la z F ↔ F = A.FSumShift k α th la z := by
  have key : ∀ n : ℤ, (∑ᶠ (m : A.X) (_ : A.exponent k (α + la.y) m + A.be la.y α / k = n),
      A.term k α th m (z + (k : ℂ)⁻¹ • A.P0 la)) = (A.FSumShift k α th la z).coeff n := fun n => by
    rw [AnArc.coeff_FSumShift]
    refine finsum_cond_eq_sum_of_cond_iff _ fun {m} _ => ?_
    rw [AnArc.mem_level, eq_sub_iff_add_eq]
  unfold IsFShift
  simp only [key]
  exact ⟨fun h => HahnSeries.ext (funext h.2), fun h => ⟨⟨NeZero.ne k, hd⟩, fun n => by rw [h]⟩⟩

theorem theta_sum_shift : ∀ (O : Type) [CommRing O] [StarRing O] (A : AnArc O), ∀ (k : ℕ) [NeZero k] (la : A.La), (∀ α, (k : ℤ) ∣ A.be la.y α) → ∃ cz : A.V → ℂ, (∀ z, cz z ≠ 0) ∧ ∀ α, ∀ th ∈ A.Theta k α, ∃ th' ∈ A.Theta k (α + la.y), (th ≠ 0 → th' ≠ 0) ∧ ∀ z, (∀ F, IsFShift A k α th la z F ↔ F = HahnSeries.single (A.be la.y α / k) (cz z) * A.FSum k (α + la.y) th' z) ∧ ∀ w : ℂ, A.Sum k α th w (z + (k : ℂ)⁻¹ • A.Pw w la) = cz z * eTwoPi (w * ((A.be la.y α / k : ℤ) : ℂ)) * A.Sum k (α + la.y) th' w z := by
  intro O _ _ A k _ la hla
  have hk : (k : ℂ) ≠ 0 := NeZero.ne _
  refine ⟨fun z => Complex.exp (A.lin la z), fun z => Complex.exp_ne_zero _, fun α th hth =>
    ⟨A.shift k la α th, A.shift_mem_Theta hth la, fun h h' => h ?_, fun z => ⟨fun F => ?_, fun w => ?_⟩⟩⟩
  · exact A.shift_injective k la α (h'.trans (map_zero _).symm)
  · rw [isFShift_iff A k α th la z F (hla α), A.FSumShift_eq k la (Int.mul_ediv_cancel' (hla α)).symm]
  · obtain ⟨m, hm⟩ := hla α
    rw [A.Sum_add_Pw_div, hm, Int.mul_ediv_cancel_left _ (NeZero.ne (k : ℤ))]
    congr 3
    push_cast
    field_simp

end GlobalTheory.ArcPts
