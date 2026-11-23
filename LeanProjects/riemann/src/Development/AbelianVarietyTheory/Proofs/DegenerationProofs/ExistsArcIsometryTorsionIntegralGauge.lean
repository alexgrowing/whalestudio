import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralDegenerationValuesStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.ArcLift

theorem mem_of_pow_mem {K : Type} [Field K] (W : ValuationSubring K) {x : K} {n : ℕ} (hn : n ≠ 0) (h : x ^ n ∈ W) :
    x ∈ W := by
  rw [← W.valuation_le_one_iff] at h ⊢
  rw [map_pow] at h
  exact (pow_le_one_iff hn).1 h

theorem local_noeth {O' : Type} [CommRing O'] [IsDomain O'] {ϖ : O'} (h : GlobalTheory.LN.ArcBase O' ϖ) :
    IsLocalRing O' ∧ IsNoetherianRing O' := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩
  · letI := h.toField
    exact ⟨inferInstance, inferInstance⟩
  · exact ⟨inferInstance, inferInstance⟩

theorem exists_lift : Laws → BrGtSt → AllA fun {_} _ _ _ {_} {_} {_} {_} {_} {_} _ {O'} _ _ {_} a => ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing O') F] (S : ValuationSubring F), (∀ r : O', algebraMap (FractionRing O') F (algebraMap O' _ r) ∈ S) → ∃ A : Lift a F, A.ν.Integral S := by
  intro hL hG E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a hb F _ _ _ S hS
  obtain ⟨_, _⟩ := local_noeth hb
  obtain ⟨N, ν, hν⟩ := GlobalTheory.T.exists_integral_degeneration_values hL O' a.D₀ a.even a.bimult F S hS
  have hr : H.rt0 ∈ c.F := c.le (IntermediateField.subset_adjoin _ _ (by simp))
  have hz : zeta l.A ∈ c.F := c.le (IntermediateField.subset_adjoin _ _ (by simp))
  have hrW : H.rt0 ∈ W₀ := mem_of_pow_mem W₀ two_ne_zero (by
    rw [H.sqrt_neg_disc_sq]; exact neg_mem (natCast_mem W₀ _))
  have hzW : zeta l.A ∈ W₀ := mem_of_pow_mem W₀ l.A_pos.ne' (by
    rw [zeta, (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one]; exact one_mem _)
  let r : c.V W₀ := ⟨⟨H.rt0, hr⟩, hrW⟩
  let z : c.V W₀ := ⟨⟨zeta l.A, hz⟩, hzW⟩
  obtain ⟨hdet, I, hζ, hA, hM⟩ := a.geom F r z rfl rfl _ rfl
  have hq := fun n (v : D.La) =>
    (((hG O' a.D₀ a.even a.bimult F N ν).2.2.2.2 n).1 (I.ev n v)).exists
  choose q hq using hq
  have hr2 : r ^ 2 = -(H.d : c.V W₀) := by
    apply Subtype.ext; apply Subtype.ext
    simpa [r] using H.sqrt_neg_disc_sq
  refine ⟨{ ρ := algebraMap (FractionRing O') F (algebraMap O' _ (b r))
            ρ_sq := by rw [← map_pow, ← map_pow, ← map_pow, hr2, map_neg, map_neg, map_neg, map_natCast, map_natCast, map_natCast]
            det := fun τ => by
              obtain ⟨n, h1, h2⟩ := hdet τ
              exact ⟨n, h1, by
                rw [h2]
                by_cases h : τ H.rt = algebraMap (FractionRing O') F (algebraMap O' _ (b r))
                · rw [if_pos h]; exact if_pos h
                · rw [if_neg h]; exact if_neg h⟩
            I := I, N := N, ν := ν, q := q, hq := hq
            be := { be := a.be.comp ν.eX.toIntLinearEquiv.toLinearMap ν.eX.toIntLinearEquiv.toLinearMap
                    symm := fun y z => a.be_symm _ _
                    pos := fun y hy => a.be_pos _ (by simpa using hy)
                    dvd := fun y z => a.be_dvd _ _ }
            be_eq := fun _ _ => rfl
            ρ_eq := fun r' h => by
              obtain rfl : r' = r := Subtype.ext (Subtype.ext h)
              rfl
            ζ_eq := fun z' h => by
              obtain rfl : z' = z := Subtype.ext (Subtype.ext h)
              exact hζ
            levA := hA
            levM := hM
            closed := inferInstance }, hν⟩

end GlobalTheory.Ex.ArcLift
