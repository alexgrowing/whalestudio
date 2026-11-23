import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory.LatChain

theorem not_ov_iff_unitAt_natCast {X : Scheme.{0}} [IsIntegral X] {p : ℕ} {x : X} :
    ¬ Ov p x ↔ UnitAt x (p : X.functionField) := by
  rw [Ov, not_not]
  refine ⟨fun h => ⟨_, h, map_natCast _ p⟩, fun ⟨a, ha, e⟩ => ?_⟩
  obtain rfl := IsFractionRing.injective (X.presheaf.stalk x) X.functionField
    (e.trans (map_natCast _ p).symm)
  exact ha

theorem exists_vert_isEqn : ∀ (X : Scheme.{0}) [IsIntegral X] (p : ℕ) (η : X → X.functionFieldˣ), VEq p η → ∃ E : CartierDiv X, Vert p E ∧ ∀ x, Ov p x → E.IsEqn x (η x) := by
  intro X _ p η h
  have key (x : X) : ∀ᶠ z in 𝓝 x, germOf z (if Ov p z then η z else 1) = germOf z (if Ov p x then η x else 1) := by
    by_cases hx : Ov p x
    · obtain ⟨h₁, ⟨a, h₂⟩, h₃⟩ := h x hx
      filter_upwards [eventually_regAt h₁, eventually_regAt h₂, h₃] with z k₁ k₂ k₃
      rw [if_pos hx, germOf_eq_iff]
      by_cases hz : Ov p z
      · rw [if_pos hz]; exact k₃ hz
      · rw [if_neg hz, Units.val_one, div_one, unitAt_iff (η x).ne_zero]
        refine ⟨k₁, ?_⟩
        have hu := not_ov_iff_unitAt_natCast.1 hz
        have hr : RegAt z (((p : X.functionField)⁻¹) ^ a) := mem_loc.1 (pow_mem (mem_loc.2 hu.inv.regAt) a)
        have := hr.mul k₂
        rwa [div_eq_mul_inv, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hu.ne_zero, one_pow, one_mul] at this
    · filter_upwards [eventually_unitAt (not_ov_iff_unitAt_natCast.1 hx)] with z hz
      rw [if_neg hx, if_neg (not_ov_iff_unitAt_natCast.2 hz)]
  refine ⟨show cartierGroup X from ⟨fun x => germOf x (if Ov p x then η x else 1), fun x => ?_⟩,
    fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨U, hU, ho, hx⟩ := eventually_nhds_iff.1 (key x)
    exact ⟨⟨U, ho⟩, hx, _, hU⟩
  · exact congrArg (germOf x) (if_neg hx)
  · exact congrArg (germOf x) (if_pos hx)

end GlobalTheory.LatChain
