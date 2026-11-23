import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.FnInt

theorem main : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ (l : Fin (D + 1)) (w : X.functionField), x l ≠ 0 → (∀ z ∈ NV P e 0 (x l), RegAt z w) → IsIntegral (ratR x l) w := by
  intro k _ X _ p D hA P e x hG l w hl hw
  have : IsProper p := by
    obtain ⟨m, i, hi, rfl⟩ := hA.isProjOver
    have := isProper_str k m
    infer_instance
  have hmem : w ∈ (integralClosure (Subring.closure (Set.range fun j => x j / x l)) X.functionField).toSubring := by
    rw [← iInf_valuationSubring_superset, Subring.mem_iInf]
    rintro ⟨V, hV⟩
    change w ∈ V
    have hk : ∀ a : k, toFunctionField p a ∈ V := by
      intro a
      have := hA.finite
      have h1 : IsIntegral ℤ (toFunctionField p a) :=
        (Algebra.IsIntegral.isIntegral (R := ℤ) a).map (toFunctionField p).toIntAlgHom
      have h2 : IsIntegral V (toFunctionField p a) := h1.tower_top
      obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
      rw [← hy]; exact y.2
    have hd := dominatesStalk_centre p V hk
    obtain ⟨j, hj⟩ := hG.cover (centre p V hk)
    have hz : centre p V hk ∈ NV P e 0 (x l) := by
      intro i i' hi hi'
      have hu := hj i i' hi hi'
      have hr := hG.mem l (centre p V hk) i i' hi hi'
      have hne := hu.ne_zero
      have hxj : x j ≠ 0 := fun h0 => hne (by simp [Pair.loc, h0])
      have hloc : P.loc (e : ℤ) 0 (x l) i i' = x l / x j * P.loc (e : ℤ) 0 (x j) i i' := by
        simp only [Pair.loc]; field_simp
      have hg : RegAt (centre p V hk) (x l / x j) := by
        have : x l / x j = P.loc (e : ℤ) 0 (x l) i i' * (P.loc (e : ℤ) 0 (x j) i i')⁻¹ := by
          rw [hloc, mul_assoc, mul_inv_cancel₀ hne, mul_one]
        rw [this]; exact hr.mul hu.inv.regAt
      have hgu : UnitAt (centre p V hk) (x l / x j) := by
        by_contra hn
        obtain ⟨a, ha, hag⟩ := zeroAt_iff.2 ⟨hg, hn⟩
        have h1 := hd.2 a ha
        rw [hag] at h1
        have hgV : x l / x j ∈ V := by rw [← hag]; exact hd.1 a
        have h2 : (x l / x j)⁻¹ ∈ V := by
          rw [inv_div]; exact hV ⟨j, rfl⟩
        have hgne : x l / x j ≠ 0 := div_ne_zero hl hxj
        have hu' : IsUnit (⟨x l / x j, hgV⟩ : V) := by
          refine ⟨⟨⟨_, hgV⟩, ⟨_, h2⟩, Subtype.ext (mul_inv_cancel₀ hgne), Subtype.ext (inv_mul_cancel₀ hgne)⟩, rfl⟩
        exact (V.coe_mem_nonunits_iff (a := ⟨_, hgV⟩)).mp h1 hu'
      rw [hloc]; exact hgu.mul hu
    obtain ⟨a, ha⟩ := hw _ hz
    rw [← ha]; exact hd.1 a
  exact hmem

end GlobalTheory.FnInt
