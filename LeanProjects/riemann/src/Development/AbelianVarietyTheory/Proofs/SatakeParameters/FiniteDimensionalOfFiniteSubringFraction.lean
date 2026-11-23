import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KaehlerOneFormsToExtensionDeRhamMulSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

theorem finiteDimensional_of_finite_subring_fraction :
    ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (B : Subring K) (B' : Subring L)
      (φ : B →+* B'), (∀ x : B, (φ x : L) = algebraMap K L x) → φ.Finite →
      (∀ y : L, ∃ a ∈ B', ∃ b ∈ B', b ≠ 0 ∧ y * b = a) → FiniteDimensional K L := by
  intro K L _ _ _ B B' φ hφ hfin hfrac
  letI : Algebra B B' := φ.toAlgebra
  have hMF : Module.Finite B B' := hfin
  obtain ⟨s, hs⟩ := hMF.fg_top

  have hB'span : ∀ x : B', (x : L) ∈ Submodule.span K ((fun z : B' => (z : L)) '' (s : Set B')) := by
    intro x
    have hx : x ∈ Submodule.span B (s : Set B') := by rw [hs]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span ⟨z, hz, rfl⟩
    | zero => simp
    | add u v _ _ hu hv => simpa using Submodule.add_mem _ hu hv
    | smul b u _ hu =>
      have : ((b • u : B') : L) = (b : K) • (u : L) := by
        rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, Subring.coe_mul, hφ, Algebra.smul_def]
      rw [this]; exact Submodule.smul_mem _ _ hu
  let S : Subalgebra K L := Algebra.adjoin K (B' : Set L)
  have hSsub : Subalgebra.toSubmodule S =
      Submodule.span K ((fun z : B' => (z : L)) '' (s : Set B')) := by
    apply le_antisymm
    · rw [Algebra.adjoin_eq_span]
      apply Submodule.span_le.mpr
      intro y hy
      have hy' : y ∈ B'.toSubmonoid := by
        rw [← Submonoid.closure_eq B'.toSubmonoid]; exact hy
      exact hB'span ⟨y, hy'⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨z, _, rfl⟩
      exact Algebra.subset_adjoin z.2
  have hFG : (Subalgebra.toSubmodule S).FG := by
    rw [hSsub]
    exact Submodule.fg_span ((s.finite_toSet).image _)
  have hB'S : ∀ y ∈ B', y ∈ S := fun y hy => Algebra.subset_adjoin hy
  have htop : ∀ y : L, y ∈ S := by
    intro y
    obtain ⟨a, ha, b, hb, hb0, hyb⟩ := hfrac y
    have hbinv : b⁻¹ ∈ S := by
      have hint : IsIntegral K b := IsIntegral.of_mem_of_fg S hFG b (hB'S b hb)
      exact Subalgebra.inv_mem_of_algebraic (A := S) (x := ⟨b, hB'S b hb⟩) hint.isAlgebraic
    have : y = a * b⁻¹ := by rw [← hyb, mul_assoc, mul_inv_cancel₀ hb0, mul_one]
    rw [this]; exact S.mul_mem (hB'S a ha) hbinv
  refine ⟨?_⟩
  obtain ⟨t, ht⟩ := hFG
  refine ⟨t, ?_⟩
  rw [ht, eq_top_iff]
  intro y _
  exact htop y

end GlobalTheory
