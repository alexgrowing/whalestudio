import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ModNSqIffExistsGenLatSum
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem sq_dvd_sum_EF_of_killed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → ∀ a a' : Fin n → Dw.La, (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) → ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) → ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • a j)) → (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) → ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) → ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • a' j)) → ((N : ℤ) ^ 2) ∣ ∑ b, Dw.EF (a b) (a' b) := by
  intro E _ _ _ H Dw n Λ N hU hN hle a a' ha ha'
  obtain ⟨m, x, v, hv, hav⟩ := (GlobalTheory.modN_sq_iff_exists_genLat_sum E H Dw n Λ N hU hN hle a).1 ha
  obtain ⟨m', x', v', hv', hav'⟩ := (GlobalTheory.modN_sq_iff_exists_genLat_sum E H Dw n Λ N hU hN hle a').1 ha'
  have key : ∑ b, Dw.EF (a b) (a' b)
      = ∑ i, ∑ j, Dw.EF (x i) ((∑ b, H.bar (v i b) * v' j b) • x' j) := by
    simp only [hav, hav', Finset.sum_smul, map_sum, LinearMap.sum_apply, Dw.adj, mul_smul]
    rw [Finset.sum_comm]
    simp only [Finset.sum_comm (s := (Finset.univ : Finset (Fin n)))]
    exact Finset.sum_comm
  rw [key]
  refine Finset.dvd_sum fun i _ => Finset.dvd_sum fun j _ => ?_
  obtain ⟨w, hw, hvw⟩ := hv i
  obtain ⟨w', hw', hvw'⟩ := hv' j
  obtain ⟨c, hc⟩ := (hU w).1 hw w' hw'
  have hs : (∑ b, H.bar (v i b) * v' j b) = ((N : ℤ) ^ 2) • c := by
    apply IsFractionRing.injective (𝓞 E) E
    rw [map_sum, map_zsmul, hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, ← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap, H.bar_eq,
      hvw, hvw', map_mul, map_natCast, zsmul_eq_mul]
    push_cast
    ring
  rw [hs, smul_assoc, map_zsmul, smul_eq_mul]
  exact dvd_mul_right _ _

end GlobalTheory
