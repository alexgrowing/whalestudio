import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RStabFin

theorem rStab_conj_index_ne_zero : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K K' : Subgroup G)
    (f : G → ℂ) (δ : G), IsCompact (K : Set G) → IsOpen (K' : Set G) → K' ≤ K →
    (∀ k ∈ K', ∀ x, f (k * x) = f x ∧ f (x * k) = f x) → ∀ x : G,
    (rStab fun k : K => f ((x * k)⁻¹ * δ * (x * k))).index ≠ 0 := by
  intro G _ _ _ K K' f δ hK hK' _ hf x
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hopen : IsOpen ((K'.subgroupOf K : Subgroup K) : Set K) := hK'.preimage continuous_subtype_val
  have hfin : Finite (K ⧸ K'.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hopen
  have h0 : (K'.subgroupOf K).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hle : K'.subgroupOf K ≤ rStab fun k : K => f ((x * k)⁻¹ * δ * (x * k)) := by
    intro k hk y
    have hk' : ((k : K) : G) ∈ K' := hk
    show f ((x * ((y * k : K) : G))⁻¹ * δ * (x * ((y * k : K) : G))) = f ((x * (y : G))⁻¹ * δ * (x * (y : G)))
    have e : (x * ((y * k : K) : G))⁻¹ * δ * (x * ((y * k : K) : G))
        = ((k : G))⁻¹ * ((x * (y : G))⁻¹ * δ * (x * (y : G)) * (k : G)) := by
      simp only [Subgroup.coe_mul, _root_.mul_inv_rev]; group
    rw [e, (hf _ (inv_mem hk') _).1, (hf _ hk' _).2]
  exact fun h => h0 (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_dvd_of_le hle))

end GlobalTheory.RStabFin
