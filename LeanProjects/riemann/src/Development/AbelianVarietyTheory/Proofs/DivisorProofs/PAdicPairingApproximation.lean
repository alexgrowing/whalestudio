import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option autoImplicit false

namespace GlobalTheory.FlatModel.HTCong

theorem norm_natp (p : ℕ) [Fact p.Prime] : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  have e : (p : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := (map_natCast _ p).symm
  rw [e, norm_algebraMap', Padic.norm_p]

theorem norm_le_of_mem_span (p : ℕ) [Fact p.Prime] (n : ℕ) (z : 𝓞_ℂ_[p])
    (hz : z ∈ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}) : ‖(z : ℂ_[p])‖ ≤ (p : ℝ)⁻¹ ^ n := by
  obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  have hw : ‖(w : ℂ_[p])‖ ≤ 1 := (GlobalTheory.PadicComplexHost.mem_iff_norm p _).1 w.2
  push_cast
  rw [norm_mul, norm_pow, norm_natp]
  exact mul_le_of_le_one_left (by positivity) hw

end GlobalTheory.FlatModel.HTCong

namespace GlobalTheory.FlatModel.HTCong

theorem pair_comb_congr : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p) (n N g : ℕ) {J : Type}
    (ta : Fin N → P.T) (x : Fin g → LieG P.Gt) (h : Fin N → Fin g → 𝓞_ℂ_[p]) (Tc : J → Fin N → 𝓞_ℂ_[p])
    (U : Fin g → 𝓞_ℂ_[p]), (∀ m b, h m b - (P.al₀ (ta m)).1 (x b) ∈ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}) → ∀ i : J,
    ‖(((∑ b, (∑ a, Tc i a * h a b) * U b : 𝓞_ℂ_[p]) : ℂ_[p]) -
      P.pairV (∑ b, (U b : ℂ_[p]) • P.bLie (x b)) (∑ m, (Tc i m : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m))‖ ≤ (p : ℝ)⁻¹ ^ n := by
  intro E _ _ p _ _ P n N g J ta x h Tc U hh i
  have key : P.pairV (∑ b, (U b : ℂ_[p]) • P.bLie (x b)) (∑ m, (Tc i m : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m) =
      ((∑ b, (∑ a, Tc i a * (P.al₀ (ta a)).1 (x b)) * U b : 𝓞_ℂ_[p]) : ℂ_[p]) := by
    have e1 : ∀ m, (Tc i m : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m = (Tc i m : ℂ_[p]) • ((1 : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m) := by
      intro m; rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    simp only [e1, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, P.pairV_bLie, smul_eq_mul]
    push_cast
    simp only [Finset.sum_mul, Finset.mul_sum]
    have ha : ∀ z : 𝓞_ℂ_[p], algebraMap 𝓞_ℂ_[p] ℂ_[p] z = (z : ℂ_[p]) := fun _ => rfl
    simp only [ha]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [key, ← AddSubgroupClass.coe_sub]
  refine norm_le_of_mem_span p n _ ?_
  have e2 : (∑ b, (∑ a, Tc i a * h a b) * U b) - (∑ b, (∑ a, Tc i a * (P.al₀ (ta a)).1 (x b)) * U b) =
      ∑ b, ∑ a, (Tc i a * U b) * (h a b - (P.al₀ (ta a)).1 (x b)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← sub_mul, ← Finset.sum_sub_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [e2]
  exact Ideal.sum_mem _ fun b _ => Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (hh a b)

end GlobalTheory.FlatModel.HTCong
