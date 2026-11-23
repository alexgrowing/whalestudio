import Formalism.LocalToGlobal.GroupLattices.PerfectRings.IntermediateMapWittQuadratic

noncomputable section

namespace Formalism.L2.G

open Formalism.MainNotions.FormalGroupSystem

variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [NormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  (f : K0 p →+* C)

def iC : Kc p →+* C :=
  letI : Algebra (K0 p) C := f.toAlgebra
  (IsAlgClosed.lift : Kc p →ₐ[K0 p] C).toRingHom

theorem iC_alg (y : K0 p) : iC f (algebraMap (K0 p) (Kc p) y) = f y := by
  let : Algebra (K0 p) C := f.toAlgebra
  exact (IsAlgClosed.lift : Kc p →ₐ[K0 p] C).commutes y

variable (hf : ∀ x : WW p, ‖f (algebraMap (WW p) (K0 p) x)‖ ≤ 1)

include hf

theorem iC_le {x : Kc p} (hx : x ∈ Oc p) : ‖iC f x‖ ≤ 1 := by
  let v : Valuation C NNReal := NormedField.valuation
  let φ : WW p →+* v.integer := (f.comp (algebraMap (WW p) (K0 p))).codRestrict v.integer (fun x => by
    show ‖f (algebraMap (WW p) (K0 p) x)‖₊ ≤ 1
    exact_mod_cast hf x)
  have h1 : IsIntegral v.integer (iC f x) :=
    ((mem_Oc p x).1 hx).map_of_comp_eq φ (iC f) (by
      ext z
      show f (algebraMap (WW p) (K0 p) z) = iC f (algebraMap (WW p) (Kc p) z)
      rw [IsScalarTower.algebraMap_apply (WW p) (K0 p) (Kc p), iC_alg])
  have h2 : v (iC f x) ≤ 1 := (Valuation.integer.integers v).isIntegral_iff_v_le_one.1 h1
  exact_mod_cast h2

theorem iC_int (hp1 : ‖(p : C)‖ < 1) (x : Kc p) : x ∈ Oc p ↔ ‖iC f x‖ ≤ 1 := by
  refine ⟨iC_le f hf, fun hx => ?_⟩
  by_contra hnot
  obtain ⟨e, d, hd, he⟩ := exists_pow_of_notMem_Oc hnot
  have h1 := congrArg (fun z => ‖iC f z‖) he
  simp only [map_pow, map_inv₀, map_mul, map_natCast, norm_pow, norm_inv, norm_mul] at h1
  have h2 : ‖(p : C)‖ * ‖iC f d‖ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (iC_le f hf hd)) hp1
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hnot (Oc p).zero_mem
  have hpos : 0 < ‖iC f x‖ := norm_pos_iff.2 ((map_ne_zero _).2 hx0)
  have h3 : 1 ≤ (‖iC f x‖⁻¹) ^ e := one_le_pow₀ ((one_le_inv₀ hpos).2 hx)
  rw [h1] at h3
  exact absurd h2 (not_lt.2 h3)

omit hf

end Formalism.L2.G

namespace Formalism.L2.G

open Formalism.MainNotions.FormalGroupSystem

variable {p : ℕ} [hp : Fact p.Prime]

theorem norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  have h := PadicComplex.norm_extends' p (p : ℚ_[p])
  have h2 : ‖(p : ℂ_[p])‖ = ‖(p : ℚ_[p])‖ := by
    rw [← h]
    congr 1
    simp
  rw [h2]
  exact Padic.norm_p_lt_one

theorem iC_int_Cp (f : K0 p →+* ℂ_[p]) (hf : ∀ x : WW p, ‖f (algebraMap (WW p) (K0 p) x)‖ ≤ 1) (x : Kc p) :
    x ∈ Oc p ↔ ‖iC f x‖ ≤ 1 :=
  iC_int f hf norm_p_lt_one x

end Formalism.L2.G
