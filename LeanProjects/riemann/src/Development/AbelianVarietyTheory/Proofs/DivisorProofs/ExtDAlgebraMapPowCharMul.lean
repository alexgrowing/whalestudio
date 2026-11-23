import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift

open GlobalTheory GlobalTheory.DI

set_option autoImplicit false

namespace GlobalTheory.DI

section

variable {K : Type} [CommRing K]

theorem kaehlerZ_span_induction {P : Ω[K⁄ℤ] → Prop} (v : Ω[K⁄ℤ]) (hD : ∀ a, P (KaehlerDifferential.D ℤ K a))
    (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y)) (hsmul : ∀ (c : K) x, P x → P (c • x)) : P v := by
  have hv : v ∈ Submodule.span K (Set.range (KaehlerDifferential.D ℤ K)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact hD a
  | zero => exact h0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul c x _ hx => exact hsmul c x hx

variable (p : ℕ) [Fact p.Prime] [CharP K p]

theorem kaehlerZ_D_pow_char (c : K) : KaehlerDifferential.D ℤ K (c ^ p) = 0 := by
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]

theorem extD_algebraMap_pow_char_mul {d : ExteriorAlgebra K Ω[K⁄ℤ] →+ ExteriorAlgebra K Ω[K⁄ℤ]} (hd : IsExtD ℤ K d)
    (c : K) (x : ExteriorAlgebra K Ω[K⁄ℤ]) :
    d (algebraMap K _ (c ^ p) * x) = algebraMap K _ (c ^ p) * d x := by
  rw [hd.mul, hd.alg, kaehlerZ_D_pow_char p, map_zero, zero_mul, zero_add]
  congr 1
  exact AlgHom.commutes _ _

end

end GlobalTheory.DI

namespace GlobalTheory.DI

theorem isDatum_of_frobenius_lifts {K Kt : Type} [CommRing K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p]
    (π : Kt →+* K) {ι : Type} (F : ι → Kt →+* Kt) (d : ExteriorAlgebra K Ω[K⁄ℤ] →+ ExteriorAlgebra K Ω[K⁄ℤ])
    (f : ι → Ω[K⁄ℤ] →+ Ω[K⁄ℤ]) (h : ι → ι → Ω[K⁄ℤ] →+ K) (hπ : IsFlatLift p π)
    (hF : ∀ i, IsFrob p π (F i)) (hd : IsExtD ℤ K d) (hf : ∀ i, IsF p π (F i) (f i))
    (hh : ∀ i j, IsH p π (F i) (F j) (h i j)) : IsDatum p d f h := by

  have hw : ∀ i z, ∃ w, F i z = z ^ p + p * w := by
    intro i z
    obtain ⟨w, hw⟩ := (hπ.ker (F i z - z ^ p)).1 (by rw [map_sub, hF i, map_pow, sub_self])
    exact ⟨w, by rw [← hw]; ring⟩
  have hsm : ∀ (c : K) (x : ExteriorAlgebra K Ω[K⁄ℤ]), d (c ^ p • x) = c ^ p • d x := by
    intro c x
    rw [Algebra.smul_def, Algebra.smul_def, extD_algebraMap_pow_char_mul p hd]

  have hfD : ∀ i z w, F i z = z ^ p + p * w → ExteriorAlgebra.ι K (f i (KaehlerDifferential.D ℤ K (π z))) =
      algebraMap K _ (π z ^ (p - 1)) * ExteriorAlgebra.ι K (KaehlerDifferential.D ℤ K (π z)) +
        d (algebraMap K _ (π w)) := by
    intro i z w hz
    rw [(hf i).2 z w hz, map_add, map_smul, Algebra.smul_def, hd.alg]
  refine ⟨fun i c v => (hf i).1 c v, fun i j c v => (hh i j).1 c v, ?_, ?_, ?_⟩
  · intro i v
    induction v using kaehlerZ_span_induction with
    | hD a =>
      obtain ⟨z, rfl⟩ := hπ.surj a
      obtain ⟨w, hz⟩ := hw i z
      have h2 : d (ExteriorAlgebra.ι K (KaehlerDifferential.D ℤ K (π z))) = 0 := by
        rw [← hd.alg, hd.sq]
      rw [hfD i z w hz, map_add, hd.sq, add_zero, hd.mul, h2, mul_zero, add_zero, hd.alg,
        Derivation.leibniz_pow, map_nsmul, map_smul, smul_mul_assoc, smul_mul_assoc,
        ExteriorAlgebra.ι_sq_zero, smul_zero, smul_zero]
    | h0 => simp
    | hadd x y hx hy => rw [map_add, map_add, map_add, hx, hy, add_zero]
    | hsmul c x hx => rw [(hf i).1, map_smul, hsm, hx, smul_zero]
  · intro i j v
    induction v using kaehlerZ_span_induction with
    | hD a =>
      obtain ⟨z, rfl⟩ := hπ.surj a
      obtain ⟨wi, hzi⟩ := hw i z
      obtain ⟨wj, hzj⟩ := hw j z
      rw [(hh i j).2 z (wj - wi) (by rw [hzi, hzj]; ring), hfD i z wi hzi, hfD j z wj hzj, map_sub, map_sub,
        map_sub]
      abel
    | h0 => simp
    | hadd x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add, map_add, map_add, map_add]; abel
    | hsmul c x hx =>
      rw [(hh i j).1, (hf i).1, (hf j).1, map_mul, ← Algebra.smul_def, hsm, hx, map_smul, map_smul, smul_sub]
  · intro i j l v
    induction v using kaehlerZ_span_induction with
    | hD a =>
      obtain ⟨z, rfl⟩ := hπ.surj a
      obtain ⟨wi, hzi⟩ := hw i z
      obtain ⟨wj, hzj⟩ := hw j z
      obtain ⟨wl, hzl⟩ := hw l z
      rw [(hh i j).2 z (wj - wi) (by rw [hzi, hzj]; ring), (hh j l).2 z (wl - wj) (by rw [hzj, hzl]; ring),
        (hh i l).2 z (wl - wi) (by rw [hzi, hzl]; ring), map_sub, map_sub, map_sub]
      ring
    | h0 => simp
    | hadd x y hx hy => rw [map_add, map_add, map_add, ← hx, ← hy]; ring
    | hsmul c x hx => rw [(hh i j).1, (hh j l).1, (hh i l).1, ← hx]; ring

end GlobalTheory.DI
