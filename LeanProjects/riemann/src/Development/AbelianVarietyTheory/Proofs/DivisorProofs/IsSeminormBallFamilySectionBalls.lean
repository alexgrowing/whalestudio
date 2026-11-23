import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VolBr.BallFam

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {y : CxPts p σ} {f g : X.functionField}

theorem ratVal_sub (hf : RegAt (under y) f) (hg : RegAt (under y) g) :
    ratVal (f - g) y = ratVal f y - ratVal g y := by
  obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
  obtain ⟨W, hW, b, rfl⟩ := hg.exists_fnOf
  have hy : y ∈ ptsIn p σ (U ⊓ W) := mem_ptsIn.2 ⟨hU, hW⟩
  rw [← fnOf_resG (inf_le_left : U ⊓ W ≤ U) (gen_mem (memInf hU hW)),
    ← fnOf_resG (inf_le_right : U ⊓ W ≤ W) (gen_mem (memInf hU hW)), ← map_sub,
    ratVal_fnOf hy, ratVal_fnOf hy, ratVal_fnOf hy, ev_eq hy, ev_eq hy, ev_eq hy, map_sub]

theorem ratVal_zero : ratVal (0 : X.functionField) y = 0 := by
  have h0 : RegAt (under y) (0 : X.functionField) := ⟨0, map_zero _⟩
  simpa using ratVal_sub h0 h0

theorem ratVal_nsmul (hf : RegAt (under y) f) (n : ℕ) : ratVal (n • f) y = n • ratVal f y := by
  obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
  have hy : y ∈ ptsIn p σ U := mem_ptsIn.2 hU
  rw [← map_nsmul, ratVal_fnOf hy, ratVal_fnOf hy, ev_eq hy, ev_eq hy, map_nsmul]

namespace Pair

variable (P : Pair p) (a b : ℤ)

theorem regAt_loc {f : X.functionField} (hf : f ∈ P.H a b) (σ : k →+* ℂ) (y : CxPts p σ) :
    RegAt (under y) (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) :=
  hf _ _ _ (mem_ptsIn.1 (mem_pick _ y)) (mem_ptsIn.1 (mem_pick _ y))

theorem loc_sub (f g : X.functionField) (i j) : P.loc a b (f - g) i j = P.loc a b f i j - P.loc a b g i j := by
  simp only [VolBr.Pair.loc]; ring

theorem loc_nsmul (n : ℕ) (f : X.functionField) (i j) : P.loc a b (n • f) i j = n • P.loc a b f i j := by
  simp only [VolBr.Pair.loc, nsmul_eq_mul]; ring

theorem nu_zero (σ : k →+* ℂ) (y : CxPts p σ) : P.nu a b σ y 0 = 0 := by
  simp only [VolBr.Pair.nu, VolBr.Pair.loc, zero_mul, ratVal_zero, norm_zero]

theorem nu_sub {f g : X.functionField} (hf : f ∈ P.H a b) (hg : g ∈ P.H a b) (σ : k →+* ℂ) (y : CxPts p σ) :
    P.nu a b σ (y) (f - g) ≤ P.nu a b σ y f + P.nu a b σ y g := by
  simp only [VolBr.Pair.nu]
  rw [loc_sub, ratVal_sub (regAt_loc P a b hf σ y) (regAt_loc P a b hg σ y), ← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (Real.exp_pos _).le

theorem nu_nsmul {f : X.functionField} (hf : f ∈ P.H a b) (n : ℕ) (σ : k →+* ℂ) (y : CxPts p σ) :
    P.nu a b σ y (n • f) = n * P.nu a b σ y f := by
  simp only [VolBr.Pair.nu]
  rw [loc_nsmul, ratVal_nsmul (regAt_loc P a b hf σ y), nsmul_eq_mul, norm_mul, Complex.norm_natCast, mul_assoc]

end Pair

end GlobalTheory.VolBr.BallFam

open GlobalTheory.VolBr.BallFam in

theorem GlobalTheory.VolBr.Pair.isBallFam : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ a b : ℤ, IsBallFam (P.H a b) (P.Bl a b) := by
  intro k _ X _ p P a b
  exact {
    subset := fun r f hf => hf.1
    zero_mem := fun r hr => ⟨zero_mem _, fun σ y => by rw [Pair.nu_zero]; exact hr⟩
    sub_mem := fun r r' f g hf hg => ⟨sub_mem hf.1 hg.1, fun σ y =>
      (Pair.nu_sub P a b hf.1 hg.1 σ y).trans (add_le_add (hf.2 σ y) (hg.2 σ y))⟩
    nsmul_iff := fun n r f hn hf => by
      have h0 : (0 : ℝ) < n := by exact_mod_cast hn
      simp only [VolBr.Pair.Bl, Set.mem_setOf_eq, Pair.nu_nsmul P a b hf, mul_le_mul_iff_right₀ h0,
        and_iff_right (nsmul_mem hf n), and_iff_right hf] }
