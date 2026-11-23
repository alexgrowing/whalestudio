import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.GdegPow

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem isometric_comb_unit (L : HermLB p) (n : ℕ) :
    (comb (fun _ : Unit => L) fun _ => (n : ℤ)).Isometric (L.pow n) :=
  HermLB.icls_eq_iff.1 (by rw [icls_comb, HermLB.icls_pow, Fintype.sum_unique, natCast_zsmul])

theorem lin_unit (c : ℝ) : (lin fun _ : Unit => c) = c • (MvPolynomial.X () : MvPolynomial Unit ℝ) := by
  rw [lin, Fintype.sum_unique, MvPolynomial.C_mul']

theorem gdeg_pow : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (L : HermLB p) (n : ℕ), gdeg (L.pow n) D = (n : ℝ) ^ D * gdeg L D := by
  intro hC k _ X _ p D hX L n
  obtain ⟨Ψ, hΨ, -⟩ := ((hC.arExists k X p D hX).2 Unit fun _ => L).2
  have key (m : ℕ) : gdeg (L.pow m) D = (m : ℝ) ^ D * Ψ ((MvPolynomial.X () : MvPolynomial Unit ℝ) ^ D) := by
    rw [← (isometric_comb_unit L m).gdeg_eq, ← hΨ fun _ => (m : ℤ)]
    simp only [Int.cast_natCast]
    rw [lin_unit, smul_pow, map_smul, smul_eq_mul]
  have h1 : gdeg L D = Ψ ((MvPolynomial.X () : MvPolynomial Unit ℝ) ^ D) := by
    rw [← (HermLB.icls_eq_iff.1 (by rw [HermLB.icls_pow, one_smul]) : (L.pow 1).Isometric L).gdeg_eq, key 1]
    simp
  rw [key n, h1]

end GlobalTheory.GdegPow
