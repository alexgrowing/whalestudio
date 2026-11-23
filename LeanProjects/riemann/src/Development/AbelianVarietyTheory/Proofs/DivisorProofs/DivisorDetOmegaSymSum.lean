import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
open NumberField Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Cartier CategoryTheory AlgebraicGeometry

namespace GlobalTheory.DetOm

open Classical in

theorem expo_detOmSym {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (g : ℕ) (a : ℕ → Bool) :
    expo Dw (detOmSym E g) = ∑ k : Fin g, (-1 : ℤ) • expo Dw (Finsupp.single (a, none, Sum.inr (k : ℕ)) 1) := by
  funext x
  have h1 : expo Dw (detOmSym E g) x =
      ∑ k : Fin g, expo Dw (wholeSym (fun _ => false) none (.inr k : Fin g ⊕ Fin g)) x := by
    unfold detOmSym expo
    rw [Finsupp.sum_finset_sum_index (fun _ => by simp) (fun _ _ _ => by split_ifs <;> simp)]
  rw [h1, Finset.sum_apply]
  simp only [wholeSym, expo_single, Pi.smul_apply, smul_eq_mul]
  rw [← Equiv.sum_comp (Fin.revPerm (n := g))]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev]
  split_ifs <;> simp

theorem div_adl_detOmegaSym (D : D7) (O : Setup D) (c : O.s.Comp) : (O.adl0 c (detOmSym D.host.E (D.R.f * O.N))).D = ∑ k : Fin (D.R.f * O.N), (-1 : ℤ) • (O.adl0 c (Finsupp.single (ArIn.ind ∅, none, Sum.inr (k : ℕ)) 1)).D := by
  simp only [Setup.adl0, adlOf]
  rw [expo_detOmSym _ _ (ArIn.ind ∅)]
  unfold divOf
  simp only [Finset.sum_apply, Pi.smul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm
end GlobalTheory.DetOm
