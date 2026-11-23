import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpMapResMap
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.FlagGen

set_option autoImplicit false

namespace GlobalTheory.FlagGen

def lowEquivSigma (m : ℕ) : Low m ≃ Σ j : Fin m, Fin (j : ℕ) where
  toFun q := ⟨q.1.2, ⟨q.1.1, q.2⟩⟩
  invFun s := ⟨(⟨s.2, s.2.2.trans s.1.2⟩, s.1), s.2.2⟩
  left_inv q := by rcases q with ⟨⟨i, j⟩, h⟩; rfl
  right_inv s := by rcases s with ⟨j, i⟩; rfl

theorem card_low (m : ℕ) : Fintype.card (Low m) = m.choose 2 := by
  rw [Fintype.card_congr (lowEquivSigma m), Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun j => j) m, Finset.sum_range_id, Nat.choose_two_right]

end GlobalTheory.FlagGen
