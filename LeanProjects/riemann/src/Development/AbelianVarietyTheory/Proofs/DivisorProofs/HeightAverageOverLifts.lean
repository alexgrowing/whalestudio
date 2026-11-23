import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinsumSubConst

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.Mean4O

theorem mean_listed_eq : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (e : ℕ) (M : Man e) (I : ManIs M Y) (x : Y.X)
    (d : ℕ) (z : ∀ a, Fin (d + 1) → M.X a) (g : ∀ σ, Pts Y σ → ℝ), IsClosed ({x} : Set Y.X) → I.Lists x z →
    M.κ * ∑ a, (∑ i, g (I.ε a) (I.pt a (z a i))) / ((d : ℝ) + 1) =
      (∑ σ : F →+* ℂ, ∑ᶠ (w : Pts Y σ) (_ : under w = x), g σ w) /
        ((Module.finrank ℚ F : ℝ) * (Nat.card {y : AlgPt Y // below y.1 = x} : ℝ)) := by
  intro F _ _ Y e M I x d z g hx hL
  obtain ⟨N, hN, hc⟩ := HtTwist.exists_card Y.str x hx
  have hA : Nat.card {y : AlgPt Y // below y.1 = x} = N := hc _ _
  have hmem (a) (i : Fin (d + 1)) : under (I.pt a (z a i)) = x := by
    have : z a i ∈ Set.range (z a) := ⟨i, rfl⟩
    rw [(hL a).2] at this
    exact this
  let P (a) : Fin (d + 1) → {w : Pts Y (I.ε a) // under w = x} := fun i => ⟨I.pt a (z a i), hmem a i⟩
  have hP (a) : Function.Bijective (P a) := by
    constructor
    · intro i j hij
      exact (hL a).1 ((I.pt a).injective (congrArg Subtype.val hij))
    · rintro ⟨w, hw⟩
      have : (I.pt a).symm w ∈ {u | under (I.pt a u) = x} := by simpa using hw
      rw [← (hL a).2] at this
      obtain ⟨i, hi⟩ := this
      exact ⟨i, Subtype.ext (by simp [P, hi])⟩
  have hd : N = d + 1 := by
    have h1 : Nat.card {w : Pts Y (I.ε 0) // under w = x} = N := hc ℂ (I.ε 0)
    rw [← h1, ← Nat.card_congr (Equiv.ofBijective _ (hP 0)), Nat.card_eq_fintype_card, Fintype.card_fin]
  have hs (a) : ∑ᶠ (w : Pts Y (I.ε a)) (_ : under w = x), g (I.ε a) w = ∑ i, g (I.ε a) (I.pt a (z a i)) := by
    rw [← finsum_subtype_eq_finsum_cond, ← finsum_eq_sum_of_fintype]
    exact (finsum_eq_of_bijective (P a) (hP a) fun i => rfl).symm
  have hF : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hd' : (d : ℝ) + 1 ≠ 0 := by positivity
  rw [I.κ_eq, hA, hd, ← Equiv.sum_comp I.ε, Finset.sum_congr rfl fun a _ => hs a, ← Finset.sum_div]
  push_cast
  field_simp

end GlobalTheory.Mean4O
