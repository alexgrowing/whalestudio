import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalRootReZeroImSq

open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureType

namespace GlobalTheory.CompRat

theorem exists_isSplit_of_splitLat (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (g : ℕ) (ty : Fin g → (E →+* ℂ)) (hty : IsTypeFn H D.p D.q ty) (hD : SplitLat D) :
    ∃ (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P), IsSplit hP := by
  obtain ⟨Lp, Lm, hs, ho, -, -, hp, hm⟩ := hD
  have two : ∀ m, (D.EF (H.rt • m) m : ℝ) = 2 * D.EF (H.w0 • m) m := fun m => by
    have : D.EF ((2 * H.w0) • m) m = D.EF ((1 + H.rt) • m) m := by rw [H.two_weight_eq_one_add_root]
    rw [two_mul, add_smul, add_smul, one_smul, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
      D.alt] at this
    have h : D.EF (H.rt • m) m = 2 * D.EF (H.w0 • m) m := by linarith
    exact_mod_cast h
  obtain ⟨P, hP, k₁, k₂⟩ := GlobalTheory.CM.FamCompare.exists_period D Lp Lm
    (fun z => ⟨1, one_pos, hs ▸ Submodule.mem_top⟩) ho
    (fun x hx => by
      by_cases h : x = 0
      · simp [h]
      · have := hp x hx h
        rw [two] at this
        linarith)
    (fun x hx => by
      by_cases h : x = 0
      · simp [h]
      · have := hm x hx h
        rw [two] at this
        linarith) hty
  exact ⟨P, hP, top_le_iff.1 (hs ▸ sup_le_sup k₁ k₂)⟩

end GlobalTheory.CompRat
