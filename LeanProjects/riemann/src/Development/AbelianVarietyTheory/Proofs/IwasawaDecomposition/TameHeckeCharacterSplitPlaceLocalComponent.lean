import Mathlib
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionRealSubfieldRingEquiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoTame
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuCharacterDetLevelEqLocalTameProduct
open NumberField IsDedekindDomain Formalism.L2

noncomputable section

namespace GlobalTheory.HeckeSplitComp

open ReciprocityTheory.Aut

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-(1 : ℕ) : ℤ) := by
  by_cases hx : x = 0
  · rw [hx]; exact zero_le'
  rw [← WithZero.exp_log hx] at h ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
  rw [WithZero.exp_le_exp]; push_cast; omega

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L) (χ : Formalism.L2.Host.HChar L), χ.TameAt s.w → ∃ ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ, NG.IsCompAt χ s ξ ∧ ∀ (u : (s.v.adicCompletion (maximalRealSubfield L))ˣ) (a : 𝓞 L) (k : Lˣ), (k : L) = (a : L) → Valued.v (u : s.v.adicCompletion (maximalRealSubfield L)) = 1 → Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - s.i (a : L)) < 1 → ξ u = χ.locK s.w k := by
  intro L _ _ _ s χ hχ
  obtain ⟨c, hc, -, hci⟩ := GlobalTheory.SplitCompl.exists_ringEquiv L s
  have hlt : ∀ y, Valued.v (c y) < 1 ↔ Valued.v y < 1 := GlobalTheory.TypeBlockFix.v_map_lt_one_iff s.v s.w c hc
  have hle : ∀ y, Valued.v (c y) ≤ 1 ↔ Valued.v y ≤ 1 := GlobalTheory.TypeBlockFix.v_map_le_one_iff s.v s.w c hc
  have heq1 : ∀ y, Valued.v y = 1 → Valued.v (c y) = 1 := by
    intro y hy
    refine le_antisymm ((hle y).2 hy.le) (not_lt.1 fun h => ?_)
    have := (hlt y).1 h
    rw [hy] at this
    exact lt_irrefl _ this
  refine ⟨(χ.loc s.w).comp (Units.map c.toRingHom.toMonoidHom), ⟨⟨1, fun u hu => ?_⟩, fun k => ?_⟩, ?_⟩
  · have hu1 : Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) < 1 :=
      lt_of_le_of_lt hu (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
    have hv : Valued.v (u : s.v.adicCompletion (maximalRealSubfield L)) = 1 := by
      have := Valuation.map_eq_of_sub_lt Valued.v (x := 1)
        (y := (u : s.v.adicCompletion (maximalRealSubfield L))) (by rw [map_one]; exact hu1)
      rwa [map_one] at this
    show χ.loc s.w (Units.map c.toRingHom.toMonoidHom u) = 1
    refine hχ _ (heq1 _ hv) ?_
    have e : ((Units.map c.toRingHom.toMonoidHom u : (s.w.adicCompletion L)ˣ) : s.w.adicCompletion L) - 1 =
        c ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) := by
      rw [map_sub, map_one]; rfl
    rw [e]
    exact le_exp_neg_one_of_lt_one ((hlt _).2 hu1)
  · show χ.loc s.w (Units.map c.toRingHom.toMonoidHom (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k)) =
      χ.loc s.w (Formalism.L2.Host.atFin s.w k)
    congr 1
    ext
    simp [Formalism.L2.Host.atFin, hci]
  · intro u a k hka hu hua
    show χ.loc s.w (Units.map c.toRingHom.toMonoidHom u) = χ.locK s.w k
    have hia : Valued.v (s.i (a : L)) = 1 := by
      have := Valuation.map_eq_of_sub_lt Valued.v (x := (u : s.v.adicCompletion (maximalRealSubfield L)))
        (y := s.i (a : L)) (by rw [Valuation.map_sub_swap, hu]; exact hua)
      rw [this, hu]
    have hk : s.w.valuation L (k : L) = 1 := by
      have h1 := heq1 _ hia
      rw [hci, ← hka] at h1
      rwa [Formalism.UG.P.levelaf_valued_algebraMap] at h1
    refine GlobalTheory.LevMuDet.loc_eq_locK hχ hk ?_
    have e : ((Units.map c.toRingHom.toMonoidHom u : (s.w.adicCompletion L)ˣ) : s.w.adicCompletion L) -
        algebraMap L _ (k : L) = c ((u : s.v.adicCompletion (maximalRealSubfield L)) - s.i (a : L)) := by
      rw [map_sub, hci, hka]; rfl
    rw [e]
    exact (hlt _).2 hua

end GlobalTheory.HeckeSplitComp
