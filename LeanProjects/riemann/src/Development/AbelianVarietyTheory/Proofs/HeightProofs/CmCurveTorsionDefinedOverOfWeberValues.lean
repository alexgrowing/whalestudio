import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmHostRootComplexEqPmSqrt

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin.CurveField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_periodPair (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    ∃ L : PeriodPair, ∀ x, x ∈ L.lattice ↔ ∃ s, x = wC H s := by
  have hd : 7 ≤ H.d := by have := H.d_mod; omega
  have hs : √(H.d : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < H.d))).ne'
  refine ⟨⟨1, (1 + Complex.I * Real.sqrt H.d) / 2, LinearIndependent.pair_iff.2 fun a b h => ?_⟩, fun x => ?_⟩
  · have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp [hs] at h1 h2
    simp [h2] at h1
    exact ⟨h1, h2⟩
  · rw [GlobalTheory.CompRat.Weber.exists_wC_iff, PeriodPair.mem_lattice]
    simp only [_root_.mul_one]
    exact ⟨fun ⟨m, n, e⟩ => ⟨m, n, e.symm⟩, fun ⟨m, n, e⟩ => ⟨m, n, e.symm⟩⟩

theorem actsBy_of_dvd {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (C : Curve H) (τ : ℂ ≃+* ℂ) (ι : _) {n m : ℕ}
    (hn : 0 < n) (hm : m ∣ n) (s : ℤ × ℤ) (h : C.ActsBy τ ι n s) : C.ActsBy τ ι m s := by
  obtain ⟨k, rfl⟩ := hm
  have hk : (k : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mul_pos_left hn).ne'
  have e : ∀ a : ℤ × ℤ, wC H (k * a.1, k * a.2) = k * wC H a := fun a => by
    simp only [wC]; push_cast; ring
  refine ⟨h.1, fun a => ?_⟩
  have h2 := h.2 (k * a.1, k * a.2)
  rw [e, Nat.cast_mul, mul_left_comm, mul_comm (m : ℂ), mul_div_mul_left _ _ hk, mul_div_mul_left _ _ hk] at h2
  exact h2

theorem curveOver_of_weberIn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (F : IntermediateField ℚ ℂ) (n : ℕ), 0 < n → (H.rt0 ∈ F → WeberIn H F n → CurveOver H F n) ∧ ∀ m, m ∣ n → CurveOver H F n → CurveOver H F m := by
  intro E _ _ _ H F n hn
  refine ⟨fun h0 hW τ hτ => ?_, fun m hm h τ hτ => ?_⟩
  · obtain ⟨L, hL⟩ := exists_periodPair H
    exact GlobalTheory.CompRat.Weber.fixesCurve_of_weber E H L n hn hL τ (hτ _ h0) (hτ _ (hW L hL).1)
      fun s hs => hτ _ ((hW L hL).2 s hs)
  · obtain ⟨C, ι, h'⟩ := h τ hτ
    exact ⟨C, ι, actsBy_of_dvd C τ ι hn hm _ h'⟩

end GlobalTheory.FinalJoin.CurveField
