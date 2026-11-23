import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FmTools
open scoped Classical

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS
open PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.F.Tail
open PositivityTheory.Rg.BcB.F (LF)

namespace GlobalTheory.CompanionTheory.TailLocPow

theorem hint_fun_zero {H : Type} [Group H] (K : Subgroup H) : hint K (fun _ : H => (0 : ℂ)) = 0 := by
  simp [hint]

theorem rStab_smul {H : Type} [Group H] (c : ℂ) (hc : c ≠ 0) (u : H → ℂ) :
    rStab (fun x => c * u x) = rStab u := by
  ext k
  show (∀ x, c * u (x * k) = c * u x) ↔ (∀ x, u (x * k) = u x)
  exact forall_congr' fun x => mul_right_inj' hc

theorem hint_smul {H : Type} [Group H] (K : Subgroup H) (c : ℂ) (u : H → ℂ) :
    hint K (fun x => c * u x) = c * hint K u := by
  by_cases hc : c = 0
  · subst hc
    simpa using hint_fun_zero K
  · have key : ∀ S : Subgroup H, S = rStab u →
        (((S ⊓ K).relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : H ⧸ (S ⊓ K), c * u q.out =
          c * ((((rStab u ⊓ K).relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : H ⧸ (rStab u ⊓ K), u q.out) := by
      rintro S rfl
      have h : (∑ᶠ q : H ⧸ (rStab u ⊓ K), c * u q.out) = c * ∑ᶠ q : H ⧸ (rStab u ⊓ K), u q.out := by
        simpa only [smul_eq_mul] using (smul_finsum c (fun q : H ⧸ (rStab u ⊓ K) => u q.out)).symm
      rw [h]
      ring
    exact key _ (rStab_smul c hc u)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

variable {k : Type} [Fintype k]

end GlobalTheory.CompanionTheory.TailLocPow

end
