import Development.AutomorphicArithmetic.PrimitiveCosets.CoreGm
import Development.AutomorphicArithmetic.PrimitiveCosets.Imports
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.TopWin

noncomputable section

namespace UpperTheory.Comparison₂

open Formalism.HC Formalism.MainNotions Formalism.BasicNotions

def FamCoreConstantBounds {eps : ℝ} (Fm : FamCore eps) (eD eL K cHH eK x : ℝ) : Prop :=
  ∃ i : Fm.Ix x, CoreAtH (Fm.D x i).host.toHostRaw (Fm.D x i).host.TT eD eL K cHH eK eps x

variable {Fam : ℝ → Type 1} {core : ∀ {eps : ℝ}, Fam eps → FamCore eps}
  {Tied : ∀ {eps : ℝ}, Fam eps → (eD eL K cHH eK CL x : ℝ) → Prop}

theorem windowInequality_of_artinInputs
    (h : ∀ {eps : ℝ} (Fm : Fam eps) (eD eL K cHH eK CL x : ℝ), Tied Fm eD eL K cHH eK CL x → FamCoreConstantBounds (core Fm) eD eL K cHH eK x)
    (Λ : Level) : ChebyshevInequalityOnWindows @core @Tied Λ := by
  rintro eD eL eps he Fm ⟨C, xE, hE⟩ ⟨K, cHH, eK, CL, x0, hT⟩
  obtain ⟨x1, hx1⟩ := core_gm Λ eD eL K cHH eK C eps he
  refine ⟨max x1 (max x0 xE), fun x hx hw => ?_⟩
  have b := le_of_max_le_right hx
  obtain ⟨i, hi⟩ := h Fm _ _ _ _ _ _ _ (hT x (le_of_max_le_left b) hw)
  exact hx1 x (le_of_max_le_left hx) _ ((core Fm).D x i).host.toHostAx _ (hE x (le_of_max_le_right b) i) hi

theorem zeroFreeOn_of_core {Q : PChar → Prop}
    (h : ∀ {eps : ℝ} (Fm : Fam eps) (eD eL K cHH eK CL x : ℝ), Tied Fm eD eL K cHH eK CL x → FamCoreConstantBounds (core Fm) eD eL K cHH eK x)
    (hW : ∀ ψ, Q ψ → ∃ (Λ : Level) (la : ℝ), ψ ∈ Λ.KEPT ∧ 1 < la ∧ ChebyshevInequalityAtWindowScale @core @Tied la Λ) : ZeroFreeOn Q :=
  zeroFreeOn_of_tiedWin fun ψ hψ => by
    obtain ⟨Λ, la, a, b, c⟩ := hW ψ hψ
    exact ⟨Λ, la, a, b, windowInequality_of_artinInputs h Λ, formB Λ, c⟩

end UpperTheory.Comparison₂

end
