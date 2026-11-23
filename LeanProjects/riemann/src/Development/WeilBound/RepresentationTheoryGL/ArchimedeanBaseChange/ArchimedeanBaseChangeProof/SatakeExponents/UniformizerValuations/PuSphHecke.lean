import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ExistsEigv

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.U

open PositivityTheory.Rg.BcB.F.Eig

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

section Word

variable {S : Set (Pl E)} {lam : InfinitePlace E → DomWeight n} {K' : ∀ w : Pl E, Subgroup (UL n w)}
  {F : UFam S lam K'} {B : Finset (Pl E)}

theorem pu_sph_inl (c : ℂ) (l : List (UGen E n)) (w : Pl E) : UGen.sph (Sum.inl c :: l) w = UGen.sph l w := rfl

theorem pu_sph_inr (w0 : Pl E) (h : UL n w0 → ℂ) (l : List (UGen E n)) (w : Pl E) :
    UGen.sph (Sum.inr ⟨w0, h⟩ :: l) w = if hw : w0 = w then lconv (hw ▸ h) (UGen.sph l w) else UGen.sph l w := rfl

theorem pu_sph_self (w0 : Pl E) (h : UL n w0 → ℂ) (l : List (UGen E n)) :
    UGen.sph (Sum.inr ⟨w0, h⟩ :: l) w0 = lconv h (UGen.sph l w0) := by
  rw [pu_sph_inr, dif_pos rfl]

theorem pu_sph_ne (w0 : Pl E) (h : UL n w0 → ℂ) (l : List (UGen E n)) (w : Pl E) (hw : w0 ≠ w) :
    UGen.sph (Sum.inr ⟨w0, h⟩ :: l) w = UGen.sph l w := by
  rw [pu_sph_inr, dif_neg hw]

def pu_pls (l : List (UGen E n)) : Finset (Pl E) :=
  (l.filterMap fun x => Sum.elim (fun _ => none) (fun y : Σ w : Pl E, UL n w → ℂ => some y.1) x).toFinset

end Word

section Word2

variable {S : Set (Pl E)} {lam : InfinitePlace E → DomWeight n} {K' : ∀ w : Pl E, Subgroup (UL n w)}
  {F : UFam S lam K'} {B : Finset (Pl E)}

end Word2

end PositivityTheory.Rg.BcB.F.U

end
