import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Target
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameL

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
  PositivityTheory.Rg.BcB.F.Choice PositivityTheory.Rg.BcB.F
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.Choice

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def ShufEx : Prop := ∀ (n a : ℕ) (s : Finset (Fin (n / 2))), LocData.admitted n a s →
  Disjoint (symIdx n (a % 2 = 1) s) (symIdx n ((n - a) % 2 = 1) sᶜ) ∧
    symIdx n (a % 2 = 1) s ∪ symIdx n ((n - a) % 2 = 1) sᶜ = Finset.univ

def shufOf (w : Pl E) (n a : ℕ) (s : Finset (Fin (n / 2))) (h : LocData.admitted n a s)
    (e : Fin a ⊕ Fin (n - a) ≃ Fin n)
    (he : (∀ i, e (.inl i) = (symIdx n (a % 2 = 1) s).orderEmbOfFin h.2.1 i) ∧
      ∀ j, e (.inr j) = (symIdx n ((n - a) % 2 = 1) sᶜ).orderEmbOfFin h.2.2 j)
    (sgA sgB : ℂˣ) : Shuf n where
  a := a
  b := n - a
  e := e
  monoL := by intro i j hij; simp only [he.1]; exact ((symIdx n (a % 2 = 1) s).orderEmbOfFin h.2.1).strictMono hij
  monoR := by intro i j hij; simp only [he.2]; exact ((symIdx n ((n - a) % 2 = 1) sᶜ).orderEmbOfFin h.2.2).strictMono hij
  eps := fun k => Sum.elim (fun _ => sgA) (fun _ => sgB) (e.symm k) *
    qU w (rh n k - Sum.elim (fun i : Fin a => rh a i) (fun j : Fin (n - a) => rh (n - a) j) (e.symm k))

def VResStd : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n a : ℕ) (s : Finset (Fin (n / 2)))
  (h : LocData.admitted n a s) (e : Fin a ⊕ Fin (n - a) ≃ Fin n)
  (he : (∀ i, e (.inl i) = (symIdx n (a % 2 = 1) s).orderEmbOfFin h.2.1 i) ∧
      ∀ j, e (.inr j) = (symIdx n ((n - a) % 2 = 1) sᶜ).orderEmbOfFin h.2.2 j) (x : Fin n → ℤ), x ∈ coneGL n 2 →
  (-qh w) ^ (-vRes n a (lOf x) s) =
      ((∏ k, (shufOf w n a s h e he ((-1) ^ (n - a)) ((-1) ^ a)).eps k ^ x k : ℂˣ) : ℂ) ∧
    restr x _ h.2.1 = resL (shufOf w n a s h e he ((-1) ^ (n - a)) ((-1) ^ a)) x ∧
    restr x _ h.2.2 = resR (shufOf w n a s h e he ((-1) ^ (n - a)) ((-1) ^ a)) x

def ShufStd : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n a : ℕ) (s : Finset (Fin (n / 2)))
  (h : LocData.admitted n a s) (e : Fin a ⊕ Fin (n - a) ≃ Fin n) he,
  IsStd w (shufOf w n a s h e he ((-1) ^ (n - a)) ((-1) ^ a))
    (fun k => Sum.elim (fun _ => ((-1) ^ (n - a) : ℂˣ)) (fun _ => (-1) ^ a) (e.symm k))

def ConeTwo : Prop := ∀ (n : ℕ) (x : Fin n → ℤ), 2 ≤ n → x ∈ coneGL n 2 → Cone (lOf x)

end PositivityTheory.Rg.BcB.F.Choice

end
