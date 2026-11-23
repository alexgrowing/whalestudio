import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomJet

set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts

theorem exists_jet_factor {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F) {k : K.K} {T : K.Obj} (f₁ f₂ : K.triv k ⟶ T) (n : Fin g → T.C) (hd : f₁.deg = f₂.deg)
    (hJ : ∀ a, n a ∈ T.J) (hn : ∀ a b, n a * n b = 0)
    (hf : ∀ x : Hol (K.W k), f₂.φ x = f₁.φ x + ∑ a, f₁.φ (dw a x : Hol (K.W k)) * n a) :
    ∃ χ : K.jet k ⟶ T, χ.deg = f₁.deg ∧ jet0 k ≫ χ = f₁ ∧ jet1 k ≫ χ = f₂ ∧
      ∀ x : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)),
        χ.φ x = f₁.φ (x.fst : Hol (K.W k)) + ∑ a, f₁.φ (x.snd a : Hol (K.W k)) * n a := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet
  | exact @_root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet
  | exact _root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet
  | (apply _root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet <;> assumption)
  | (intros; apply _root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet ..)

end GlobalTheory.AnPer.Charts
