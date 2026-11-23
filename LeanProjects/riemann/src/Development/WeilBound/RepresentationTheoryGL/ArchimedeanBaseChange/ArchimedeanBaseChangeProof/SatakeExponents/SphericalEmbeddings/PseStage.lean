import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.PseStageC

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
open scoped TensorProduct

namespace PositivityTheory.Rg.BcB.N3.PseStage

open PositivityTheory.Rg.BcB.N3 PositivityTheory.Rg.BcB.N3.Pse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

set_option maxHeartbeats 2000000 in

theorem main {r t : ℕ} (A : Fin r → ℂˣ) (a b : ℂˣ) (B : Fin t → ℂˣ)
    (T : (iP (k := k) ![a, b]).IntertwiningMap (iP (k := k) ![b, a])) (hT : KInj k T) :
    ∃ T' : (iP (k := k) (Fin.append A (Fin.append ![a, b] B))).IntertwiningMap
      (iP (k := k) (Fin.append A (Fin.append ![b, a] B))), KInj k T' := by
  obtain ⟨Ei⟩ := iP_append (k := k) 2 t ![a, b] B
  obtain ⟨Ei'⟩ := iP_append (k := k) 2 t ![b, a] B
  obtain ⟨Eo⟩ := iP_append (k := k) r (2 + t) A (Fin.append ![a, b] B)
  obtain ⟨Eo'⟩ := iP_append (k := k) r (2 + t) A (Fin.append ![b, a] B)
  exact mainGen _ _ Ei Ei' Eo Eo' T hT

set_option maxHeartbeats 2000000 in
variable (k) in
theorem stageLift : StageLift k := by
  intro n η i j hij ⟨T, hT⟩
  obtain ⟨r, hr⟩ : ∃ r, i.val = r := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, n = r + (2 + t) := ⟨n - (r + 2), by have := j.isLt; omega⟩
  subst ht
  obtain ⟨A, hA⟩ : ∃ A : Fin r → ℂˣ, ∀ l, A l = η (Fin.castAdd (2 + t) l) := ⟨_, fun _ => rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Fin t → ℂˣ, ∀ l, B l = η (Fin.natAdd r (Fin.natAdd 2 l)) := ⟨_, fun _ => rfl⟩
  have ei : ∀ h : 0 < 2, Fin.natAdd r (Fin.castAdd t (⟨0, h⟩ : Fin 2)) = i := fun h => Fin.ext (by simp [hr])
  have ej : ∀ h : 1 < 2, Fin.natAdd r (Fin.castAdd t (⟨1, h⟩ : Fin 2)) = j := fun h => Fin.ext (by simp [hr, hij])
  have h1 : η = Fin.append A (Fin.append ![η i, η j] B) := by
    funext x
    refine Fin.addCases (fun l => ?_) (fun l => ?_) x
    · rw [Fin.append_left, hA]
    · rw [Fin.append_right]
      refine Fin.addCases (fun m => ?_) (fun m => ?_) l
      · rw [Fin.append_left]
        match m with
        | ⟨0, h⟩ => rw [ei h]; rfl
        | ⟨1, h⟩ => rw [ej h]; rfl
      · rw [Fin.append_right, hB]
  have h2 : η ∘ Equiv.swap i j = Fin.append A (Fin.append ![η j, η i] B) := by
    funext x
    refine Fin.addCases (fun l => ?_) (fun l => ?_) x
    · have e1 : Fin.castAdd (2 + t) l ≠ i := fun e => by
        have := congrArg Fin.val e; simp at this; omega
      have e2 : Fin.castAdd (2 + t) l ≠ j := fun e => by
        have := congrArg Fin.val e; simp at this; omega
      rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne e1 e2, Fin.append_left, hA]
    · rw [Fin.append_right]
      refine Fin.addCases (fun m => ?_) (fun m => ?_) l
      · rw [Fin.append_left]
        match m with
        | ⟨0, h⟩ => rw [Function.comp_apply, ei h, Equiv.swap_apply_left]; rfl
        | ⟨1, h⟩ => rw [Function.comp_apply, ej h, Equiv.swap_apply_right]; rfl
      · have e1 : Fin.natAdd r (Fin.natAdd 2 m) ≠ i := fun e => by
          have := congrArg Fin.val e; simp at this; omega
        have e2 : Fin.natAdd r (Fin.natAdd 2 m) ≠ j := fun e => by
          have := congrArg Fin.val e; simp at this; omega
        rw [Fin.append_right, hB, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne e1 e2]
  have := main (k := k) A (η i) (η j) B T hT
  rw [← h1, ← h2] at this
  exact this

end PositivityTheory.Rg.BcB.N3.PseStage

end
