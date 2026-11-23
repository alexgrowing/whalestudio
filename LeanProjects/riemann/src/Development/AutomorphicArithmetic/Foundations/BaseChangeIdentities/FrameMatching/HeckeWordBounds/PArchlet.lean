import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.HeckeLevelWordBase

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.B3 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {l₁ : InfinitePlace E → DomWeight a}
  {l₂ : InfinitePlace E → DomWeight b} {μ₁ : Measure (GA E a)} {μ₂ : Measure (GA E b)} {μa : Measure (G a)}
  {μb : Measure (G b)} (A : Arch E a b l₁ l₂ μ₁ μ₂ μa μb)

private theorem val_pt {κ : Type} [Fintype κ] (wa wb : InfinitePlace E → List (Bool × ℕ))
    (ψ : Matrix κ κ (Hf E a b → ℂ)) (r : ℝ) :
    (A.pt wa wb ψ r).val A.χa A.χb = (∏ v, zVal (wa v) (A.χa v)) * ∏ v, zVal (wb v) (A.χb v) := by
  have h1 : (∏ v, coshT A.bump (cas (A.χa v))) * ∏ v, coshT A.bump (cas (A.χb v)) = 1 := A.one
  show (∏ v, A.valW (wa v) (A.χa v)) * (∏ v, A.valW (wb v) (A.χb v)) = _
  simp only [Arch.valW, Finset.prod_mul_distrib]
  linear_combination ((∏ v, zVal (wa v) (A.χa v)) * ∏ v, zVal (wb v) (A.χb v)) * h1

private theorem zVal_nil {m : ℕ} (χ : Inf m) : zVal [] χ = 1 := rfl

private theorem zVal_ite {m : ℕ} (c : Prop) [Decidable c] (L : List (Bool × ℕ)) (χ : Inf m) :
    zVal (if c then L else []) χ = if c then zVal L χ else 1 := by
  split_ifs <;> rfl

private theorem val_nil {κ : Type} [Fintype κ] (ψ : Matrix κ κ (Hf E a b → ℂ)) (r : ℝ) :
    (A.pt (fun _ => []) (fun _ => []) ψ r).val A.χa A.χb = 1 := by
  rw [val_pt]
  simp [zVal_nil]

private theorem val_der {κ : Type} [Fintype κ] (v : InfinitePlace E) (s : Bool) (m : ℕ) (side : Bool)
    (ψ : Matrix κ κ (Hf E a b → ℂ)) (r : ℝ) :
    (A.pt (fun v' => if v' = v ∧ side = false then [(s, m)] else [])
      (fun v' => if v' = v ∧ side = true then [(s, m)] else []) ψ r).val A.χa A.χb =
      if side then zVal [(s, m)] (A.χb v) else zVal [(s, m)] (A.χa v) := by
  rw [val_pt]
  simp only [zVal_ite]
  cases side <;> simp

end Val

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.archlet_pf :
    BlockOperatorsProductAdjoint → FBL.HermInf → ArchLet := by
  intro hO hH hR E _ _ _ n π S T F₀ F hS i
  have ha : ∀ v, IsHerm ((F₀.A i).χa v) := fun v => hH _ _
  have hb : ∀ v, IsHerm ((F₀.A i).χb v) := fun v => hH _ _
  have base : ∀ x, Sum.elim id (fun s : PT (F.B i) => s.val (F₀.A i).χa (F₀.A i).χb) (F.g x i) =
      Sum.elim id (fun _ => 1) (F.ug x) := by
    intro x
    rcases x with u | y | y
    · exact val_nil (F₀.A i) _ _
    · rcases y with ⟨j, v, s, m, side⟩
      by_cases hij : i = j
      · subst hij
        simp only [RunFrame.g, RunFrame.ug, if_true, Sum.elim_inr, Sum.elim_inl, id, RunFrame.tD, RunFrame.dval]
        exact val_der (F₀.A i) v s m side _ _
      · simp only [RunFrame.g, RunFrame.ug, hij, if_false, Sum.elim_inl, id]
    · exact val_nil (F₀.A i) _ _
  refine ⟨fun p => ?_, val_nil (F₀.A i) _ _, val_nil (F₀.A i) _ _, val_nil (F₀.A i) _ _⟩
  rcases p with ⟨x, s⟩
  cases s
  · simpa [gl, ul] using base x
  · have hadj : ∀ (g : BGen (F.B i)), g.Ok → Sum.elim id (fun s : PT (F.B i) => s.val (F₀.A i).χa (F₀.A i).χb) g.adj =
        starRingEnd ℂ (Sum.elim id (fun s : PT (F.B i) => s.val (F₀.A i).χa (F₀.A i).χb) g) := by
      rintro (c | t) hg
      · simp [BGen.adj]
      · have ht : t.Ok := hg
        simpa [BGen.adj] using (hO E (F.B i) t t ht ht).2.2.2.2.2.2.2 _ _ ha hb
    have huadj : ∀ (u : U.UGen E n), Sum.elim id (fun _ => (1 : ℂ)) (U.UGen.adj u) =
        starRingEnd ℂ (Sum.elim id (fun _ => (1 : ℂ)) u) := by
      rintro (c | y) <;> simp [U.UGen.adj]
    simp only [gl, ul, if_true]
    rw [hadj _ (hS.ok x i), huadj, base]

end
