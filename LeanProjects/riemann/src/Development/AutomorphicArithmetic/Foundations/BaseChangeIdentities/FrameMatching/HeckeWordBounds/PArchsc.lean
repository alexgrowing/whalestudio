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

private theorem val_mul {E : Type} [Field E] [NumberField E] [IsCMField E] {B : Block E} (s t : PT B)
    (χa : InfinitePlace E → Inf B.a) (χb : InfinitePlace E → Inf B.b) :
    (s.mul t).val χa χb = s.val χa χb * t.val χa χb := by
  simp only [PT.val, PT.mul, valA, Pi.mul_apply, Finset.prod_mul_distrib]
  ring

private theorem val_wd {E : Type} [Field E] [NumberField E] [IsCMField E] {B : Block E} (w : List (BGen B)) (t₀ : PT B)
    (χa : InfinitePlace E → Inf B.a) (χb : InfinitePlace E → Inf B.b) :
    (BGen.wd w t₀).val χa χb = (w.map (Sum.elim (fun _ => (1 : ℂ)) fun s : PT B => s.val χa χb)).prod * t₀.val χa χb := by
  induction w with
  | nil => simp [BGen.wd]
  | cons g w ih =>
    rcases g with c | s
    · have e : BGen.wd (Sum.inl c :: w) t₀ = BGen.wd w t₀ := rfl
      rw [e, ih]; simp
    · have e : BGen.wd (Sum.inr s :: w) t₀ = s.mul (BGen.wd w t₀) := rfl
      rw [e, val_mul, ih]; simp [mul_assoc]

private theorem sc_val {E : Type} [Field E] [NumberField E] [IsCMField E] {B : Block E} (w : List (BGen B))
    (χa : InfinitePlace E → Inf B.a) (χb : InfinitePlace E → Inf B.b) :
    BGen.sc w * (w.map (Sum.elim (fun _ => (1 : ℂ)) fun s : PT B => s.val χa χb)).prod =
      (w.map (Sum.elim id fun s : PT B => s.val χa χb)).prod := by
  induction w with
  | nil => simp [BGen.sc]
  | cons g w ih =>
    have hs : BGen.sc (g :: w) = Sum.elim id (fun _ => 1) g * BGen.sc w := by simp [BGen.sc]
    rw [hs, List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, ← ih]
    rcases g with c | s <;> simp <;> ring

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.archsc_pf :
    BlockWordOperators → TwOk → ArchLet → ArchSc := by
  intro _ _ hL hR E _ _ _ n π S T F₀ F hS i ws
  obtain ⟨hg, hβ, h1, h2⟩ := hL hR E n π S T F₀ F hS i
  set χa := (F₀.A i).χa
  set χb := (F₀.A i).χb
  set f : BGen (F.B i) → ℂ := Sum.elim id fun s : PT (F.B i) => s.val χa χb with hf
  have hv : (tw F i ws).val χa χb =
      ((ws.map (bw F i)).flatten.map (Sum.elim (fun _ => (1 : ℂ)) fun s : PT (F.B i) => s.val χa χb)).prod := by
    have e : tw F i ws = (F.t₁ i).mul (BGen.wd (ws.map (bw F i)).flatten (F.t₂ i)) := rfl
    rw [e, val_mul, val_wd, h1, h2]; simp
  rw [hv, sc_val]
  have hw : ∀ w : List (F.Γ × Bool), ((bw F i w).map f).prod = ((w.map (ul F)).map (Sum.elim id fun _ => (1 : ℂ))).prod := by
    intro w
    have hb : f (Sum.inr (F.β i)) = 1 := hβ
    simp only [bw, List.map_append, List.map_replicate, List.prod_append, hb, List.prod_replicate, one_pow, one_mul,
      List.map_map]
    congr 1
    apply List.map_congr_left
    intro p _
    exact hg p
  simp only [U.UGen.sc]
  clear hv
  induction ws with
  | nil => simp
  | cons w ws ih =>
    simp only [List.map_cons, List.flatten_cons, List.map_append, List.prod_append]
    rw [ih]
    congr 1
    exact hw w

end
