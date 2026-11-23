import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.PowNeOf

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.RgTw (Mat G)
open scoped Classical

set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Rg.BcB.F.BC

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {l₁ : InfinitePlace E → DomWeight a}
  {l₂ : InfinitePlace E → DomWeight b} {μ₁ : Measure (GA E a)} {μ₂ : Measure (GA E b)} {μa : Measure (G a)}
  {μb : Measure (G b)}

theorem prod_valW_ite (A : Arch E a b l₁ l₂ μ₁ μ₂ μa μb) {k : ℕ} (χ : InfinitePlace E → Inf k) (v : InfinitePlace E)
    (w : List (Bool × ℕ)) (p : Prop) [Decidable p] :
    (∏ v', A.valW (if v' = v ∧ p then w else []) (χ v')) =
      (if p then zVal w (χ v) else 1) * ∏ v', A.valW [] (χ v') := by
  have e : ∀ v', A.valW (if v' = v ∧ p then w else []) (χ v') =
      (if v' = v then (if p then zVal w (χ v) else 1) else 1) * A.valW [] (χ v') := by
    intro v'
    by_cases h1 : v' = v
    · subst h1
      by_cases hp : p
      · simp [hp, Arch.valW, zVal]
      · simp [hp]
    · simp [h1]
  rw [Finset.prod_congr rfl fun v' _ => e v', Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp

end

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)}
  {S T : Finset (Pl E)} {F₀ : Frame0 hR π S} (F : RunFrame F₀ T) (i : F₀.C.ι)

theorem val_tD (v : InfinitePlace E) (s : Bool) (m : ℕ) (side : Bool)
    (χa : InfinitePlace E → Inf (F.B i).a) (χb : InfinitePlace E → Inf (F.B i).b) :
    (F.tD i v s m side).val χa χb =
      (if side then zVal [(s, m)] (χb v) else zVal [(s, m)] (χa v)) * (F.t₀ i).val χa χb := by
  simp only [PT.val, valA, RunFrame.tD, RunFrame.t₀, RunFrame.ptL, Arch.pt]
  rw [prod_valW_ite, prod_valW_ite]
  cases side <;> simp <;> ring

end

set_option maxHeartbeats 2000000 in
theorem identOf' : IdentOf := by
  intro hG hR E _ _ _ n π S T F₀ F i χ hχ O
  have h0 := O.eigArch (.inl ()) (F.t₀ i) rfl rfl
  have h3 := hχ.2.1 (.inl ())
  have one : (F.t₀ i).val O.χa O.χb = 1 := by
    rw [← h0]
    exact h3
  have key : ∀ (v : InfinitePlace E) (s : Bool) (m : ℕ) (side : Bool),
      (if side then zVal [(s, m)] (O.χb v) else zVal [(s, m)] (O.χa v)) =
        (if side then zVal [(s, m)] ((F₀.A i).χb v) else zVal [(s, m)] ((F₀.A i).χa v)) := by
    intro v s m side
    have h1 := O.eigArch (.inr (.inl (i, v, s, m, side))) (F.tD i v s m side) (by simp [RunFrame.g]) rfl
    have h2 := hχ.2.1 (.inr (.inl (i, v, s, m, side)))
    rw [val_tD, one, mul_one] at h1
    rw [← h1, h2]
    cases side <;> rfl
  constructor
  · intro τ
    refine hG _ _ _ fun m => ?_
    have := key (InfinitePlace.mk τ) (decide (τ = (InfinitePlace.mk τ).embedding)) m false
    simpa [zVal] using this
  · intro τ
    refine hG _ _ _ fun m => ?_
    have := key (InfinitePlace.mk τ) (decide (τ = (InfinitePlace.mk τ).embedding)) m true
    simpa [zVal] using this

end PositivityTheory.Rg.BcB.F.BC

end
