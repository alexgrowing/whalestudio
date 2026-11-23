import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdjKer0
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ActHecke

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.R3

attribute [local instance] borelG borelF borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem convF_zero {a b : ℕ} {A κ : Type} [Fintype κ] (ν : Measure (Hf E a b)) (ψ : Matrix κ κ (Hf E a b → ℂ)) :
    convF ν ψ (0 : A × κ → H E a b → ℂ) = 0 := by
  funext i x
  simp [convF]

theorem pw_succ_psi {B : Block E} (t : PT B) (j : ℕ) : (t.pw (j + 1)).ψ = mulF B.ν t.ψ (t.pw j).ψ := rfl

theorem pw_zero {B : Block E} (t : PT B) : t.pw 0 = t := rfl

theorem sq_psi {B : Block E} (t : PT B) (k : ℕ) : (t.sq k).ψ = mulF B.ν (t.adj'.pw k).ψ (t.pw k).ψ := rfl

theorem convF_pw (hCM : Tail.ConvMul) {B : Block E} (t : PT B) {A : Type} (U : Subgroup (Hf E B.a B.b))
    (F : A × B.κ → H E B.a B.b → ℂ) (hU : IsOpen (U : Set (Hf E B.a B.b)))
    (hF : ∀ i, ∀ u ∈ U, ∀ x, F i (x * finH u) = F i x) :
    ∀ k, (∀ j ≤ k, IsFinM (t.pw j).ψ) → convF B.ν (t.pw k).ψ F = (convF B.ν t.ψ)^[k + 1] F := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hfin
    have h0 : IsFinM t.ψ := hfin 0 (Nat.zero_le _)
    have hk : IsFinM (t.pw k).ψ := hfin k (Nat.le_succ k)
    rw [pw_succ_psi, (hCM E B A t.ψ (t.pw k).ψ U F h0 hk hU hF).1, ih (fun j hj => hfin j (Nat.le_succ_of_le hj)),
      Function.iterate_succ_apply' (convF B.ν t.ψ) (k + 1)]

theorem betaPow (hCM : Tail.ConvMul) {B : Block E} (t : PT B) (k : ℕ) {A : Type} (U : Subgroup (Hf E B.a B.b))
    (F : A × B.κ → H E B.a B.b → ℂ) (hU : IsOpen (U : Set (Hf E B.a B.b)))
    (hF : ∀ i, ∀ u ∈ U, ∀ x, F i (x * finH u) = F i x)
    (hfin : ∀ j ≤ k, IsFinM (t.pw j).ψ) (hfinA : IsFinM (t.adj'.pw k).ψ)
    (c : ℂ) (hc : c ≠ 0) (hF0 : F ≠ 0) (heig : convF B.ν (t.sq k).ψ F = c • F) :
    (convF B.ν t.ψ)^[k + 1] F ≠ 0 := by
  intro h0
  have h1 : convF B.ν (t.sq k).ψ F = convF B.ν (t.adj'.pw k).ψ (convF B.ν (t.pw k).ψ F) :=
    (hCM E B A (t.adj'.pw k).ψ (t.pw k).ψ U F hfinA (hfin k le_rfl) hU hF).1
  rw [convF_pw hCM t U F hU hF k hfin, h0, convF_zero] at h1
  rw [h1] at heig
  rcases smul_eq_zero.mp heig.symm with h | h
  · exact hc h
  · exact hF0 h

end PositivityTheory.Rg.BcB.F.R3

end
