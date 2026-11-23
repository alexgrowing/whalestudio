import Formalism.LocalToGlobal.CharacterGerms.RankMaximalOfNondegenerate

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section Defs

variable {C : Type} [Field C]

def frobTw {σ : Type} (l : ℕ) (c : MvPowerSeries σ C) : MvPowerSeries σ C :=
  fun μ => if ∀ s, l ∣ μ s then (MvPowerSeries.coeff (μ.mapRange (fun n => n / l) (Nat.zero_div l)) c) ^ l else 0

def cobd {dd : ℕ} (F : Fin dd → PS C 2 dd) (b : PS C 1 dd) : PS C 2 dd :=
  ev (n := 2) ![addOf F (pt C dd 0) (pt C dd 1)] b - ev (n := 2) ![pt C dd 0] b - ev (n := 2) ![pt C dd 1] b

end Defs

def FirstStepFirstHalfCondition : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I),
    (Y.raw p).RankHyp → ∀ Hc : ∀ g, (Y.raw p).CartHyp V g, (Y.raw p).AltC →
    ∀ (g : Fin 2) (a : ZMod d), (Y.raw p).big g a →
    ∀ (w : I g → C) (x : ℕ → I g ⊕ JJ I g → C), (RawChart.cart (Hc g)).Good a w x →
    (∀ q, V.MM ((RawChart.cart (Hc g)).c0' x q)) →
    ∀ (γ : Fin dd → PowerSeries C) (lam : JJ I g → PowerSeries C), (Y.raw p).TyWit V g x γ lam →
      ∃ A : PS C 1 dd, IntS V A ∧
        (∀ j : Fin dd, V.MM (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) A)) ∧
        ∀ μ, V.MM (MvPowerSeries.coeff μ
          (cobd Y.B.G.F A - frobTw V.l (Y.chartLinearTerm (fun i => PowerSeries.coeff 1 (γ i)))))

def FirstStepSecondHalfCondition : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C), IsAlgClosed C →
    ∀ (dd : ℕ) (G : FGLaw C dd), (∀ i, IntS V (G.F i)) →
    ∀ (A : PS C 1 dd) (c : PS C 2 dd), IntS V A → IntS V c →
      (∀ j : Fin dd, V.MM (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) A)) →
      (∀ μ, V.MM (MvPowerSeries.coeff μ (cobd G.F A - frobTw V.l c))) →
      ∃ b : PS C 1 dd, IntS V b ∧ ∀ μ, V.MM (MvPowerSeries.coeff μ (c - cobd G.F b))

theorem intS_c2lin {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (Y : FBChart C V O dd) (u : Fin dd → C) (hu : ∀ i, V.Ge 0 (u i)) : IntS V (Y.chartLinearTerm u) := by
  intro μ
  show V.Ge 0 (∑ i, u i * MvPowerSeries.coeff
    (μ.mapDomain (fun p : Fin 2 × Fin dd => (p.1.succ, p.2)) + Finsupp.single ((0 : Fin 3), i) 1) Y.B.ph2)
  exact VF.Ge.sum fun i _ => by simpa using (hu i).mul (Y.intPh2 _)

theorem rank_maximal_first_step_of_halves (hP : FirstStepFirstHalfCondition) (hQ : FirstStepSecondHalfCondition) : RankMaximalInitialCoefficient := by
  intro C _ _ V O _ _ dd Y d _ I _ p hrk Hc hAlt g a hbig w x hG hc0 γ lam hW
  obtain ⟨A, hA, hlin, hfe⟩ := hP C V O dd Y d I p hrk Hc hAlt g a hbig w x hG hc0 γ lam hW
  have hc := intS_c2lin Y (fun i => PowerSeries.coeff 1 (γ i)) fun i => (hW.1 i).2 1
  exact hQ C V Y.algClosed dd Y.B.G Y.intF A _ hA hc hlin hfe

theorem rank_maximal_of_halves (hP : FirstStepFirstHalfCondition) (hQ : FirstStepSecondHalfCondition) : RankMaximalOfNondegenerate :=
  rank_maximal_of_nondegenerate (rank_maximal_first_step_of_halves hP hQ)

end Formalism.L2.FormalSeriesBounds
