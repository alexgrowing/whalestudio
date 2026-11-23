import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTrans
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPrimeOperatorsActOnRamifiedColumnsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarFormsOnChartsOfTrueColumnTupleStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms NumberField Matrix GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.AdForm ValuativeRel IsLocalRing

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sOp_zero_fun {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : Frame p S n) (P : Pair k n) (q : Unif k)
    (χ : AddChar 𝓀[k] ℂ) (ε : 𝓀[k]ˣ) : sOp β P q χ ε 0 = 0 := by
  have h0 : formAt β P 0 = 0 := by
    funext P₁
    simp [formAt]
  simp [sOp, h0]

theorem foldr_sOp_zero_fun {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ι : Type} {p : ι → SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : ∀ i, Frame (p i) S n)
    (P : ι → Pair k n) (q : Unif k) (χ : ι → AddChar 𝓀[k] ℂ) (η : ι → 𝓀[k]ˣ) (J : List ι) :
    J.foldr (fun i f => sOp (β i) (P i) q (χ i) (η i) f) 0 = 0 := by
  induction J with
  | nil => rfl
  | cons i J ih => simp only [List.foldr_cons, ih]; exact sOp_zero_fun _ _ _ _ _

theorem infM_one_eq {D : D7} (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (τ : D.what₂.Tau) :
    infM θ V hn 1 τ = 1 := by
  simp [infM, Formalism.L2.Theta.mt, Datum.compAt]

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
  {Ch : ℕ → Type}

theorem TwDat.rd_eq_zero_of_vanish (A : TwDat I l Z u a Ch) (θ : InfFam (I.rec7 l Z)) (j : ℕ) (hj : j ≤ B.R.m) (b : Ch j)
    (φ : ColT I l u a j) (hφ : ∀ c, A.chOf j c = b → φ c = 0) (y : (I.chain l u a).Y j) : A.rd θ j hj b φ y = 0 := by
  funext g
  unfold TwDat.rd rdS
  split_ifs with h
  · simp [hφ _ h.choose.1.2, atFr]
    intro _
    rfl
  · rfl

theorem twS_ramL : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch₀ Ch : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ιc : ∀ j, Ch j → Ch₀ j), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, GlobalTheory.FinPl.Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank)) (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)), StdT I l Z u p β Q L → ∀ (J : List ι) (q : Unif k) (χ : ι → AddChar k Circle) (hχ : ∀ i, HasConductor (χ i) 1), ∃ S : ∀ j, (ι → 𝓀[k]ˣ) → ColT I l u a j → ColT I l u a j, ∀ j (hj : j ≤ B.R.m) φ, A.RamL ιc j φ → (∀ b y, IsContAut _ (A.rd θ j hj b φ y) ∧ ∀ i, GlobalTheory.FinPl.RamAt (β j i) (Q j i) (A.rd θ j hj b φ y)) ∧ ∀ η, A.RamL ιc j (S j η φ) ∧ ∀ b y, A.rd θ j hj b (S j η φ) y = J.foldr (fun i f => sOp (β j i) (Q j i) q (resChar (χ i) (hχ i) q) (η i) f) (A.rd θ j hj b φ y) := by
  intro B X I hOk hPins l Z u a Ch₀ Ch A ιc hA θ hθ k _ _ _ _ ι p β Q L hStd J q χ hχ
  obtain ⟨S, hS⟩ := GlobalTheory.T.levelPrime_operators_act_on_ramified_columns I hOk hPins l Z u a Ch₀ A hA θ hθ k ι p β Q L hStd J q χ hχ
  refine ⟨S, fun j hj φ hφ => ?_⟩
  obtain ⟨h1, h2⟩ := hS j hj φ hφ.1
  refine ⟨h1, fun η => ⟨⟨(h2 η).1, ?_⟩, (h2 η).2⟩⟩
  intro c hc
  have hrd0 : ∀ y, A.rd θ j hj (A.chOf j c) φ y = 0 := fun y =>
    TwDat.rd_eq_zero_of_vanish A θ j hj _ φ (fun c' hc' => hφ.2 c' (by rw [hc']; exact hc)) y
  have hrdS : ∀ y, A.rd θ j hj (A.chOf j c) (S j η φ) y = 0 := by
    intro y
    rw [(h2 η).2, hrd0]
    exact foldr_sOp_zero_fun _ _ _ _ _ _
  funext y'
  have hTr : IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) j hj) 1) ⟨y'.1, y'.2⟩ ⟨y'.1, y'.2⟩ := by
    intro τ
    rw [infM_one_eq]
    first
    | exact (Matrix.one_mul _).symm
    | exact (one_mul _).symm
    | exact (one_smul _ _).symm
    | (show _ = _; simp [Matrix.one_mul])
  have key := (GlobalTheory.T.scalarForms_on_charts_of_trueColumnTuple I hOk hPins l Z u a Ch₀ A hA θ hθ j hj (S j η φ) (h2 η).1.1).2 (A.chOf j c) y' 1 (one_mem _)
    ⟨c, rfl⟩ 1 (one_mem _) 1 y' hTr
  rw [hrdS] at key
  simpa using key.symm

end GlobalTheory.AdForm
