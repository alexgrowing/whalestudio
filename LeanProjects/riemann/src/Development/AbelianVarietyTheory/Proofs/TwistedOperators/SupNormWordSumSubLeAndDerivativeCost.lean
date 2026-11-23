import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerAlong
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DRhoSumAndSobOLe

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped ENNReal

namespace GlobalTheory.Size.SupWord

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.OrientedHeis

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} {f f' : WO V W → ℂ}
  {p : (WO V W → ℂ) → ℝ≥0∞}

theorem word_add (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (l : List (D.what₂.Tau × Fin W.rank × Fin V.rank × Bool))
    (h : IsThetaFunO ψ V W f) (h' : IsThetaFunO ψ V W f') :
    wordAct (heisDer ψ θ) l (f + f') = wordAct (heisDer ψ θ) l f + wordAct (heisDer ψ θ) l f' := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [wordAct_cons, wordAct_cons, wordAct_cons, ih]
    exact dRho_add hψ hθ a.1 _ (theta_word hψ hθ l h) (theta_word hψ hθ l h')

theorem word_smul (l : List (D.what₂.Tau × Fin W.rank × Fin V.rank × Bool)) (c : ℂ) (f : WO V W → ℂ) :
    wordAct (heisDer ψ θ) l (c • f) = c • wordAct (heisDer ψ θ) l f :=
  wordAct_rel (R := fun g g' => g = c • g') l (fun a _ _ _ e => e ▸ dRho_smul a.1 _ c _) rfl

theorem ws_add_le (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hp : ∀ g g', p (g + g') ≤ p g + p g')
    (h : IsThetaFunO ψ V W f) (h' : IsThetaFunO ψ V W f') (k : ℕ) :
    wordSum (heisDer ψ θ) p k (f + f') ≤ wordSum (heisDer ψ θ) p k f + wordSum (heisDer ψ θ) p k f' :=
  wordSum_le_add fun l => by rw [word_add hψ hθ l h h']; exact hp _ _

theorem ws_smul (hp : ∀ (c : ℂ) g, p (c • g) = ‖c‖ₑ * p g) (k : ℕ) (c : ℂ) (f : WO V W → ℂ) :
    wordSum (heisDer ψ θ) p k (c • f) = ‖c‖ₑ * wordSum (heisDer ψ θ) p k f :=
  wordSum_eq_mul fun l => by rw [word_smul]; exact hp _ _

theorem ws_sum_le (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hp : ∀ g g', p (g + g') ≤ p g + p g')
    (hs : ∀ (c : ℂ) g, p (c • g) = ‖c‖ₑ * p g) {ι : Type} (s : Finset ι) {g : ι → WO V W → ℂ}
    (hg : ∀ i ∈ s, IsThetaFunO ψ V W (g i)) (k : ℕ) :
    wordSum (heisDer ψ θ) p k (∑ i ∈ s, g i) ≤ ∑ i ∈ s, wordSum (heisDer ψ θ) p k (g i) := by
  refine Finset.le_sum_of_subadditive_on_pred (wordSum (heisDer ψ θ) p k) (IsThetaFunO ψ V W) ?_
    (fun _ _ a b => ws_add_le hψ hθ hp a b k) (fun _ _ => theta_add) g hg
  have := ws_smul (ψ := ψ) (θ := θ) hs k 0 (0 : WO V W → ℂ)
  rw [zero_smul, enorm_zero, zero_mul] at this
  simp [this]

theorem ws_dRho_le (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hp : ∀ g g', p (g + g') ≤ p g + p g')
    (hs : ∀ (c : ℂ) g, p (c • g) = ‖c‖ₑ * p g) (hf : IsThetaFunO ψ V W f) (τ : D.what₂.Tau)
    (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (k : ℕ) :
    wordSum (heisDer ψ θ) p k (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f) ≤
      ENNReal.ofReal (∑ i, ∑ j, (|(z i j).re| + |(z i j).im|)) * wordSum (heisDer ψ θ) p (k + 1) f := by
  have ht : ∀ (c : ℂ) a, IsThetaFunO ψ V W (c • heisDer ψ θ a f) := fun c a =>
    theta_smul c (theta_dRho hθ hψ a.1 _ hf)
  have hb : ∀ (c : ℝ) a, wordSum (heisDer ψ θ) p k ((c : ℂ) • heisDer ψ θ a f) ≤
      ENNReal.ofReal |c| * wordSum (heisDer ψ θ) p (k + 1) f := fun c a => by
    rw [ws_smul hs, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    exact wordSum_letter_le k a f
  rw [dRho_eq_sum_heisDer hψ hθ hf, ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity, Finset.sum_mul]
  refine (ws_sum_le hψ hθ hp hs _ (fun i _ => theta_finsetSum _ fun j _ => theta_add (ht _ _) (ht _ _)) k).trans
    (Finset.sum_le_sum fun i _ => ?_)
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity, Finset.sum_mul]
  refine (ws_sum_le hψ hθ hp hs _ (fun j _ => theta_add (ht _ _) (ht _ _)) k).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _), add_mul]
  exact (ws_add_le hψ hθ hp (ht _ _) (ht _ _) k).trans (add_le_add (hb _ _) (hb _ _))

theorem supN_add_le (g g' : WO V W → ℂ) : (⨆ w, ‖(g + g') w‖ₑ) ≤ (⨆ w, ‖g w‖ₑ) + ⨆ w, ‖g' w‖ₑ :=
  iSup_le fun w => (enorm_add_le (g w) (g' w)).trans (add_le_add (le_iSup (fun w => ‖g w‖ₑ) w)
    (le_iSup (fun w => ‖g' w‖ₑ) w))

theorem supN_smul (c : ℂ) (g : WO V W → ℂ) : (⨆ w, ‖(c • g) w‖ₑ) = ‖c‖ₑ * ⨆ w, ‖g w‖ₑ := by
  simp only [Pi.smul_apply, enorm_smul, ENNReal.mul_iSup]

theorem wordSum_sup_sub_and_derAlong :
    ∀ (D : D7) (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → (∀ (G H : WO V W → ℂ) (c : ℂ) (k : ℕ), IsThetaFunO ψ V W G → IsThetaFunO ψ V W H → GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) k (G - c • H) ≤ GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) k G + ‖c‖ₑ * GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) k H) ∧ ∀ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (x : Matrix (Fin W.rank) (Fin r) D.host.E), ∃ c : ℝ, 0 ≤ c ∧ ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G → ∀ k : ℕ, GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) k (derAlong ψ θ V W C x G) ≤ ENNReal.ofReal c * GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) (k + 1) G := by
  intro D V W ψ hψ θ hθ
  have ha : ∀ g g' : WO V W → ℂ, (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) (g + g') ≤
      (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) g + (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) g' := supN_add_le
  have hs : ∀ (c : ℂ) (g : WO V W → ℂ), (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) (c • g) =
      ‖c‖ₑ * (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) g := supN_smul
  refine ⟨fun G H c k hG hH => ?_, fun r C x => ?_⟩
  · rw [sub_eq_add_neg, ← neg_smul]
    refine (ws_add_le hψ hθ ha hG (theta_smul _ hH) k).trans ?_
    rw [ws_smul hs, enorm_neg]
  · refine ⟨∑ τ, ∑ i, ∑ j, (|(dirAt V W C τ (x.map (tauE D τ)) i j).re| +
      |(dirAt V W C τ (x.map (tauE D τ)) i j).im|), by positivity, fun G hG k => ?_⟩
    unfold derAlong
    refine (ws_sum_le hψ hθ ha hs _ (fun τ _ => theta_dRho hθ hψ τ _ hG) k).trans ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun τ _ => by positivity), Finset.sum_mul]
    exact Finset.sum_le_sum fun τ _ => ws_dRho_le hψ hθ ha hs hG τ _ k

end GlobalTheory.Size.SupWord

end
