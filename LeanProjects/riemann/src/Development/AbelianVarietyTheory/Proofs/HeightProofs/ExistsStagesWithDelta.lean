import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreHasLetters

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.EX GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize

namespace GlobalTheory.StandInStages

def reweight {B : Base} {C : Cols B} (W : RowsRest B C) (kb : ∀ j, Tau B.R → Fin (B.R.sigW j).1 → ℤ)
    (ks : ∀ j, Tau B.R → Fin (B.R.sigW j).2 → ℤ) : RowsRest B C :=
  { W with kaBig := kb, kaSmall := ks, Ij := fun _ _ _ => 0, jw := fun _ _ _ => 0 }

def retol {B : Base} {C : Cols B} {W : RowsRest B C} (V : DivStage B C W) (η : ℝ) : DivStage B C W :=
  { V with div := { V.div with etaF := η } }

theorem exists_stages_blocks (B : Base) (Del : ℚ) (letter : B.Word → Fin (B.R.k - 2) → Bool) (η : ℝ) (D : ℕ)
    (hD : 0 < Del) (hinj : Function.Injective letter)
    (gap : ∀ w τ (l : ℕ) (h : l + 1 < B.R.k - 1),
      (B.hcW w τ).v ⟨l, by omega⟩ - (B.hcW w τ).v ⟨l + 1, h⟩ = 4 * Del)
    (hu : ∀ w τ (l : ℕ) (h : l < B.R.k - 2), (B.hcW w τ).u ⟨l + 1, by omega⟩ =
      (B.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then Del else 0))
    (kb : ∀ j, Tau B.R → Fin (B.R.sigW j).1 → ℤ) (ks : ∀ j, Tau B.R → Fin (B.R.sigW j).2 → ℤ) :
    ∃ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (_ : NStage B C W)
      (G : GJStage B C), S.s.Del = Del ∧ S.s.letter = letter ∧ V.div.etaF = η ∧ W.kaBig = kb ∧ W.kaSmall = ks ∧
      (∀ μ j w, W.Ij μ j w = 0) ∧ (∀ μ j w, W.jw μ j w = 0) ∧ W.Drows = D ∧ W.Dall = D ∧
      (∀ u, Nontrivial (W.Mu u)) ∧ (∀ u i, Nonempty ((C.mem u).C.cls i)) ∧ Nonempty G.jet.Sit := by
  obtain ⟨W₀, h1, h2, h3⟩ := StagesInhab.exists_rows B D
  let W := reweight W₀ kb ks
  have hc : ∀ u i, Nonempty (((ColsModel.cols B).mem u).C.cls i) :=
    fun u _ => ⟨(1 : Tau B.R → (ZMod (B.T u))ˣ)⟩
  obtain ⟨L⟩ := locStage_inhabited
  obtain ⟨N, -⟩ := GaloisStage.exists_nStage_adapt B _ W L
  obtain ⟨V, -⟩ := DivInhab.exists_divStage B _ (GaloisStage.adapt W)
  obtain ⟨S, hS, hl, -⟩ := SStageInhab.exists_sStage B _ (GaloisStage.adapt W) Del hD gap letter hinj hu
    (fun u x _ y _ => (StagesInhab.ipC_conj B u y x).symm) (fun u x _ h => StagesInhab.ipC_pos B u x h)
    (show W₀.Drows ≤ W₀.Dall by omega)
  obtain ⟨G, -, hG⟩ := (GJInhab.inhabited_stage B (ColsModel.cols B)).2.2 (hc _ _) (hc _ _)
  exact ⟨_, GaloisStage.adapt W, retol V η, S, N, G, hS, hl, rfl, rfl, rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
    h1, h2, h3, hc, hG⟩

theorem exists_stages_kapDef (B : Base) (Del : ℚ) (letter : B.Word → Fin (B.R.k - 2) → Bool) (η : ℝ) (D : ℕ)
    (hD : 0 < Del) (hinj : Function.Injective letter)
    (gap : ∀ w τ (l : ℕ) (h : l + 1 < B.R.k - 1),
      (B.hcW w τ).v ⟨l, by omega⟩ - (B.hcW w τ).v ⟨l + 1, h⟩ = 4 * Del)
    (hu : ∀ w τ (l : ℕ) (h : l < B.R.k - 2), (B.hcW w τ).u ⟨l + 1, by omega⟩ =
      (B.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then Del else 0)) :
    ∃ X : Stages, X.B = B ∧ X.toD7.s.Del = Del ∧ X.toD7.div.etaF = η ∧ DV.KapDef X.toD7 ∧
      (∀ w j, X.toD7.what₂.Aj j w = 0) ∧ X.W.Drows = D ∧ X.W.Dall = D ∧ (∀ u, Nontrivial (X.W.Mu u)) ∧
      (∀ u i, Nonempty ((X.C.mem u).C.cls i)) ∧ Nonempty X.G.jet.Sit := by
  obtain ⟨C₀, W₀, V₀, S₀, N₀, G₀, -⟩ :=
    exists_stages_blocks B Del letter η D hD hinj gap hu (fun _ _ _ => 0) (fun _ _ _ => 0)
  obtain ⟨kb, ks, hk⟩ := DV.exists_blocks (assemble B C₀ W₀ V₀ S₀ N₀ G₀)
  obtain ⟨C, W, V, S, N, G, a1, -, a2, a3, a4, a5, a6, a7⟩ :=
    exists_stages_blocks B Del letter η D hD hinj gap hu kb ks
  refine ⟨⟨B, C, W, V, S, N, G⟩, rfl, a1, a2, fun j _ _ τ => ⟨fun i => ?_, fun c => ?_⟩, fun w j => ?_, a7⟩
  · exact (congrArg (fun f => ((f j τ i : ℤ) : ℚ)) a3).trans ((hk j τ).1 i)
  · exact (congrArg (fun f => ((f j τ c : ℤ) : ℚ)) a4).trans ((hk j τ).2 c)
  · exact congrArg₂ (· + ·) (congrArg₂ (· + ·) (a5 _ _ _) (a5 _ _ _)) (a6 _ _ _)

theorem exists_stages_prescribed : ∀ (B : Base) (Del : ℚ) (letter : B.Word → Fin (B.R.k - 2) → Bool) (η : ℝ), 0 < Del → 0 < η → Function.Injective letter → (∀ w τ (l : ℕ) (h : l + 1 < B.R.k - 1), (B.hcW w τ).v ⟨l, by omega⟩ - (B.hcW w τ).v ⟨l + 1, h⟩ = 4 * Del) → (∀ w τ (l : ℕ) (h : l < B.R.k - 2), (B.hcW w τ).u ⟨l + 1, by omega⟩ = (B.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then Del else 0)) → ∃ X : Stages, X.B = B ∧ X.toD7.s.Del = Del ∧ X.toD7.div.etaF = η ∧ DV.KapDef X.toD7 ∧ ∀ w, X.toD7.what₂.muAt w = X.toD7.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ X.toD7.R.m → X.toD7.what₂.Aj j w = 0 := by
  intro B Del letter η hD _ hinj gap hu
  obtain ⟨X, h1, h2, h3, h4, h5, -⟩ := exists_stages_kapDef B Del letter η 1 hD hinj gap hu
  exact ⟨X, h1, h2, h3, h4, fun w _ j _ _ => h5 w j⟩

end GlobalTheory.StandInStages

end
