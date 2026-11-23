import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDblClosed
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHeisenbergCombinationSplitPlaceDatum

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.CombAt

theorem exists_isCombAt {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (p : Place D k) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsStdChar D ψ (-1)) {S T : HSp D} (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y)
    (Ξ : Matrix Y Y' k → ℂ) : ∃ c : WO S T →₀ ℂ, p.IsCombAt ψ FS FT c Ξ := by
  by_cases h : ∃ Φ : SB (Matrix Y Y' k), Φ.1 = Ξ
  · obtain ⟨Φ, hΦ⟩ := h
    obtain ⟨O, hO, hO0⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := k) (Y := Y) (Y' := Y')
    have hne : O ≠ 0 := by
      rintro rfl
      simp at hO0
    obtain ⟨c, h1, h2⟩ := GlobalTheory.LocComb.exists_comb D k p Y Y' S T FS FT ψ hψ O Φ hne
    refine ⟨c, h1, fun Tm hT Φ₀ Φ' h₀ h' => ?_⟩
    obtain rfl : Φ' = Φ := Subtype.ext (h'.trans hΦ.symm)
    obtain rfl : Φ₀ = O := Subtype.ext (h₀.trans hO.symm)
    exact h2 Tm hT
  · exact ⟨0, by simp, fun Tm _ Φ₀ Φ _ h' => (h ⟨Φ, h'⟩).elim⟩

theorem exists_cg : ∀ (D : D7) (u : D.what₂.Word) (d : Dat D u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (q : GlobalTheory.FinPl.SplitPt D k) (s : ℕ) (S : SymData k s D.R.k) (FX : ∀ j, j ≤ s + 1 → GlobalTheory.LocMod.Frame k (D.sp.X j).rank (XIx (Fin D.R.k) (Fin D.R.t) j)) (FM : GlobalTheory.LocMod.Frame k (D.sp.X (s + 1 + 1)).rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit)), IsStdChar D d.c.ψ (-1) → ∃ cg : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ, (∀ j c (H : j + 1 + c = s), (ofSplit q).IsCombAt d.c.ψ (FX j (by omega)) (FX (j + 1) (by omega)) (cg j) ((S.T (Fin D.R.t)).entry S.ψ ν j c H 1 1)) ∧ (ofSplit q).IsCombAt d.c.ψ (FX s (by omega)) (FX (s + 1) le_rfl) (cg s) (fun x₀ => (S.T (Fin D.R.t)).Psi 1 x₀ (S.y0 (Fin D.R.t))) ∧ (ofSplit q).IsCombAt d.c.ψ (FX (s + 1) le_rfl) FM (cg (s + 1)) ((S.T (Fin D.R.t)).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 (Fin D.R.t)))) := by
  intro D u d k _ _ _ _ _ _ ν q s S FX FM hψ
  obtain ⟨c₁, h₁⟩ := exists_isCombAt (ofSplit q) hψ (FX s (by omega)) (FX (s + 1) le_rfl)
    (fun x₀ => (S.T (Fin D.R.t)).Psi 1 x₀ (S.y0 (Fin D.R.t)))
  obtain ⟨c₂, h₂⟩ := exists_isCombAt (ofSplit q) hψ (FX (s + 1) le_rfl) FM
    ((S.T (Fin D.R.t)).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 (Fin D.R.t))))
  have key : ∀ j, ∃ c : WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ,
      (∀ c' (H : j + 1 + c' = s), (ofSplit q).IsCombAt d.c.ψ (FX j (by omega)) (FX (j + 1) (by omega)) c
        ((S.T (Fin D.R.t)).entry S.ψ ν j c' H 1 1)) ∧ (j = s → HEq c c₁) ∧ (j = s + 1 → HEq c c₂) := by
    intro j
    by_cases hj : j < s
    · obtain ⟨c', H⟩ : ∃ c', j + 1 + c' = s := ⟨s - j - 1, by omega⟩
      obtain ⟨c, hc⟩ := exists_isCombAt (ofSplit q) hψ (FX j (by omega)) (FX (j + 1) (by omega))
        ((S.T (Fin D.R.t)).entry S.ψ ν j c' H 1 1)
      refine ⟨c, fun c'' H' => ?_, fun h => by omega, fun h => by omega⟩
      obtain rfl : c'' = c' := by omega
      exact hc
    · by_cases h1 : j = s
      · subst h1
        exact ⟨c₁, fun c' H => by omega, fun _ => HEq.rfl, fun h => by omega⟩
      · by_cases h2 : j = s + 1
        · subst h2
          exact ⟨c₂, fun c' H => by omega, fun h => by omega, fun _ => HEq.rfl⟩
        · exact ⟨0, fun c' H => by omega, fun h => (h1 h).elim, fun h => (h2 h).elim⟩
  choose cg k1 k2 k3 using key
  refine ⟨cg, k1, ?_, ?_⟩
  · rw [eq_of_heq (k2 s rfl)]; exact h₁
  · rw [eq_of_heq (k3 (s + 1) rfl)]; exact h₂

end GlobalTheory.LocMod.CombAt
end
