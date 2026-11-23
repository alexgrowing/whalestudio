import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SplitLatticeBasisExists

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA MassDataIdxAdA
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (IdxD D) (FpX X p))

def colV : IdxD D → Formalism.L2.SG.HidaSetting.VA X.B.I
  | Sum.inl a => X.e0 a
  | Sum.inr (Sum.inl (Sum.inl i)) => X.bw i
  | Sum.inr (Sum.inl (Sum.inr _)) => X.z0
  | Sum.inr (Sum.inr c) => X.f0 (Fin.rev c)

def rowV : IdxD D → Formalism.L2.SG.HidaSetting.VA X.B.I
  | Sum.inl a => X.f0 a
  | Sum.inr (Sum.inl (Sum.inl i)) => X.bwd i
  | Sum.inr (Sum.inl (Sum.inr _)) => X.z0
  | Sum.inr (Sum.inr c) => X.e0 (Fin.rev c)

def sgnV : IdxD D → FpX X p
  | Sum.inr (Sum.inl (Sum.inr _)) => -1
  | _ => 1

theorem fin_dir (hθ : IsSplitEquiv X p θ) (hL : LatBasis X p θ (reindex₂ X p Q)) (x y : Formalism.L2.SG.HidaSetting.VA X.B.I)
    (h : ZMod' X.B.I X.B.g (hA X.B.I x y)) :
    ∃ z : OvA X p, crd2 X p θ Q (PI.FinKW.vecV X.B.I p.1 x) ⬝ᵥ crd1 X p θ Q (PI.FinKW.vecV X.B.I p.1 y) =
      ((gOf p : ℕ) : FpX X p) * (z : FpX X p) := by
  obtain ⟨z, hz⟩ := cong_dir X p θ Q hθ hL x y 0 (by simpa using h)
  exact ⟨z, by simpa using hz⟩

theorem fin_sym (hθ : IsSplitEquiv X p θ) (hL : LatBasis X p θ (reindex₂ X p Q)) (x y : Formalism.L2.SG.HidaSetting.VA X.B.I)
    (h : ZMod' X.B.I X.B.g (hA X.B.I y x)) :
    ∃ z : OvA X p, crd2 X p θ Q (PI.FinKW.vecV X.B.I p.1 x) ⬝ᵥ crd1 X p θ Q (PI.FinKW.vecV X.B.I p.1 y) =
      ((gOf p : ℕ) : FpX X p) * (z : FpX X p) := by
  obtain ⟨z, hz⟩ := cong_sym X p θ Q hθ hL x y 0 (by simpa using h)
  exact ⟨z, by simpa using hz⟩

theorem psiV_ite_one (c : Prop) [Decidable c] :
    θ (PI.FinKW.psiV X.B.I p.1 (if c then 1 else 0)) = if c then 1 else 0 := by
  split_ifs <;> simp

theorem rc_cong (hθ : IsSplitEquiv X p θ) (hε : θ (epsP X p) = (1, 0)) (hL : LatBasis X p θ (reindex₂ X p Q))
    (s t : IdxD D) :
    ∃ z : OvA X p, sgnV X p s * (crd2 X p θ Q (PI.FinKW.vecV X.B.I p.1 (rowV X s)) ⬝ᵥ
      crd1 X p θ Q (PI.FinKW.vecV X.B.I p.1 (colV X t))) =
      (1 : Matrix (IdxD D) (IdxD D) (FpX X p)) s t + ((gOf p : ℕ) : FpX X p) * (z : FpX X p) := by
  have hg := X.gramIntegral
  have hz := X.formsAtZero
  have hW := X.weightVectorsIntegral
  rcases s with a | ((i | u) | c) <;> rcases t with b | ((j | v) | c') <;> simp only [rowV, colV, sgnV, one_mul]
  · obtain ⟨z, e⟩ := cong_sym X p θ Q hθ hL _ _ _ (hg b a).2.2
    refine ⟨z, ?_⟩
    rw [e, psiV_ite_one]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Ne.symm hab]
  · obtain ⟨z, e⟩ := fin_dir X p θ Q hθ hL _ _ ((hW j).2.2 a).2.1
    exact ⟨z, by rw [e]; simp⟩
  · obtain ⟨z, e⟩ := fin_dir X p θ Q hθ hL _ _ (hz.2 a).2
    exact ⟨z, by rw [e]; simp⟩
  · obtain ⟨z, e⟩ := fin_dir X p θ Q hθ hL _ _ (hg a (Fin.rev c')).2.1
    exact ⟨z, by rw [e]; simp⟩
  · obtain ⟨z, e⟩ := fin_sym X p θ Q hθ hL _ _ ((hW i).2.2 b).2.2.1
    exact ⟨z, by rw [e]; simp⟩
  · obtain ⟨z, e⟩ := cong_dir X p θ Q hθ hL _ _ _ (X.bw_dual i j)
    refine ⟨z, ?_⟩
    rw [e]
    by_cases hij : i = j
    · subst hij
      simp only [if_true]
      have : PI.FinKW.psiV X.B.I p.1 X.ew = epsP X p := rfl
      rw [this, hε]
      simp
    · simp [hij]
  · obtain ⟨z, e⟩ := fin_sym X p θ Q hθ hL _ _ (hW i).2.1
    exact ⟨z, by rw [e]; simp⟩
  · obtain ⟨z, e⟩ := fin_sym X p θ Q hθ hL _ _ ((hW i).2.2 (Fin.rev c')).2.2.2
    exact ⟨z, by rw [e]; simp⟩
  · obtain ⟨z, e⟩ := fin_sym X p θ Q hθ hL _ _ (hz.2 b).1
    exact ⟨-z, by rw [e]; simp⟩
  · obtain ⟨z, e⟩ := fin_dir X p θ Q hθ hL _ _ (hW j).1
    exact ⟨-z, by rw [e]; simp⟩
  · obtain ⟨z, e⟩ := cong_dir X p θ Q hθ hL _ _ (-1) (by rw [sub_neg_eq_add]; exact hz.1)
    refine ⟨-z, ?_⟩
    rw [e]
    simp
    ring
  · obtain ⟨z, e⟩ := fin_sym X p θ Q hθ hL _ _ (hz.2 (Fin.rev c')).2
    exact ⟨-z, by rw [e]; simp⟩
  · obtain ⟨z, e⟩ := fin_dir X p θ Q hθ hL _ _ (hg (Fin.rev c) b).1
    exact ⟨z, by rw [e]; simp⟩
  · obtain ⟨z, e⟩ := fin_dir X p θ Q hθ hL _ _ ((hW j).2.2 (Fin.rev c)).1
    exact ⟨z, by rw [e]; simp⟩
  · obtain ⟨z, e⟩ := fin_dir X p θ Q hθ hL _ _ (hz.2 (Fin.rev c)).1
    exact ⟨z, by rw [e]; simp⟩
  · obtain ⟨z, e⟩ := cong_dir X p θ Q hθ hL _ _ _ (hg (Fin.rev c) (Fin.rev c')).2.2
    refine ⟨z, ?_⟩
    rw [e, psiV_ite_one]
    by_cases hcc : c = c'
    · subst hcc; simp
    · simp [hcc]

end Loc

end MassDataIdxSteps
