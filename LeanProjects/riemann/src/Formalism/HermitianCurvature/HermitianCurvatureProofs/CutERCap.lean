import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutER

namespace Formalism.FourierDecayAlt.P.CutMP.ER

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants
open scoped ComplexConjugate

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section consts

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rw_const (a : E) : ∀ v : List (B.Mat k r),
    B.Rw v (fun _ => a) = (fun _ => a) ∨ B.Rw v (fun _ => a) = (fun _ => (0 : E))
  | [] => Or.inl rfl
  | X :: v => by
    right
    funext g
    simp only [B.Rw, List.foldr_cons]
    rcases rw_const a v with h | h
    · simp only [B.Rw] at h
      rw [h]; simp [RdV]
    · simp only [B.Rw] at h
      rw [h]; simp [RdV]

theorem dLR_const (a : E) (u v : List (B.Mat k r)) :
    B.dLR u v (fun _ => a) = (fun _ => a) ∨ B.dLR u v (fun _ => a) = (fun _ => (0 : E)) := by
  induction u with
  | nil => exact rw_const a v
  | cons X u ih =>
    right
    simp only [Formalism.FourierDecayAlt.B.dLR, List.foldr_cons] at ih ⊢
    rcases ih with h | h <;> (rw [h]; funext g; simp [Formalism.FourierDecayAlt.B.LdV])

theorem norm_dLR_const_le (a : E) (u v : List (B.Mat k r)) (g : B.Mat k r) : ‖B.dLR u v (fun _ => a) g‖ ≤ ‖a‖ := by
  rcases dLR_const a u v with h | h <;> simp [h]

theorem ckOn_const' {m : ℕ∞} {UU : Set (B.Mat k r)} (a : E) : B.CkOn m UU (fun _ => a) := by
  intro g₀ _
  exact ⟨Set.univ, fun _ => a, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

end consts

theorem mem_capOp {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (s : ℂ)
    (Lw : List (ℂ × List (B.Mat k r))) {T : B.DTerm k r Wp Wq} (hT : T ∈ TLB.capOp k r Wp Wq s Lw) :
    ∃ (c : ℂ) (w : List (B.Mat k r)), T = TLB.cTerm c w := by
  unfold TLB.capOp at hT
  rcases List.mem_cons.1 hT with h | h
  · exact ⟨0, _, h⟩
  · obtain ⟨cw, -, rfl⟩ := List.mem_map.1 h
    exact ⟨_, _, rfl⟩

theorem capacity_theta_facts : CapThFacts := by
  intro k r Wp Wq _ _ _ _ _ _ D s Y ε m
  obtain ⟨hLw, hCV⟩ := Classical.choose_spec (Formalism.FourierDecayAlt.P.capelli_word_sum k r Y)
  have hLie : ∀ cw ∈ capLw k r Y, ∀ X ∈ cw.2, B.inLie k r X := fun cw h X hX => ((hLw cw h).1 X hX).1
  have hlen : ∀ cw ∈ capLw k r Y, cw.2.length ≤ 2 * r + k + 1 := fun cw h => (hLw cw h).2
  have hord : B.opOrder (capTh k r Wp Wq s Y) = 2 * r + k + 1 := TLB.opOrder_capOp s _ hlen
  have hApp : ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (B.GV k r) F →
      ∀ g ∈ B.GV k r, B.opApply (capTh k r Wp Wq s Y) F g = s • Q.CV k r Y F g := by
    intro F hF g hg
    unfold capTh
    rw [TLB.opApply_capOp s _ hLie, hCV _ _ F hF g hg hg]
    rfl
  refine ⟨hord, ?_, ?_, ?_, hApp⟩
  · intro T hT
    obtain ⟨c, w, rfl⟩ := mem_capOp s _ hT
    exact ⟨ckOn_const' _, ckOn_const' _⟩
  · intro p hp f hf g hg
    rw [hord] at hf
    have hgG : g ∈ B.GV k r := hg.1
    have hs' := Formalism.FourierDecayAlt.P.B7.sgs_mem D hp hgG
    rw [hApp _ (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp hf) g hgG,
      Formalism.FourierDecayAlt.P.capelli_rho_commute k r Wp Wq D Y f p hp hf g hgG]
    simp only [B.rho]
    rw [hApp f hf _ hs', ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  · intro T hT
    obtain ⟨c, w, rfl⟩ := mem_capOp s _ hT
    refine ⟨‖c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)‖ + ‖conj c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)‖,
      fun u v _ _ _ g _ _ => ?_⟩
    rw [Real.rpow_zero, mul_one]
    have h1 := norm_dLR_const_le (c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) u v g
    have h2 := norm_dLR_const_le (conj c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) u v g
    have n1 := norm_nonneg (c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp))
    have n2 := norm_nonneg (conj c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp))
    exact ⟨by simp only [TLB.cTerm]; linarith, by simp only [TLB.cTerm]; linarith⟩

theorem beta_form_congr_holds : BetaCongr := by
  intro k r Wp Wq _ _ _ _ _ _ D F F₁ F' F₁' hF hF'
  unfold B.beta
  refine Formalism.FourierDecayAlt.P.JFxG.betaBig_congr D (fun g hg => ?_) (fun g hg => ?_)
  · have h := Formalism.FourierDecayAlt.P.Qx8.JF_congr D (F := F) (F' := F₁) (a := 1) (fun g hg => by rw [one_smul, hF g hg]) hg.1
    rw [h, one_smul]
  · have h := Formalism.FourierDecayAlt.P.Qx8.JF_congr D (F := F') (F' := F₁') (a := 1) (fun g hg => by rw [one_smul, hF' g hg]) hg.1
    rw [h, one_smul]

end

end Formalism.FourierDecayAlt.P.CutMP.ER
