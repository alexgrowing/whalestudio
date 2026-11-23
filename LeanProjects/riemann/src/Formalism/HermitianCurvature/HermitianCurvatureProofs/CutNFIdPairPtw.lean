import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFId
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopPtw

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem topPD_cut_eq (p : KB.Pl P Wp Wq) {Cb : ℝ} (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) {χ χ' : ℝ → ℝ}
    (hχ : C6.IsCut0 χ) (hχ' : C6.IsCut0 χ') {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : B.CkOn ⊤ (B.GV P.k P.r) F)
    {ε : ℝ} (hε : 0 < ε) {w : List C.Letter} (hw : KB.CutWord P p.l0 w) (c : Fin (P.r + 1) → ℂ)
    (hγ : ¬ (0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (TBB.bigPt P.r c)) ∨
      ε < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (TBB.bigPt P.r c)) :
    topPD p (D.cutF p.T.base χ' F ε) (D.cutF p.T.base χ F ε) w c = topD p F w c := by
  rw [← topPD_self]
  have hV : ∀ H₁ H₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp),
      (∀ g ∈ B.GV P.k P.r, ε < Gf P.k P.r p.T.base.z p.T.base.z' g → H₁ g = H₂ g) →
      D.vecV p.T.base p.ν' p.m₀ H₁ (TBB.bigPt P.r c) = D.vecV p.T.base p.ν' p.m₀ H₂ (TBB.bigPt P.r c) :=
    fun H₁ H₂ h => vecV_congr_gt p.T.base p.ν' p.m₀ _ ε h hγ
  have hcut : ∀ χ₀ : ℝ → ℝ, C6.IsCut0 χ₀ → ∀ g ∈ B.GV P.k P.r, ε < Gf P.k P.r p.T.base.z p.T.base.z' g →
      D.cutF p.T.base χ₀ F ε g = F g := by
    intro χ₀ hχ₀ g _ hg
    have h1 : 1 ≤ Gf P.k P.r p.T.base.z p.T.base.z' g / ε := by rw [le_div_iff₀ hε]; linarith
    simp only [D.cutF, hχ₀.2.2 _ h1, Complex.ofReal_one, one_smul]
  have hP : topPair p (D.cutF p.T.base χ' F ε) (D.cutF p.T.base χ F ε) w (TBB.bigPt P.r c) =
      topPair p F F w (TBB.bigPt P.r c) := by
    unfold topPair
    by_cases h3 : w = []
    · rw [if_pos h3, if_pos h3]
      unfold KB.Pl.V
      rw [hV _ _ (hcut χ' hχ'), hV _ _ (hcut χ hχ)]
    · rw [if_neg h3, if_neg h3]
      refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun ρ _ => ?_
      rw [hV _ _ (theta_cutF_gt p hCb hχ' hF hε hw e), hV _ _ (theta_cutF_gt p hCb hχ hF hε hw e)]
  unfold topPD
  rw [hP]

end place

theorem pairing_pointwise_all_levels_holds : NFPairPtwAll := by
  intro Cb
  refine ⟨0, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH χ' hχ' w hw _
  obtain ⟨hχ, hCb, hf, -, -, -⟩ := hH
  have hF : B.CkOn ⊤ (B.GV P.k P.r) (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) :=
    ckOn_fpm p p₀ hf (Formalism.FourierDecayAlt.P.CutMP.ER.ckOn_const' _)
  refine Filter.Eventually.of_forall fun c => ?_
  set Gγ := D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (TBB.bigPt P.r c) with hGγ
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ (¬ (0 < Gγ) ∨ ε < Gγ) := by
    by_cases hG : 0 < Gγ
    · filter_upwards [Ioo_mem_nhdsGT hG] with ε hε
      exact ⟨hε.1, Or.inr hε.2⟩
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact ⟨hε, Or.inl hG⟩
  filter_upwards [hev] with ε hε
  exact topPD_cut_eq p hCb hχ hχ' hF hε.1 hw.1 c hε.2

theorem top_identity_of_domination_limits (hA : P5.ThmPActual) (h3 : NFTopDomAll) (s1 : NFPolFormAll) (s4 : NFBetaLimAll) :
    NFTopIdAll :=
  nfTopIdAll_of hA h3 s1 pairing_pointwise_all_levels_holds s4

end

end Formalism.FourierDecayAlt.P.CutBP
