import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutDec
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordBoundCompactSupportCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.VecOpApplyCutFEq
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IteratedDerivBddOfEventuallyConst
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ContinuousOfIsPolyDeg

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF Filter Topology

namespace GlobalTheory.HatNF

theorem tendsto_list_map_sum_real {α : Type*} (l : List α) (u : α → ℕ → ℝ) (v : α → ℝ)
    (h : ∀ x ∈ l, Tendsto (u x) atTop (𝓝 (v x))) :
    Tendsto (fun n => (l.map fun x => u x n).sum) atTop (𝓝 (l.map v).sum) :=
  tendsto_list_sum l h

theorem wordBound_decay : ∀ a : ℕ → ℕ, BasicLiftAll a → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CutWord P p.l0 w → w.length ≤ N → ∃ (C : ℝ) (J : ℕ) (Θs : List (B.DiffOp P.k P.r Wp Wq)), WordBound p (a P.r) w C J Θs (fun φ f => ∃ (e : ℕ) (A : ℝ), CutPow e φ ∧ B.CkOn ⊤ (B.GV P.k P.r) f ∧ (∀ m : ℕ, B.InCC A m f) ∧ Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A - (2 * (P.r : ℝ) + 2) * e) := by
  intro a ha Cb
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.HatNF.vecV_cut_polyOp
  obtain ⟨c₂, hc₂⟩ := Formalism.FourierDecayAlt.P.PBE.vecV_cut_op
  refine ⟨5 * max Cb 8 + max Cb 8 ^ 2 + 1 + |max c₁ c₂|, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P0 p N w hDD hw hwN
  obtain ⟨C, J, Θs, hC, hpoly, hB⟩ := GlobalTheory.T.wordBound_compactSupportCoefficients a ha Wp Wq P0 p w hw
  refine ⟨C, J, Θs, hC, hpoly, ?_⟩
  rintro φ f ⟨e₀, A, hφ, hf, hfA, hA⟩ e c hc hG
  have hXn : ((2 * P0.r + P0.k + 1 : ℕ) : ℝ) = 2 * (P0.r : ℝ) + P0.k + 1 := by push_cast; ring
  have hr0 : (0 : ℝ) ≤ P0.r := Nat.cast_nonneg _
  have hrX : (P0.r : ℝ) + 1 ≤ 2 * (P0.r : ℝ) + P0.k + 1 := by
    have : (0 : ℝ) ≤ P0.k := Nat.cast_nonneg _
    linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hCb8 : (8 : ℝ) ≤ max Cb 8 := le_max_right _ _
  have hCb0 : (0 : ℝ) ≤ max Cb 8 := by linarith
  have hwN' : (w.length : ℝ) ≤ N := by exact_mod_cast hwN
  have hw0 : (0 : ℝ) ≤ w.length := Nat.cast_nonneg _
  have he0 : (0 : ℝ) ≤ (2 * (P0.r : ℝ) + 2) * e₀ := by positivity
  have hcut' : ∀ n g, Formalism.FourierDecayAlt.P.CutBP.cutN P0.k P0.r n g = 1 - Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g := by
    intro n g
    simp [Formalism.FourierDecayAlt.P.CutBP.cutN, Formalism.FourierDecayAlt.P.JCx2.pdPsi, Formalism.FourierDecayAlt.P.JCx2.pdPhi, Formalism.FourierDecayAlt.P.JCx2.pdChi,
      Formalism.FourierDecayAlt.P.JCx2.pdSq]
  have hmono : ∀ c : ℝ, c ≤ max c₁ c₂ → ∀ B' : ℝ,
      max c₁ c₂ * ((P0.r : ℝ) + 1) ^ 2 * ((P0.r : ℝ) * (2 * (P0.r : ℝ) + P0.k + 1) + 1) ≤ B' →
      c * ((P0.r : ℝ) + 1) ^ 2 * ((P0.r : ℝ) * ((2 * P0.r + P0.k + 1 : ℕ) : ℝ) + 1) ≤ B' := by
    intro c hc B' hB
    rw [hXn]
    refine le_trans ?_ hB
    apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)
  obtain ⟨δ₀, hδ₀, hφ0⟩ := hφ.2.1
  set γ := TBB.bigPt P0.r c with hγ
  set δ : ℝ := min δ₀ (TBB.Gp p γ / 2) with hδdef
  have hδ : 0 < δ := lt_min hδ₀ (by linarith)
  have hδ1 : δ ≤ δ₀ := min_le_left _ _
  have hδ2 : δ < TBB.Gp p γ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨χ, hχ⟩ : ∃ χ : ℝ → ℝ, C6.IsCut0 χ := ⟨_, Formalism.FourierDecayAlt.P.Topx2.base_cutoff_is_truncation⟩
  have hmul : ∀ n, mulG p.T.base φ (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f δ) n) =
      fun g => Formalism.FourierDecayAlt.P.CutBP.cutN P0.k P0.r n g • mulG p.T.base φ f g := by
    intro n
    funext g
    simp only [mulG, Formalism.FourierDecayAlt.P.CutBP.apx, D.cutF]
    by_cases hg : Gf P0.k P0.r p.T.base.z p.T.base.z' g < δ₀
    · simp [hφ0 _ hg]
    · rw [hχ.2.2 _ ((one_le_div hδ).2 (hδ1.trans (not_lt.1 hg)))]
      simp only [Complex.ofReal_one, one_smul]
      exact smul_comm _ _ _
  have hn := fun n => hB φ (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f δ) n)
    ⟨hφ.1, Formalism.FourierDecayAlt.P.CutBP.cptCoef_apx P0 p.T.base hχ hf hδ n⟩ e c hc hG
  simp only [hmul] at hn
  refine le_of_tendsto_of_tendsto' (b := atTop) ?_ ?_ hn
  · refine Tendsto.norm ((Formalism.FourierDecayAlt.P.BetaSesquilinearity.hsVec_cont.tendsto _).comp ?_)
    obtain ⟨nf, fib, o, κ, Dop, hfib, hIn, ho, hκ, hΘ⟩ := hDD w hw e
    have hcongr : ∀ G, p.V (p.Θ.Θ w e G) γ = D.vecV p.T.base p.ν' p.m₀ (B.opApply Dop G) γ :=
      fun G => Formalism.FourierDecayAlt.P.PBE.vecV_congrGPos p.T.base p.ν' p.m₀ γ
        (fun g hg => hΘ G g ⟨hg.1, hg.2, fun l hl => by simp at hl⟩)
    rw [hcongr]
    have ho' : (o : ℝ) ≤ max Cb 8 * N * (2 * (P0.r : ℝ) + P0.k + 1) := by
      calc (o : ℝ) ≤ Cb * w.length * ((2 * P0.r + P0.k + 1 : ℕ) : ℝ) := ho
        _ ≤ max Cb 8 * w.length * (2 * (P0.r : ℝ) + P0.k + 1) := by
          rw [hXn]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
            (by linarith)
        _ ≤ max Cb 8 * N * (2 * (P0.r : ℝ) + P0.k + 1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwN' hCb0) (by linarith)
    have hκ' : (κ : ℝ) ≤ max Cb 8 * ((P0.r : ℝ) + 1) * o :=
      hκ.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
        (Nat.cast_nonneg _))
    have hthr := Formalism.FourierDecayAlt.P.PBE.thr_arith (P0.r) (2 * (P0.r : ℝ) + P0.k + 1) N (max Cb 8) (max c₁ c₂) o κ _
      hr0 hrX hN0 hCb0 (Nat.cast_nonneg _) ho' (Nat.cast_nonneg _) hκ' hA
    obtain ⟨hck, bF, hbF⟩ := GlobalTheory.HatNF.mulG_ckOn_inCC Wp Wq P0 p.T.base e₀ o φ f A hφ hf (hfA o)
    have hv : ∀ g, Gf P0.k P0.r p.T.base.z p.T.base.z' g < δ₀ → mulG p.T.base φ f g = 0 := by
      intro g hg
      simp [mulG, hφ0 _ hg]
    have hth := hmono c₂ (le_max_right _ _)
      (A - (2 * (P0.r : ℝ) + 2) * ((e₀ : ℝ) + o) - 1 - ((κ : ℝ) + 3 * ((P0.r : ℝ) + 1) * o)) (by linarith [hthr])
    have key := hc₂ P0.k P0.r Wp Wq p.T.base p.ν' p.m₀ γ (mulG p.T.base φ f) (Formalism.FourierDecayAlt.P.CutBP.cutN P0.k P0.r)
      nf fib o κ Dop δ₀ _ bF hfib hIn hδ₀ hv hck hbF hcut' hth
    exact key.congr fun n => (hcongr _).symm
  · refine Tendsto.const_mul _ (tendsto_list_map_sum_real Θs
      (fun Θ n => ‖B.hsVec (p.V (B.opApply Θ (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f δ) n)) γ)‖)
      (fun Θ => ‖B.hsVec (p.V (B.opApply Θ f) γ)‖) fun Θ hΘ => ?_)
    refine Tendsto.norm ((Formalism.FourierDecayAlt.P.BetaSesquilinearity.hsVec_cont.tendsto _).comp ?_)
    rw [← GlobalTheory.HatNF.vec_opApply_cutF_eq Wp Wq P0 p Θ f χ δ γ hχ hδ hδ2]
    set o : ℕ := w.length * (2 * P0.r + P0.k + 1) with ho
    set κ : ℕ := w.length * (8 * (P0.r + 1) * (2 * P0.r + P0.k + 1)) with hκ
    have hoR : (o : ℝ) = w.length * (2 * (P0.r : ℝ) + P0.k + 1) := by rw [ho]; push_cast; ring
    have hκR : (κ : ℝ) = 8 * ((P0.r : ℝ) + 1) * o := by rw [hoR, hκ]; push_cast; ring
    have ho' : (o : ℝ) ≤ max Cb 8 * N * (2 * (P0.r : ℝ) + P0.k + 1) := by
      rw [hoR]
      exact mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)
    have hκ' : (κ : ℝ) ≤ max Cb 8 * ((P0.r : ℝ) + 1) * o := by
      rw [hκR]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCb8 (by linarith)) (Nat.cast_nonneg _)
    have hthr := Formalism.FourierDecayAlt.P.PBE.thr_arith (P0.r) (2 * (P0.r : ℝ) + P0.k + 1) N (max Cb 8) (max c₁ c₂) o κ _
      hr0 hrX hN0 hCb0 (Nat.cast_nonneg _) ho' (Nat.cast_nonneg _) hκ' hA
    have h3 : (0 : ℝ) ≤ 3 * ((P0.r : ℝ) + 1) * o := by positivity
    exact hc₁ Wp Wq P0 p o κ Θ (D.cutF p.T.base χ f δ) (A - 2 * ((P0.r : ℝ) + 1) * o) (hpoly Θ hΘ)
      (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hχ hf δ)
      (Formalism.FourierDecayAlt.P.PBE.cutF_inCC p.T.base hχ hfA hδ _ o (by linarith))
      (hmono c₁ (le_max_left _ _) _ (by linarith [hthr])) (Formalism.FourierDecayAlt.P.CutBP.cutN P0.k P0.r) (fun _ _ => rfl) γ

end GlobalTheory.HatNF
