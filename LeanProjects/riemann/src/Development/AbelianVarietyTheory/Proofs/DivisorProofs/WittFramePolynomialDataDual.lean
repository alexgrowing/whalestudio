import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignatureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameDualSoTypeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameDualSoBoundStatement

noncomputable section

namespace GlobalTheory.ThK.ExpSmall

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

theorem cuspExp_neg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin (a + a')) (Fin r) E), IsWittFrame σ (c • G.W.J.map σ) Xf Yf →
        ∀ K, IsMaxCpt σ (c • G.W.J.map σ) K →
          IsAut σ (c • G.W.J.map σ) K (fun x => G.M'.I om' Φ ((toGAd hσ G.W.J hc).symm x)) →
          ∀ S s, GlobalTheory.StdPar.IsCuspExp σ (c • G.W.J.map σ) Xf Yf S K (fun x => G.M'.I om' Φ ((toGAd hσ G.W.J hc).symm x)) s →
            ∀ k ∈ S, ∑ i with i ≤ k, (s i).re < 0 := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' hP hT c hc hcs Φ hΦ r Xf Yf hW K hK hA S s hs k hk
  have hdc := GlobalTheory.T.witt_frame_dual_so_type F E σ hσ B a a' G X om om' hP hT c hc hcs Φ hΦ r Xf Yf hW K hK hA S s hs
  have hex := GlobalTheory.T.witt_frame_dual_so_bound F E σ hσ B a a' G X om om' hP hT c hc hcs Φ hΦ r Xf Yf hW K hK hA S s hs hdc
  have hr := (GlobalTheory.T.witt_rank_le_skew_signature F E σ B (a + a') G.W _ _ hT.base hT.geo.hW c hc hcs r Xf Yf hW).2
  have hab := hT.geo.aBig
  have hlt := hT.geo.lt
  have neg : ∀ i ∈ Finset.univ.filter (fun i : Fin r => i ≤ k), (s i).re < 0 := by
    intro i hi
    have hik : i ≤ k := (Finset.mem_filter.1 hi).2
    obtain ⟨j, hj, h⟩ := hex i (hdc k hk i hik)
    have hi1 : i.val < G.p + G.q := lt_of_lt_of_le i.2 hr
    have h1 : (j : ℝ) + 1 ≤ (G.p + G.q : ℕ) := by exact_mod_cast (by omega : j + 1 ≤ G.p + G.q)
    have h2 : (2 * (G.p + G.q) + 1 : ℕ) < (a' : ℝ) := by exact_mod_cast hab
    have h3 : (a' : ℝ) < a := by exact_mod_cast hlt
    push_cast at h1 h2
    rcases h with h | h <;> rw [h] <;> linarith
  have hne : (Finset.univ.filter (fun i : Fin r => i ≤ k)).Nonempty := ⟨k, by simp⟩
  have := Finset.sum_lt_sum_of_nonempty hne neg
  simpa using this

end GlobalTheory.ThK.ExpSmall

end
