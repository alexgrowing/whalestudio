import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameThetaIntegralBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameThetaIntegralDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSignatureSumStatement

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

namespace GlobalTheory.ThK.ExpV

theorem negative : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M,
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin (a + a')) (Fin r) E), IsWittFrame σ (c • G.W.J.map σ) Xf Yf →
        ∀ K, IsMaxCpt σ (c • G.W.J.map σ) K →
          IsAut σ (c • G.W.J.map σ) K (fun x => G.M.I om Φ ((toGAd hσ G.W.J hc).symm x)) →
          ∀ S s, GlobalTheory.StdPar.IsCuspExp σ (c • G.W.J.map σ) Xf Yf S K (fun x => G.M.I om Φ ((toGAd hσ G.W.J hc).symm x)) s →
            ∀ k ∈ S, ∑ i with i ≤ k, (s i).re < 0 := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' hKP hT c hc hcs Φ hΦ r Xf Yf hW K hK hA S s hs k hk
  have hb := GlobalTheory.T.witt_frame_theta_integral_bound F E σ hσ B a a' G X om om' hKP hT c hc hcs Φ hΦ r Xf Yf hW K hK hA S s hs
  have he := GlobalTheory.T.witt_frame_theta_integral_dual F E σ hσ B a a' G X om om' hKP hT c hc hcs Φ hΦ r Xf Yf hW K hK hA S s hs hb
  have hr := GlobalTheory.T.witt_rank_le_signature_sum F E σ B a a' G X om om' hT c hc hcs r Xf Yf hW
  have hlt : a' < a := hT.geo.lt
  have hbig : 2 * (G.p + G.q) + 1 < a' := hT.geo.aBig
  have key : ∀ i ∈ Finset.univ.filter (fun i : Fin r => i ≤ k), (s i).re < 0 := by
    intro i hi
    have hik : i ≤ k := (Finset.mem_filter.1 hi).2
    obtain ⟨j, hj, h⟩ := he i (hb k hk i hik)
    have hjr : j < G.p + G.q := lt_of_lt_of_le (lt_of_le_of_lt hj i.2) hr
    have h1 : ((j : ℕ) : ℝ) + 1 ≤ ((G.p + G.q : ℕ) : ℝ) := by exact_mod_cast hjr
    have h2 : (2 * ((G.p + G.q : ℕ) : ℝ)) + 1 < (a' : ℝ) := by exact_mod_cast hbig
    have h3 : (a' : ℝ) < a := by exact_mod_cast hlt
    rcases h with h | h <;> rw [h] <;> linarith
  have hne : (Finset.univ.filter (fun i : Fin r => i ≤ k)).Nonempty := ⟨k, by simp⟩
  exact Finset.sum_neg key hne

end GlobalTheory.ThK.ExpV
