import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDetProdConstAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralRationalFrameExpansionSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericGlLocalComponentExponentLeOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetShalikaExcludesRatioGapStatement

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
  GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK.DetProd

namespace GlobalTheory.ThK.ExpVBlocks

theorem downClosed : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M,
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin (a + a')) (Fin r) E), IsWittFrame σ (c • G.W.J.map σ) Xf Yf →
        ∀ K, IsMaxCpt σ (c • G.W.J.map σ) K →
          IsAut σ (c • G.W.J.map σ) K (fun x => G.M.I om Φ ((toGAd hσ G.W.J hc).symm x)) →
          ∀ S s, GlobalTheory.StdPar.IsCuspExp σ (c • G.W.J.map σ) Xf Yf S K (fun x => G.M.I om Φ ((toGAd hσ G.W.J hc).symm x)) s →
            ∀ k ∈ S, ∀ i, i ≤ k → i ∈ S := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' hKP hT c hc hcσ Φ hΦ r Xf Yf hW K hK hA S s hS k hk i hik
  haveI : IsTotallyComplex E := hT.base.cm.2.1
  classical
  by_contra hi
  have hne : (S.filter (fun j => i ≤ j)).Nonempty := ⟨k, Finset.mem_filter.2 ⟨hk, hik⟩⟩
  obtain ⟨hk₀S, hik₀'⟩ := Finset.mem_filter.1 (Finset.min'_mem _ hne)
  set k₀ := (S.filter (fun j => i ≤ j)).min' hne with hk₀def
  have hmin : ∀ j ∈ S, i ≤ j → k₀ ≤ j := fun j hj hij => Finset.min'_le _ _ (Finset.mem_filter.2 ⟨hj, hij⟩)
  have hik₀ : i < k₀ := lt_of_le_of_ne hik₀' fun e => hi (e ▸ hk₀S)

  have hbelow : ∀ j ∈ S, j < k₀ → j < i := fun j hj hjk =>
    lt_of_not_ge fun hij => absurd (hmin j hj hij) (not_le.2 hjk)
  let P := S.filter (fun j => j < k₀)
  let l : ℕ := if h : P.Nonempty then (P.max' h).val + 1 else 0
  have hl1 : ∀ j ∈ S, j < k₀ → j.val < l := fun j hj hjk => by
    have hP : P.Nonempty := ⟨j, Finset.mem_filter.2 ⟨hj, hjk⟩⟩
    have := Finset.le_max' P j (Finset.mem_filter.2 ⟨hj, hjk⟩)
    simp only [l, dif_pos hP]
    have : j.val ≤ (P.max' hP).val := this
    omega
  have hl2 : l = 0 ∨ ∃ j ∈ S, j.val + 1 = l := by
    by_cases hP : P.Nonempty
    · exact Or.inr ⟨P.max' hP, (Finset.mem_filter.1 (Finset.max'_mem P hP)).1, by simp only [l, dif_pos hP]⟩
    · exact Or.inl (by simp only [l, dif_neg hP])
  have hli : l ≤ i.val := by
    by_cases hP : P.Nonempty
    · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 (Finset.max'_mem P hP)
      have : (P.max' hP) < i := hbelow _ h1 h2
      have : (P.max' hP).val < i.val := this
      simp only [l, dif_pos hP]
      omega
    · simp only [l, dif_neg hP]; omega
  have hik₀v : i.val < k₀.val := hik₀
  obtain ⟨n, hn⟩ : ∃ n, n = k₀.val + 1 - l := ⟨_, rfl⟩
  obtain ⟨w, τ, ρ, x, x', χ₁, χ₂, hxx, hu, hloc, h1, h2, hp, hgap⟩ :=
    GlobalTheory.T.theta_integral_rational_frame_expansion_second F E σ hσ B a a' G X om om' hKP hT c hc hcσ Φ hΦ r Xf Yf hW K hK hA S s hS k₀ l hk₀S (by omega) hl1 hl2 n hn
  obtain ⟨hx, hx'⟩ := GlobalTheory.T.generic_gl_local_component_exponent_le_one E n τ w ρ x x' χ₁ χ₂ hKP.genericityGL (by omega) hloc h1 h2 hp
  obtain rfl : x = 1 := by omega
  obtain rfl : x' = 1 := by omega
  subst hxx
  exact GlobalTheory.T.jacquet_shalika_excludes_ratio_gap E τ w ρ χ₁ χ₂ hKP.jacquetShalika.2 hu hloc h1 h2 hp (hgap rfl rfl)

end GlobalTheory.ThK.ExpVBlocks
