import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDetProdConstAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSignatureSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolDataWittFrameDecompStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetSubquotientCharExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedLocalCharactersGoodStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK.DetProd

namespace GlobalTheory.ThK.Heightsridge

open GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LFun

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem isUnram_mul {k : Type} [Field k] [ValuativeRel k] {μ ν : kˣ →* ℂˣ} (hμ : IsUnram μ) (hν : IsUnram ν) :
    IsUnram (μ * ν) := fun x hx => by rw [MonoidHom.mul_apply, hμ x hx, hν x hx, one_mul]

theorem norm_absPow {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (t : ℝ) (y : kˣ) : ‖((absPow k (t : ℂ) y : ℂˣ) : ℂ)‖ = nabs k y ^ t := by
  rw [val_absPow_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (nabs_pos' k y) t)]

theorem bridge : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M,
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin (a + a')) (Fin r) E), IsWittFrame σ (c • G.W.J.map σ) Xf Yf →
        ∀ K, IsMaxCpt σ (c • G.W.J.map σ) K →
          IsAut σ (c • G.W.J.map σ) K (fun x => G.M.I om Φ ((toGAd hσ G.W.J hc).symm x)) →
          ∀ S s, GlobalTheory.StdPar.IsCuspExp σ (c • G.W.J.map σ) Xf Yf S K (fun x => G.M.I om Φ ((toGAd hσ G.W.J hc).symm x)) s →
            ∀ (k : Fin r) (l : ℕ), k ∈ S → l ≤ k.val → (∀ j ∈ S, j < k → j.val < l) → (l = 0 ∨ ∃ j ∈ S, j.val + 1 = l) →
            ∀ n : ℕ, n = k.val + 1 - l →
            ∃ (w : HeightOneSpectrum (𝓞 E)) (τ : GlobalTheory.CuspRep.CuspSub E n)
              (ρ : GlobalTheory.CuspRep.SmIrr (GL (Fin n) (w.adicCompletion E))) (x x' : ℕ) (χ₁ χ₂ : (w.adicCompletion E)ˣ →* ℂˣ),
              x + x' = n ∧ (GlobalTheory.CuspRep.CG.mk τ).IsUnitary ∧ τ.IsLocComp w ρ ∧ IsUnramAt w χ₁ ∧ IsUnramAt w χ₂ ∧
                IsDetProdConstAt w x x' χ₁ χ₂ ρ.ρ ∧ (x = 1 → x' = 1 → RatioGapAt w χ₁ χ₂) := by
  intro F E _ _ _ _ _ _ σ hσ B a a' G X om om' hKP hT c hc hσc Φ hΦ r Xf Yf hW K hK hA S s hS k l hk hl hlt hl0 n hn
  have hr := GlobalTheory.WittBoundSkew.wittIndex_le F E σ B a a' G X om om' hT c hc hσc r Xf Yf hW
  have hkr := k.2
  have h1 := hT.geo.aBig
  have h2 := hT.geo.eBig
  have h3 := hT.geo.lt
  obtain ⟨t, ht⟩ := hT.geo.even
  have hd : l + n ≤ a + a' := by omega
  obtain ⟨w, τ, ρ, z, hw, hu, hloc, hsq⟩ :=
    GlobalTheory.T.pol_data_witt_frame_decomp F E σ hσ B a a' G X om om' hKP hT c hc hσc Φ hΦ r Xf Yf hW K hK hA S s hS k l hk hl hlt hl0 n hn hd
  obtain ⟨hα, hβ⟩ := GlobalTheory.T.unramified_local_characters_good F E σ B a a' G X om om' hT w hw
  change IsUnram _ at hα hβ
  have hα' := isUnram_mul hα (isUnram_absPow _ (z : ℂ))
  have hβ' := isUnram_mul hβ (isUnram_absPow _ (z : ℂ))
  obtain ⟨x, x', j, j', hxx, hjj, hja, hja', hdp⟩ :=
    GlobalTheory.T.jacquet_subquotient_char_exists _ hKP.geometricLemmaFiltration a a' l n hd _ _ hα' hβ' ρ hsq
  refine ⟨w, τ, ρ, x, x', _, _, hxx, hu, hloc, isUnram_mul hα' (isUnram_absPow _ _),
    isUnram_mul hβ' (isUnram_absPow _ _), hdp, fun hx hx' => ?_⟩
  subst hx hx'
  have he : a = a' + 2 * ((a - a') / 2) := by omega
  have he' : (a : ℝ) = a' + 2 * (((a - a') / 2 : ℕ) : ℝ) := by exact_mod_cast he
  have hjr : (j : ℝ) + j' + 2 ≤ G.p + G.q := by exact_mod_cast (show j + j' + 2 ≤ G.p + G.q by omega)
  have hb2 : (2 * (G.p + G.q) + 1 : ℝ) < (((a - a') / 2 : ℕ) : ℝ) := by exact_mod_cast h2
  refine ⟨((1 : ℝ) - a) / 2 + j + (((1 : ℕ) : ℝ) - 1) / 2 - (((1 : ℝ) - a') / 2 + j' + (((1 : ℕ) : ℝ) - 1) / 2), ?_,
    fun y => ?_⟩
  · refine lt_abs.2 (Or.inr ?_)
    push_cast
    nlinarith
  · have hpos := nabs_pos' (w.adicCompletion E) y
    simp only [MonoidHom.mul_apply, Units.val_mul, norm_div, norm_mul, norm_locChar, one_mul, norm_absPow]
    rw [Real.rpow_sub hpos]
    field_simp

end GlobalTheory.ThK.Heightsridge
