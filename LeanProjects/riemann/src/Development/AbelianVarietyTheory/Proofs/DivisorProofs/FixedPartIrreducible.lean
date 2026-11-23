import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixPartEqBotOfLt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemDegLE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanThetaPolynomialLiftExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanPolynomialTensorCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanPolynomialTensorWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFixedIrreducibleLowestDegreeStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

open scoped Classical

open GlobalTheory.RealLift GlobalTheory.RealLift.Main Formalism.BasicNotions.TH

namespace GlobalTheory.KFixIrr

theorem fixPart_irreducible : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ m : ℕ, m ≤ fixDeg B G.M om → ∀ H : Submodule ℂ (SInf F (Fin a × Fin (a + a'))),
      H ≤ fixPart B G.M om m → KStabUp B om H → H = ⊥ ∨ H = fixPart B G.M om m := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT m hm H hH hK
  obtain ⟨hb, hg, hc, hw, hw'⟩ := hT
  choose A hA hAθ using fun w => i_frameex _ _ _ _ _ (hg.hV.sig w) (hg.hV.cartan w)
  choose C hC hCθ using fun w => i_frameex _ _ _ _ _ (hg.hW.sig w) (hg.hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_piInf, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F G.W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [incM_map_piInf]; exact hC w
  have fr : Framed B.emb (incM F G.V.J) (incM F G.W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  have hvl := i_vacline i_derex
  have hfe := i_fockex i_derex
  have hsec := i_liesecond hKP.base i_derex hfe hvl (i_liescalar hKP.base i_derex hvl)
  have hfst := i_liefirst hsec
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := i_polrange i_actslaws i_derex hvl F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hw
  have hW2 := hsec F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C Φ _ X.β B.mβ hb.cm hb.std fr hΦ hwp.1 hc.expβ
  obtain ⟨d, hd, hB1⟩ := hwp.2.1
  have hW1 := hfst F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co d 1 Complex.I A C Φ _ _ _ hb.cm hb.std fr hΦ hd hB1
    (hasExp_div B.emb hc.expβ hc.expα)
  have hadm := fun g => (hwp.isUSplitting).adm g
  let c : InfinitePlace F → ℚ := fun w => ((B.mα w - B.mβ w : ℤ) : ℚ) / 2
  have ec : (fun w => -((c w : ℚ) : ℂ)) = fun w => ((B.mβ w - B.mα w : ℤ) : ℂ) / 2 := by
    funext w; simp only [c]; push_cast; ring
  have hW1' : ActsBy B.emb A (om.comp (MonoidHom.inl _ _)) Φ (fockAct1 _ _ _ _) (fun w => -((c w : ℚ) : ℂ)) := by
    rw [ec]; exact hW1
  have hinj : Function.Injective Φ := hΦ.1
  have L1 := GlobalTheory.T.archimedean_theta_polynomial_lift_exists i_actslaws i_derex hvl F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ
  have L2 := GlobalTheory.T.archimedean_polynomial_tensor_character i_actslaws i_lineex (i_kline i_lineex) F E σ B _ _ _ _ _ _ G.V G.W om A Φ c hb.cm hA1 hAθ hinj hW1' hadm
  have key : ∀ k, fixPart B G.M om k =
      (GlobalTheory.KFixIrr.chiPart (InfinitePlace F) (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) c ⊓ GlobalTheory.KFixIrr.degLE (InfinitePlace F) (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) k).map Φ := by
    intro k
    have hs : {f | f ∈ fockDeg G.M B.ψ B.emb k ∧ IsKFix B om f} =
        Φ '' ((GlobalTheory.KFixIrr.chiPart (InfinitePlace F) (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) c ⊓ GlobalTheory.KFixIrr.degLE (InfinitePlace F) (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) k : Submodule ℂ _) : Set _) := by
      ext f
      constructor
      · rintro ⟨hf, hfix⟩
        rw [L1 k] at hf
        obtain ⟨T, hT, rfl⟩ := hf
        exact ⟨T, ⟨(L2 T).1 hfix, hT⟩, rfl⟩
      · rintro ⟨T, ⟨h1, h2⟩, rfl⟩
        exact ⟨by rw [L1 k]; exact ⟨T, h2, rfl⟩, (L2 T).2 h1⟩
    rw [fixPart, hs, Submodule.span_image, Submodule.span_eq]
  have bot : ∀ k < fixDeg B G.M om, GlobalTheory.KFixIrr.chiPart (InfinitePlace F) (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) c ⊓ GlobalTheory.KFixIrr.degLE (InfinitePlace F) (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) k = ⊥ := by
    intro k hk
    have h0 := fixPart_eq_bot_of_lt B G.M om hk
    rw [key] at h0
    rw [← Submodule.comap_map_eq_of_injective hinj (GlobalTheory.KFixIrr.chiPart (InfinitePlace F) (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) c ⊓ GlobalTheory.KFixIrr.degLE (InfinitePlace F) (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) k), h0,
      Submodule.comap_bot, LinearMap.ker_eq_bot.2 hinj]
  let N := H.comap Φ
  have hHpol : H ≤ LinearMap.range Φ := hr ▸ hH.trans (fixPart_le_pol B G.M om m)
  have hHN : H = N.map Φ := (Submodule.map_comap_eq_of_le hHpol).symm
  have hNle : N ≤ GlobalTheory.KFixIrr.chiPart (InfinitePlace F) (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) c ⊓ GlobalTheory.KFixIrr.degLE (InfinitePlace F) (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) m := by
    intro T hT
    have h1 : Φ T ∈ (GlobalTheory.KFixIrr.chiPart (InfinitePlace F) (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) c ⊓ GlobalTheory.KFixIrr.degLE (InfinitePlace F) (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) m).map Φ := key m ▸ hH hT
    obtain ⟨T', hT', e⟩ := h1
    exact hinj e ▸ hT'
  have hNst := GlobalTheory.T.archimedean_polynomial_tensor_weight i_actslaws i_lineex F E σ B _ _ _ _ _ _ G.V G.W om C Φ _ hb.cm hC1 hCθ hinj hW2 hadm N
    (fun k hk T hT f₁ h => hHN ▸ hK k hk (Φ T) hT f₁ h)
  have hPR : a - G.p ≤ a + a' - (G.p + G.q) := by have := hg.aBig; omega
  have hQS : G.p ≤ G.p + G.q := Nat.le_add_right _ _
  have hnum : ∀ w, ∃ k k' : ℕ, 0 < k ∧ 0 < k' ∧ c w - cPair (a + a' - (G.p + G.q)) (G.p + G.q) = k ∧
      c w + cPair (a + a' - (G.p + G.q)) (G.p + G.q) = k' := by
    intro w
    have hk := hg.kappa w
    have hev := i_parity F E σ B a a' G X om om' ⟨hb, hg, hc, hw, hw'⟩ w
    obtain ⟨j, hj⟩ := hev
    obtain ⟨i, hi⟩ := hg.even
    have h1 := hg.eBig
    have h2 := hg.aBig
    have hle : G.p + G.q ≤ a + a' := by omega
    have hR : ((a + a' - (G.p + G.q) : ℕ) : ℚ) = (i : ℚ) + i - ((G.p : ℚ) + G.q) := by
      rw [Nat.cast_sub hle, hi]; push_cast; ring
    refine ⟨(j - i + (G.p + G.q : ℕ)).toNat, (j + i - (G.p + G.q : ℕ)).toNat, by omega, by omega, ?_, ?_⟩
    · rw [show (((j - i + (G.p + G.q : ℕ)).toNat : ℕ) : ℚ) = ((j - i + (G.p + G.q : ℕ) : ℤ) : ℚ) from by
        exact_mod_cast Int.toNat_of_nonneg (by omega)]
      simp only [c, cPair, hj, hR]; push_cast; ring
    · rw [show (((j + i - (G.p + G.q : ℕ)).toNat : ℕ) : ℚ) = ((j + i - (G.p + G.q : ℕ) : ℤ) : ℚ) from by
        exact_mod_cast Int.toNat_of_nonneg (by omega)]
      simp only [c, cPair, hj, hR]; push_cast; ring
  rcases GlobalTheory.T.k_fixed_irreducible_lowest_degree _ _ _ _ _ c hPR hQS hnum m (fun m' hm' => bot m' (lt_of_lt_of_le hm' hm)) N hNle hNst with h | h
  · left; rw [hHN, h, Submodule.map_bot]
  · right; rw [hHN, h, ← key]

end GlobalTheory.KFixIrr

end
