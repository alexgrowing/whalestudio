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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanPolynomialTensorCharacter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsSubOfDisjoint
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFixedDegreeFiltrationStepUpStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open GlobalTheory.RealLift GlobalTheory.RealLift.Main Formalism.BasicNotions.TH
open scoped Classical

namespace GlobalTheory.EvenStep

theorem exists_upq_decomp {R S : ℕ} (Z : Formalism.BasicNotions.TH.Mat R S) :
    ∃ A B : Formalism.BasicNotions.TH.Mat R S, A ∈ upq R S ∧ B ∈ upq R S ∧ Z = A + Complex.I • B := by
  have hJ : Jm R S * Jm R S = 1 := by
    rw [GlobalTheory.KFixIrr.jm_eq_diagonal, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]; congr 1; funext i; rcases i with i | i <;> simp
  have hJH : (Jm R S)ᴴ = Jm R S := by
    rw [GlobalTheory.KFixIrr.jm_eq_diagonal, Matrix.diagonal_conjTranspose]; congr 1; funext i; rcases i with i | i <;> simp
  refine ⟨(1 / 2 : ℂ) • (Z + conjR Z), (-(Complex.I / 2)) • (Z - conjR Z), ?_, ?_, ?_⟩
  · show _ * Jm R S + Jm R S * _ = 0
    simp only [conjR, adjZ, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_neg,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJH, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, hJ, Matrix.mul_one]
    simp only [← Matrix.mul_assoc, hJ, Matrix.one_mul]
    ext i j; simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]; try ring
  · show _ * Jm R S + Jm R S * _ = 0
    simp only [conjR, adjZ, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_neg,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJH, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, hJ, Matrix.mul_one]
    simp only [← Matrix.mul_assoc, hJ, Matrix.one_mul]
    ext i j; simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]; try ring
  · ext i j; simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]; ring_nf; rw [Complex.I_sq]; ring

end GlobalTheory.EvenStep

namespace GlobalTheory.EvenStep

theorem even_step : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
      ∀ k : ℕ, ∀ f ∈ fockDeg G.M B.ψ B.emb (fixDeg B G.M om + 2 * k + 2), IsKFix B om f →
        f ∈ fockDeg G.M B.ψ B.emb (fixDeg B G.M om + 2 * k + 1) ⊔ Submodule.span ℂ
          {f₁ | ∃ γ ∈ Lines σ G.W, ∃ g ∈ fockDeg G.M B.ψ B.emb (fixDeg B G.M om + 2 * k + 1), IsKFix B om g ∧
            ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) g f₁} := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM k f hf hfix
  obtain ⟨hb, hg, hc, hw, hw'⟩ := hM.triple
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
  have L2 := GlobalTheory.KFixIrr.kFix_iff_mem_chiPart i_actslaws i_lineex (i_kline i_lineex) F E σ B _ _ _ _ _ _ G.V G.W om A Φ c
    hb.cm hA1 hAθ hinj hW1' hadm
  set m := fixDeg B G.M om + 2 * k with hm

  have hder : ∀ (w : InfinitePlace F) (Y : Formalism.BasicNotions.TH.Mat (a + a' - (G.p + G.q)) (G.p + G.q)), Y ∈ upq _ _ →
      ∀ T₁ ∈ GlobalTheory.KFixIrr.chiPart (InfinitePlace F) (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) c ⊓
        GlobalTheory.KFixIrr.degLE (InfinitePlace F) (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) m,
      Φ (atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q)) w
        (fockAct2 _ _ _ _ Y) T₁) ∈
      fockDeg G.M B.ψ B.emb (m + 1) ⊔ Submodule.span ℂ
          {f₁ | ∃ γ ∈ Lines σ G.W, ∃ g ∈ fockDeg G.M B.ψ B.emb (m + 1), IsKFix B om g ∧
            ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) g f₁} := by
    intro w Y hY T₁ hT₁
    set Y' : InfinitePlace F → Formalism.BasicNotions.TH.Mat (a + a' - (G.p + G.q)) (G.p + G.q) := Function.update 0 w Y with hY'
    have hY'u : ∀ w', Y' w' ∈ upq _ _ := by
      intro w'
      by_cases h : w' = w
      · subst h; simpa [hY'] using hY
      · rw [hY', Function.update_of_ne h]; show (0 : Formalism.BasicNotions.TH.Mat _ _)ᴴ * _ + _ * 0 = 0; simp
    obtain ⟨γ, hγ, hgen⟩ := i_lineex F E σ _ _ _ B.emb (incM F G.W.J) Complex.I C hb.cm hC1 Y' hY'u
    have h2 := hW2 γ hγ Y' hgen T₁
    have hsum : sumPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q))
        (fun w' => fockAct2 _ _ _ _ (Y' w') + (((B.mβ w' : ℂ) / 2) * (Y' w').trace) • 1) =
        atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q)) w
          (fockAct2 _ _ _ _ Y + (((B.mβ w : ℂ) / 2) * Y.trace) • 1) := by
      unfold sumPl
      rw [Finset.sum_eq_single w]
      · simp [hY']
      · intro w' _ hne
        simp only [hY', Function.update_of_ne hne, Pi.zero_apply, map_zero, Matrix.trace_zero, mul_zero, zero_smul,
          add_zero]
        exact GlobalTheory.KFixIrr.atPl_zero' w'
      · intro h; exact absurd (Finset.mem_univ w) h
    rw [hsum] at h2
    have hAD := (i_actslaws F (Fin a × Fin (a + a')) (Φ T₁) _ (Φ T₁)).1 _ (fun t => map_zero _) h2
    rw [GlobalTheory.KFixIrr.atPl_shift_apply, map_add, map_smul] at hAD
    have hg1 : Φ T₁ ∈ fockDeg G.M B.ψ B.emb (m + 1) := by
      rw [L1]; exact ⟨T₁, GlobalTheory.KFixIrr.degLE_mono (Nat.le_succ m) hT₁.2, rfl⟩
    have hgfix : IsKFix B om (Φ T₁) := (L2 T₁).2 hT₁.1
    have e : Φ (atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q)) w
        (fockAct2 _ _ _ _ Y) T₁) = (Φ (atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q)) w
        (fockAct2 _ _ _ _ Y) T₁) + (((B.mβ w : ℂ) / 2) * Y.trace) • Φ T₁) - (((B.mβ w : ℂ) / 2) * Y.trace) • Φ T₁ := by
      abel
    rw [e]
    refine Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.subset_span ⟨γ, hγ, Φ T₁, hg1, hgfix, hAD⟩))
      (Submodule.smul_mem _ _ (Submodule.mem_sup_left hg1))
  rw [L1] at hf
  obtain ⟨T, hT, rfl⟩ := hf
  have hTc := (L2 T).1 hfix
  by_cases hT0 : T = 0
  · rw [hT0, map_zero]; exact Submodule.zero_mem _
  have hne : {m | ∃ f ∈ fockDeg G.M B.ψ B.emb m, f ≠ 0 ∧ IsKFix B om f}.Nonempty :=
    ⟨_, Φ T, by rw [L1]; exact ⟨T, hT, rfl⟩, fun h => hT0 (hinj (by rw [h, map_zero])), hfix⟩
  obtain ⟨f₀, hf₀, hf₀0, hf₀fix⟩ := Nat.sInf_mem hne
  rw [L1] at hf₀
  obtain ⟨T₀, hT₀, rfl⟩ := hf₀
  have hstep := GlobalTheory.T.k_fixed_degree_filtration_step_up (InfinitePlace F) _ _ _ _ c m T₀ T (fun h => hf₀0 (by rw [h, map_zero]))
    ⟨(L2 T₀).1 hf₀fix, GlobalTheory.KFixIrr.degLE_mono (by rw [hm]; exact Nat.le_add_right _ _) hT₀⟩ ⟨hTc, hT⟩
  have hle : GlobalTheory.KFixIrr.degLE (InfinitePlace F) (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) (m + 1) ⊔
      Submodule.span ℂ {T' | ∃ (w : InfinitePlace F) (Z : Formalism.BasicNotions.TH.Mat (a + a' - (G.p + G.q)) (G.p + G.q)),
        ∃ T₁ ∈ GlobalTheory.KFixIrr.chiPart (InfinitePlace F) (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) c ⊓
          GlobalTheory.KFixIrr.degLE (InfinitePlace F) (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) m,
        T' = atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q)) w
          (fockAct2 _ _ _ _ Z) T₁} ≤
      (fockDeg G.M B.ψ B.emb (m + 1) ⊔ Submodule.span ℂ
          {f₁ | ∃ γ ∈ Lines σ G.W, ∃ g ∈ fockDeg G.M B.ψ B.emb (m + 1), IsKFix B om g ∧
            ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) g f₁}).comap Φ := by
    refine sup_le (fun T' hT' => Submodule.mem_comap.2 (Submodule.mem_sup_left (by rw [L1]; exact ⟨T', hT', rfl⟩)))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨w, Z, T₁, hT₁, rfl⟩
    obtain ⟨A', B', hA', hB', rfl⟩ := exists_upq_decomp Z
    rw [SetLike.mem_coe, Submodule.mem_comap, map_add, map_smul, GlobalTheory.TensIrr.atPl_add, LinearMap.add_apply, map_add,
      GlobalTheory.TensIrr.atPl_smul, LinearMap.smul_apply, map_smul]
    exact Submodule.add_mem _ (hder w A' hA' T₁ hT₁) (Submodule.smul_mem _ _ (hder w B' hB' T₁ hT₁))
  exact hle hstep

end GlobalTheory.EvenStep

end
