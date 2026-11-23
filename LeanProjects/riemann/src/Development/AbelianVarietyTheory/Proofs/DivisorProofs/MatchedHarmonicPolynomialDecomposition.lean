import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdaptedFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensInclInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixPartEqBotOfLt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemDegLE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerUpperFixedPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartLeFixedPartImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanPolynomialTensorCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedPartIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowDegreeLeFixedDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedHarmonicPolynomialIntegral
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.FockIncl

noncomputable section
open scoped Classical
open GlobalTheory.RealLift.Main

namespace GlobalTheory.HarmInj

theorem harmTy_le_ker {P Q R S : ℕ} (x : ℚ) (X : Mat P Q) (hX : IsKC X) :
    harmTy P Q R S x ≤ LinearMap.ker (fockAct1 P Q R S X - ((x : ℂ) * X.trace) • 1) := by
  refine Submodule.span_le.2 ?_
  rintro f ⟨_, hf⟩
  simp [sub_eq_zero, hf X hX]

theorem tensHarm_le_chiPart {F : Type} [Field F] [NumberField F] {P Q R S : ℕ} (x : InfinitePlace F → ℚ) :
    tensHarm F P Q R S x ≤ GlobalTheory.KFixIrr.chiPart (InfinitePlace F) P Q R S x := by
  refine Submodule.span_le.2 ?_
  rintro T ⟨f, hf, rfl⟩
  rw [SetLike.mem_coe, GlobalTheory.KFixIrr.mem_chiPart]
  intro w X hX
  have h1 : fockAct1 P Q R S X (f w) = ((x w : ℂ) * X.trace) • f w := by
    have := harmTy_le_ker (R := R) (S := S) (x w) X hX (hf w)
    simpa [sub_eq_zero] using this
  rw [atPl, PiTensorProduct.map_tprod]
  have e : (fun i => (Function.update (fun i => (LinearMap.id : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] _)) w
      (fockAct1 P Q R S X)) i (f i)) = Function.update f w (((x w : ℂ) * X.trace) • f w) := by
    funext i
    by_cases h : i = w
    · subst h; simp [h1]
    · simp [Function.update_of_ne h]
  rw [e, (PiTensorProduct.tprod ℂ).map_update_smul, Function.update_eq_self]

theorem pInf_injOn_harm : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (Rm : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' Rm Rf →
    ∀ (P Q Rn Sn : ℕ) (A : InfinitePlace F → Matrix (Fin a) (Ix P Q) ℂ) (C : InfinitePlace F → Matrix (Fin (a + a')) (Ix Rn Sn) ℂ)
      (Φ : Tens F P Q Rn Sn →ₗ[ℂ] SInf F (Fin a × Fin (a + a'))), GlobalTheory.FockBridge.IsFockData B G.M A C Φ →
      ∀ f ∈ (tensHarm F P Q Rn Sn (halfKap B)).map Φ, Rm.p f = 0 → f = 0 := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' Rm Rf hM P Q Rn Sn A C Φ hF f hf hpf
  obtain ⟨hb, hg, hc, hw, hw'⟩ := hM.triple
  obtain ⟨⟨fr, hAθ, hCθ⟩, hΦ⟩ := hF
  have hvl := i_vacline i_derex
  have hfe := i_fockex i_derex
  have hsec := i_liesecond hKP.base i_derex hfe hvl (i_liescalar hKP.base i_derex hvl)
  have hfst := i_liefirst hsec
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hw
  obtain ⟨d, hd, hB1⟩ := hwp.2.1
  have hW1 := hfst F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co d 1 Complex.I A C Φ _ _ _ hb.cm hb.std fr hΦ hd hB1
    (hasExp_div B.emb hc.expβ hc.expα)
  have hadm := fun g => (hwp.isUSplitting).adm g
  let c : InfinitePlace F → ℚ := halfKap B
  have ec : (fun w => -((c w : ℚ) : ℂ)) = fun w => ((B.mβ w - B.mα w : ℤ) : ℂ) / 2 := by
    funext w; simp only [c, halfKap]; push_cast; ring
  have hW1' : ActsBy B.emb A (om.comp (MonoidHom.inl _ _)) Φ (fockAct1 _ _ _ _) (fun w => -((c w : ℚ) : ℂ)) := by
    rw [ec]; exact hW1
  have hinj : Function.Injective Φ := hΦ.1
  have L2 := GlobalTheory.KFixIrr.kFix_iff_mem_chiPart i_actslaws i_lineex (i_kline i_lineex) F E σ B _ _ _ _ _ _ G.V G.W om A Φ c
    hb.cm fr.2.1 hAθ hinj hW1' hadm
  have hdeg := GlobalTheory.T.low_degree_le_fixed_degree hKP F E σ B a a' G X om om' Rm Rf hM
  have hlowH := (GlobalTheory.T.matched_harmonic_polynomial_integral hKP F E σ B a a' G X om om' Rm Rf hM P Q Rn Sn A C Φ ⟨⟨fr, hAθ, hCθ⟩, hΦ⟩).1
  have step1 : ∀ T ∈ tensHarm F P Q Rn Sn c, Φ T ∈ fixPart B G.M om (fixDeg B G.M om) := by
    intro T hT
    have hfix : IsKFix B om (Φ T) := (L2 T).2 (tensHarm_le_chiPart c hT)
    exact Submodule.subset_span ⟨fockDeg_mono G.M B.ψ B.emb hdeg (hlowH ⟨T, hT, rfl⟩), hfix⟩
  have hfP := fixPart_le_pol B G.M om (fixDeg B G.M om)
  let H := fixPart B G.M om (fixDeg B G.M om) ⊓ LinearMap.ker Rm.p
  have hHs : KStabUp B om H := by
    intro k hk g hg g₁ hg₁
    refine ⟨GlobalTheory.IndLine.fixPart_kStabUp hKP F E σ B a a' G X om om' hM.triple _ k hk g hg.1 g₁ hg₁, ?_⟩
    have h0 : Acts (evI F) (om' (1, k)) (⇑(0 : SInf F (Fin a' × Fin (a + a')))) ⇑(0 : SInf F (Fin a' × Fin (a + a'))) := by
      intro r _
      have hz : tens (evI F) ⇑(0 : SInf F (Fin a' × Fin (a + a'))) r = 0 := by
        funext x; simp [tens]
      rw [hz, map_zero]
    have h2 := hM.real.cpt k hk g (hfP hg.1) 0 (Submodule.zero_mem _) g₁ 0 hg₁ h0
      (by rw [map_zero]; exact hg.2)
    show Rm.p g₁ = 0
    rw [h2, map_zero]
  rcases GlobalTheory.T.fixed_part_irreducible hKP F E σ B a a' G X om om' hM.triple _ le_rfl H inf_le_left hHs with h | h
  · obtain ⟨T, hT, rfl⟩ := hf
    have h' : Φ T ∈ H := ⟨step1 T hT, hpf⟩
    rw [h, Submodule.mem_bot] at h'
    exact h'
  · exfalso
    haveI := hM.real.nontriv
    have hkill : (fixPart B G.M om (fixDeg B G.M om)).map Rm.p = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨g, hg, rfl⟩
      have h' : g ∈ H := h ▸ hg
      exact (Submodule.mem_bot ℂ).2 h'.2
    have hlow := GlobalTheory.LowFixCover.lowPartInf_le_fixPart hKP F E σ B a a' G X om om' Rm Rf hM
    have hmono : fixPart B G.M om (lowDegInf B G.M Rm.p) ≤ fixPart B G.M om (fixDeg B G.M om) :=
      Submodule.span_mono fun g hg => ⟨fockDeg_mono G.M B.ψ B.emb hdeg hg.1, hg.2⟩
    obtain ⟨y, hy⟩ := exists_ne (0 : Rm.Pi)
    have hy' : y ∈ (G.M.Pol B.ψ B.emb).map Rm.p := hM.real.quot.onto ▸ Submodule.mem_top
    obtain ⟨g, hg, rfl⟩ := hy'
    apply lowPartInf_ne_bot B G.M Rm.p ⟨g, hg, hy⟩
    rw [eq_bot_iff, ← hkill]
    exact hlow.trans (Submodule.map_mono hmono)

end GlobalTheory.HarmInj
