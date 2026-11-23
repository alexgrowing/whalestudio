import Mathlib
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBMatchedThetaLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDegreeEvenMapLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionHomogeneousEigenvector
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.FockIncl

namespace GlobalTheory.HarmLow

private theorem frame_trace {n P Q : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} {C : Matrix (Fin n) (Ix P Q) ℂ}
    (hC : IsFrame M C) (hθ : θ * C = C * Formalism.BasicNotions.TH.Jm P Q) : (n : ℂ) = P + Q ∧ θ.trace = P - Q := by
  obtain ⟨h1, C', h2⟩ := hC
  have hJJ : Formalism.BasicNotions.TH.Jm P Q * Formalism.BasicNotions.TH.Jm P Q = 1 := by
    simp [Formalism.BasicNotions.TH.Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply]
  have hJt : (Formalism.BasicNotions.TH.Jm P Q)ᵀ = Formalism.BasicNotions.TH.Jm P Q := by
    simp [Formalism.BasicNotions.TH.Jm, Formalism.UG.Jpq, Matrix.fromBlocks_transpose]
  have hJtr : (Formalism.BasicNotions.TH.Jm P Q).trace = P - Q := by
    simp [Formalism.BasicNotions.TH.Jm, Formalism.UG.Jpq, Matrix.trace, Fintype.sum_sum_type, sub_eq_add_neg]
  have hL : (Formalism.BasicNotions.TH.Jm P Q * ((C.map star)ᵀ * Mᵀ)) * C = 1 := by
    have := congrArg Matrix.transpose h1
    rw [hJt, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at this
    rw [Matrix.mul_assoc, Matrix.mul_assoc, this, hJJ]
  have h3 : C' * C = 1 := by
    have : C' = Formalism.BasicNotions.TH.Jm P Q * ((C.map star)ᵀ * Mᵀ) := by
      rw [← Matrix.one_mul C', ← hL, Matrix.mul_assoc, h2, Matrix.mul_one]
    rw [this, hL]
  constructor
  · have := Matrix.trace_mul_comm C C'
    rw [h2, h3] at this
    simpa using this
  · rw [← Matrix.mul_one θ, ← h2, ← Matrix.mul_assoc, hθ, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, h3,
      Matrix.mul_one, hJtr]

private theorem frame_sig {n P Q P' Q' : ℕ} {M M' θ : Matrix (Fin n) (Fin n) ℂ} {C : Matrix (Fin n) (Ix P Q) ℂ}
    {C' : Matrix (Fin n) (Ix P' Q') ℂ} (hC : IsFrame M C) (hθ : θ * C = C * Formalism.BasicNotions.TH.Jm P Q)
    (hC' : IsFrame M' C') (hθ' : θ * C' = C' * Formalism.BasicNotions.TH.Jm P' Q') : P = P' ∧ Q = Q' := by
  obtain ⟨a1, a2⟩ := frame_trace hC hθ
  obtain ⟨b1, b2⟩ := frame_trace hC' hθ'
  constructor
  · have : (P : ℂ) = P' := by linear_combination (-a1 + b1 - a2 + b2) / 2
    exact_mod_cast this
  · have : (Q : ℂ) = Q' := by linear_combination (-a1 + b1 + a2 - b2) / 2
    exact_mod_cast this

open GlobalTheory.JointHarm in

private theorem harmTy_deg {P Q R S : ℕ} {x : ℚ} {k k' : ℕ} (ek : x - cPair R S = k) (ek' : x + cPair R S = k')
    {f : Formalism.BasicNotions.TH.Pol P Q R S} (hf : f ∈ harmTy P Q R S x) : f.totalDegree ≤ P * k + Q * k' := by
  have hle : harmTy P Q R S x ≤ homog (Ln P Q R S) (P * k + Q * k') := by
    refine Submodule.span_le.2 ?_
    rintro g ⟨h1, h2⟩
    by_cases h0 : g = 0
    · subst h0; exact Submodule.zero_mem _
    obtain ⟨d, hd1, hd2⟩ := isSide_one.homog_of_hw Function.bijective_id
      (GlobalTheory.FockScalarType.isHW_of_mem (x := x) h0 h2) ((mem_harm1 g).1 h1)
    have : d = P * k + Q * k' := by
      have e : (d : ℚ) = ((P * k + Q * k' : ℕ) : ℚ) := by
        rw [hd1]
        simp [degW, shiftNu, Fintype.sum_sum_type, ek, ek']
      exact_mod_cast e
    subst this
    exact hd2
  exact MvPolynomial.IsHomogeneous.totalDegree_le (hle hf)

open GlobalTheory.JointHarm in

private theorem lowOne_le_harmTy {P Q R S : ℕ} {x : ℚ} {k k' : ℕ} (ek : x - cPair R S = k) (ek' : x + cPair R S = k') :
    GlobalTheory.KFixIrr.lowOne P Q R S x (P * k + Q * k') ≤ harmTy P Q R S x := by
  intro g hg
  rw [GlobalTheory.KFixIrr.mem_lowOne] at hg
  have hc := (GlobalTheory.KFixIrr.mem_chiOne _ _).1 hg.1
  refine Submodule.subset_span ⟨fun Z hZ => ?_, hc⟩
  rw [fockAct2_eq, (parts_omAct (odd_kron2 hZ) g).2]
  have hsum := MvPolynomial.sum_homogeneousComponent g
  have hh : ∀ d, MvPolynomial.homogeneousComponent d g ∈ homog (Ln P Q R S) d := fun d =>
    MvPolynomial.homogeneousComponent_mem d g
  have hchi : dnOp (kron2 P Q Z) g ∈ GlobalTheory.KFixIrr.chiOne P Q R S x := by
    rw [GlobalTheory.KFixIrr.mem_chiOne]
    intro Y hY
    rw [← map_smul, ← hc Y hY, ← hsum]
    simp only [map_sum]
    exact Finset.sum_congr rfl fun d _ => (GlobalTheory.FockScalarType.comm_parts hY hZ (hh d)).2
  by_contra h0
  have hlow := GlobalTheory.FockLowDeg.lowerDeg P Q R S x k k' ek ek' _ hchi h0
  by_cases h2 : g.totalDegree < 2
  · apply h0
    rw [← hsum, map_sum]
    exact Finset.sum_eq_zero fun d hd => dnOp_low _ d (by have := Finset.mem_range.1 hd; omega) _ (hh d)
  · have : (dnOp (kron2 P Q Z) g).totalDegree ≤ g.totalDegree - 2 := by
      conv_lhs => rw [← hsum, map_sum]
      refine MvPolynomial.totalDegree_finsetSum_le fun d hd => ?_
      refine (MvPolynomial.IsHomogeneous.totalDegree_le (dnOp_homog _ d _ (hh d))).trans ?_
      have := Finset.mem_range.1 hd; omega
    have := hg.2
    omega

end GlobalTheory.HarmLow

theorem _root_.GlobalTheory.T.matched_harmonic_polynomial_integral : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (Rm : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' Rm Rf →
    ∀ (P Q Rn Sn : ℕ) (A : InfinitePlace F → Matrix (Fin a) (Ix P Q) ℂ) (C : InfinitePlace F → Matrix (Fin (a + a')) (Ix Rn Sn) ℂ)
      (Φ : Tens F P Q Rn Sn →ₗ[ℂ] SInf F (Fin a × Fin (a + a'))), GlobalTheory.FockBridge.IsFockData B G.M A C Φ →
      (tensHarm F P Q Rn Sn (halfKap B)).map Φ ≤ fockDeg G.M B.ψ B.emb (lowDegInf B G.M Rm.p) ∧
        tensHarm F P Q Rn Sn (halfKap B) ≠ ⊥ := by
  classical
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' Rm Rf hM P Q Rn Sn A C Φ hD
  obtain ⟨hb, hg, hc, hw, hw'⟩ := hM.triple
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨A₂, hA₂, hA₂'⟩ := Main.i_frameex _ _ _ _ _ (hg.hV.sig w₀) (hg.hV.cartan w₀)
  obtain ⟨C₂, hC₂, hC₂'⟩ := Main.i_frameex _ _ _ _ _ (hg.hW.sig w₀) (hg.hW.cartan w₀)
  obtain ⟨eP, eQ⟩ := GlobalTheory.HarmLow.frame_sig (hD.1.1.2.1 w₀) (hD.1.2.1 w₀) hA₂ hA₂'
  obtain ⟨eR, eS⟩ := GlobalTheory.HarmLow.frame_sig (hD.1.1.2.2 w₀) (hD.1.2.2 w₀) hC₂ hC₂'
  subst eP eQ eR eS
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hw
  obtain ⟨d, hd, hB1⟩ := hwp.2.1
  have hW1 := Main.i_liefirst (GlobalTheory.FockBottom.lieSecond hKP) F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co d 1 Complex.I A C Φ _ _ _
    hb.cm hb.std hD.1.1 hD.2 hd hB1 (Main.hasExp_div B.emb hc.expβ hc.expα)
  have ec : (fun w => -((halfKap B w : ℚ) : ℂ)) = fun w => ((B.mβ w - B.mα w : ℤ) : ℂ) / 2 := by
    funext w; simp only [halfKap]; push_cast; ring
  have hW1' : ActsBy B.emb A (om.comp (MonoidHom.inl _ _)) Φ (fockAct1 _ _ _ _) (fun w => -((halfKap B w : ℚ) : ℂ)) := by
    rw [ec]; exact hW1
  have hinj : Function.Injective Φ := hD.2.1
  have L1 := GlobalTheory.T.archimedean_theta_polynomial_lift_exists Main.i_actslaws Main.i_derex (Main.i_vacline Main.i_derex) F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb
    A C Φ hb.cm hb.std hD.1.1 hD.1.2.1 hD.1.2.2 hD.2
  have L2 := GlobalTheory.T.archimedean_polynomial_tensor_character Main.i_actslaws Main.i_lineex (Main.i_kline Main.i_lineex) F E σ B _ _ _ _ _ _ G.V G.W om A Φ
    (halfKap B) hb.cm hD.1.1.2.1 hD.1.2.1 hinj hW1' (GlobalTheory.FockBottom.admissible_weil_action hM.triple)
  have hPR : a - G.p ≤ a + a' - (G.p + G.q) := by have := hg.aBig; omega
  have hQS : G.p ≤ G.p + G.q := Nat.le_add_right _ _
  have hnum : ∀ w, ∃ k k' : ℕ, 0 < k ∧ 0 < k' ∧ halfKap B w - cPair (a + a' - (G.p + G.q)) (G.p + G.q) = k ∧
      halfKap B w + cPair (a + a' - (G.p + G.q)) (G.p + G.q) = k' := by
    intro w
    have hk := hg.kappa w
    obtain ⟨j, hj⟩ := Main.i_parity F E σ B a a' G X om om' hM.triple w
    obtain ⟨i, hi⟩ := hg.even
    have h1 := hg.eBig
    have h2 := hg.aBig
    have hle : G.p + G.q ≤ a + a' := by omega
    have hR : ((a + a' - (G.p + G.q) : ℕ) : ℚ) = (i : ℚ) + i - ((G.p : ℚ) + G.q) := by
      rw [Nat.cast_sub hle, hi]; push_cast; ring
    refine ⟨(j - i + (G.p + G.q : ℕ)).toNat, (j + i - (G.p + G.q : ℕ)).toNat, by omega, by omega, ?_, ?_⟩
    · rw [show (((j - i + (G.p + G.q : ℕ)).toNat : ℕ) : ℚ) = ((j - i + (G.p + G.q : ℕ) : ℤ) : ℚ) from by
        exact_mod_cast Int.toNat_of_nonneg (by omega)]
      simp only [halfKap, cPair, hj, hR]; push_cast; ring
    · rw [show (((j + i - (G.p + G.q : ℕ)).toNat : ℕ) : ℚ) = ((j + i - (G.p + G.q : ℕ) : ℤ) : ℚ) from by
        exact_mod_cast Int.toNat_of_nonneg (by omega)]
      simp only [halfKap, cPair, hj, hR]; push_cast; ring
  choose k k' hk hk' ek ek' using hnum
  have hdeg : ∑ w, ((a - G.p) * k w + G.p * k' w) ≤ lowDegInf B G.M Rm.p := by
    haveI := hM.real.nontriv
    obtain ⟨x, hx⟩ := exists_ne (0 : Rm.Pi)
    have hx' : x ∈ (G.M.Pol B.ψ B.emb).map Rm.p := by rw [hM.real.quot.onto]; trivial
    obtain ⟨f, hf, rfl⟩ := hx'
    rw [pol_eq_iSup_fockDeg] at hf
    obtain ⟨m, hm⟩ := (Submodule.mem_iSup_of_directed _ (fockDeg_mono G.M B.ψ B.emb).directed_le).1 hf
    have hne : {k | ∃ f ∈ fockDeg G.M B.ψ B.emb k, Rm.p f ≠ 0}.Nonempty := ⟨m, f, hm, hx⟩
    obtain ⟨g, hg₁, hpg⟩ : ∃ g ∈ fockDeg G.M B.ψ B.emb (lowDegInf B G.M Rm.p), Rm.p g ≠ 0 := Nat.sInf_mem hne
    obtain ⟨g₀, hg₀, hfix, hpe⟩ := GlobalTheory.LieGenStep.exists_kFix_map_eq hM _ g hg₁
    rw [L1] at hg₀
    obtain ⟨T, hT, rfl⟩ := hg₀
    have hspan := GlobalTheory.T.character_part_tensor_span (InfinitePlace F) _ _ _ _ (halfKap B) _ T ⟨(L2 T).1 hfix, hT⟩
    by_contra hlt
    apply hpg
    have hT0 : T ∈ (⊥ : Submodule ℂ _) := by
      refine (Submodule.span_le.2 ?_) hspan
      rintro _ ⟨u, hu, hs, rfl⟩
      by_cases h0 : ∃ w, u w = 0
      · obtain ⟨w, hw⟩ := h0
        rw [MultilinearMap.map_coord_zero _ w hw]
        exact Submodule.zero_mem _
      push Not at h0
      exact absurd ((Finset.sum_le_sum fun w _ =>
        GlobalTheory.FockLowDeg.lowerDeg _ _ _ _ (halfKap B w) (k w) (k' w) (ek w) (ek' w) (u w) (hu w) (h0 w)).trans hs) hlt
    rw [← hpe, (Submodule.mem_bot ℂ).1 hT0, map_zero, map_zero]
  constructor
  · rw [L1]
    refine Submodule.map_mono (Submodule.span_le.2 ?_)
    rintro _ ⟨f, hf, rfl⟩
    exact GlobalTheory.KFixIrr.tprod_mem_degLE f
      ((Finset.sum_le_sum fun w _ => GlobalTheory.HarmLow.harmTy_deg (ek w) (ek' w) (hf w)).trans hdeg)
  · choose v hv hv0 using fun w => Submodule.exists_mem_ne_zero_of_ne_bot
      (GlobalTheory.T.lowest_degree_component_nonzero _ _ _ _ (halfKap B w) (k w) (k' w) hPR hQS (hk w) (hk' w) (ek w) (ek' w))
    intro h
    refine GlobalTheory.FockBottom.tprod_ne_zero v hv0 ((Submodule.eq_bot_iff _).1 h _ (Submodule.subset_span ⟨v, fun w => ?_, rfl⟩))
    exact GlobalTheory.HarmLow.lowOne_le_harmTy (ek w) (ek' w) (hv w)
