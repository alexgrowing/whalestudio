import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.MatchLM
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingUnitOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HintConstMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactMaximalPairPlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermMultiplicative
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingSplitOf

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F
open PositivityTheory.Rg.BcB.F.U (lpow lone)
open PositivityTheory.Rg.BcB.F.MLM (wordL wordU)
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.MatchWord

section Generic

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

omit [TopologicalSpace H] [IsTopologicalGroup H] in
theorem hint_mul_right (K : Subgroup H) (u : H → ℂ) (c : ℂ) : hint K (fun x => u x * c) = hint K u * c := by
  rw [mul_comm, ← GlobalTheory.CompanionTheory.ActTr.hint_const_mul]
  simp only [mul_comm]

theorem conv_assoc {K : Subgroup H} (hK : IsCompact (K : Set H)) (hO : IsOpen (K : Set H)) {f g k : H → ℂ}
    (hf : IsHecke K f) (hg : IsHecke K g) (hk : IsHecke K k) (y : H) :
    hint K (fun z => hint K (fun x => f x * g (x⁻¹ * z)) * k (z⁻¹ * y)) =
      hint K (fun x => f x * hint K (fun z => g z * k (z⁻¹ * (x⁻¹ * y)))) := by
  have hC₁ : IsCompact ((fun t => y * t⁻¹) '' tsupport k) :=
    IsCompact.image hk.1 (continuous_const.mul continuous_inv)
  have h₁ : ∀ l ∈ K, ∀ z x, f x * g (x⁻¹ * (z * l)) * k ((z * l)⁻¹ * y) = f x * g (x⁻¹ * z) * k (z⁻¹ * y) := by
    intro l hl z x
    have e : (z * l)⁻¹ * y = l⁻¹ * (z⁻¹ * y) := by group
    have e2 : x⁻¹ * (z * l) = x⁻¹ * z * l := by group
    rw [e, e2, (hg.2 l hl _).2, (hk.2 l⁻¹ (inv_mem hl) _).1]
  have h₂ : ∀ l ∈ K, ∀ z x, f (x * l) * g ((x * l)⁻¹ * z) * k (z⁻¹ * y) = f x * g (x⁻¹ * z) * k (z⁻¹ * y) := by
    intro l hl z x
    have e : (x * l)⁻¹ * z = l⁻¹ * (x⁻¹ * z) := by group
    rw [e, (hf.2 l hl x).2, (hg.2 l⁻¹ (inv_mem hl) _).1]
  have h₃ : ∀ z x, f x * g (x⁻¹ * z) * k (z⁻¹ * y) ≠ 0 →
      z ∈ (fun t => y * t⁻¹) '' tsupport k ∧ x ∈ tsupport f := by
    intro z x h
    refine ⟨⟨z⁻¹ * y, subset_tsupport _ (right_ne_zero_of_mul h), by group⟩,
      subset_tsupport _ (left_ne_zero_of_mul (left_ne_zero_of_mul h))⟩
  have e := GlobalTheory.CompanionTheory.ActTr.hint_comm hK hO le_rfl hC₁ hK hO le_rfl hf.1
    (fun z x => f x * g (x⁻¹ * z) * k (z⁻¹ * y)) h₁ h₂ h₃
  calc hint K (fun z => hint K (fun x => f x * g (x⁻¹ * z)) * k (z⁻¹ * y))
      = hint K (fun z => hint K (fun x => f x * g (x⁻¹ * z) * k (z⁻¹ * y))) := by
        congr 1
        funext z
        rw [hint_mul_right]
    _ = hint K (fun x => hint K (fun z => f x * g (x⁻¹ * z) * k (z⁻¹ * y))) := e
    _ = _ := by
        congr 1
        funext x
        have e' : (fun z => f x * g (x⁻¹ * z) * k (z⁻¹ * y)) =
            fun z => f x * (fun t => g t * k (t⁻¹ * (x⁻¹ * y))) (x⁻¹ * z) := by
          funext z
          have e2 : (x⁻¹ * z)⁻¹ * (x⁻¹ * y) = z⁻¹ * y := by group
          simp only [e2, mul_assoc]
        rw [e', GlobalTheory.CompanionTheory.ActTr.hint_const_mul, GlobalTheory.CompanionTheory.CtMulSplit.hint_left K x⁻¹ (fun t => g t * k (t⁻¹ * (x⁻¹ * y)))]

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem lconv_assoc (hE : Unr E) {w : Pl E} {f g k : UL n w → ℂ} (hf : IsHecke (KL n w) f) (hg : IsHecke (KL n w) g)
    (hk : IsHecke (KL n w) k) : lconv (lconv f g) k = lconv f (lconv g k) := by
  funext y
  exact conv_assoc (GlobalTheory.CompanionTheory.SphLine.isCompact_KL hE n w) (GlobalTheory.CompanionTheory.SphLine.isOpen_KL n w) hf hg hk y

theorem lconv_lone_left {w : Pl E} {f : UL n w → ℂ} (hf : IsHecke (KL n w) f) : lconv (lone (KL n w)) f = f := by
  funext m
  exact GlobalTheory.CompanionTheory.FmPowP.hint_ind_left _ _ le_rfl (by simp [Subgroup.relIndex_self]) f (fun u hu g => (hf.2 u hu g).1) m

theorem lconv_lone_right {w : Pl E} {f : UL n w → ℂ} (hf : IsHecke (KL n w) f) : lconv f (lone (KL n w)) = f := by
  funext m
  exact GlobalTheory.CompanionTheory.FmPowP.hint_ind_right _ _ le_rfl (by simp [Subgroup.relIndex_self]) f (fun u hu g => (hf.2 u hu g).2) m

theorem isHecke_ctMu {a b : ℕ} (h : a + b = n) {w : Pl E} (hU : UL n w = ⊤) (μ : (w.adicCompletion E)ˣ →* ℂˣ)
    (hμ : ∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → μ u = 1) {f : UL n w → ℂ}
    (hf : IsHecke (KL n w) f) : IsHecke (K2 a b w) (ctMu h w μ f) := by
  have hH := GlobalTheory.CompanionTheory.CtMulSplit.isHk_of_isHecke hU hf
  set F : GLw n w → ℂ := fun y => f (toSub (UL n w) y) with hF
  have hb : ∀ u ∈ GlobalTheory.LFun.KGL w n, ∀ g, F (u * g) = F g ∧ F (g * u) = F g := fun u hu g =>
    ⟨by simpa using hH.2.2.2 u hu 1 (Subgroup.one_mem _) g, by simpa using hH.2.2.2 1 (Subgroup.one_mem _) u hu g⟩
  have hbi := GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.constant_term_bi_invariant (a := a) (b := b) h w (GlobalTheory.LFun.KGL w n) le_rfl
    (fun k hk k' hk' => mul_mem (mul_mem hk hk') (inv_mem hk)) F hH.2.2.2 1 1 (one_mem _) (one_mem _)
  have hone : (1 : GLw a w × GLw b w) ∈ leviOf h w (GlobalTheory.LFun.KGL w n) := GlobalTheory.CompanionTheory.CtHecke.blk_zero_mem h w (one_mem _)
  have e : ctMu h w μ f = fun m => GlobalTheory.CompanionTheory.CtHecke.cMu μ m * phi3 h w F 1 1 m := by
    funext m
    show GlobalTheory.CompanionTheory.CtHecke.cMu μ m * ct h w F m = _
    rw [GlobalTheory.CompanionTheory.CtMulSplit.constant_term_eq_mackey_entry h w hb]
  rw [e]
  refine ⟨?_, fun κ hκ x => ⟨?_, ?_⟩⟩
  · exact (GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.constant_term_compact_support h w _ hH.2.2.1 1 1).mul_left
  · have := hbi κ 1 (GlobalTheory.CompanionTheory.CtHecke.blk_zero_mem h w hκ) hone x
    rw [mul_one] at this
    simp only [GlobalTheory.CompanionTheory.CtHecke.cMu_mul_left hμ hκ, this]
  · have := hbi 1 κ hone (GlobalTheory.CompanionTheory.CtHecke.blk_zero_mem h w hκ) x
    rw [one_mul] at this
    simp only [GlobalTheory.CompanionTheory.CtHecke.cMu_mul_right hμ hκ, this]

theorem isHecke_hU (d : LocData E n) (hd : d.Ok) {w : Pl E} (hU : UL n w = ⊤) (k : ℕ) : IsHecke (KL n w) (d.hU w k) := by
  have h0 : (d.ϖ w : w.adicCompletion E) ≠ 0 := (d.ϖ w).ne_zero
  have hϖ : IsUnifV E w (d.ϖ w : w.adicCompletion E) := GlobalTheory.CompanionTheory.CtHecke.isUnifV_of_ordL h0 (hd.unif w)
  have hT := Tj_mem_hecke (n := n) hϖ k
  have hcl : IsClosed ((UL n w : Subgroup (GLw n w)) : Set (GLw n w)) := by
    rw [hU]
    exact isClosed_univ
  refine ⟨(GlobalTheory.CompanionTheory.CtHecke.hasCompactSupport_Tj h0 k).comp_isClosedEmbedding hcl.isClosedEmbedding_subtypeVal,
    fun κ hκ x => ⟨?_, ?_⟩⟩
  · have := hT.1 ⟨κ.1, hκ⟩ 1 x.1
    simpa [LocData.hU] using this
  · have := hT.1 1 ⟨κ.1, hκ⟩ x.1
    simpa [LocData.hU] using this

theorem hc_eq (d : LocData E n) (a : ℕ) (ha : a ≤ n) {w : Pl E}
    (hμ : ∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → d.μ w u = 1) (k : ℕ) :
    d.hc a ha w k = ctMu (Nat.add_sub_cancel' ha) w (d.μ w) (d.hU w k) := by
  have h1 : d.sgn a w = 1 := by
    unfold LocData.sgn
    rw [map_pow, hμ _ (GlobalTheory.CompanionTheory.CtMulSplit.ordL_neg_one w)]
    simp
  unfold LocData.hc
  rw [h1, inv_one, one_smul]
  rfl

theorem word_ct (d : LocData E n) (a : ℕ) (ha : a ≤ n) {w : Pl E} (hCt : MT.CtMul) (hSp : SphComm) (hE : Unr E)
    (hd : d.Ok) (hG : d.Good w) (l : List (ℕ × Bool)) :
    IsHecke (KL n w) (wordU d w l) ∧ ∃ A B : UL n w → ℂ, IsHecke (KL n w) A ∧ IsHecke (KL n w) B ∧
      (wordL d a ha w l).s w = ctMu (Nat.add_sub_cancel' ha) w (d.μ w) A ∧
      (wordL d a ha w l).t w = ctMu (Nat.add_sub_cancel' ha) w (d.μ w) B ∧
      mconv (ctMu (Nat.add_sub_cancel' ha) w (d.μ w) A) (ctMu (Nat.add_sub_cancel' ha) w (d.μ w) B) =
        ctMu (Nat.add_sub_cancel' ha) w (d.μ w) (wordU d w l) := by
  obtain ⟨hw, hT, hS₀, hBad, hμ⟩ := hG
  have hU : UL n w = ⊤ := if_pos hw
  set C := ctMu (Nat.add_sub_cancel' ha) w (d.μ w) with hC
  have conv : ∀ {f g : UL n w → ℂ}, IsHecke (KL n w) f → IsHecke (KL n w) g → IsHecke (KL n w) (lconv f g) :=
    fun hf hg => GlobalTheory.CompanionTheory.UnitaryWord.isHecke_lconv GlobalTheory.CompanionTheory.LocHecke.locAlg (GlobalTheory.CompanionTheory.MatchPowers.isLevel_KL n w) hf hg
  have mul : ∀ {f g : UL n w → ℂ}, IsHecke (KL n w) f → IsHecke (KL n w) g → C (lconv f g) = mconv (C f) (C g) :=
    fun hf hg => hCt E n a ha w hw (d.μ w) hμ _ _ hf hg
  have hone : IsHecke (KL n w) (lone (KL n w)) := GlobalTheory.CompanionTheory.MatchUnit.isHecke_lone_KL hE
  have hunit : C (lone (KL n w)) = PositivityTheory.Rg.BcB.F.idem (K2 a (n - a) w) := GlobalTheory.CompanionTheory.MatchUnit.ctMu_lone _ hU _ hμ
  have hlev : d.lev a w = K2 a (n - a) w := by
    unfold LocData.lev
    rw [if_neg hT, if_neg (by simp [hS₀, hBad])]
  have hlev₂ : d.lev₂ a w = K2 a (n - a) w := by
    unfold LocData.lev₂
    rw [if_neg (by simp [hS₀, hBad])]
  have hes : (d.eL a).s w = C (lone (KL n w)) := by
    rw [hunit]
    show PositivityTheory.Rg.BcB.F.idem (d.lev a w) = _
    rw [hlev]
  have het : (d.eL a).t w = C (lone (KL n w)) := by
    rw [hunit]
    show PositivityTheory.Rg.BcB.F.idem (d.lev₂ a w) = _
    rw [hlev₂]
  induction l with
  | nil =>
    refine ⟨?_, lone (KL n w), lone (KL n w), hone, hone, hes, het, ?_⟩
    · show IsHecke (KL n w) ((KL n w : Set (UL n w)).indicator 1)
      rw [GlobalTheory.CompanionTheory.UnitaryWord.lone_KL] at hone
      exact hone
    · rw [← mul hone hone, lconv_lone_left hone, GlobalTheory.CompanionTheory.UnitaryWord.lone_KL]
      rfl
  | cons x l ih =>
    obtain ⟨hW, A, B, hA, hB, hs, ht, hm⟩ := ih
    obtain ⟨k, intersection_update_fsHerm_neg_one⟩ := x
    have hTk := isHecke_hU d hd hU k
    have hck : d.hc a ha w k = C (d.hU w k) := hc_eq d a ha hμ k
    have hWc : wordU d w ((k, intersection_update_fsHerm_neg_one) :: l) = lconv (d.hU w k) (wordU d w l) := rfl
    have key : mconv (C (lconv (d.hU w k) A)) (C B) = C (lconv (d.hU w k) (wordU d w l)) := by
      rw [← mul (conv hTk hA) hB, lconv_assoc hE hTk hA hB, mul hTk (conv hA hB), mul hA hB, hm, ← mul hTk hW]
    refine ⟨hWc ▸ conv hTk hW, ?_⟩
    rw [hWc]
    cases intersection_update_fsHerm_neg_one with
    | false =>
      refine ⟨lconv (d.hU w k) A, B, conv hTk hA, hB, ?_, ?_, key⟩
      · show mconv ((d.hL a ha w k false).s w) ((wordL d a ha w l).s w) = _
        have e : (d.hL a ha w k false).s w = d.hc a ha w k := by simp [LocData.hL]
        rw [e, hs, hck, ← mul hTk hA]
      · show mconv ((d.eL a).t w) ((wordL d a ha w l).t w) = _
        rw [het, ht, ← mul hone hB, lconv_lone_left hB]
    | true =>
      refine ⟨A, lconv (d.hU w k) B, hA, conv hTk hB, ?_, ?_, ?_⟩
      · show mconv ((d.eL a).s w) ((wordL d a ha w l).s w) = _
        rw [hes, hs, ← mul hone hA, lconv_lone_left hA]
      · show mconv ((d.hL a ha w k true).t w) ((wordL d a ha w l).t w) = _
        have e : (d.hL a ha w k true).t w = d.hc a ha w k := by simp [LocData.hL]
        rw [e, ht, hck, ← mul hTk hB]
      · rw [← mul hA (conv hTk hB), ← lconv_assoc hE hA hTk hB, mul (conv hA hTk) hB, mul hA hTk,
          hSp E a (n - a) w (C A) (C (d.hU w k)) (isHecke_ctMu _ hU _ hμ hA) (isHecke_ctMu _ hU _ hμ hTk),
          ← mul hTk hA]
        exact key

theorem matchLMWordOf : PositivityTheory.Rg.BcB.F.MLM.MatchLMWordOf := by
  intro hS hCt hSp _ E _ _ _ hE n d hd a ha w hG l
  have hP : w ∉ d.P := by simp [LocData.P, hG.2.1, hG.2.2.1]
  have htr : (wordL d a ha w l).tr d.P d.one w = (wordL d a ha w l).s w := if_neg hP
  obtain ⟨hW, A, B, -, -, hs, ht, hm⟩ := word_ct d a ha hCt hSp hE hd hG l
  rw [htr, hs, ht, hm]
  have hμ := hG.2.2.2.2
  have hw := hG.1
  have h1 := hS E n a ha w hw (d.μ w) hμ _ hW 1 le_rfl
  have hone : IsHecke (KL n w) (lone (KL n w)) := GlobalTheory.CompanionTheory.MatchUnit.isHecke_lone_KL hE
  have e1 : lpow (KL n w) (wordU d w l) 1 = wordU d w l := lconv_lone_right hW
  have e2 : mconv (ctMu (Nat.add_sub_cancel' ha) w (d.μ w) (wordU d w l))
      (ctMu (Nat.add_sub_cancel' ha) w (d.μ w) (lone (KL n w))) =
      ctMu (Nat.add_sub_cancel' ha) w (d.μ w) (wordU d w l) := by
    rw [← hCt E n a ha w hw (d.μ w) hμ _ _ hW hone, lconv_lone_right hW]
  rw [e1] at h1
  exact e2 ▸ h1

end GlobalTheory.CompanionTheory.MatchWord

end
