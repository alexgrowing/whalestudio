import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteClassBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteClassBoundStatement

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim
namespace GlobalTheory.ClassCount
set_option maxHeartbeats 2000000 in
theorem archimedean_class_count_bound : _root_.GlobalTheory.FunPr.ThetaLocalInputs → InfClassK := by
  intro _
  obtain ⟨c1, hT1⟩ := GlobalTheory.T.principalCongruence_le_topLevel_classSum
  obtain ⟨c2, hR1⟩ := GlobalTheory.T.classSum_vertexLevels_contain_principalCongruence
  refine ⟨max c1 c2, fun CF hCF => ⟨144, fun ε C hC => ?_⟩⟩
  obtain ⟨x1, hx1⟩ := hT1 CF ((le_max_left _ _).trans hCF) ε
  obtain ⟨x2, hx2⟩ := hR1 CF ((le_max_right _ _).trans hCF) ε
  refine ⟨max x1 x2, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt hFO => ?_⟩
  have hTop := hx1 D large₂ he ((le_max_left _ _).trans hx) Γ Pl0 T A Ks R F hS ch hIs hAt hFO
  have hRow := hx2 D large₂ he ((le_max_right _ _).trans hx) Γ Pl0 T A Ks R F hS ch hIs hAt hFO
  obtain ⟨hNb, hfb, hN1, hf1, hm2, hrd1, hlrd, hb12⟩ := GlobalTheory.T.parameterSizeConditions_numericBounds large₂ hS.size
  set b := large₂.sc.b with hb
  set N := bigN D with hNdef
  have hsig : 0 ≤ sig ch.G := Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  have hb0 : 0 < b := by linarith
  have hlb : 0 ≤ Real.log b := Real.log_nonneg (by linarith)
  have hrd0 : 0 < D.host.rdE := by linarith
  have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hf0 : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf1
  set base := 12 * (D.R.f : ℝ) ^ 2 * (N : ℝ) ^ 4 * D.host.rdE ^ 2 with hbase
  have hbase1 : 1 ≤ base := by
    have : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 2 := one_le_pow₀ hf0
    have : (1 : ℝ) ≤ (N : ℝ) ^ 4 := one_le_pow₀ hN0
    have : (1 : ℝ) ≤ D.host.rdE ^ 2 := one_le_pow₀ hrd1
    have : (1 : ℝ) ≤ 12 * (D.R.f : ℝ) ^ 2 := by nlinarith
    have : (1 : ℝ) ≤ 12 * (D.R.f : ℝ) ^ 2 * (N : ℝ) ^ 4 := by nlinarith
    nlinarith
  have hlbase : Real.log base ≤ 8 * Real.log b := by
    have h12 : Real.log 12 ≤ Real.log b := Real.log_le_log (by norm_num) hb12
    have hlf : Real.log (D.R.f:ℝ) ≤ Real.log b := Real.log_le_log (by linarith) hfb
    have hlN : Real.log N ≤ Real.log b := Real.log_le_log (by linarith) hNb
    have e : Real.log base = Real.log 12 + 2 * Real.log (D.R.f:ℝ) + 4 * Real.log N + 2 * Real.log D.host.rdE := by
      rw [hbase, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
      push_cast; ring
    rw [e]; nlinarith
  set M := hBd D N * Real.exp (2 * sig ch.G) ^ (N ^ 2) with hM
  have hM0 : 0 ≤ M := by rw [hM, hBd]; positivity
  have factor : ∀ (n : ℕ), n ≤ N → ∀ a : ℝ, 0 ≤ a → a ≤ Real.exp (2 * sig ch.G) → hBd D n * a ^ (n ^ 2) ≤ M := by
    intro n hn a ha0 ha
    have h1 : hBd D n ≤ hBd D N := hBd_mono hn hbase1 hrd0.le
    have h2 : a ^ (n ^ 2) ≤ Real.exp (2 * sig ch.G) ^ (N ^ 2) :=
      (pow_le_pow_left₀ ha0 ha _).trans (pow_le_pow_right₀ (Real.one_le_exp (by linarith)) (by gcongr))
    exact mul_le_mul h1 h2 (by positivity) (by rw [hBd]; positivity)
  have hmod := GlobalTheory.T.absNorm_gridModulus_le_exp_depthLogNormSum ch.G hS.hF
  have fin : ∀ (X : Node), DefNode D.R.m X → ∀ K : Subgroup (GL (Fin (ch.G.V X).rank) (Lev.EAf D)),
      congLev D.sp.cm (ch.G.V X).gram (ch.G.Λ X) ch.G.modul ≤ K → (Nat.card (FinCl (ch.G.V X) K) : ℝ) ≤ M := fun X hX K hK =>
    (GlobalTheory.T.definiteVertexClasses_card_le_principalCongruence ch.G ch.S.N X hX _ (ch.G.pl.modul_ne_bot _) K hK).trans
      (factor _ (GlobalTheory.T.definiteKernelNode_rank_le_totalRank ch.G X hX) _ (Nat.cast_nonneg _) hmod)
  set K0 := 48 * (D.R.f:ℝ) * (N : ℝ) ^ 2 * Real.log b + 2 * (N : ℝ) ^ 2 * sig ch.G with hK0
  have hK00 : 0 ≤ K0 := by positivity
  have hMK : M ≤ Real.exp K0 := by
    have e1 : hBd D N ≤ Real.exp ((6 * D.R.f * N ^ 2 : ℕ) * (8 * Real.log b)) := by
      rw [Real.exp_nat_mul]
      refine pow_le_pow_left₀ (by positivity) ?_ _
      rw [← Real.log_le_iff_le_exp (by positivity)]
      exact hlbase
    have e2 : Real.exp (2 * sig ch.G) ^ (N ^ 2) = Real.exp ((N ^ 2 : ℕ) * (2 * sig ch.G)) := (Real.exp_nat_mul _ _).symm
    rw [hM, e2, hK0]
    calc _ ≤ Real.exp ((6 * D.R.f * N ^ 2 : ℕ) * (8 * Real.log b)) * Real.exp ((N ^ 2 : ℕ) * (2 * sig ch.G)) :=
          mul_le_mul_of_nonneg_right e1 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; push_cast; ring_nf
  have hm0 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
  have key : ((2 * D.R.m + 1 : ℕ) : ℝ) * K0 ≤ D.R.m * aOne ch.G C b := by
    have hm00 : (0 : ℝ) ≤ D.R.m := by linarith
    have h3 : ((2 * D.R.m + 1 : ℕ) : ℝ) * K0 ≤ 3 * D.R.m * K0 :=
      mul_le_mul_of_nonneg_right (by push_cast; linarith) hK00
    refine h3.trans ?_
    have hX : 0 ≤ (D.R.f : ℝ) * N * Real.log b := by positivity
    have t1 : 144 * (D.R.f : ℝ) * (N : ℝ) ^ 2 * Real.log b ≤ C * D.R.f * N * b * Real.log b :=
      calc 144 * (D.R.f : ℝ) * (N : ℝ) ^ 2 * Real.log b = 144 * ((D.R.f * N * Real.log b) * N) := by ring
        _ ≤ 144 * ((D.R.f * N * Real.log b) * b) := by gcongr
        _ ≤ C * ((D.R.f * N * Real.log b) * b) := by gcongr
        _ = C * D.R.f * N * b * Real.log b := by ring
    have hCm : (6 : ℝ) ≤ C * D.R.m := by
      have := mul_le_mul hC hm0 (by norm_num) (by linarith)
      linarith
    have t2 : 6 * ((N : ℝ) ^ 2 * sig ch.G) ≤ (C * D.R.m) * ((N : ℝ) ^ 2 * sig ch.G) :=
      mul_le_mul_of_nonneg_right hCm (by positivity)
    calc 3 * (D.R.m : ℝ) * K0 = D.R.m * (144 * (D.R.f : ℝ) * (N : ℝ) ^ 2 * Real.log b + 6 * ((N : ℝ) ^ 2 * sig ch.G)) := by
          rw [hK0]; ring
      _ ≤ D.R.m * (C * D.R.f * N * b * Real.log b + (C * D.R.m) * ((N : ℝ) ^ 2 * sig ch.G)) :=
          mul_le_mul_of_nonneg_left (add_le_add t1 t2) hm00
      _ = D.R.m * aOne ch.G C b := by rw [aOne]; ring
  have hexp : Real.exp K0 ^ (2 * D.R.m + 1) ≤ Real.exp (D.R.m * aOne ch.G C b) := by
    rw [← Real.exp_nat_mul]; exact Real.exp_le_exp.2 key
  refine ⟨?_, fun Φ β hβ => ?_⟩
  ·
    have h := (GlobalTheory.T.card_topVertexClasses_le_classNumberBound_norm_pow ch.G ch.S.N).trans
      (factor _ (GlobalTheory.T.definiteKernelNode_rank_le_totalRank ch.G (.top 0) (by simp [DefNode])) _ (Nat.cast_nonneg _) hmod)
    refine h.trans (hMK.trans ((le_self_pow₀ (Real.one_le_exp hK00) (by omega)).trans hexp))
  ·
    rw [GridChoice.Classes, Nat.card_prod, Nat.card_pi, Nat.card_pi]
    push_cast
    have hT : ∏ j : Fin D.R.m, (Nat.card (FinCl (ch.G.V (.top j)) (ch.S.levTop A.μ0 Φ β j j.2)) : ℝ) ≤ M ^ D.R.m := by
      calc _ ≤ ∏ _j : Fin D.R.m, M := Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) fun j _ =>
            fin (.top j) (by simp [DefNode]) _
            (hTop Φ β hβ j)
        _ = _ := by simp
    have hR : ∏ i : Fin (D.R.m + 1), (Nat.card (FinCl (ch.G.V (.grid i D.R.m))
        (ch.S.levRow A.μ0 i (Nat.le_of_lt_succ i.2))) : ℝ) ≤ M ^ (D.R.m + 1) := by
      calc _ ≤ ∏ _i : Fin (D.R.m + 1), M := Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) fun i _ =>
            fin (.grid i D.R.m) (by simp [DefNode]; omega) _
            (hRow i)
        _ = _ := by simp
    calc _ ≤ M ^ D.R.m * M ^ (D.R.m + 1) := mul_le_mul hT hR (by positivity) (by positivity)
      _ = M ^ (2 * D.R.m + 1) := by rw [← pow_add]; congr 1; omega
      _ ≤ Real.exp K0 ^ (2 * D.R.m + 1) := pow_le_pow_left₀ hM0 hMK _
      _ ≤ _ := hexp
end GlobalTheory.ClassCount
end
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.class_count_bound_archimedean : _root_.GlobalTheory.FunPr.ThetaLocalInputs → InfClassK := by
  first | exact @_root_.GlobalTheory.ClassCount.archimedean_class_count_bound | exact _root_.GlobalTheory.ClassCount.archimedean_class_count_bound | (intros; apply _root_.GlobalTheory.ClassCount.archimedean_class_count_bound <;> assumption)
end
