import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSub
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePullbackMetricFlagsCompat
open NumberField MvPolynomial
open Formalism.BasicNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RelabDRVdm

open Classical

theorem prod_fin_split (N j : ℕ) (h : j ≤ N) :
    ∏ i : Fin N, (if (i : ℕ) < j then (i : ℕ) + 1 else N - i) = j.factorial * (N - j).factorial := by
  rw [Fin.prod_univ_eq_prod_range (fun i => if i < j then i + 1 else N - i) N,
    ← Finset.prod_range_mul_prod_Ico _ h]
  congr 1
  · rw [← Finset.prod_range_add_one_eq_factorial]
    exact Finset.prod_congr rfl fun i hi => if_pos (Finset.mem_range.1 hi)
  · rw [Finset.prod_Ico_eq_prod_range, ← Finset.prod_range_add_one_eq_factorial,
      ← Finset.prod_range_reflect (fun k => k + 1)]
    refine Finset.prod_congr rfl fun k hk => ?_
    have := Finset.mem_range.1 hk
    rw [if_neg (by omega)]
    omega

theorem rootDiscr_pairs {ι : Type} [Fintype ι] (m : ι → ℕ) :
    GlobalTheory.GoodMetric.rootDiscr m = ∏ z : GlobalTheory.GoodMetric.Root m, ∏ z' : GlobalTheory.GoodMetric.Root m,
      (if z'.1 = z.1 ∧ (z'.2 : ℕ) < z.2 then X z - X z' else 1) := by
  unfold GlobalTheory.GoodMetric.rootDiscr
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun σ _ => Finset.prod_congr rfl fun k _ => ?_
  rw [Fintype.prod_sigma, Finset.prod_eq_single σ
    (fun σ' _ h => Finset.prod_eq_one fun i _ => if_neg fun h' => h h'.1) (by simp)]
  rw [← Finset.prod_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio, Fin.lt_def]

variable {D : D7} (O : Setup D)

theorem rootL_bijective : Function.Bijective (GlobalTheory.RelabDR.rootL O) := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨GlobalTheory.ShFam.Pad.LieGen.rootLetter_injective O.S, ?_⟩
  rw [Fintype.card_of_bijective (GlobalTheory.ShFam.Pad.LieGen.rootIdx_bijective O.S), Fintype.card_fin,
    ← Fintype.card_congr ((GlobalTheory.Proof.LetterConjugation.nodup_letters O.S.Dw).getEquivOfForallMemList _
      (GlobalTheory.Proof.LetterConjugation.mem_letters O.S.Dw)), Fintype.card_fin, GlobalTheory.ShFam.Pad.length_letters]

theorem rootL_val (x : DV.Rt D.what₂.Tau O.N) :
    ((GlobalTheory.RelabDR.rootL O x).2 : ℕ) = if (x.2 : ℕ) < O.j then (x.2 : ℕ) else O.N - 1 - x.2 := by
  by_cases h : (x.2 : ℕ) < O.j
  · have e : GlobalTheory.RelabDR.rootL O x =
        ⟨DV.tauEmb D x.1, ⟨x.2, by rw [GlobalTheory.ShFam.Pad.LieGen.mult_tau O.S]; exact h⟩⟩ := dif_pos h
    rw [e, if_pos h]
  · have := x.2.2
    have e : GlobalTheory.RelabDR.rootL O x =
        ⟨conjEmb (DV.tauEmb D x.1), ⟨O.N - 1 - x.2, by rw [GlobalTheory.ShFam.Pad.LieGen.mult_conj_tau O.S]; omega⟩⟩ :=
      dif_neg h
    rw [e, if_neg h]

theorem rootL_fst (x : DV.Rt D.what₂.Tau O.N) :
    (GlobalTheory.RelabDR.rootL O x).1 = if (x.2 : ℕ) < O.j then DV.tauEmb D x.1 else conjEmb (DV.tauEmb D x.1) := by
  unfold GlobalTheory.RelabDR.rootL GlobalTheory.ShFam.Pad.LieGen.rootLetter
  split <;> rfl

theorem fst_eq_iff (x y : DV.Rt D.what₂.Tau O.N) :
    (GlobalTheory.RelabDR.rootL O x).1 = (GlobalTheory.RelabDR.rootL O y).1 ↔ x.1 = y.1 ∧ ((x.2 : ℕ) < O.j ↔ (y.2 : ℕ) < O.j) := by
  have hinj : Function.Injective (DV.tauEmb D) := fun a b e =>
    D.eTau.injective (Subtype.ext (Formalism.MainNotions.LocalModelPeriodLattices.emb_injective D e))
  have hcc : ∀ τ : D.host.E →+* ℂ, conjEmb (conjEmb τ) = τ := fun τ => by ext x; simp [conjEmb]
  have hne : ∀ t t' : D.what₂.Tau, conjEmb (DV.tauEmb D t) ≠ DV.tauEmb D t' := fun t t' e =>
    GlobalTheory.Proof.LetterConjugation.conj_ne (O.A.cm t)
      ((congrArg (fun σ : D.host.E →+* ℂ => σ (O.A.H.rt : D.host.E)) e).trans (O.A.cm t'))
  rw [rootL_fst, rootL_fst]
  obtain ⟨t, a⟩ := x
  obtain ⟨t', b⟩ := y
  dsimp only
  split_ifs with h1 h2 h2
  · exact ⟨fun e => ⟨hinj e, iff_of_true h1 h2⟩, fun h => by rw [h.1]⟩
  · exact iff_of_false (fun e => hne t' t e.symm) (fun h => h2 (h.2.1 h1))
  · exact iff_of_false (fun e => hne t t' e) (fun h => h1 (h.2.2 h2))
  · exact ⟨fun e => ⟨hinj (by rw [← hcc (DV.tauEmb D t), e, hcc]), iff_of_false h1 h2⟩, fun h => by rw [h.1]⟩

theorem cond_iff (τ : D.what₂.Tau) (a b : Fin O.N) :
    ((GlobalTheory.RelabDR.rootL O (τ, a)).1 = (GlobalTheory.RelabDR.rootL O (τ, b)).1 ∧
      ((GlobalTheory.RelabDR.rootL O (τ, a)).2 : ℕ) < (GlobalTheory.RelabDR.rootL O (τ, b)).2) ↔
      ((a < b ∧ (b : ℕ) < O.j) ∨ (b < a ∧ O.j ≤ (b : ℕ))) := by
  rw [fst_eq_iff, rootL_val, rootL_val]
  dsimp only
  have := a.2
  have := b.2
  simp only [true_and, Fin.lt_def]
  split_ifs <;> omega

abbrev gF (τ : D.what₂.Tau) (a b : Fin O.N) : MvPolynomial (GlobalTheory.ShFam.Pad.Letter O.S.Dw) ℝ :=
  if a < b ∧ (b : ℕ) < O.j then X (GlobalTheory.RelabDR.rootL O (τ, b)) - X (GlobalTheory.RelabDR.rootL O (τ, a)) else 1

abbrev hF (τ : D.what₂.Tau) (a b : Fin O.N) : MvPolynomial (GlobalTheory.ShFam.Pad.Letter O.S.Dw) ℝ :=
  if a < b ∧ O.j ≤ (a : ℕ) then X (GlobalTheory.RelabDR.rootL O (τ, a)) - X (GlobalTheory.RelabDR.rootL O (τ, b)) else 1

theorem split_pair (τ : D.what₂.Tau) (a b : Fin O.N) :
    (if (GlobalTheory.RelabDR.rootL O (τ, a)).1 = (GlobalTheory.RelabDR.rootL O (τ, b)).1 ∧
        ((GlobalTheory.RelabDR.rootL O (τ, a)).2 : ℕ) < (GlobalTheory.RelabDR.rootL O (τ, b)).2 then
      X (GlobalTheory.RelabDR.rootL O (τ, b)) - X (GlobalTheory.RelabDR.rootL O (τ, a)) else 1 :
        MvPolynomial (GlobalTheory.ShFam.Pad.Letter O.S.Dw) ℝ) = gF O τ a b * hF O τ b a := by
  rw [if_congr (cond_iff O τ a b) rfl rfl]
  unfold gF hF
  by_cases h1 : a < b ∧ (b : ℕ) < O.j <;> by_cases h2 : b < a ∧ O.j ≤ (b : ℕ)
  · exact absurd (h1.1.trans h2.1) (lt_irrefl _)
  · rw [if_pos (Or.inl h1), if_pos h1, if_neg h2, mul_one]
  · rw [if_pos (Or.inr h2), if_neg h1, if_pos h2, one_mul]
  · rw [if_neg (by tauto), if_neg h1, if_neg h2, mul_one]

theorem rootDiscr_eq :
    (GlobalTheory.GoodMetric.rootDiscr O.S.Dw.mult : MvPolynomial (GlobalTheory.ShFam.Pad.Letter O.S.Dw) ℝ) =
      ∏ τ : D.what₂.Tau, ((∏ a : Fin O.N, ∏ b : Fin O.N, gF O τ a b) * ∏ a : Fin O.N, ∏ b : Fin O.N, hF O τ a b) := by
  have hb := rootL_bijective O
  rw [rootDiscr_pairs, ← hb.prod_comp]
  simp_rw [← hb.prod_comp (fun z' => if z'.1 = _ ∧ _ then _ else _)]
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have e : ∀ b : Fin O.N, (∏ x' : DV.Rt D.what₂.Tau O.N,
      (if (GlobalTheory.RelabDR.rootL O x').1 = (GlobalTheory.RelabDR.rootL O (τ, b)).1 ∧
          ((GlobalTheory.RelabDR.rootL O x').2 : ℕ) < (GlobalTheory.RelabDR.rootL O (τ, b)).2 then
        X (GlobalTheory.RelabDR.rootL O (τ, b)) - X (GlobalTheory.RelabDR.rootL O x') else 1 :
          MvPolynomial (GlobalTheory.ShFam.Pad.Letter O.S.Dw) ℝ)) = ∏ a : Fin O.N, gF O τ a b * hF O τ b a := by
    intro b
    rw [Fintype.prod_prod_type, Finset.prod_eq_single τ
      (fun τ' _ h => Finset.prod_eq_one fun a _ => if_neg fun h' => h ((fst_eq_iff O _ _).1 h'.1).1)
      (by simp)]
    exact Finset.prod_congr rfl fun a _ => split_pair O τ a b
  rw [Finset.prod_congr rfl fun b _ => e b]
  simp_rw [Finset.prod_mul_distrib]
  rw [Finset.prod_comm]

theorem aeval_vdmCl :
    aeval (GlobalTheory.RelabDR.rootSub O) (GlobalTheory.CovTestDR.vdmCl D.what₂.Tau O.N O.j) =
      C (((O.j.factorial : ℝ)⁻¹ * ((O.N - O.j).factorial : ℝ)⁻¹) ^ Fintype.card D.what₂.Tau) *
        ∏ τ : D.what₂.Tau, ((∏ a : Fin O.N, ∏ b : Fin O.N, gF O τ a b) * ∏ a : Fin O.N, ∏ b : Fin O.N, hF O τ a b) := by
  unfold GlobalTheory.CovTestDR.vdmCl
  rw [map_prod, map_pow, map_mul, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hg : aeval (GlobalTheory.RelabDR.rootSub O) (∏ a : Fin O.N, ∏ b : Fin O.N,
      (if a < b ∧ (b : ℕ) < O.j then X (τ, b) - X (τ, a) else 1 : Pol D.what₂.Tau O.N)) =
      ∏ a : Fin O.N, ∏ b : Fin O.N, gF O τ a b := by
    simp only [map_prod]
    refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => ?_
    unfold gF
    split_ifs with h
    · have ha : (a : ℕ) < O.j := lt_trans (Fin.lt_def.1 h.1) h.2
      simp [GlobalTheory.RelabDR.rootSub, GlobalTheory.RelabDR.rootSg, h.2, ha]
    · simp
  have hh : aeval (GlobalTheory.RelabDR.rootSub O) (∏ a : Fin O.N, ∏ b : Fin O.N,
      (if a < b ∧ O.j ≤ (a : ℕ) then X (τ, b) - X (τ, a) else 1 : Pol D.what₂.Tau O.N)) =
      ∏ a : Fin O.N, ∏ b : Fin O.N, hF O τ a b := by
    simp only [map_prod]
    refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => ?_
    unfold hF
    split_ifs with h
    · have ha : ¬ (a : ℕ) < O.j := not_lt.2 h.2
      have hb' : ¬ (b : ℕ) < O.j := not_lt.2 (h.2.trans (Fin.lt_def.1 h.1).le)
      simp only [map_sub, aeval_X, GlobalTheory.RelabDR.rootSub, GlobalTheory.RelabDR.rootSg, if_neg ha, if_neg hb']
      simp only [Int.cast_neg, Int.cast_one, map_neg, map_one]
      ring
    · simp
  rw [map_mul, map_mul, map_mul, aeval_C, aeval_C, hg, hh]
  simp only [algebraMap_eq]
  ring

theorem prod_fact :
    ∏ σ, (O.S.Dw.mult σ).factorial = (O.j.factorial * (O.N - O.j).factorial) ^ Fintype.card D.what₂.Tau := by
  have hb := rootL_bijective O
  calc ∏ σ, (O.S.Dw.mult σ).factorial = ∏ σ, ∏ k : Fin (O.S.Dw.mult σ), ((k : ℕ) + 1) :=
        Finset.prod_congr rfl fun σ _ => by
          rw [Fin.prod_univ_eq_prod_range (fun k => k + 1), Finset.prod_range_add_one_eq_factorial]
    _ = ∏ z : GlobalTheory.ShFam.Pad.Letter O.S.Dw, ((z.2 : ℕ) + 1) := by
          rw [Fintype.prod_sigma]
    _ = ∏ x : DV.Rt D.what₂.Tau O.N, (((GlobalTheory.RelabDR.rootL O x).2 : ℕ) + 1) :=
        (hb.prod_comp (fun z : GlobalTheory.ShFam.Pad.Letter O.S.Dw => (z.2 : ℕ) + 1)).symm
    _ = ∏ τ : D.what₂.Tau, ∏ i : Fin O.N, (if (i : ℕ) < O.j then (i : ℕ) + 1 else O.N - i) := by
        rw [Fintype.prod_prod_type]
        refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun i _ => ?_
        rw [rootL_val]
        have := i.2
        dsimp only
        split_ifs <;> omega
    _ = ∏ _τ : D.what₂.Tau, (O.j.factorial * (O.N - O.j).factorial) :=
        Finset.prod_congr rfl fun _ _ => prod_fin_split O.N O.j O.indef.2.le
    _ = _ := by rw [Finset.prod_const, Finset.card_univ]

theorem antisymm_C_mul (k : ℝ) (Q : MvPolynomial (GlobalTheory.ShFam.Pad.Letter O.S.Dw) ℝ) :
    GlobalTheory.GoodMetric.antisymm (C k * Q) = C k * GlobalTheory.GoodMetric.antisymm Q := by
  unfold GlobalTheory.GoodMetric.antisymm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_mul, rename_C, mul_smul_comm]

theorem antisymm_vdmCl : ∀ (D : D7) (O : Setup D),
    GlobalTheory.GoodMetric.antisymm (aeval (GlobalTheory.RelabDR.rootSub O) (GlobalTheory.CovTestDR.vdmCl D.what₂.Tau O.N O.j)) =
      GlobalTheory.GoodMetric.rootDiscr O.S.Dw.mult := by
  intro D O
  rw [aeval_vdmCl, ← rootDiscr_eq, antisymm_C_mul, GlobalTheory.FlagPullSquare.antisymm_rootDiscr, smul_eq_C_mul,
    ← mul_assoc, ← C_mul]
  have hf : (∏ σ, ((O.S.Dw.mult σ).factorial : ℝ)) =
      ((O.j.factorial : ℝ) * ((O.N - O.j).factorial : ℝ)) ^ Fintype.card D.what₂.Tau := by
    rw [← Nat.cast_prod, prod_fact]
    push_cast
    rfl
  rw [hf, ← mul_pow]
  have h1 : (O.j.factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((O.N - O.j).factorial : ℝ) ≠ 0 := by positivity
  rw [show (O.j.factorial : ℝ)⁻¹ * ((O.N - O.j).factorial : ℝ)⁻¹ * ((O.j.factorial : ℝ) * ((O.N - O.j).factorial : ℝ)) = 1
    by field_simp, one_pow, C_1, one_mul]

end GlobalTheory.RelabDRVdm

end
