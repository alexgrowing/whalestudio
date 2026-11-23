import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.ConsumerC
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.ConsumerA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PuniqSmoothAddSmul
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Compact
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef
import Formalism.PeriodIntegrals.ZuckTensor
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

theorem cns_shift_int (dual : Bool) {μ : Fin n → ℝ} (hμ : S7.IsHCParam μ) (s : Fin n) :
    ∀ a, ∃ m : ℤ, shiftF dual μ s a - ((n : ℝ) - 1) / 2 = m := by
  intro a
  obtain ⟨m, hm⟩ := hμ.2 a
  by_cases has : a = s
  · subst has
    cases dual
    · exact ⟨m + 1, by simp only [shiftF, cond_false, Pi.add_apply, Pi.single_eq_same]; push_cast; linarith⟩
    · exact ⟨m - 1, by simp only [shiftF, cond_true, Pi.sub_apply, Pi.single_eq_same]; push_cast; linarith⟩
  · refine ⟨m, ?_⟩
    cases dual
    · simp only [shiftF, cond_false, Pi.add_apply, Pi.single_eq_of_ne has]
      linarith
    · simp only [shiftF, cond_true, Pi.sub_apply, Pi.single_eq_of_ne has]
      linarith

theorem cns_lowK_shiftV (ε : Fin n → Bool) (μ : Fin n → ℝ) (s : Fin n) :
    lowK ε (shiftF false μ s) = lowK ε μ + HW.stdWt n s := by
  funext a
  simp only [lowK, shiftF, cond_false, HW.stdWt, Pi.add_apply, Pi.sub_apply]
  ring

theorem cns_lowK_shiftVd (ε : Fin n → Bool) (μ : Fin n → ℝ) (s : Fin n) :
    lowK ε (shiftF true μ s) = lowK ε μ + HW.dualWt n s := by
  funext a
  simp only [lowK, shiftF, cond_true, HW.dualWt, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
  ring

private theorem gap_lemma {ν : Fin n → ℝ} (h : S7.IsHCParam ν) :
    ∀ d : ℕ, ∀ a b : Fin n, b.val = a.val + d → (d : ℝ) ≤ ν a - ν b := by
  intro d
  induction d with
  | zero =>
    intro a b hab
    have : a = b := Fin.ext (by omega)
    subst this
    simp
  | succ d ih =>
    intro a b hab
    have hc : a.val + d < n := by omega
    have h1 := ih a ⟨a.val + d, hc⟩ rfl
    have hcb : (⟨a.val + d, hc⟩ : Fin n) < b := Fin.lt_iff_val_lt_val.mpr (by simp only; omega)
    have hlt := h.1 hcb
    obtain ⟨m1, hm1⟩ := h.2 b
    obtain ⟨m2, hm2⟩ := h.2 ⟨a.val + d, hc⟩
    have hint : ν ⟨a.val + d, hc⟩ - ν b = ((m2 - m1 : ℤ) : ℝ) := by push_cast; linarith
    have h0 : (0 : ℤ) < m2 - m1 := by
      have : (0 : ℝ) < ((m2 - m1 : ℤ) : ℝ) := by rw [← hint]; linarith
      exact_mod_cast this
    have h2 : (1 : ℝ) ≤ ν ⟨a.val + d, hc⟩ - ν b := by
      rw [hint]
      exact_mod_cast (by omega : (1 : ℤ) ≤ m2 - m1)
    push_cast
    linarith

private theorem lowK_diff_lemma_2 (ε : Fin n → Bool) (ν : Fin n → ℝ) (a b : Fin n) :
    lowK ε ν b - lowK ε ν a = ν b - ν a + (∑ c : Fin n,
      (((if b < c ∧ ε c ≠ ε b then 1 else 0 : ℝ) - (if c < b ∧ ε c ≠ ε b then 1 else 0)) -
        ((if b < c ∧ ε c = ε b then 1 else 0 : ℝ) - (if c < b ∧ ε c = ε b then 1 else 0)) -
      (((if a < c ∧ ε c ≠ ε a then 1 else 0 : ℝ) - (if c < a ∧ ε c ≠ ε a then 1 else 0)) -
        ((if a < c ∧ ε c = ε a then 1 else 0 : ℝ) - (if c < a ∧ ε c = ε a then 1 else 0))))) / 2 := by
  simp only [lowK, rhoN, rhoC, Pi.add_apply, Pi.sub_apply, Finset.card_filter, Finset.sum_sub_distrib]
  push_cast
  ring

private theorem term_lemma_3 {ε : Fin n → Bool} {a b : Fin n} (he : ε a = ε b) (hab : a < b) (c : Fin n) :
    (((if b < c ∧ ε c ≠ ε b then 1 else 0 : ℝ) - (if c < b ∧ ε c ≠ ε b then 1 else 0)) -
        ((if b < c ∧ ε c = ε b then 1 else 0 : ℝ) - (if c < b ∧ ε c = ε b then 1 else 0)) -
      (((if a < c ∧ ε c ≠ ε a then 1 else 0 : ℝ) - (if c < a ∧ ε c ≠ ε a then 1 else 0)) -
        ((if a < c ∧ ε c = ε a then 1 else 0 : ℝ) - (if c < a ∧ ε c = ε a then 1 else 0)))) ≤
      ((if a < c ∧ c ≤ b then 1 else 0 : ℝ) + (if a ≤ c ∧ c < b then 1 else 0)) ∧
    (ε c = ε a → (((if b < c ∧ ε c ≠ ε b then 1 else 0 : ℝ) - (if c < b ∧ ε c ≠ ε b then 1 else 0)) -
        ((if b < c ∧ ε c = ε b then 1 else 0 : ℝ) - (if c < b ∧ ε c = ε b then 1 else 0)) -
      (((if a < c ∧ ε c ≠ ε a then 1 else 0 : ℝ) - (if c < a ∧ ε c ≠ ε a then 1 else 0)) -
        ((if a < c ∧ ε c = ε a then 1 else 0 : ℝ) - (if c < a ∧ ε c = ε a then 1 else 0)))) =
      ((if a < c ∧ c ≤ b then 1 else 0 : ℝ) + (if a ≤ c ∧ c < b then 1 else 0))) := by
  rw [Fin.lt_iff_val_lt_val] at hab
  by_cases e : ε c = ε a
  · have e' : ε c = ε b := e.trans he
    refine ⟨?_, fun _ => ?_⟩
    all_goals
      simp only [e', he, ne_eq, not_true_eq_false, and_false, and_true, if_false, if_true,
        Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val]
      split_ifs <;> first | (exfalso; omega) | norm_num
  · have e' : ¬ ε c = ε b := fun h => e (h.trans he.symm)
    refine ⟨?_, fun h => absurd h e⟩
    simp only [e, e', ne_eq, not_false_eq_true, and_false, and_true, if_false, if_true,
      Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val]
    split_ifs <;> first | (exfalso; omega) | norm_num

private theorem sumR_lemma_4 {a b : Fin n} (hab : a < b) :
    ∑ c : Fin n, ((if a < c ∧ c ≤ b then 1 else 0 : ℝ) + (if a ≤ c ∧ c < b then 1 else 0)) = 2 * ((b.val - a.val : ℕ) : ℝ) := by
  rw [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_boole]
  have h1 : (Finset.univ.filter fun c : Fin n => a < c ∧ c ≤ b) = Finset.Ioc a b := by
    ext
    simp
  have h2 : (Finset.univ.filter fun c : Fin n => a ≤ c ∧ c < b) = Finset.Ico a b := by
    ext
    simp
  rw [h1, h2, Fin.card_Ioc, Fin.card_Ico]
  ring

theorem cns_hc_of_dom {ε : Fin n → Bool} (he : ∀ a b, ε a = ε b) {ν : Fin n → ℝ}
    (hint : ∀ a, ∃ m : ℤ, ν a - ((n : ℝ) - 1) / 2 = m) (hdom : HW.KDom ε (lowK ε ν)) : S7.IsHCParam ν := by
  classical
  refine ⟨fun a b hab => ?_, hint⟩
  have hd := lowK_diff_lemma_2 ε ν a b
  have hs := Finset.sum_congr rfl fun c (_ : c ∈ Finset.univ) => (term_lemma_3 (he a b) hab c).2 (he c a)
  rw [sumR_lemma_4 hab] at hs
  have hk := hdom a b hab (he a b)
  have hba : (1 : ℝ) ≤ ((b.val - a.val : ℕ) : ℝ) := by
    have := Fin.lt_iff_val_lt_val.mp hab
    exact_mod_cast (by omega : 1 ≤ b.val - a.val)
  linarith

theorem cns_dom_of_hc {ε : Fin n → Bool} {ν : Fin n → ℝ} (h : S7.IsHCParam ν) : HW.KDom ε (lowK ε ν) := by
  classical
  intro a b hab he
  have hd := lowK_diff_lemma_2 ε ν a b
  have hs := Finset.sum_le_sum fun c (_ : c ∈ Finset.univ) => (term_lemma_3 he hab c).1
  rw [sumR_lemma_4 hab] at hs
  have hg := gap_lemma h (b.val - a.val) a b (by have := Fin.lt_iff_val_lt_val.mp hab; omega)
  linarith

theorem cns_kfin_fd {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    {ε : Fin n → Bool} (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H) : PI.UpqRep.IsKFin ε σ v := ⟨⊤, inferInstance, Submodule.mem_top, fun _ _ _ _ => Submodule.mem_top⟩

theorem cns_orth_sum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*} (Sm : Finset ι)
    {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℂ (V i)] (j : ∀ i, V i →ₗ[ℂ] E)
    (hI : ∀ i ∈ Sm, ∀ v w, inner ℂ (j i v) (j i w) = inner ℂ v w)
    (hO : ∀ i ∈ Sm, ∀ i' ∈ Sm, i ≠ i' → ∀ v v', inner ℂ (j i v) (j i' v') = 0) (b c : ∀ i, V i) :
    inner ℂ (∑ i ∈ Sm, j i (b i)) (∑ i ∈ Sm, j i (c i)) = ∑ i ∈ Sm, inner ℂ (b i) (c i) := by
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [inner_sum, Finset.sum_eq_single i]
  · exact hI i hi _ _
  · intro i' hi' hne
    exact hO i hi i' hi' (Ne.symm hne) _ _
  · intro h
    exact absurd hi h

theorem cns_key_std {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : S7.KType ε Λ) (k : S7.KG ε)
    (F G : PiLp 2 (fun _ : Fin n => T.V)) :
    inner ℂ G (HW.tensOp T (HW.stdRho ε) k F) =
      ∑ c, inner ℂ (G c) (tensGrp false (fun _ => T.op k) (S7.toMK k) (fun d => F d) c) := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  unfold HW.tensOp HW.tensL HW.piIn tensGrp
  simp [Pi.single_apply]
  rfl

theorem cns_inv_entry {ε : Fin n → Bool} (k : S7.KG ε) (c d : Fin n) :
    (S7.toMK k)⁻¹ d c = star (S7.toMK k c d) := by
  have hu : S7.toMK k ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := k.2.1
  rw [Matrix.inv_eq_left_inv (Unitary.star_mul_self_of_mem hu), Matrix.star_apply]

theorem cns_key_dual {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : S7.KType ε Λ) (k : S7.KG ε)
    (F G : PiLp 2 (fun _ : Fin n => T.V)) :
    inner ℂ G (HW.tensOp T (HW.rhoDual ε) k F) =
      ∑ c, inner ℂ (G c) (tensGrp true (fun _ => T.op k) (S7.toMK k) (fun d => F d) c) := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  unfold HW.tensOp HW.tensL HW.piIn tensGrp
  simp [Pi.single_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [cns_inv_entry]
  rfl

theorem cns_zuck_cpt {ε : Fin n → Bool} (hpq : pOf ε = 0 ∨ qOf ε = 0) {μ : Fin n → ℝ} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hμ : PI.UpqRep.IsHCParam μ) (hd : PI.UpqRep.IsDS ε μ σ) :
    ∃ X : PI.ZuckTensor.TensorDS n ε μ H σ, ∀ s, s ∈ X.Sm ↔ PI.UpqRep.IsHCParam (μ + Pi.single s 1) := by
  classical
  have he := cmpt_eps_eq hpq
  have hμ' : S7.IsHCParam μ := hμ
  obtain ⟨T⟩ := HW.kType_exists ε μ hμ'
  obtain ⟨-, -, U0, hU0⟩ := compact_isDS_unique hpq hμ' hd T
  haveI : FiniteDimensional ℂ H := LinearEquiv.finiteDimensional U0.toLinearEquiv
  have hdat : ∀ s, ∃ lam' : Fin n → ℝ, ∃ T' : S7.KType ε (lowK ε lam'),
      ∃ σ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V), S7.IsHCParam lam' ∧ Formalism.MainNotions.S.IsDS ε lam' σ' ∧
        (∀ k, σ' (S7.toMK k) = T'.op k) ∧ (S7.IsHCParam (shiftF false μ s) → lam' = shiftF false μ s) := by
    intro s
    by_cases hs : S7.IsHCParam (shiftF false μ s)
    · obtain ⟨T'⟩ := HW.kType_exists ε _ hs
      obtain ⟨σ', h1, -, h3⟩ := isDS_compact hpq hs T'
      exact ⟨_, T', σ', hs, h1, h3, fun _ => rfl⟩
    · obtain ⟨σ', h1, -, h3⟩ := isDS_compact hpq hμ' T
      exact ⟨μ, T, σ', hμ', h1, h3, fun h => absurd h hs⟩
  choose lamS Ts σs hHC hDS hσT hsh using hdat
  obtain ⟨hP1, hP2, hP3⟩ := HW.pieriStd n ε (lowK ε μ) T
  have hSm : ∀ s, s ∈ univ.filter (fun s => S7.IsHCParam (shiftF false μ s)) ↔
      HW.KDom ε (lowK ε μ + HW.stdWt n s) := by
    intro s
    rw [mem_filter, ← cns_lowK_shiftV]
    exact ⟨fun h => cns_dom_of_hc h.2, fun h => ⟨mem_univ _, cns_hc_of_dom he (cns_shift_int false hμ' s) h⟩⟩
  have hΛs : ∀ s ∈ univ.filter (fun s => S7.IsHCParam (shiftF false μ s)),
      lowK ε (lamS s) = lowK ε μ + HW.stdWt n s := fun s hs => by
    rw [hsh s (mem_filter.1 hs).2, cns_lowK_shiftV]
  obtain ⟨j, hjI, hjE, hjO, hjS⟩ := cns_cpt_dec T (HW.stdRho ε) LinearMap.id (HW.stdRho_cont ε)
    (HW.stdRho_hasDeriv ε) (HW.stdWt n) (HW.stdWt_injective n) hP1 hP2 hP3 _ hSm (fun s => lowK ε (lamS s)) hΛs Ts
  refine ⟨{ Sm := univ.filter (fun s => S7.IsHCParam (shiftF false μ s))
            Hs := fun s => (Ts s).V
            σs := σs
            ds := ?_, inequiv := ?_, toSum := ?_, ofSum := ?_ }, ?_⟩
  · intro s hs
    have hs' := (mem_filter.1 hs).2
    refine ⟨hs', ?_⟩
    have e : (μ + Pi.single s 1) = lamS s := (hsh s hs').symm
    rw [e]
    exact hDS s
  · rintro s hs s' hs' hne ⟨V, hV⟩
    apply hne
    obtain ⟨S, hS⟩ := (hDS s).2.2.2.2.2.1
    have h1 := puniq_isKTypeOf_map V (fun g hg x => hV g (puniq_kset hg) x) hS
    obtain ⟨S', hS'⟩ := (hDS s').2.2.2.2.2.1
    have htop := (compact_isDS_unique hpq (hHC s') (hDS s') (Ts s')).2.1 S' hS'
    rw [htop] at hS'
    have e := cns_kt_weight_eq h1 hS'
    have e2 : lamS s = lamS s' := by
      funext a
      have := congrFun e a
      simp only [Formalism.QuantumDeterminants.lowK, PI.UpqRep.lowK, lowK, Pi.add_apply, Pi.sub_apply] at this
      linarith
    rw [hsh s (mem_filter.1 hs).2, hsh s' (mem_filter.1 hs').2] at e2
    exact cns_shift_inj false μ e2
  · intro v w x y hv hw
    obtain ⟨a, ha⟩ := hjS (WithLp.toLp 2 (fun d => x d • U0.symm v))
    obtain ⟨b, hb⟩ := hjS (WithLp.toLp 2 (fun c => y c • U0.symm w))
    refine ⟨{s // s ∈ univ.filter (fun s => S7.IsHCParam (shiftF false μ s))}, Finset.Subtype.fintype _, fun i => i.1,
      fun i => a i.1, fun i => b i.1, fun i => ⟨i.2, cns_kfin_fd _ _, cns_kfin_fd _ _⟩, fun g hg => ?_⟩
    obtain ⟨k, rfl⟩ := S7.exists_toMK (cmpt_inUJ_Kset he hg)
    simp only [hσT]
    rw [← U0.apply_symm_apply v, ← U0.apply_symm_apply w, ← hU0, LinearIsometryEquiv.inner_map_map,
      cns_coefV (fun _ => T.op k) (S7.toMK k) (U0.symm v) (U0.symm w) x y]
    have h1 := cns_key_std T k (WithLp.toLp 2 (fun d => x d • U0.symm v)) (WithLp.toLp 2 (fun c => y c • U0.symm w))
    simp only [PiLp.toLp_apply] at h1
    rw [← h1, ha, hb, map_sum,
      show (∑ s ∈ univ.filter (fun s => S7.IsHCParam (shiftF false μ s)), HW.tensOp T (HW.stdRho ε) k (j s (a s))) =
        ∑ s ∈ univ.filter (fun s => S7.IsHCParam (shiftF false μ s)), j s ((Ts s).op k (a s)) from
        Finset.sum_congr rfl fun s hs => (hjE s hs k (a s)).symm,
      cns_orth_sum _ j hjI hjO b (fun s => (Ts s).op k (a s)), ← Finset.sum_coe_sort]
    all_goals rfl
  · intro s hs v w hv hw
    refine ⟨Fin n × Fin n, inferInstance, fun p => U0 ((j s v) p.2), fun p => U0 ((j s w) p.1),
      fun p => Pi.single p.2 1, fun p => Pi.single p.1 1, fun p => ⟨cns_kfin_fd _ _, cns_kfin_fd _ _⟩,
      fun g hg => ?_⟩
    obtain ⟨k, rfl⟩ := S7.exists_toMK (cmpt_inUJ_Kset he hg)
    dsimp only
    rw [hσT, ← hjI s hs, hjE s hs, cns_key_std, cns_expandV]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← hU0, LinearIsometryEquiv.inner_map_map]
  · intro s
    exact ⟨fun hs => (mem_filter.1 hs).2, fun hs => mem_filter.2 ⟨mem_univ _, hs⟩⟩

theorem cns_zuckd_cpt {ε : Fin n → Bool} (hpq : pOf ε = 0 ∨ qOf ε = 0) {μ : Fin n → ℝ} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hμ : PI.UpqRep.IsHCParam μ) (hd : PI.UpqRep.IsDS ε μ σ) :
    ∃ X : PI.ZuckTensor.TensorDSd n ε μ H σ, ∀ s, s ∈ X.Sm ↔ PI.UpqRep.IsHCParam (μ - Pi.single s 1) := by
  classical
  have he := cmpt_eps_eq hpq
  have hμ' : S7.IsHCParam μ := hμ
  obtain ⟨T⟩ := HW.kType_exists ε μ hμ'
  obtain ⟨-, -, U0, hU0⟩ := compact_isDS_unique hpq hμ' hd T
  haveI : FiniteDimensional ℂ H := LinearEquiv.finiteDimensional U0.toLinearEquiv
  have hdat : ∀ s, ∃ lam' : Fin n → ℝ, ∃ T' : S7.KType ε (lowK ε lam'),
      ∃ σ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V), S7.IsHCParam lam' ∧ Formalism.MainNotions.S.IsDS ε lam' σ' ∧
        (∀ k, σ' (S7.toMK k) = T'.op k) ∧ (S7.IsHCParam (shiftF true μ s) → lam' = shiftF true μ s) := by
    intro s
    by_cases hs : S7.IsHCParam (shiftF true μ s)
    · obtain ⟨T'⟩ := HW.kType_exists ε _ hs
      obtain ⟨σ', h1, -, h3⟩ := isDS_compact hpq hs T'
      exact ⟨_, T', σ', hs, h1, h3, fun _ => rfl⟩
    · obtain ⟨σ', h1, -, h3⟩ := isDS_compact hpq hμ' T
      exact ⟨μ, T, σ', hμ', h1, h3, fun h => absurd h hs⟩
  choose lamS Ts σs hHC hDS hσT hsh using hdat
  obtain ⟨hP1, hP2, hP3⟩ := HW.pieriDual n ε (lowK ε μ) T
  rw [← HW.dualD_units] at hP1 hP2 hP3
  have hSm : ∀ s, s ∈ univ.filter (fun s => S7.IsHCParam (shiftF true μ s)) ↔
      HW.KDom ε (lowK ε μ + HW.dualWt n s) := by
    intro s
    rw [mem_filter, ← cns_lowK_shiftVd]
    exact ⟨fun h => cns_dom_of_hc h.2, fun h => ⟨mem_univ _, cns_hc_of_dom he (cns_shift_int true hμ' s) h⟩⟩
  have hΛs : ∀ s ∈ univ.filter (fun s => S7.IsHCParam (shiftF true μ s)),
      lowK ε (lamS s) = lowK ε μ + HW.dualWt n s := fun s hs => by
    rw [hsh s (mem_filter.1 hs).2, cns_lowK_shiftVd]
  obtain ⟨j, hjI, hjE, hjO, hjS⟩ := cns_cpt_dec T (HW.rhoDual ε) HW.dualD (HW.continuous_rhoDual ε)
    (HW.hasDeriv_rhoDual ε) (HW.dualWt n) HW.dualWt_injective hP1 hP2 hP3 _ hSm (fun s => lowK ε (lamS s)) hΛs Ts
  refine ⟨{ Sm := univ.filter (fun s => S7.IsHCParam (shiftF true μ s))
            Hs := fun s => (Ts s).V
            σs := σs
            ds := ?_, inequiv := ?_, toSum := ?_, ofSum := ?_ }, ?_⟩
  · intro s hs
    have hs' := (mem_filter.1 hs).2
    refine ⟨hs', ?_⟩
    have e : (μ - Pi.single s 1) = lamS s := (hsh s hs').symm
    rw [e]
    exact hDS s
  · rintro s hs s' hs' hne ⟨V, hV⟩
    apply hne
    obtain ⟨S, hS⟩ := (hDS s).2.2.2.2.2.1
    have h1 := puniq_isKTypeOf_map V (fun g hg x => hV g (puniq_kset hg) x) hS
    obtain ⟨S', hS'⟩ := (hDS s').2.2.2.2.2.1
    have htop := (compact_isDS_unique hpq (hHC s') (hDS s') (Ts s')).2.1 S' hS'
    rw [htop] at hS'
    have e := cns_kt_weight_eq h1 hS'
    have e2 : lamS s = lamS s' := by
      funext a
      have := congrFun e a
      simp only [Formalism.QuantumDeterminants.lowK, PI.UpqRep.lowK, lowK, Pi.add_apply, Pi.sub_apply] at this
      linarith
    rw [hsh s (mem_filter.1 hs).2, hsh s' (mem_filter.1 hs').2] at e2
    exact cns_shift_inj true μ e2
  · intro v w x y hv hw
    obtain ⟨a, ha⟩ := hjS (WithLp.toLp 2 (fun d => star (y d) • U0.symm v))
    obtain ⟨b, hb⟩ := hjS (WithLp.toLp 2 (fun c => star (x c) • U0.symm w))
    refine ⟨{s // s ∈ univ.filter (fun s => S7.IsHCParam (shiftF true μ s))}, Finset.Subtype.fintype _, fun i => i.1,
      fun i => a i.1, fun i => b i.1, fun i => ⟨i.2, cns_kfin_fd _ _, cns_kfin_fd _ _⟩, fun g hg => ?_⟩
    obtain ⟨k, rfl⟩ := S7.exists_toMK (cmpt_inUJ_Kset he hg)
    simp only [hσT]
    rw [← U0.apply_symm_apply v, ← U0.apply_symm_apply w, ← hU0, LinearIsometryEquiv.inner_map_map,
      cns_coefVd (fun _ => T.op k) (S7.toMK k) (U0.symm v) (U0.symm w) x y]
    have h1 := cns_key_dual T k (WithLp.toLp 2 (fun d => star (y d) • U0.symm v))
      (WithLp.toLp 2 (fun c => star (x c) • U0.symm w))
    simp only [PiLp.toLp_apply] at h1
    rw [← h1, ha, hb, map_sum,
      show (∑ s ∈ univ.filter (fun s => S7.IsHCParam (shiftF true μ s)), HW.tensOp T (HW.rhoDual ε) k (j s (a s))) =
        ∑ s ∈ univ.filter (fun s => S7.IsHCParam (shiftF true μ s)), j s ((Ts s).op k (a s)) from
        Finset.sum_congr rfl fun s hs => (hjE s hs k (a s)).symm,
      cns_orth_sum _ j hjI hjO b (fun s => (Ts s).op k (a s)), ← Finset.sum_coe_sort]
    all_goals rfl
  · intro s hs v w hv hw
    refine ⟨Fin n × Fin n, inferInstance, fun p => U0 ((j s v) p.2), fun p => U0 ((j s w) p.1),
      fun p => Pi.single p.1 1, fun p => Pi.single p.2 1, fun p => ⟨cns_kfin_fd _ _, cns_kfin_fd _ _⟩,
      fun g hg => ?_⟩
    obtain ⟨k, rfl⟩ := S7.exists_toMK (cmpt_inUJ_Kset he hg)
    dsimp only
    rw [hσT, ← hjI s hs, hjE s hs, cns_key_dual, cns_expandVd]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← hU0, LinearIsometryEquiv.inner_map_map]
  · intro s
    exact ⟨fun hs => (mem_filter.1 hs).2, fun hs => mem_filter.2 ⟨mem_univ _, hs⟩⟩

end ReciprocityTheory.ChartRestriction.DS.G2
