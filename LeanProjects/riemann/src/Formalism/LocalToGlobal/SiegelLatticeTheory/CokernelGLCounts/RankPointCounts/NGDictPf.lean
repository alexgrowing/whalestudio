import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGDict

noncomputable section

open scoped Classical
open ValuativeRel

namespace Formalism.L2.SG.Pf

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.MainNotions.BridgeLemma Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.NGDict

section HpSec

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
variable {H : HermSp M V} {r : ℕ} {P : FPair H r}

omit [TopologicalSpace E] [MeasurableSpace E] [CommRing E] in
theorem le_mul_mul_rpow_neg_half_of_le_inv_sq {a b c q : ℝ} (hq : 0 < q) (a0 : 0 < a) (a1 : a ≤ 1) (b0 : 0 < b) (b1 : b ≤ 1)
    (c0 : 0 < c) (h : c ≤ (q ^ 2)⁻¹) : q ≤ (a * b * c) ^ (-(1 / 2 : ℝ)) := by
  have hx : a * b * c ≤ (q ^ 2)⁻¹ := by
    calc a * b * c ≤ 1 * 1 * c := by gcongr
      _ = c := by ring
      _ ≤ _ := h
  have e : ((q ^ 2)⁻¹) ^ (-(1 / 2 : ℝ)) = q := by
    rw [Real.rpow_neg (by positivity), Real.inv_rpow (by positivity), inv_inv, ← Real.sqrt_eq_rpow,
      Real.sqrt_sq hq.le]
  calc q = ((q ^ 2)⁻¹) ^ (-(1 / 2 : ℝ)) := e.symm
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by positivity) hx (by norm_num)

theorem ends_isUnit {l : ℕ} (hl : l ∈ P.ends) : IsUnit (P.Dm l) :=
  (((@Finset.mem_filter _ _ (Classical.decPred _) _ _).1 hl).2).2

theorem residue_le_height_nonprime (hOK : M.OK) (hR : P.RelG (theta M))
    (hex : ∃ (d : Datum P) (t : Term V M r), IsTermOver P d t) (hp : ¬ P.PrimeTo) : StepHp P := by
  obtain ⟨d, t, ht⟩ := hex
  have hG : P.Gv ≠ 0 := hR.2.2.1
  obtain ⟨⟨a0, a1⟩, ⟨b0, b1⟩, c0, c1⟩ := ng_factors hOK hG ht
  have hq : (0 : ℝ) < qF F := by
    have := two_le_residue_card hOK
    exact_mod_cast (by omega : 0 < qF F)
  have hnt := Formalism.MainNotions.LocalModelPeriodLattices.nontrivial_E M.L
  have hm1 : ((-1 : F) ^ (r + 1)) ∈ 𝒪[F] := pow_mem (neg_mem (one_mem _)) _
  unfold StepHp FPair.Hp
  rcases hs : M.split with _ | g
  · have hnot : ¬ IsUnitO M P.Gv ∨ ∃ l ∈ P.ends, ¬ IsUnitO M (P.Dm l) := by
      by_contra hc
      push Not at hc
      exact hp ⟨hs, hc.1, hc.2⟩
    rcases hnot with hGn | ⟨l, hl, hDn⟩
    · refine ng_real_q hq a0 a1 b0 b1 c0 c1 (Or.inr ?_)
      have hfix : M.L.cj P.Gv = P.Gv := by
        unfold FPair.Gv HermSp.Gdet HermSp.normE
        simp only [map_sub, map_mul, M.L.cj_cj, AlgEquiv.commutes]
        ring
      obtain ⟨a, ha⟩ := (M.L.cj_fix _).1 hfix
      have hdet : (H.gram P.MMgen).det = algebraMap F E ((-1) ^ (r + 1) * a) := by
        rw [gram_det_eq P hs, ← ha, map_mul, map_pow, map_neg, map_one]
      have hmem : (H.gram P.MMgen).det ∈ M.L.O := by
        rw [← ng_term_gram ht]
        exact ng_det_mem _ (fun a b => ng_term_int ht (ng_term_MM ht _) (ng_term_MM ht _))
      have haO : (-1) ^ (r + 1) * a ∈ 𝒪[F] :=
        Formalism.MainNotions.LocalModelPeriodLattices.mem_OF_of_mem_O M.L _ (by rw [← hdet]; exact hmem)
      have haO' : a ∈ 𝒪[F] := by
        have h2 := mul_mem hm1 haO
        have e : ((-1 : F) ^ (r + 1)) * ((-1) ^ (r + 1) * a) = a := by
          rw [← mul_assoc, ← mul_pow]; simp
        rwa [e] at h2
      have ha0 : (-1) ^ (r + 1) * a ≠ 0 := by
        refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (fun h => hG ?_)
        rw [← ha, h, map_zero]
      rw [hdet]
      refine ng_modK_nonunit hOK ⟨_, haO⟩ ha0 (fun hu => hGn ?_)
      obtain ⟨y, hy⟩ := hu.exists_right_inv
      have hy' : ((-1) ^ (r + 1) * a) * (y : F) = 1 := congrArg Subtype.val hy
      refine ⟨?_, algebraMap F E ((-1) ^ (r + 1) * (y : F)), ?_, ?_⟩
      · rw [← ha]; exact Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L ⟨a, haO'⟩
      · exact Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L ⟨_, mul_mem hm1 y.2⟩
      · rw [← ha, ← map_mul]
        have : a * ((-1) ^ (r + 1) * (y : F)) = ((-1) ^ (r + 1) * a) * (y : F) := by ring
        rw [this, hy', map_one]
    · have hlu : IsUnit (P.Dm l) := ends_isUnit hl
      have hfac : ∀ l' ∈ P.ends, 0 < M.modK (P.Dm l' * M.L.cj (P.Dm l')) ∧
          M.modK (P.Dm l' * M.L.cj (P.Dm l')) ≤ 1 := by
        intro l' hl'
        have hu := ends_isUnit hl'
        have h := ng_modK hOK (hu.mul (hu.map M.L.cj))
        exact ⟨h.1, h.2 (M.L.O.mul_mem (ng_term_Dm ht l')
          (Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O M.L _ (ng_term_Dm ht l')))⟩
      have hcl : ∏ l' ∈ P.ends, M.modK (P.Dm l' * M.L.cj (P.Dm l')) ≤
          M.modK (P.Dm l * M.L.cj (P.Dm l)) := by
        rw [← Finset.mul_prod_erase _ _ hl]
        have h1 : ∏ x ∈ P.ends.erase l, M.modK (P.Dm x * M.L.cj (P.Dm x)) ≤ 1 :=
          Finset.prod_le_one (fun x hx => (hfac x (Finset.mem_of_mem_erase hx)).1.le)
            (fun x hx => (hfac x (Finset.mem_of_mem_erase hx)).2)
        have h0 := (hfac l hl).1.le
        calc _ ≤ M.modK (P.Dm l * M.L.cj (P.Dm l)) * 1 := mul_le_mul_of_nonneg_left h1 h0
          _ = _ := mul_one _
      refine le_mul_mul_rpow_neg_half_of_le_inv_sq hq a0 a1 b0 b1 c0 (le_trans hcl ?_)
      have hfix : M.L.cj (P.Dm l * M.L.cj (P.Dm l)) = P.Dm l * M.L.cj (P.Dm l) := by
        rw [map_mul, M.L.cj_cj, mul_comm]
      obtain ⟨a, ha⟩ := (M.L.cj_fix _).1 hfix
      have hxO : P.Dm l * M.L.cj (P.Dm l) ∈ M.L.O :=
        M.L.O.mul_mem (ng_term_Dm ht l) (Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O M.L _ (ng_term_Dm ht l))
      have haO : a ∈ 𝒪[F] := Formalism.MainNotions.LocalModelPeriodLattices.mem_OF_of_mem_O M.L _ (by rw [ha]; exact hxO)
      have hxu : IsUnit (P.Dm l * M.L.cj (P.Dm l)) := hlu.mul (hlu.map M.L.cj)
      have ha0 : a ≠ 0 := by
        rintro rfl
        rw [map_zero] at ha
        rw [← ha] at hxu
        exact not_isUnit_zero hxu
      rw [← ha]
      refine ng_modK_nonunit hOK ⟨a, haO⟩ ha0 (fun hu => hDn ?_)
      obtain ⟨y, hy⟩ := hu.exists_right_inv
      have hy' : a * (y : F) = 1 := congrArg Subtype.val hy
      refine ⟨ng_term_Dm ht l, M.L.cj (P.Dm l) * algebraMap F E (y : F),
        M.L.O.mul_mem (Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O M.L _ (ng_term_Dm ht l))
          (Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L y), ?_⟩
      rw [← mul_assoc, ← ha, ← map_mul, hy', map_one]
  · refine ng_real_q hq a0 a1 b0 b1 c0 c1 (Or.inl ?_)
    have hθ : theta M = (g.q : F) := by
      unfold theta
      split
      · rename_i hg
        rw [hs] at hg
        cases hg
      · rename_i g' hg
        rw [hs] at hg
        cases hg
        rfl
    rw [hθ]
    exact ng_modK_nonunit hOK g.q (fun h => g.q_irr.ne_zero (Subtype.ext h)) g.q_irr.not_isUnit

end HpSec

section GlueSec

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
variable {H : HermSp M V} {r : ℕ} {P : FPair H r}

theorem massS_congr (R : Reps P) (d : Datum P) {S S' : Term V M r → Prop}
    (h : ∀ t ∈ R.RT d, (S t ↔ S' t)) : massS R d S = massS R d S' := by
  unfold massS
  exact Equiv.tsum_eq (Equiv.subtypeEquivRight (fun t => and_congr_right (fun ht => h t ht)))
    (fun t => mu P t.1)

theorem amp_congr (R : Reps P) (d : Datum P) {S S' : Term V M r → Prop}
    (h : ∀ t ∈ R.RT d, (S t ↔ S' t)) : amp R d S = amp R d S' := by
  unfold amp
  exact Equiv.tsum_eq (Equiv.subtypeEquivRight (fun t => and_congr_right (fun ht => h t ht)))
    (fun t => (mu P t.1 : ℂ) * om P t.1)

theorem amp_false (R : Reps P) (d : Datum P) : amp R d (fun _ => False) = 0 := by
  have e1 : IsEmpty {t // t ∈ R.RT d ∧ False} := ⟨fun t => t.2.2⟩
  unfold amp
  rw [tsum_empty]

theorem massS_false (R : Reps P) (d : Datum P) : massS R d (fun _ => False) = 0 := by
  have e1 : IsEmpty {t // t ∈ R.RT d ∧ False} := ⟨fun t => t.2.2⟩
  unfold massS
  rw [tsum_empty]

theorem massE_eq (R : Reps P) (d : Datum P) (hs : Summable (fun t : R.RT d => mu P t.1))
    (S : Term V M r → Prop) : massE R d S = ENNReal.ofReal (massS R d S) := by
  unfold massE massS
  rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => mu_nonneg _) (summable_sub R d hs S)]

theorem massS_le_finsum (R : Reps P) (d : Datum P) (hs : Summable (fun t : R.RT d => mu P t.1))
    (S : Term V M r → Prop) {ι : Type} (s : Finset ι) (Si : ι → Term V M r → Prop)
    (h : ∀ t ∈ R.RT d, S t → ∃ i ∈ s, Si i t) : massS R d S ≤ ∑ i ∈ s, massS R d (Si i) := by
  set f : Term V M r → ℝ := fun t => mu P t with hf
  have e : ∀ S' : Term V M r → Prop, massS R d S' = ∑' t, ({t | t ∈ R.RT d ∧ S' t} : Set _).indicator f t :=
    fun S' => tsum_subtype ({t | t ∈ R.RT d ∧ S' t} : Set _) f
  have hsum : ∀ S' : Term V M r → Prop, Summable (({t | t ∈ R.RT d ∧ S' t} : Set _).indicator f) := by
    intro S'
    rw [← summable_subtype_iff_indicator]
    exact summable_sub R d hs S'
  have hnn : ∀ (S' : Term V M r → Prop) t, 0 ≤ ({t | t ∈ R.RT d ∧ S' t} : Set _).indicator f t :=
    fun S' t => Set.indicator_nonneg (fun _ _ => mu_nonneg _) t
  rw [e S]
  simp only [e]
  rw [← Summable.tsum_finsetSum (fun i _ => hsum _)]
  refine Summable.tsum_le_tsum (fun t => ?_) (hsum S) (summable_sum (fun i _ => hsum _))
  by_cases ht : t ∈ R.RT d ∧ S t
  · obtain ⟨i, hi, hSi⟩ := h t ht.1 ht.2
    rw [Set.indicator_of_mem (show t ∈ {t | t ∈ R.RT d ∧ S t} from ht)]
    calc f t = ({t | t ∈ R.RT d ∧ Si i t} : Set _).indicator f t :=
          (Set.indicator_of_mem (show t ∈ {t | t ∈ R.RT d ∧ Si i t} from ⟨ht.1, hSi⟩) f).symm
      _ ≤ ∑ j ∈ s, ({t | t ∈ R.RT d ∧ Si j t} : Set _).indicator f t :=
          Finset.single_le_sum (f := fun j => ({t | t ∈ R.RT d ∧ Si j t} : Set _).indicator f t)
            (fun j _ => hnn _ t) hi
  · rw [Set.indicator_of_notMem (show t ∉ {t | t ∈ R.RT d ∧ S t} from ht)]
    exact Finset.sum_nonneg (fun j _ => hnn _ t)

theorem massS_mono (R : Reps P) (d : Datum P) (hs : Summable (fun t : R.RT d => mu P t.1))
    {S S' : Term V M r → Prop} (h : ∀ t ∈ R.RT d, S t → S' t) : massS R d S ≤ massS R d S' := by
  have := massS_le_finsum R d hs S ({()} : Finset Unit) (fun _ => S')
    (fun t ht hS => ⟨(), Finset.mem_singleton_self _, h t ht hS⟩)
  simpa using this

theorem massSubset_le_geometric (hOK : M.OK) {k : ℕ} (hk : 2 ≤ k) {R : Reps P} (hBB : StepBB P) (hC2 : MassBoundIndexSets k R)
    (hH : 1 ≤ P.Hp) (d : Datum P) (hs : Summable (fun t : R.RT d => mu P t.1)) (S : Term V M r → Prop) (N : ℕ)
    (h : ∀ t ∈ R.RT d, S t → Icard H t ≤ qF F ^ N) :
    massS R d S ≤ 2 * A0 P * ((qF F : ℝ) ^ N) ^ (k - 1) := by
  have hq2 := two_le_residue_card hOK
  have hA0 : 0 ≤ A0 P := by unfold A0; exact pow_nonneg (by linarith) _
  calc massS R d S ≤ ∑ i ∈ Finset.range (N + 1), massS R d (fun t => Icard H t = qF F ^ i) := by
        refine massS_le_finsum R d hs S _ _ (fun t ht hSt => ?_)
        obtain ⟨_, _, _, i, hi⟩ := hBB d t ((R.hRT d).1 ht)
        refine ⟨i, Finset.mem_range.2 ?_, hi⟩
        have h1 := h t ht hSt
        rw [hi] at h1
        have := (Nat.pow_le_pow_iff_right (by omega)).1 h1
        omega
    _ ≤ ∑ i ∈ Finset.range (N + 1), A0 P * ((qF F : ℝ) ^ i) ^ (k - 1) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have h1 := hC2 d (qF F ^ i)
        rw [massE_eq R d hs] at h1
        have h2 : (0 : ℝ) ≤ A0 P * (((qF F ^ i : ℕ) : ℝ)) ^ (k - 1) := by positivity
        have h3 := (ENNReal.ofReal_le_ofReal_iff h2).1 h1
        push_cast at h3
        exact h3
    _ = A0 P * ∑ i ∈ Finset.range (N + 1), ((qF F : ℝ) ^ i) ^ (k - 1) := by rw [Finset.mul_sum]
    _ ≤ A0 P * (2 * ((qF F : ℝ) ^ N) ^ (k - 1)) :=
        mul_le_mul_of_nonneg_left (Formalism.HermitianLatticeCounting.Final.S4.geomPowers (qF F) k N hq2 hk) hA0
    _ = 2 * A0 P * ((qF F : ℝ) ^ N) ^ (k - 1) := by ring

theorem sum_wt_mul_massS_le_inv_pow_mul_total_mass {k : ℕ} {R : Reps P} {d0 : Datum P} (hC1 : MassBoundLevelSets k R d0) (hH : 1 ≤ P.Hp) (Ds : Finset R.RD)
    (off : ∀ d : R.RD, d ∉ Ds → R.RT d.1 = ∅) (summ : ∀ d : R.RD, Summable (fun t : R.RT d.1 => mu P t.1))
    (β : ℕ) (hβ : 1 ≤ β) (S : Term V M r → Prop) (h : ∀ (d : Datum P), ∀ t ∈ R.RT d, S t → be H t = β) :
    ∑ d : Ds, Datum.wt d0 d.1.1 * massS R d.1.1 S ≤
      A1 P * ((β : ℝ) ^ (k - 1))⁻¹ * ∑ d : Ds, Datum.wt d0 d.1.1 * ∑' t : R.RT d.1.1, mu P t.1 := by
  have hA : 0 ≤ A1 P * ((β : ℝ) ^ (k - 1))⁻¹ := by
    unfold A1
    have : (0 : ℝ) ≤ P.Hp := by linarith
    positivity
  have hle : ∑ d : Ds, Datum.wt d0 d.1.1 * massS R d.1.1 S ≤
      ∑ d : Ds, Datum.wt d0 d.1.1 * massS R d.1.1 (fun t => be H t = β) := by
    refine Finset.sum_le_sum (fun d _ => mul_le_mul_of_nonneg_left ?_ (wt_nonneg _ _))
    exact massS_mono R d.1.1 (summ d.1) (fun t ht hS => h _ t ht hS)
  refine le_trans hle ?_
  have key := hC1 β hβ
  have e1 : ∑' d : R.RD, ENNReal.ofReal (Datum.wt d0 d.1) * massE R d.1 (fun t => be H t = β) =
      ENNReal.ofReal (∑ d : Ds, Datum.wt d0 d.1.1 * massS R d.1.1 (fun t => be H t = β)) := by
    rw [tsum_eq_sum (s := Ds) (fun d hd => by
        have e3 : massE R d.1 (fun t => be H t = β) = 0 := by
          unfold massE
          have e2 : IsEmpty {t // t ∈ R.RT d.1 ∧ be H t = β} :=
            ⟨fun t => (Set.ext_iff.1 (off d hd) t.1).1 t.2.1⟩
          rw [tsum_empty]
        rw [e3, mul_zero]),
      Finset.sum_coe_sort Ds (fun d : R.RD => Datum.wt d0 d.1 * massS R d.1 (fun t => be H t = β)),
      ENNReal.ofReal_sum_of_nonneg (fun d _ => mul_nonneg (wt_nonneg _ _) (massS_nonneg _ _ _))]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [ENNReal.ofReal_mul (wt_nonneg _ _), massE_eq R d.1 (summ d) _]
  rw [e1, nn_eq R d0 Ds off summ, ← ENNReal.ofReal_mul hA] at key
  have hX : 0 ≤ ∑ d : Ds, Datum.wt d0 d.1.1 * ∑' t : R.RT d.1.1, mu P t.1 :=
    Finset.sum_nonneg (fun d _ => mul_nonneg (wt_nonneg _ _) (tsum_nonneg (fun _ => mu_nonneg _)))
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hA hX)).1 key

theorem theta_G {g : SplitG M.L} (hs : M.split = some g) : theta M = (g.q : F) := by
  unfold theta
  split
  · rename_i hg
    rw [hs] at hg
    cases hg
  · rename_i g' hg
    rw [hs] at hg
    cases hg
    rfl

theorem theta_L (hs : M.split = none) : theta M = 1 := by
  unfold theta
  split
  · rfl
  · rename_i g' hg
    rw [hs] at hg
    cases hg

theorem MM_G {g : SplitG M.L} (hs : M.split = some g) (t : Term V M r) :
    H.MMfam t = Sum.elim t.f (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a)) := by
  unfold HermSp.MMfam
  split
  · rename_i hg
    rw [hs] at hg
    cases hg
  · rename_i g' hg
    rw [hs] at hg
    cases hg
    rfl

theorem outAt_of_not_mem (t : Term V M r) {v : V}
    (hME : v ∈ Submodule.span E (Set.range (H.MMfam t)))
    (hn : v ∉ Submodule.span M.L.O (Set.range (H.MMfam t))) : ∃ i, OutAt t v i := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hME
  by_contra hno
  push Not at hno
  apply hn
  have hcO : ∀ j, c j ∈ M.L.O := by
    rcases hs : M.split with _ | g
    · have hMM : H.MMfam t = Sum.elim t.f t.f' := ng_MM_L hs t
      have hth : thE M = 1 := by unfold thE; rw [theta_L hs, map_one]
      have hexp : thE M • v = ∑ j, c (Sum.inl j) • t.f j + ∑ j, c (Sum.inr j) • t.f' j := by
        rw [hth, one_smul, ← hc, Fintype.sum_sum_type, hMM]
        simp only [Sum.elim_inl, Sum.elim_inr]
      have hRR : ∀ i, InRR M (c (Sum.inl i)) (c (Sum.inr i)) := fun i => by
        by_contra hi
        exact hno i ⟨_, _, hexp, hi⟩
      rintro (j | j)
      · obtain ⟨h1, d, hd, he⟩ := hRR j
        rw [hth, one_mul] at he
        have e : c (Sum.inl j) = d - c (Sum.inr j) := by rw [← he]; ring
        rw [e]
        exact M.L.O.sub_mem hd h1
      · exact (hRR j).1
    · have hMM := MM_G (H := H) hs t
      have hq0 : (g.q : F) ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext h)
      have hth : thE M = algebraMap F E (g.q : F) := by unfold thE; rw [theta_G hs]
      have hu : algebraMap F E (g.q : F) * algebraMap F E ((g.q : F)⁻¹) = 1 := by
        rw [← map_mul, mul_inv_cancel₀ hq0, map_one]
      have hexp : thE M • v = ∑ j, (thE M * c (Sum.inl j) - c (Sum.inr j)) • t.f j +
          ∑ j, c (Sum.inr j) • t.f' j := by
        rw [← hc, Fintype.sum_sum_type, hMM]
        simp only [Sum.elim_inl, Sum.elim_inr]
        rw [smul_add, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [smul_smul, smul_smul, smul_smul, hth,
          show algebraMap F E (g.q : F) * c (Sum.inr j) * algebraMap F E ((g.q : F)⁻¹) = c (Sum.inr j) by
            linear_combination (c (Sum.inr j)) * hu, smul_sub, sub_smul]
        abel
      have hRR : ∀ i, InRR M (thE M * c (Sum.inl i) - c (Sum.inr i)) (c (Sum.inr i)) := fun i => by
        by_contra hi
        exact hno i ⟨_, _, hexp, hi⟩
      rintro (j | j)
      · obtain ⟨h1, d, hd, he⟩ := hRR j
        rw [sub_add_cancel, hth] at he
        have e : c (Sum.inl j) = d := by
          calc c (Sum.inl j) = (algebraMap F E ((g.q : F)⁻¹) * algebraMap F E (g.q : F)) * c (Sum.inl j) := by
                rw [mul_comm (algebraMap F E ((g.q : F)⁻¹)), hu, one_mul]
            _ = algebraMap F E ((g.q : F)⁻¹) * (algebraMap F E (g.q : F) * c (Sum.inl j)) := by ring
            _ = algebraMap F E ((g.q : F)⁻¹) * (algebraMap F E (g.q : F) * d) := by rw [he]
            _ = d := by rw [← mul_assoc, mul_comm (algebraMap F E ((g.q : F)⁻¹)), hu, one_mul]
        rw [e]; exact hd
      · exact (hRR j).1
  rw [← hc]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  exact Submodule.smul_mem (Submodule.span M.L.O (Set.range (H.MMfam t))) (⟨c j, hcO j⟩ : M.L.O)
    (Submodule.subset_span ⟨j, rfl⟩)

theorem lev_bdd (t : Term V M r) (y : V) :
    BddAbove {n | ∃ i : Fin (r + 1), n = i.val + 1 ∧ OutAt t y i} :=
  ⟨r + 1, by rintro n ⟨i, rfl, _⟩; have := i.isLt; omega⟩

theorem lev_le (t : Term V M r) (y : V) : lev t y ≤ r + 1 := by
  unfold lev
  apply csSup_le'
  rintro n ⟨i, rfl, _⟩
  have := i.isLt
  omega

theorem le_lev {t : Term V M r} {y : V} {i : Fin (r + 1)} (h : OutAt t y i) : i.val + 1 ≤ lev t y :=
  le_csSup (lev_bdd t y) ⟨i, rfl, h⟩

theorem lev_le_r {t : Term V M r} {y : V} (h : ¬ OutAt t y (Fin.last r)) : lev t y ≤ r := by
  unfold lev
  apply csSup_le'
  rintro n ⟨i, rfl, hi⟩
  have hne : i ≠ Fin.last r := fun e => h (e ▸ hi)
  have := Fin.val_lt_last hne
  omega

theorem levC_le (t : Term V M r) (c : BB H t) : levC H t c ≤ r + 1 :=
  csSup_le' (by rintro n ⟨y, _, rfl⟩; exact lev_le t y)

theorem lev_le_levC (t : Term V M r) (y : satM H t) :
    lev t y ≤ levC H t (Submodule.Quotient.mk y) :=
  le_csSup ⟨r + 1, by rintro n ⟨y, _, rfl⟩; exact lev_le t y⟩ ⟨y, rfl, rfl⟩

theorem Jmax_bdd (t : Term V M r) : BddAbove (Set.range (levC H t)) :=
  ⟨r + 1, by rintro n ⟨c, rfl⟩; exact levC_le t c⟩

theorem BBne_class {t : Term V M r} (hB : BBne (H := H) t) :
    ∃ y : satM H t, (Submodule.Quotient.mk y : BB H t) ≠ 0 ∧ 1 ≤ lev t y := by
  obtain ⟨v, hv, hME, hn⟩ := hB
  have hs : v ∈ satM H t := Submodule.mem_inf.2 ⟨hv, hME⟩
  refine ⟨⟨v, hs⟩, fun h0 => hn ?_, ?_⟩
  · have := (Submodule.Quotient.mk_eq_zero _).1 h0
    exact this
  · obtain ⟨i, hi⟩ := outAt_of_not_mem t hME hn
    exact le_trans (Nat.le_add_left 1 _) (le_lev hi)

theorem be_ge_two {t : Term V M r} (hB : BBne (H := H) t) (hF : Finite (BB H t)) : 2 ≤ be H t := by
  obtain ⟨y, hy, _⟩ := BBne_class hB
  have : Nontrivial (BB H t) := ⟨⟨_, 0, hy⟩⟩
  have := Finite.one_lt_card_iff_nontrivial.2 this
  unfold be
  omega

theorem one_le_Jmax {t : Term V M r} (hB : BBne (H := H) t) : 1 ≤ Jmax H t := by
  obtain ⟨y, _, hy⟩ := BBne_class hB
  exact le_trans hy (le_trans (lev_le_levC t y) (le_csSup (Jmax_bdd t) ⟨_, rfl⟩))

theorem Jmax_le_r {t : Term V M r} (hT : IsTypeBe H t) : Jmax H t ≤ r := by
  unfold Jmax
  apply csSup_le'
  rintro n ⟨c, rfl⟩
  apply csSup_le'
  rintro n ⟨y, _, rfl⟩
  exact lev_le_r (hT.2.1 y y.2)

theorem one_le_beJ {t : Term V M r} (hF : Finite (BB H t)) : 1 ≤ beJ H t := by
  have hne : (Set.range (levC H t)).Nonempty := ⟨_, 0, rfl⟩
  have hfin : (Set.range (levC H t)).Finite := Set.finite_range _
  obtain ⟨c, hc⟩ := hne.csSup_mem hfin
  have : Nonempty {c : BB H t // levC H t c = Jmax H t} := ⟨⟨c, hc⟩⟩
  unfold beJ
  exact Nat.one_le_iff_ne_zero.2 (Nat.card_pos).ne'

theorem Icard_le_be {t : Term V M r} (hF : Finite (BB H t)) : Icard H t ≤ be H t :=
  Finite.card_subtype_le _

theorem typOf_be (t : Term V M r) : (typOf H t).be = be H t := by
  unfold typOf; split <;> rfl

theorem typOf_kind (t : Term V M r) : (typOf H t).kindBe = true ↔ IsTypeBe H t := by
  unfold typOf; split <;> simp_all

theorem typOf_eq_FF (t : Term V M r) (β J βJ : ℕ) : typOf H t = ⟨true, β, J, βJ⟩ ↔ FF H β J βJ t := by
  unfold typOf FF
  split
  · rename_i h; simp [h]
  · rename_i h; simp [h]

theorem two_mul_A0_le (hH2 : 2 ≤ P.Hp) : 2 * A0 P ≤ P.Hp ^ (22 * (r + 1) ^ 2) := by
  unfold A0
  have hH : 1 ≤ P.Hp := by linarith
  calc 2 * P.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) ≤ P.Hp * P.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) :=
        mul_le_mul_of_nonneg_right hH2 (pow_nonneg (by linarith) _)
    _ = P.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1) + 1) := by ring
    _ ≤ _ := pow_le_pow_right₀ hH (by nlinarith)

theorem A1_le_Hp_pow (hH2 : 2 ≤ P.Hp) : A1 P ≤ P.Hp ^ (22 * (r + 1) ^ 2) := by
  unfold A1
  have hH : 1 ≤ P.Hp := by linarith
  calc 4 * P.Hp ^ (4 * (r + 1)) ≤ P.Hp ^ 2 * P.Hp ^ (4 * (r + 1)) :=
        mul_le_mul_of_nonneg_right (by nlinarith) (pow_nonneg (by linarith) _)
    _ = P.Hp ^ (4 * (r + 1) + 2) := by ring
    _ ≤ _ := pow_le_pow_right₀ hH (by nlinarith)

theorem nnR_nonneg {R : Reps P} (d0 : Datum P) (Ds : Finset R.RD) :
    0 ≤ ∑ d : Ds, Datum.wt d0 d.1.1 * ∑' t : R.RT d.1.1, mu P t.1 :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (wt_nonneg _ _) (tsum_nonneg (fun _ => mu_nonneg _)))

theorem be_log (hOK : M.OK) (hBB : StepBB P) {d : Datum P} {t : Term V M r} (ht : IsTermOver P d t) :
    be H t = qF F ^ Nat.log (qF F) (be H t) ∧ Nat.log (qF F) (be H t) < ⌊P.Hp⌋₊ := by
  have hq2 := two_le_residue_card hOK
  obtain ⟨_, hle, ⟨i, hi⟩, _⟩ := hBB d t ht
  rw [hi, Nat.log_pow (by omega)]
  refine ⟨rfl, ?_⟩
  have h1 : i < qF F ^ i := Nat.lt_pow_self (by omega)
  have h2 : qF F ^ i ≤ ⌊P.Hp⌋₊ := Nat.le_floor (by rw [← hi]; exact hle)
  omega

theorem localBoundSecond_of (hOK : M.OK) {k : ℕ} (hk : 4 * r + 7 ≤ k) (hG : P.Gv ≠ 0)
    (hex : ∃ (d : Datum P) (t : Term V M r), IsTermOver P d t)
    (hHp : StepHp P) {R : Reps P} {d0 : Datum P} (hS : Steps k R d0) (S : Term V M r → Prop) :
    Nonempty (NGCore2 k R d0 22 S) := by
  obtain ⟨hFin, hBB, hC2, hC1, -, -, -⟩ := hS
  obtain ⟨d1, t1, ht1⟩ := hex
  have hH : 1 ≤ P.Hp := ng_Hp_ge_one hOK hG ht1
  have hq2 := two_le_residue_card hOK
  have hq : (2 : ℝ) ≤ qF F := by exact_mod_cast hq2
  have hH2 : (2 : ℝ) ≤ P.Hp := le_trans hq hHp
  have hN2 : 2 ≤ ⌊P.Hp⌋₊ := Nat.le_floor (by exact_mod_cast hH2)
  let typ : Term V M r → Fin ⌊P.Hp⌋₊ := fun t =>
    if h : Nat.log (qF F) (be H t) < ⌊P.Hp⌋₊ then ⟨_, h⟩ else ⟨0, by omega⟩
  have htyp : ∀ (d : Datum P) (t : Term V M r), IsTermOver P d t → be H t = qF F ^ (typ t : ℕ) := by
    intro d t ht
    obtain ⟨h1, h2⟩ := be_log hOK hBB ht
    simp only [typ, dif_pos h2]
    exact h1
  have hk2 : 2 ≤ k := by omega
  refine ⟨{
    Ds := hFin.1.choose
    off := hFin.1.choose_spec
    summ := hFin.2
    Ty := Fin ⌊P.Hp⌋₊
    fin := inferInstance
    typ := typ
    be := fun τ => (qF F : ℝ) ^ (τ : ℕ)
    I := fun τ => (qF F : ℝ) ^ (τ : ℕ)
    card := ?_
    be1 := fun τ => one_le_pow₀ (by linarith)
    I0 := fun τ => by positivity
    Ibe := fun τ => le_rfl
    c2 := ?_
    c1 := ?_ }⟩
  · simp only [Fintype.card_fin]
    calc (⌊P.Hp⌋₊ : ℝ) ≤ P.Hp := Nat.floor_le (by linarith)
      _ ≤ P.Hp ^ (22 * (r + 1) ^ 2) := le_self_pow₀ hH (by positivity)
  · intro τ d
    have h1 := massSubset_le_geometric hOK hk2 hBB hC2 hH d.1.1 (hFin.2 d.1) (fun t => S t ∧ typ t = τ) τ (fun t ht hSt => by
      have hT := (R.hRT d.1.1).1 ht
      have hb := htyp d.1.1 t hT
      obtain ⟨hF, _⟩ := hBB d.1.1 t hT
      calc Icard H t ≤ be H t := Icard_le_be hF
        _ = _ := by rw [hb, hSt.2])
    refine le_trans h1 (mul_le_mul_of_nonneg_right (two_mul_A0_le hH2) (by positivity))
  · intro τ
    refine le_trans (sum_wt_mul_massS_le_inv_pow_mul_total_mass hC1 hH hFin.1.choose hFin.1.choose_spec hFin.2 (qF F ^ (τ : ℕ))
      (Nat.one_le_pow _ _ (by omega)) _ (fun d t ht hSt => by rw [htyp d t ((R.hRT d).1 ht), hSt.2])) ?_
    push_cast
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (A1_le_Hp_pow hH2) (by positivity)) (nnR_nonneg _ _)

theorem localBoundFirst_of (hOK : M.OK) {k : ℕ} (hk : 4 * r + 7 ≤ k) (hG : P.Gv ≠ 0)
    (hex : ∃ (d : Datum P) (t : Term V M r), IsTermOver P d t)
    (hHp : StepHp P) {R : Reps P} {d0 : Datum P} (hS : Steps k R d0) :
    Nonempty (NGCore1 k R d0 22 7) := by
  obtain ⟨hFin, hBB, hC2, hC1, hAl, hE, hTy⟩ := hS
  obtain ⟨d1, t1, ht1⟩ := hex
  have hH : 1 ≤ P.Hp := ng_Hp_ge_one hOK hG ht1
  have hq2 := two_le_residue_card hOK
  have hq : (2 : ℝ) ≤ qF F := by exact_mod_cast hq2
  have hH2 : (2 : ℝ) ≤ P.Hp := le_trans hq hHp
  have hk2 : 2 ≤ k := by omega
  have hfin := hTy.1
  set Sset := {x : TyV | ∃ (d : Datum P) (t : Term V M r), IsTermOver P d t ∧ BBne (H := H) t ∧
    typOf H t = x} with hSset
  let typ : Term V M r → Option {x // x ∈ hfin.toFinset} := fun t =>
    if h : typOf H t ∈ hfin.toFinset then some ⟨_, h⟩ else none
  have hmemRT : ∀ (d : Datum P) (t : Term V M r), t ∈ R.RT d → BBne (H := H) t →
      typOf H t ∈ hfin.toFinset :=
    fun d t ht hB => hfin.mem_toFinset.2 ⟨d, t, (R.hRT d).1 ht, hB, rfl⟩
  have htypS : ∀ (d : Datum P) (t : Term V M r), t ∈ R.RT d → BBne (H := H) t →
      ∀ x : {x // x ∈ hfin.toFinset}, (typ t = some x ↔ typOf H t = x.1) := by
    intro d t ht hB x
    simp only [typ, dif_pos (hmemRT d t ht hB), Option.some.injEq]
    constructor
    · intro h; rw [← h]
    · intro h; exact Subtype.ext h
  have htypN : ∀ (d : Datum P) (t : Term V M r), t ∈ R.RT d → BBne (H := H) t → typ t ≠ none := by
    intro d t ht hB
    simp only [typ, dif_pos (hmemRT d t ht hB)]
    exact Option.some_ne_none _
  have hwit : ∀ x : {x // x ∈ hfin.toFinset}, ∃ (d : Datum P) (t : Term V M r), IsTermOver P d t ∧
      BBne (H := H) t ∧ typOf H t = x.1 := fun x => hfin.mem_toFinset.1 x.2
  have hpow : ∀ x : {x // x ∈ hfin.toFinset},
      x.1.be = qF F ^ Nat.log (qF F) x.1.be ∧ 1 ≤ Nat.log (qF F) x.1.be := by
    intro x
    obtain ⟨d, t, ht, hB, hx⟩ := hwit x
    obtain ⟨hF, _, ⟨i, hi⟩, _⟩ := hBB d t ht
    have h2 := be_ge_two hB hF
    rw [← hx, typOf_be, hi, Nat.log_pow (by omega)]
    refine ⟨rfl, ?_⟩
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · rw [hi, h0] at h2; simp at h2
    · exact h0
  have hbe1 : ∀ x : {x // x ∈ hfin.toFinset}, (1 : ℝ) ≤ (x.1.be : ℝ) := by
    intro x
    have h := (hpow x).1
    have : 1 ≤ x.1.be := by rw [h]; exact Nat.one_le_pow _ _ (by omega)
    exact_mod_cast this
  refine ⟨{
    Ds := hFin.1.choose
    off := hFin.1.choose_spec
    summ := hFin.2
    Ty := Option {x // x ∈ hfin.toFinset}
    fin := inferInstance
    typ := typ
    be := fun τ => τ.elim 1 (fun x => (x.1.be : ℝ))
    I := fun τ => τ.elim 1 (fun x => if x.1.kindBe then (x.1.be : ℝ) else (x.1.be : ℝ) / qF F)
    card := ?_
    be1 := ?_
    I0 := ?_
    Ibe := ?_
    c2 := ?_
    c1 := ?_
    isBe := fun τ => τ.elim True (fun x => x.1.kindBe = true)
    Ial := ?_
    e := ?_ }⟩
  · rw [Fintype.card_option, Fintype.card_coe]
    have hn : (hfin.toFinset.card : ℝ) ≤ P.Hp ^ (r + 2) := by
      rw [← Set.ncard_eq_toFinset_card Sset hfin]; exact hTy.2
    have hp0 := pow_nonneg (show (0 : ℝ) ≤ P.Hp by linarith) (r + 2)
    have hp1 : (1 : ℝ) ≤ P.Hp ^ (r + 2) := one_le_pow₀ hH
    push_cast
    calc (hfin.toFinset.card : ℝ) + 1 ≤ P.Hp ^ (r + 2) + P.Hp ^ (r + 2) := by linarith
      _ ≤ P.Hp * P.Hp ^ (r + 2) := by nlinarith
      _ = P.Hp ^ (r + 3) := by ring
      _ ≤ _ := pow_le_pow_right₀ hH (by nlinarith)
  · rintro (_ | x)
    · exact le_rfl
    · exact hbe1 x
  · rintro (_ | x)
    · simp
    · simp only [Option.elim]
      split_ifs <;> positivity
  · rintro (_ | x)
    · exact le_rfl
    · simp only [Option.elim]
      split_ifs
      · exact le_rfl
      · exact div_le_self (Nat.cast_nonneg _) (by linarith)
  · intro τ d
    rcases τ with _ | x
    · have h1 := massSubset_le_geometric hOK hk2 hBB hC2 hH d.1.1 (hFin.2 d.1) (fun t => BBne (H := H) t ∧ typ t = none) 0
        (fun t ht hSt => absurd hSt.2 (htypN _ t ht hSt.1))
      simp only [pow_zero, one_pow, mul_one] at h1
      simp only [Option.elim, one_pow, mul_one]
      exact le_trans h1 (two_mul_A0_le hH2)
    · rcases hkind : x.1.kindBe with _ | _
      · have hN := hpow x
        have h1 := massSubset_le_geometric hOK hk2 hBB hC2 hH d.1.1 (hFin.2 d.1) (fun t => BBne (H := H) t ∧ typ t = some x)
          (Nat.log (qF F) x.1.be - 1) (fun t ht hSt => by
            have hT := (R.hRT d.1.1).1 ht
            have hty := (htypS _ t ht hSt.1 x).1 hSt.2
            have hnT : ¬ IsTypeBe H t := by
              rw [← typOf_kind, hty, hkind]; simp
            have h2 := hAl d.1.1 t hT hSt.1 hnT
            rw [← typOf_be, hty, hN.1] at h2
            have e : ((qF F ^ Nat.log (qF F) x.1.be : ℕ) : ℝ) / (qF F : ℝ) =
                ((qF F ^ (Nat.log (qF F) x.1.be - 1) : ℕ) : ℝ) := by
              have : Nat.log (qF F) x.1.be = (Nat.log (qF F) x.1.be - 1) + 1 := by omega
              rw [this, pow_succ]
              push_cast
              try simp only [Nat.add_sub_cancel]
              field_simp
            rw [e] at h2
            exact_mod_cast h2)
        simp only [Option.elim, hkind, ↓reduceIte, Bool.false_eq_true]
        have e : (x.1.be : ℝ) / (qF F : ℝ) = (qF F : ℝ) ^ (Nat.log (qF F) x.1.be - 1) := by
          obtain ⟨L, hL⟩ : ∃ L, Nat.log (qF F) x.1.be = L + 1 := ⟨_, (Nat.sub_add_cancel hN.2).symm⟩
          have hb : (x.1.be : ℝ) = (qF F : ℝ) ^ (Nat.log (qF F) x.1.be) := by exact_mod_cast hN.1
          rw [hb, hL, Nat.add_sub_cancel, pow_succ, mul_div_assoc,
            div_self (ne_of_gt (by linarith) : (qF F : ℝ) ≠ 0), mul_one]
        rw [e]
        exact le_trans h1 (mul_le_mul_of_nonneg_right (two_mul_A0_le hH2) (by positivity))
      · have hN := hpow x
        have h1 := massSubset_le_geometric hOK hk2 hBB hC2 hH d.1.1 (hFin.2 d.1) (fun t => BBne (H := H) t ∧ typ t = some x)
          (Nat.log (qF F) x.1.be) (fun t ht hSt => by
            have hT := (R.hRT d.1.1).1 ht
            have hty := (htypS _ t ht hSt.1 x).1 hSt.2
            obtain ⟨hF, _⟩ := hBB d.1.1 t hT
            calc Icard H t ≤ be H t := Icard_le_be hF
              _ = _ := by rw [← typOf_be, hty, ← hN.1])
        simp only [Option.elim, hkind, ↓reduceIte]
        have e : (x.1.be : ℝ) = (qF F : ℝ) ^ (Nat.log (qF F) x.1.be) := by
          rw [hN.1]; push_cast; simp only [Nat.log_pow (show 1 < qF F by omega)]
        rw [e]
        exact le_trans h1 (mul_le_mul_of_nonneg_right (two_mul_A0_le hH2) (by positivity))
  · intro τ
    rcases τ with _ | x
    · refine le_trans (sum_wt_mul_massS_le_inv_pow_mul_total_mass hC1 hH hFin.1.choose hFin.1.choose_spec hFin.2 1 le_rfl _
        (fun d t ht hSt => absurd hSt.2 (htypN d t ht hSt.1))) ?_
      simp only [Option.elim, Nat.cast_one, one_pow, inv_one, mul_one]
      exact mul_le_mul_of_nonneg_right (A1_le_Hp_pow hH2) (nnR_nonneg _ _)
    · have hb1 : 1 ≤ x.1.be := by exact_mod_cast hbe1 x
      refine le_trans (sum_wt_mul_massS_le_inv_pow_mul_total_mass hC1 hH hFin.1.choose hFin.1.choose_spec hFin.2 x.1.be hb1 _
        (fun d t ht hSt => by rw [← typOf_be, (htypS d t ht hSt.1 x).1 hSt.2])) ?_
      simp only [Option.elim]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (A1_le_Hp_pow hH2) (by positivity))
        (nnR_nonneg _ _)
  · intro τ hτ
    rcases τ with _ | x
    · exact absurd trivial hτ
    · simp only [Option.elim] at hτ ⊢
      rw [if_neg hτ]
  · intro τ d hτ
    rcases τ with _ | x
    · have h : ∀ t ∈ R.RT d.1.1, (BBne (H := H) t ∧ typ t = none ↔ False) :=
        fun t ht => ⟨fun h => htypN _ t ht h.1 h.2, False.elim⟩
      rw [amp_congr R d.1.1 h, massS_congr R d.1.1 h, amp_false, massS_false]
      simp
    · simp only [Option.elim] at hτ
      obtain ⟨d', t0, ht0, hB0, hx0⟩ := hwit x
      have hT0 : IsTypeBe H t0 := by rw [← typOf_kind, hx0]; exact hτ
      have hF0 := (hBB d' t0 ht0).1
      have hx : x.1 = ⟨true, be H t0, Jmax H t0, beJ H t0⟩ := by
        rw [← hx0]; unfold typOf; rw [if_pos hT0]
      have h : ∀ t ∈ R.RT d.1.1, (BBne (H := H) t ∧ typ t = some x ↔
          FF H (be H t0) (Jmax H t0) (beJ H t0) t) := by
        intro t ht
        constructor
        · rintro ⟨hB, hty⟩
          rw [← typOf_eq_FF, ← hx]
          exact (htypS _ t ht hB x).1 hty
        · intro hFF
          have hB : BBne (H := H) t := hFF.1.1
          refine ⟨hB, (htypS _ t ht hB x).2 ?_⟩
          rw [hx]
          exact (typOf_eq_FF t _ _ _).2 hFF
      rw [amp_congr R d.1.1 h, massS_congr R d.1.1 h]
      refine hE d.1.1 _ _ _ (be_ge_two hB0 hF0) (one_le_Jmax hB0) (Jmax_le_r hT0) (one_le_beJ hF0) ?_
      rw [massE_eq R d.1.1 (hFin.2 d.1)]
      exact ENNReal.ofReal_ne_top

theorem rpow_thirty_nine_eq_pow (x : ℝ) : x ^ ((39 : ℝ) * ((r : ℝ) + 1) ^ 2) = x ^ (39 * (r + 1) ^ 2) := by
  have := rpow_exp (r := r) x 39
  push_cast at this
  exact this

theorem glue_thirty_nine_first (hOK : M.OK) {k : ℕ} (hk : 4 * r + 7 ≤ k) (hG : P.Gv ≠ 0)
    (hex : ∃ (d : Datum P) (t : Term V M r), IsTermOver P d t)
    (hHp : StepHp P) {R : Reps P} {d0 : Datum P} (hS : Steps k R d0) :
    sumSq R d0 (BBne (H := H)) ≤ ENNReal.ofReal (P.Hp ^ ((39 : ℝ) * ((r : ℝ) + 1) ^ 2) *
      (qF F : ℝ) ^ (-((k : ℝ) - 2 * r - 5))) * nn R d0 := by
  obtain ⟨hFin, hBB, hC2, hC1, hAl, hE, hTy⟩ := hS
  obtain ⟨d1, t1, ht1⟩ := hex
  have hH : 1 ≤ P.Hp := ng_Hp_ge_one hOK hG ht1
  have hq2 := two_le_residue_card hOK
  have hq : (2 : ℝ) ≤ qF F := by exact_mod_cast hq2
  have hk2 : 2 ≤ k := by omega
  have hfin := hTy.1
  set Sset := {x : TyV | ∃ (d : Datum P) (t : Term V M r), IsTermOver P d t ∧ BBne (H := H) t ∧
    typOf H t = x} with hSset
  have hmemRT : ∀ (d : Datum P) (t : Term V M r), t ∈ R.RT d → BBne (H := H) t →
      typOf H t ∈ hfin.toFinset :=
    fun d t ht hB => hfin.mem_toFinset.2 ⟨d, t, (R.hRT d).1 ht, hB, rfl⟩
  by_cases hne : hfin.toFinset.Nonempty
  swap
  · have hz : sumSq R d0 (BBne (H := H)) = 0 := by
      unfold sumSq
      rw [ENNReal.tsum_eq_zero]
      intro d
      have e1 : IsEmpty {t // t ∈ R.RT d.1 ∧ BBne (H := H) t} :=
        ⟨fun t => hne ⟨_, hmemRT d.1 t.1 t.2.1 t.2.2⟩⟩
      unfold amp
      rw [tsum_empty]
      simp
    rw [hz]
    exact bot_le
  obtain ⟨x0, hx0⟩ := hne
  let typ : Term V M r → {x // x ∈ hfin.toFinset} := fun t =>
    if h : typOf H t ∈ hfin.toFinset then ⟨_, h⟩ else ⟨x0, hx0⟩
  have htypS : ∀ (d : Datum P) (t : Term V M r), t ∈ R.RT d → BBne (H := H) t →
      ∀ x : {x // x ∈ hfin.toFinset}, (typ t = x ↔ typOf H t = x.1) := by
    intro d t ht hB x
    simp only [typ, dif_pos (hmemRT d t ht hB)]
    constructor
    · intro h; rw [← h]
    · intro h; exact Subtype.ext h
  have hwit : ∀ x : {x // x ∈ hfin.toFinset}, ∃ (d : Datum P) (t : Term V M r), IsTermOver P d t ∧
      BBne (H := H) t ∧ typOf H t = x.1 := fun x => hfin.mem_toFinset.1 x.2
  have hpow : ∀ x : {x // x ∈ hfin.toFinset},
      x.1.be = qF F ^ Nat.log (qF F) x.1.be ∧ 1 ≤ Nat.log (qF F) x.1.be := by
    intro x
    obtain ⟨d, t, ht, hB, hx⟩ := hwit x
    obtain ⟨hF, _, ⟨i, hi⟩, _⟩ := hBB d t ht
    have h2 := be_ge_two hB hF
    rw [← hx, typOf_be, hi, Nat.log_pow (by omega)]
    refine ⟨rfl, ?_⟩
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · rw [hi, h0] at h2; simp at h2
    · exact h0
  have hbe1 : ∀ x : {x // x ∈ hfin.toFinset}, (1 : ℝ) ≤ (x.1.be : ℝ) := by
    intro x
    have h := (hpow x).1
    have : 1 ≤ x.1.be := by rw [h]; exact Nat.one_le_pow _ _ (by omega)
    exact_mod_cast this
  set Ds := hFin.1.choose with hDs
  have hcard : (Fintype.card {x // x ∈ hfin.toFinset} : ℝ) ≤ P.Hp ^ (r + 2) := by
    rw [Fintype.card_coe, ← Set.ncard_eq_toFinset_card Sset hfin]
    exact hTy.2
  have hcB : ∀ (x : {x // x ∈ hfin.toFinset}) (d : Ds), x.1.kindBe = true →
      massS R d.1.1 (fun t => BBne (H := H) t ∧ typ t = x) ≤
        2 * P.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (x.1.be : ℝ) ^ (k - 1) := by
    intro x d _
    have hN := hpow x
    have h1 := massSubset_le_geometric hOK hk2 hBB hC2 hH d.1.1 (hFin.2 d.1) (fun t => BBne (H := H) t ∧ typ t = x)
      (Nat.log (qF F) x.1.be) (fun t ht hSt => by
        have hT := (R.hRT d.1.1).1 ht
        have hty := (htypS _ t ht hSt.1 x).1 hSt.2
        obtain ⟨hF, _⟩ := hBB d.1.1 t hT
        calc Icard H t ≤ be H t := Icard_le_be hF
          _ = _ := by rw [← typOf_be, hty, ← hN.1])
    have hb : (x.1.be : ℝ) = (qF F : ℝ) ^ (Nat.log (qF F) x.1.be) := by exact_mod_cast hN.1
    rw [hb]
    unfold A0 at h1
    exact h1
  have hcA : ∀ (x : {x // x ∈ hfin.toFinset}) (d : Ds), ¬ x.1.kindBe = true →
      massS R d.1.1 (fun t => BBne (H := H) t ∧ typ t = x) ≤
        2 * P.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * ((x.1.be : ℝ) / (qF F : ℕ)) ^ (k - 1) := by
    intro x d hkind
    have hN := hpow x
    obtain ⟨L, hL⟩ : ∃ L, Nat.log (qF F) x.1.be = L + 1 := ⟨_, (Nat.sub_add_cancel hN.2).symm⟩
    have hb : (x.1.be : ℝ) = (qF F : ℝ) ^ (Nat.log (qF F) x.1.be) := by exact_mod_cast hN.1
    have e : (x.1.be : ℝ) / (qF F : ℝ) = (qF F : ℝ) ^ L := by
      rw [hb, hL, pow_succ, mul_div_assoc, div_self (ne_of_gt (by linarith) : (qF F : ℝ) ≠ 0), mul_one]
    have h1 := massSubset_le_geometric hOK hk2 hBB hC2 hH d.1.1 (hFin.2 d.1) (fun t => BBne (H := H) t ∧ typ t = x)
      L (fun t ht hSt => by
        have hT := (R.hRT d.1.1).1 ht
        have hty := (htypS _ t ht hSt.1 x).1 hSt.2
        have hnT : ¬ IsTypeBe H t := by
          rw [← typOf_kind, hty]; exact hkind
        have h2 := hAl d.1.1 t hT hSt.1 hnT
        rw [← typOf_be, hty, e] at h2
        exact_mod_cast h2)
    rw [e]
    unfold A0 at h1
    exact h1
  have hc1 : ∀ x : {x // x ∈ hfin.toFinset},
      ∑ d : Ds, Datum.wt d0 d.1.1 * massS R d.1.1 (fun t => BBne (H := H) t ∧ typ t = x) ≤
        4 * P.Hp ^ (4 * (r + 1)) * (((x.1.be : ℝ)) ^ (k - 1))⁻¹ *
          ∑ d : Ds, Datum.wt d0 d.1.1 * ∑' t : R.RT d.1.1, mu P t.1 := by
    intro x
    have hb1 : 1 ≤ x.1.be := by exact_mod_cast hbe1 x
    have := sum_wt_mul_massS_le_inv_pow_mul_total_mass hC1 hH Ds hFin.1.choose_spec hFin.2 x.1.be hb1 (fun t => BBne (H := H) t ∧ typ t = x)
      (fun d t ht hSt => by rw [← typOf_be, (htypS d t ht hSt.1 x).1 hSt.2])
    unfold A1 at this
    exact this
  have he : ∀ (x : {x // x ∈ hfin.toFinset}) (d : Ds), x.1.kindBe = true →
      ‖amp R d.1.1 (fun t => BBne (H := H) t ∧ typ t = x)‖ ≤
        7 * (qF F : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) *
          massS R d.1.1 (fun t => BBne (H := H) t ∧ typ t = x) := by
    intro x d hτ
    obtain ⟨d', t0, ht0, hB0, hx0'⟩ := hwit x
    have hT0 : IsTypeBe H t0 := by rw [← typOf_kind, hx0']; exact hτ
    have hF0 := (hBB d' t0 ht0).1
    have hx : x.1 = ⟨true, be H t0, Jmax H t0, beJ H t0⟩ := by
      rw [← hx0']; unfold typOf; rw [if_pos hT0]
    have h : ∀ t ∈ R.RT d.1.1, (BBne (H := H) t ∧ typ t = x ↔
        FF H (be H t0) (Jmax H t0) (beJ H t0) t) := by
      intro t ht
      constructor
      · rintro ⟨hB, hty⟩
        rw [← typOf_eq_FF, ← hx]
        exact (htypS _ t ht hB x).1 hty
      · intro hFF
        have hB : BBne (H := H) t := hFF.1.1
        refine ⟨hB, (htypS _ t ht hB x).2 ?_⟩
        rw [hx]
        exact (typOf_eq_FF t _ _ _).2 hFF
    rw [amp_congr R d.1.1 h, massS_congr R d.1.1 h]
    refine hE d.1.1 _ _ _ (be_ge_two hB0 hF0) (one_le_Jmax hB0) (Jmax_le_r hT0) (one_le_beJ hF0) ?_
    rw [massE_eq R d.1.1 (hFin.2 d.1)]
    exact ENNReal.ofReal_ne_top
  have key := Formalism.HermitianLatticeCounting.Final.S4.global_assembly k r (qF F) P.Hp
    (∑ d : Ds, Datum.wt d0 d.1.1 * ∑' t : R.RT d.1.1, mu P t.1) Ds {x // x ∈ hfin.toFinset}
    (fun d => Datum.wt d0 d.1.1) (fun τ d => amp R d.1.1 (fun t => BBne (H := H) t ∧ typ t = τ))
    (fun τ d => massS R d.1.1 (fun t => BBne (H := H) t ∧ typ t = τ)) (fun τ => (τ.1.be : ℝ))
    (fun τ => τ.1.kindBe = true) hk hq2 hH (fun _ => hHp) (nnR_nonneg _ _) (fun d => wt_nonneg _ _) hcard
    hbe1 (fun τ d => massS_nonneg _ _ _) (fun τ d h => hcB τ d h) (fun τ d h => hcA τ d h) hc1
    (fun τ d => norm_amp_le (ng_norm_om hOK) R _ (hFin.2 d.1) _) (fun τ d h => he τ d h)
  have hp0 : 0 ≤ P.Hp ^ ((39 : ℝ) * ((r : ℝ) + 1) ^ 2) * (qF F : ℝ) ^ (-((k : ℝ) - 2 * r - 5)) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)
  rw [sumSq_eq R d0 Ds hFin.1.choose_spec, nn_eq R d0 Ds hFin.1.choose_spec hFin.2, ← ENNReal.ofReal_mul hp0]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [rpow_thirty_nine_eq_pow]
  have hz : (qF F : ℝ) ^ (-((k : ℝ) - 2 * r - 5)) = (qF F : ℝ) ^ (-((k : ℤ) - 2 * r - 5)) := by
    have h : ((-((k : ℤ) - 2 * r - 5) : ℤ) : ℝ) = -((k : ℝ) - 2 * r - 5) := by push_cast; ring
    rw [← h, Real.rpow_intCast]
  rw [hz]
  refine le_trans (le_of_eq ?_) key
  exact Finset.sum_congr rfl (fun d _ => by rw [amp_split (ng_norm_om hOK) R d.1.1 (hFin.2 d.1) _ typ])

theorem sumSq_le_Hp_pow_39 (hOK : M.OK) {k : ℕ} (hk : 4 * r + 7 ≤ k) (hG : P.Gv ≠ 0)
    (hex : ∃ (d : Datum P) (t : Term V M r), IsTermOver P d t)
    (hHp : StepHp P) {R : Reps P} {d0 : Datum P} (hS : Steps k R d0) (S : Term V M r → Prop) :
    sumSq R d0 S ≤ ENNReal.ofReal (P.Hp ^ ((39 : ℝ) * ((r : ℝ) + 1) ^ 2)) * nn R d0 := by
  obtain ⟨hFin, hBB, hC2, hC1, -, -, -⟩ := hS
  obtain ⟨d1, t1, ht1⟩ := hex
  have hH : 1 ≤ P.Hp := ng_Hp_ge_one hOK hG ht1
  have hq2 := two_le_residue_card hOK
  have hq : (2 : ℝ) ≤ qF F := by exact_mod_cast hq2
  have hH2 : (2 : ℝ) ≤ P.Hp := le_trans hq hHp
  have hN2 : 2 ≤ ⌊P.Hp⌋₊ := Nat.le_floor (by exact_mod_cast hH2)
  let typ : Term V M r → Fin ⌊P.Hp⌋₊ := fun t =>
    if h : Nat.log (qF F) (be H t) < ⌊P.Hp⌋₊ then ⟨_, h⟩ else ⟨0, by omega⟩
  have htyp : ∀ (d : Datum P) (t : Term V M r), IsTermOver P d t → be H t = qF F ^ (typ t : ℕ) := by
    intro d t ht
    obtain ⟨h1, h2⟩ := be_log hOK hBB ht
    simp only [typ, dif_pos h2]
    exact h1
  have hk2 : 2 ≤ k := by omega
  set Ds := hFin.1.choose with hDs
  have hcard : (Fintype.card (Fin ⌊P.Hp⌋₊) : ℝ) ≤ P.Hp := by
    simp only [Fintype.card_fin]
    exact Nat.floor_le (by linarith)
  have hc2 : ∀ (τ : Fin ⌊P.Hp⌋₊) (d : Ds), massS R d.1.1 (fun t => S t ∧ typ t = τ) ≤
      2 * P.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * ((qF F : ℝ) ^ (τ : ℕ)) ^ (k - 1) := by
    intro τ d
    have h1 := massSubset_le_geometric hOK hk2 hBB hC2 hH d.1.1 (hFin.2 d.1) (fun t => S t ∧ typ t = τ) τ (fun t ht hSt => by
      have hT := (R.hRT d.1.1).1 ht
      have hb := htyp d.1.1 t hT
      obtain ⟨hF, _⟩ := hBB d.1.1 t hT
      calc Icard H t ≤ be H t := Icard_le_be hF
        _ = _ := by rw [hb, hSt.2])
    unfold A0 at h1
    exact h1
  have hc1 : ∀ τ : Fin ⌊P.Hp⌋₊,
      ∑ d : Ds, Datum.wt d0 d.1.1 * massS R d.1.1 (fun t => S t ∧ typ t = τ) ≤
        4 * P.Hp ^ (4 * (r + 1)) * (((qF F : ℝ) ^ (τ : ℕ)) ^ (k - 1))⁻¹ *
          ∑ d : Ds, Datum.wt d0 d.1.1 * ∑' t : R.RT d.1.1, mu P t.1 := by
    intro τ
    have := sum_wt_mul_massS_le_inv_pow_mul_total_mass hC1 hH Ds hFin.1.choose_spec hFin.2 (qF F ^ (τ : ℕ))
      (Nat.one_le_pow _ _ (by omega)) (fun t => S t ∧ typ t = τ)
      (fun d t ht hSt => by rw [htyp d t ((R.hRT d).1 ht), hSt.2])
    unfold A1 at this
    push_cast at this
    exact this
  have key := Formalism.HermitianLatticeCounting.Final.S4.global_assembly_doubled k r P.Hp
    (∑ d : Ds, Datum.wt d0 d.1.1 * ∑' t : R.RT d.1.1, mu P t.1) Ds (Fin ⌊P.Hp⌋₊)
    (fun d => Datum.wt d0 d.1.1) (fun τ d => amp R d.1.1 (fun t => S t ∧ typ t = τ))
    (fun τ d => massS R d.1.1 (fun t => S t ∧ typ t = τ)) (fun τ => (qF F : ℝ) ^ (τ : ℕ))
    hH2 (nnR_nonneg _ _) (fun d => wt_nonneg _ _) hcard (fun τ => one_le_pow₀ (by linarith))
    (fun τ d => massS_nonneg _ _ _) hc2 hc1 (fun τ d => norm_amp_le (ng_norm_om hOK) R _ (hFin.2 d.1) _)
  rw [sumSq_eq R d0 Ds hFin.1.choose_spec, nn_eq R d0 Ds hFin.1.choose_spec hFin.2,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith) _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [rpow_thirty_nine_eq_pow]
  refine le_trans (le_of_eq ?_) key
  exact Finset.sum_congr rfl (fun d _ => by rw [amp_split (ng_norm_om hOK) R d.1.1 (hFin.2 d.1) _ typ])

end GlueSec

theorem glue_constants_holds (k r : ℕ) : Glue k r := by
  intro F _ _ _ E _ _ _ _ M hOK V _ _ H hrk hk P hR hex hHp R d0 hS
  exact ⟨localBoundFirst_of hOK hk hR.2.2.1 hex hHp hS, localBoundSecond_of hOK hk hR.2.2.1 hex hHp hS _,
    localBoundSecond_of hOK hk hR.2.2.1 hex hHp hS _⟩

theorem glue_constant_thirty_nine (k r : ℕ) : AssemblyConstantThirtyNine k r := by
  intro F _ _ _ E _ _ _ _ M hOK V _ _ H hrk hk P hR hex hHp R d0 hS
  exact ⟨glue_thirty_nine_first hOK hk hR.2.2.1 hex hHp hS, sumSq_le_Hp_pow_39 hOK hk hR.2.2.1 hex hHp hS _,
    sumSq_le_Hp_pow_39 hOK hk hR.2.2.1 hex hHp hS _⟩

theorem DictAll_of_steps (k r : ℕ)
    (h : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
      (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
      (M : Model F E), M.OK →
      ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V),
        Module.finrank E V = k + 2 * r + 1 → 4 * r + 7 ≤ k →
        ∀ P : FPair H r, P.RelG (theta M) → (∃ (d : Datum P) (t : Term V M r), IsTermOver P d t) →
          ¬ P.PrimeTo → ∀ (R : Reps P) (d0 : Datum P), Steps k R d0) : DictAll k r := by
  intro F _ _ _ E _ _ _ _ M hOK V _ _ H hrk hk P hR hex hp
  exact ⟨residue_le_height_nonprime hOK hR hex hp, h F E M hOK V H hrk hk P hR hex hp⟩

theorem theoremNG_of_dictionary (k r : ℕ) (hk : 4 * r + 7 ≤ k) (hD : DictAll k r) :
    Formalism.MainNotions.NonGenericAndKTwoTheorems.NonGenericLocalBound k r 39 :=
  local_counting_bound_thirty_nine k r hk (glue_constant_thirty_nine k r) hD

theorem NGLeft_of_DictAll (k r : ℕ) (hk : 4 * r + 7 ≤ k) (hD : DictAll k r) : NGLeft k r 22 7 :=
  NGLeft_of_dict k r hk (glue_constants_holds k r) hD

end Formalism.L2.SG.Pf
