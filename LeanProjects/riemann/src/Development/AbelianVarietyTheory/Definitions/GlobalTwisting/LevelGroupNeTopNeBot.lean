import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IntegralGLSuccEmbeddingMemParahoricTimesPrincipa

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.TopStep.Model

section Q

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {m2 : ℕ}

theorem entB_topQ (hm : R.m = m2 + 2) (q : ℕ) (y : HomE X.E (R.N (m2 + 1)) (R.N R.m)) (p p' : ℕ) :
    LocE.entB q R.k (cOf R (m2 + 1)) (R.N (m2 + 1)) 0 (R.N R.m - 1) 0 0
        (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) p p' =
      if h : p < R.N R.m - 1 ∧ p' < R.N (m2 + 1) then y (Pi.single ⟨p', h.2⟩ 1) (Br.iC (N_m_succ R) ⟨p, h.1⟩) else 0 := by
  have hc : cOf R (m2 + 1) = 0 := by simp only [cOf]; omega
  have h1 : ∀ s, LocE.fIdx R.k (cOf R (m2 + 1)) (R.N (m2 + 1)) s = s := by
    intro s; rw [hc]; simp only [LocE.fIdx]; split_ifs <;> omega
  have h2 : ∀ s, LocE.fIdx R.k 0 (R.N R.m - 1) s = s := by
    intro s; simp only [LocE.fIdx]; split_ifs <;> omega
  have h3 : ∀ n l, LocE.scE n (0 : ℕ → ℕ) l = 0 := by
    intro n l; simp only [LocE.scE]; split_ifs <;> simp
  simp only [LocE.entB, h1, h2, h3, sub_self, zpow_zero, mul_one]
  have hv : ∀ v : Sp X.E (R.N R.m), ∀ (i : ℕ) (hi : i < R.N R.m - 1 + 0) (hi' : i < R.N R.m - 1),
      prXp X.E R v ⟨i, hi⟩ = v (Br.iC (N_m_succ R) ⟨i, hi'⟩) := fun _ _ _ _ => rfl
  unfold Loc.atN
  by_cases hp : p < R.N R.m - 1
  · have hp0 : p < R.N R.m - 1 + 0 := hp
    rw [dif_pos hp0]
    by_cases hq : p' < R.N (m2 + 1)
    · rw [dif_pos ⟨hp, hq⟩]
      have e : LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) (Loc.eN X.E (R.N (m2 + 1) + cOf R (m2 + 1)) p') =
          (Pi.single ⟨p', hq⟩ 1 : Sp X.E (R.N (m2 + 1))) := by
        funext i
        simp only [LinearMap.funLeft_apply, Loc.eN, Fin.val_castAdd, Pi.single_apply, Fin.ext_iff]
      simp only [LinearMap.comp_apply, e]
      exact hv _ _ _ _
    · rw [dif_neg (fun h => hq h.2)]
      have e : LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) (Loc.eN X.E (R.N (m2 + 1) + cOf R (m2 + 1)) p') = 0 := by
        funext i
        simp only [LinearMap.funLeft_apply, Loc.eN, Fin.val_castAdd, Pi.zero_apply]
        rw [if_neg]; omega
      simp only [LinearMap.comp_apply, e, map_zero, Pi.zero_apply]
  · rw [dif_neg (by omega), dif_neg (fun h => hp h.1)]

def SuppQ (P : HeightOneSpectrum (𝓞 X.E)) (M : ℕ) (y : HomE X.E (R.N (m2 + 1)) (R.N R.m)) : Prop :=
  ∀ s, (∀ i, IntAt P (y (Pi.single s 1) (Br.iC (N_m_succ R) i))) ∧
    IntAt P ((qOf P : X.E) ^ M * y (Pi.single s 1) (Br.iL (N_m_succ R)))

theorem suppQ_of_ne (hm : R.m = m2 + 2) {P : rowSG Pr sel mu} (hP : P.1 ∉ Pr.vGs) {y : HomE X.E (R.N (m2 + 1)) (R.N R.m)}
    {y' : Sp X.E (R.N (m2 + 1))} (h : locTop Ch sel mu cst m2 P y y' ≠ 0) : SuppQ P.1 cst.M y := by
  unfold locTop at h
  have hA := left_ne_zero_of_mul h
  have hB := right_ne_zero_of_mul h
  unfold ftY at hB
  rw [if_neg hP] at hB
  have hB' := cond_of_ite_ne_zero hB
  unfold PhiTop at hA
  rw [if_neg hP] at hA
  unfold LocE.PhiQ at hA
  have hA' := cond_of_ite_ne_zero hA
  intro s
  refine ⟨fun i => ?_, ?_⟩
  · have hi : i.1 < R.N R.m - 1 + 0 := i.2
    have hs : s.1 < R.N (m2 + 1) + cOf R (m2 + 1) := by have := s.2; omega
    have e := hA'.1 i.1 s.1 hi hs
    rw [entB_topQ hm, dif_pos ⟨i.2, s.2⟩] at e
    exact e
  · have e := hB' s
    rwa [LinearMap.comp_apply, atNL_last] at e

theorem move_small {P : HeightOneSpectrum (𝓞 X.E)} {M e : ℕ} {κ : GLint X.E (R.N R.m) P} (hκ : κ ∈ prinCong _ P (2 * M + e))
    {y : HomE X.E (R.N (m2 + 1)) (R.N R.m)} (hy : SuppQ P M y) (s l) :
    ∃ z, IntAt P z ∧ κ.1 (y (Pi.single s 1)) l = y (Pi.single s 1) l + (qOf P : X.E) ^ (M + e) * z := by
  obtain ⟨hC, hL⟩ := hy s
  have hq : ((qOf P : ℕ) : X.E) ≠ 0 := qOf_ne_zero
  have hw : ((qOf P : X.E) ^ M) • y (Pi.single s 1) ∈ stdAt X.E (R.N R.m) P := by
    rw [mem_stdAt]
    intro i
    rcases idx_cases (N_m_succ R) i with ⟨j, rfl⟩ | rfl
    · simp only [Pi.smul_apply, smul_eq_mul]
      exact (intAt_pow (intAt_nat _) M).mul (hC j)
    · simpa only [Pi.smul_apply, smul_eq_mul] using hL
  have h2 := mem_stdAt.1 ((mem_prinCong.1 hκ) _ hw) l
  refine ⟨_, h2, ?_⟩
  simp only [map_smul, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  field_simp
  ring

theorem suppQ_move {P : HeightOneSpectrum (𝓞 X.E)} {M e : ℕ} {κ : GLint X.E (R.N R.m) P} (hκ : κ ∈ prinCong _ P (2 * M + e))
    {y : HomE X.E (R.N (m2 + 1)) (R.N R.m)} (hy : SuppQ P M y) : SuppQ P M (κ.1.toLinearMap ∘ₗ y) := by
  intro s
  obtain ⟨hC, hL⟩ := hy s
  have hp : IntAt P ((qOf P : X.E) ^ (M + e)) := intAt_pow (intAt_nat _) _
  refine ⟨fun i => ?_, ?_⟩
  · obtain ⟨z, hz, e1⟩ := move_small hκ hy s (Br.iC (N_m_succ R) i)
    rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, e1]
    exact (hC i).add (hp.mul hz)
  · obtain ⟨z, hz, e1⟩ := move_small hκ hy s (Br.iL (N_m_succ R))
    rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, e1, mul_add]
    exact hL.add ((intAt_pow (intAt_nat _) M).mul (hp.mul hz))

private theorem phiQ_congr_of_entB_congr {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}
    (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' c n : ℕ) {x x' : HomE E (n' + c') (n + c)}
    (h : ∀ p p', ∃ w, IntAt P w ∧
      LocE.entB (qOf P) k₀ c' n' c n 0 0 x' p p' = LocE.entB (qOf P) k₀ c' n' c n 0 0 x p p' + (qOf P : E) * w)
    (hZ : ∀ p p', ¬ (p < n + c ∧ p' < n' + c') → IntAt P (LocE.entB (qOf P) k₀ c' n' c n 0 0 x p p')) :
    LocE.PhiQ (qOf P) ξ k₀ r c' n' c n x' = LocE.PhiQ (qOf P) ξ k₀ r c' n' c n x := by
  choose w hw e using h
  have hqI : IntAt P (qOf P : E) := intAt_nat _
  have hq : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero
  have ediv : ∀ p p', LocE.entB (qOf P) k₀ c' n' c n 0 0 x' p p' / (qOf P : E) =
      LocE.entB (qOf P) k₀ c' n' c n 0 0 x p p' / (qOf P : E) + w p p' := by
    intro p p'; rw [e]; field_simp
  have c1 : (∀ p p', p < n + c → p' < n' + c' → IntAt P (LocE.entB (qOf P) k₀ c' n' c n 0 0 x' p p')) ↔
      (∀ p p', p < n + c → p' < n' + c' → IntAt P (LocE.entB (qOf P) k₀ c' n' c n 0 0 x p p')) := by
    constructor
    · intro H p p' h1 h2
      have h3 := (H p p' h1 h2).add (intAt_neg (hqI.mul (hw p p')))
      rwa [e, add_neg_cancel_right] at h3
    · intro H p p' h1 h2
      rw [e]; exact (H p p' h1 h2).add (hqI.mul (hw p p'))
  have c2 : (∀ p p', r ≤ p → p < n + c → p' < r → IntAt P (LocE.entB (qOf P) k₀ c' n' c n 0 0 x' p p' / (qOf P : E))) ↔
      (∀ p p', r ≤ p → p < n + c → p' < r → IntAt P (LocE.entB (qOf P) k₀ c' n' c n 0 0 x p p' / (qOf P : E))) := by
    constructor
    · intro H p p' h1 h2 h3
      have h4 := (H p p' h1 h2 h3).add (intAt_neg (hw p p'))
      rwa [ediv, add_neg_cancel_right] at h4
    · intro H p p' h1 h2 h3
      rw [ediv]; exact (H p p' h1 h2 h3).add (hw p p')
  unfold LocE.PhiQ
  by_cases H : (∀ p p', p < n + c → p' < n' + c' → IntAt P (LocE.entB (qOf P) k₀ c' n' c n 0 0 x p p')) ∧
      (∀ p p', r ≤ p → p < n + c → p' < r → IntAt P (LocE.entB (qOf P) k₀ c' n' c n 0 0 x p p' / (qOf P : E)))
  · have H' := And.intro (c1.2 H.1) (c2.2 H.2)
    rw [if_pos H, if_pos H']
    apply unitV_det_congr
    intro i j
    have hi : IntAt P (LocE.entB (qOf P) k₀ c' n' c n 0 0 x i.1 j.1) := by
      by_cases hr : i.1 < n + c ∧ j.1 < n' + c'
      · exact H.1 _ _ hr.1 hr.2
      · exact hZ _ _ hr
    refine ⟨?_, hi, ?_⟩
    · rw [e]; exact hi.add (hqI.mul (hw _ _))
    · rw [e, add_sub_cancel_left, mul_div_cancel_left₀ _ hq]; exact hw _ _
  · have H' : ¬ ((∀ p p', p < n + c → p' < n' + c' → IntAt P (LocE.entB (qOf P) k₀ c' n' c n 0 0 x' p p')) ∧
      (∀ p p', r ≤ p → p < n + c → p' < r → IntAt P (LocE.entB (qOf P) k₀ c' n' c n 0 0 x' p p' / (qOf P : E)))) :=
      fun H2 => H ⟨c1.1 H2.1, c2.1 H2.2⟩
    rw [if_neg H, if_neg H']

theorem locTop_invQ (hm : R.m = m2 + 2) (hc : cst.Ok) {P : rowSG Pr sel mu} (hP : P.1 ∉ Pr.vGs) (hD : 2 * cst.M ≤ cst.D P)
    (c : TopDepth R cst.M) {κ : GLint X.E (R.N R.m) P.1} (hκ : κ ∈ prinCong _ P.1 c.1)
    (y : HomE X.E (R.N (m2 + 1)) (R.N R.m)) {y' : Sp X.E (R.N (m2 + 1))} (hy' : ∀ i, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y' i)) :
    locTop Ch sel mu cst m2 P (κ.1.toLinearMap ∘ₗ y) y' = locTop Ch sel mu cst m2 P y y' := by
  have hq : ((qOf P.1 : ℕ) : X.E) ≠ 0 := qOf_ne_zero
  have hqI : IntAt P.1 (qOf P.1 : X.E) := intAt_nat _
  have hc2 := c.2
  have hmax : 2 * R.m + 2 * cst.M ≤ c.1 := le_trans (le_max_right _ _) hc2
  obtain ⟨e, he⟩ : ∃ e, c.1 = 2 * cst.M + e := ⟨c.1 - 2 * cst.M, by omega⟩
  have he1 : 1 ≤ e := by omega
  have hκ' : κ ∈ prinCong _ P.1 (2 * cst.M + e) := he ▸ hκ
  have hκi : κ⁻¹ ∈ prinCong _ P.1 (2 * cst.M + e) := inv_mem hκ'
  by_cases hS : SuppQ P.1 cst.M y
  · choose z hz ez using fun s l => move_small hκ' hS s l
    have hS' : SuppQ P.1 cst.M (κ.1.toLinearMap ∘ₗ y) := suppQ_move hκ' hS
    have hpw : (qOf P.1 : X.E) ^ (cst.M + e) = (qOf P.1 : X.E) * (qOf P.1 : X.E) ^ (cst.M + e - 1) := by
      rw [← pow_succ']; congr 1; omega
    unfold locTop
    congr 1
    · unfold PhiTop
      rw [if_neg hP]
      apply phiQ_congr_of_entB_congr
      · intro p p'
        rw [entB_topQ hm, entB_topQ hm]
        split_ifs with h
        · refine ⟨(qOf P.1 : X.E) ^ (cst.M + e - 1) * z ⟨p', h.2⟩ (Br.iC (N_m_succ R) ⟨p, h.1⟩),
            (intAt_pow hqI _).mul (hz _ _), ?_⟩
          rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, ez, hpw]
          ring
        · exact ⟨0, intAt_zero, by simp⟩
      · intro p p' hp
        rw [entB_topQ hm, dif_neg]
        · exact intAt_zero
        · intro h; exact hp ⟨by have := h.1; omega, by have := h.2; omega⟩
    · unfold ftY
      rw [if_neg hP, if_neg hP]
      have hA : ∀ i : Fin (R.N (m2 + 1)), IntAt P.1 ((qOf P.1 : X.E) ^ cst.M *
          (atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ y) (Pi.single i 1)) := by
        intro i; rw [LinearMap.comp_apply, atNL_last]; exact (hS i).2
      have hA' : ∀ i : Fin (R.N (m2 + 1)), IntAt P.1 ((qOf P.1 : X.E) ^ cst.M *
          (atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ (κ.1.toLinearMap ∘ₗ y)) (Pi.single i 1)) := by
        intro i; rw [LinearMap.comp_apply, atNL_last]; exact (hS' i).2
      rw [if_pos hA, if_pos hA']
      congr 1
      have hsum : (atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ (κ.1.toLinearMap ∘ₗ y)) y' =
          (atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ y) y' +
            ∑ j, ((qOf P.1 : X.E) ^ cst.M * y' j) * ((qOf P.1 : X.E) ^ e * z j (Br.iL (N_m_succ R))) := by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, atNL_last]
        rw [show κ.1 (y y') = (κ.1.toLinearMap ∘ₗ y) y' from rfl, apply_eq_sum (κ.1.toLinearMap ∘ₗ y) y',
          apply_eq_sum y y' (Br.iL (N_m_succ R)), ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
        rw [ez]
        ring
      have hepsI : IntAt P.1 (epsSg : X.E) := by
        simp only [epsSg]; push_cast; exact intAt_neg intAt_one
      have hBI : IntAt P.1 (∑ j, ((qOf P.1 : X.E) ^ cst.M * y' j) * ((qOf P.1 : X.E) ^ e * z j (Br.iL (N_m_succ R)))) :=
        intAt_sum _ fun j _ => (hy' j).mul ((intAt_pow hqI _).mul (hz _ _))
      have hD' := hD
      have hAD : IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * ((epsSg : X.E) * (atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ y) y')) := by
        have e2 : (qOf P.1 : X.E) ^ cst.D P * ((epsSg : X.E) * (atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ y) y') =
            (qOf P.1 : X.E) ^ (cst.D P - 2 * cst.M) * (epsSg : X.E) *
              ∑ j, ((qOf P.1 : X.E) ^ cst.M * y' j) * ((qOf P.1 : X.E) ^ cst.M * y (Pi.single j 1) (Br.iL (N_m_succ R))) := by
          rw [LinearMap.comp_apply, atNL_last, apply_eq_sum y y', Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          have : cst.D P = (cst.D P - 2 * cst.M) + cst.M + cst.M := by omega
          conv_lhs => rw [this]
          ring
        rw [e2]
        exact ((intAt_pow hqI _).mul hepsI).mul (intAt_sum _ fun j _ => (hy' j).mul (hS j).2)
      rw [hsum, mul_add, hc.psi_add P _ _ hAD ((intAt_pow hqI _).mul (hepsI.mul hBI)),
        hc.psi_int P _ (hepsI.mul hBI), mul_one]
  · have h1 : locTop Ch sel mu cst m2 P y y' = 0 := by
      by_contra h; exact hS (suppQ_of_ne hm hP h)
    have h2 : locTop Ch sel mu cst m2 P (κ.1.toLinearMap ∘ₗ y) y' = 0 := by
      by_contra h
      have h3 := suppQ_move hκi (suppQ_of_ne hm hP h)
      have hh : (κ⁻¹).1 * κ.1 = 1 := by rw [← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]
      have e3 : (κ⁻¹).1.toLinearMap ∘ₗ (κ.1.toLinearMap ∘ₗ y) = y := by
        apply LinearMap.ext
        intro v
        simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
        rw [← LinearEquiv.mul_apply, hh]
        rfl
      rw [e3] at h3
      exact hS h3
    rw [h1, h2]

end Q

section Depth

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n N : ℕ} (hN : N = n + 1) {P : HeightOneSpectrum (𝓞 E)}
  (l : Lev (𝓞 E ⧸ P.asIdeal) K n)

omit [StarRing E] in
theorem not_intAt_inv_q : ¬ IntAt P ((qOf P : E)⁻¹) := by
  rintro ⟨r, s, hs, h⟩
  apply hs
  have hq : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero
  have e : algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E (r * ((qOf P : ℕ) : 𝓞 E)) := by
    rw [map_mul, ← h, map_natCast, mul_assoc, inv_mul_cancel₀ hq, mul_one]
  rw [FaithfulSMul.algebraMap_injective (𝓞 E) E e]
  exact Ideal.mul_mem_left _ _ qOf_mem

private lemma exists_prinCong_not_mem_stdAt {c : ℕ} (hc : 0 < c) :
    ∃ g ∈ prinCong N P c,
      ((qOf P : E) ^ (c + 1))⁻¹ • (g.1 (Pi.single (Br.iL hN) 1) - Pi.single (Br.iL hN) 1) ∉ stdAt E N P := by
  have hq : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero
  have hqc : ((qOf P : ℕ) : 𝓞 E) ^ c ∈ P.asIdeal := Ideal.pow_mem_of_mem _ qOf_mem c hc
  have hs : (1 + ((qOf P : ℕ) : 𝓞 E) ^ c) ∉ P.asIdeal := fun h =>
    one_notMem P (by simpa using P.asIdeal.sub_mem h hqc)
  have ht0 : (1 + (qOf P : E) ^ c) ≠ 0 := by
    have : ((1 + qOf P ^ c : ℕ) : E) ≠ 0 := Nat.cast_ne_zero.2 (by positivity)
    simpa using this
  have hti : IntAt P (1 + (qOf P : E) ^ c) := by
    simpa using IntAt.coe P (1 + ((qOf P : ℕ) : 𝓞 E) ^ c)
  have hinv : IntAt P (1 + (qOf P : E) ^ c)⁻¹ := by
    unfold IntAt
    refine ⟨1, 1 + ((qOf P : ℕ) : 𝓞 E) ^ c, hs, ?_⟩
    simp only [map_add, map_one, map_pow, map_natCast]
    exact mul_inv_cancel₀ ht0
  obtain ⟨g, hg⟩ : ∃ g : GLint E N P, g.1 = sumE hN 1 (Units.mk0 (1 + (qOf P : E) ^ c) ht0) :=
    ⟨⟨sumE hN 1 (Units.mk0 (1 + (qOf P : E) ^ c) ht0), fun x => by
      rw [mem_stdAt_succ hN, mem_stdAt_succ hN, prH_sumE, sumE_last, Units.val_mk0]
      simp only [LinearEquiv.coe_one, id_eq]
      refine and_congr_right fun _ => ⟨fun h => ?_, fun h => hti.mul h⟩
      have h' := hinv.mul h
      rwa [inv_mul_cancel_left₀ ht0] at h'⟩, rfl⟩
  refine ⟨g, mem_prinCong.2 fun x hx => ?_, fun h => ?_⟩
  · rw [mem_stdAt_succ hN] at hx ⊢
    refine ⟨?_, ?_⟩
    · rw [map_smul, map_sub, hg, prH_sumE]
      simp only [LinearEquiv.coe_one, id_eq, sub_self, smul_zero]
      exact zero_mem _
    · rw [Pi.smul_apply, Pi.sub_apply, hg, sumE_last, Units.val_mk0, smul_eq_mul,
        show (1 + (qOf P : E) ^ c) * x (Br.iL hN) - x (Br.iL hN) = (qOf P : E) ^ c * x (Br.iL hN) by ring,
        inv_mul_cancel_left₀ (pow_ne_zero _ hq)]
      exact hx.2
  · have h2 := ((mem_stdAt_succ hN).1 h).2
    rw [Pi.smul_apply, Pi.sub_apply, hg, sumE_last, Units.val_mk0, Pi.single_eq_same, smul_eq_mul,
      mul_one, add_sub_cancel_left, pow_succ, mul_inv, mul_comm ((qOf P : E) ^ c)⁻¹, mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ hq), mul_one] at h2
    exact not_intAt_inv_q h2

theorem levelGroup_succ_lt {c : ℕ} (hc : 0 < c) : K1 hN l (c + 1) < K1 hN l c := by
  obtain ⟨g, hg, hg'⟩ := exists_prinCong_not_mem_stdAt (E := E) (P := P) hN hc
  have hle : K1 hN l (c + 1) ≤ K1 hN l c := by
    unfold K1
    exact sup_le_sup_left (prinCong_anti (Nat.le_succ c)) _
  refine lt_of_le_of_ne hle fun e => hg' ?_
  have : g ∈ K1 hN l (c + 1) := by
    rw [e]
    exact principalCongruence_le_levelGroup hN l c hg
  exact levelGroup_lastColumn_congruence hN l (c + 1) this

theorem levelGroup_ne_top_ne_bot {c : ℕ} (hc : 0 < c) : K1 hN l (c + 1) ≠ ⊤ ∧ K1 hN l c ≠ ⊥ :=
  ⟨ne_top_of_lt (levelGroup_succ_lt hN l hc), ne_bot_of_gt (levelGroup_succ_lt hN l hc)⟩

end Depth

section Kernel

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {m2 : ℕ} {u : Pr.Word}

theorem repY_intQ {j : ℕ} (p : ChPt (R := R) sel mu u j) {Y : Set (Sp X.E (R.N j))} (hY : Y ∈ ybSet sel mu cst p.deco.1.N)
    {P : rowSG Pr sel mu} (hP : P.1 ∉ Pr.vGs) (i : Fin (R.N j)) :
    IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * (frsF sel mu p P).symm (repY Y) i) := by
  obtain ⟨y, hy, hYe⟩ := hY
  have hyY : y ∈ Y := by
    rw [hYe, Set.mem_setOf_eq, sub_self]
    exact zero_mem _
  have hv : repY Y ∈ Y := Classical.epsilon_spec (p := fun z => z ∈ Y) ⟨y, hyY⟩
  generalize hr : repY Y = v at hv
  have hv' := hv
  rw [hYe, Set.mem_setOf_eq] at hv'
  have h1 := (Submodule.mem_iInf _).1 hy P
  have h2 := (Submodule.mem_iInf _).1 hv' P
  rw [Submodule.mem_comap] at h1 h2
  simp only [hP, if_false, LinearMap.restrictScalars_apply, LinearMap.smul_apply, LinearMap.id_apply] at h1 h2
  rw [zpow_neg, inv_inv, zpow_natCast] at h1
  rw [zpow_natCast] at h2
  set q : 𝓞 X.E := ((qOf P.1 : ℕ) : 𝓞 X.E) with hq
  have hqE : (algebraMap (𝓞 X.E) X.E q) = (qOf P.1 : X.E) := by simp [hq]
  have hqne : ((qOf P.1 : X.E) ^ cst.M) ≠ 0 := pow_ne_zero _ qOf_ne_zero
  have h3 : ((qOf P.1 : X.E) ^ cst.M) • v ∈ p.deco.1.at P.1 := by
    have e : ((qOf P.1 : X.E) ^ cst.M) • v =
        ((qOf P.1 : X.E) ^ cst.M) • y + (q ^ cst.M * q ^ cst.M) • (((qOf P.1 : X.E) ^ cst.M)⁻¹ • (v - y)) := by
      rw [← algebraMap_smul X.E (q ^ cst.M * q ^ cst.M), map_mul, map_pow, hqE, smul_smul, mul_assoc, mul_inv_cancel₀ hqne,
        mul_one, ← smul_add, add_sub_cancel]
    rw [e]
    exact add_mem h1 (Submodule.smul_mem _ _ h2)
  have h4 : ((qOf P.1 : X.E) ^ cst.M) • (frsF sel mu p P).symm v ∈ stdAt X.E (R.N j) P.1 := by
    rw [← frsF_mem p P, map_smul, LinearEquiv.apply_symm_apply]
    exact h3
  have h5 := (mem_stdAt.1 h4) i
  simpa only [Pi.smul_apply, smul_eq_mul] using h5

theorem k2top_invQ (hm : R.m = m2 + 2) (hc : cst.Ok) (hD : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P)
    (c : TopDepth R cst.M) {T : ChTh W sel mu u m2} (hT : TameFr T.top)
    (κ : GLQ X.E (R.N R.m) (QE sel (mu : Chr X.F X.E X.K))) (hκ : ∀ P, κ P ∈ prinCong _ P.1 c.1)
    (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (p' : TopPt R sel mu u) :
    topDegreeKTwo W Ch sel mu cst T p Y (((1, 1, κ) : UF X.E (R.N R.m) × GLG X.E (R.N R.m) Pr.vGs × GLQ X.E (R.N R.m) _) • p') =
      topDegreeKTwo W Ch sel mu cst T p Y p' := by
  classical
  set a : UF X.E (R.N R.m) × GLG X.E (R.N R.m) Pr.vGs × GLQ X.E (R.N R.m) _ := (1, 1, κ) with ha
  have hdeco : (a • p').deco = p'.deco := by
    rw [GlobalTheory.FramedForms.deco_smul]
    exact one_smul _ _
  let κ' : GLQ X.E (R.N R.m) (rowSG Pr sel mu) := fun P =>
    if h : P.1 ∈ Pr.vGs then 1 else (κ ⟨P.1, (Finset.mem_union.mp P.2).resolve_left h⟩)⁻¹
  have hfr : frsF sel mu (a • p') = fun P => frsF sel mu p' P * (κ' P).1 := by
    funext P
    by_cases h : P.1 ∈ Pr.vGs
    · simp only [frsF, dif_pos h, κ', hdeco, OneMemClass.coe_one, mul_one]
    · simp only [frsF, dif_neg h, κ', GlobalTheory.FramedForms.fr_smul, ha, OneMemClass.coe_one, one_mul]
  have hred : ∀ P : rowSG Pr sel mu, redGL _ P.1 (κ' P) = 1 := by
    intro P
    by_cases h : P.1 ∈ Pr.vGs
    · simp only [κ', dif_pos h, map_one]
    · simp only [κ', dif_neg h, map_inv]
      have hk := hκ ⟨P.1, (Finset.mem_union.mp P.2).resolve_left h⟩
      exact inv_eq_one.2 (redGL_of_prinCong (n := R.N R.m) (P := P.1) c.pos hk)
  have hX : ∀ (hY : Y ∈ ybSet sel mu cst p.deco.1.N) x,
      XiTop Ch sel mu cst m2 p Y (a • p') x = XiTop Ch sel mu cst m2 p Y p' x := by
    intro hY x
    unfold XiTop
    rw [hdeco, hfr]
    congr 1
    refine Finset.prod_congr rfl fun P _ => ?_
    by_cases h : P.1 ∈ Pr.vGs
    · simp only [κ', dif_pos h, OneMemClass.coe_one, mul_one]
    · simp only [κ', dif_neg h]
      set k := κ ⟨P.1, (Finset.mem_union.mp P.2).resolve_left h⟩ with hk
      have e : inFr (frsF sel mu p P) (frsF sel mu p' P * (k⁻¹).1) x =
          k.1.toLinearMap ∘ₗ inFr (frsF sel mu p P) (frsF sel mu p' P) x := by
        apply LinearMap.ext
        intro v
        simp only [inFr, LinearMap.comp_apply, LinearEquiv.coe_coe]
        rw [LinearEquiv.symm_apply_eq, LinearEquiv.mul_apply]
        show _ = frsF sel mu p' P (k.1.symm (k.1 _))
        rw [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
      rw [e]
      have hkm : k ∈ prinCong (R.N R.m) P.1 c.1 := hκ ⟨P.1, (Finset.mem_union.mp P.2).resolve_left h⟩
      exact locTop_invQ (P := P) (κ := k) hm hc h (hD P h) c hkm _ (repY_intQ p hY h)
  unfold topDegreeKTwo
  split_ifs with hY
  · rw [hfr, hdeco]
    unfold kerOf
    congr 1
    funext x
    rw [hX hY x, hT p.deco.1.N (frsF sel mu p) p'.deco.1.N (frsF sel mu p') _ x κ' ⟨p.deco.2.lat, p.deco.2.uni⟩
      ⟨p'.deco.2.lat, p'.deco.2.uni⟩ hred]
  · rfl

end Kernel

end GlobalTheory.TopStep.Model
