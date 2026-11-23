import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousVanishingHyperplaneExtendStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmoothVanishingHyperplanesFactorStatement
open GlobalTheory.Chamber
open scoped InnerProductSpace ContDiff Classical

namespace GlobalTheory.ExtRes

theorem exists_line_reps {k : ℕ} (S : Finset (A0 k)) (hS : ∀ w ∈ S, w ≠ 0) :
    ∃ Ls ⊆ S, (∀ b ∈ Ls, ∀ b' ∈ Ls, b ≠ b' → ∀ r : ℝ, b' ≠ r • b) ∧
      ∀ w ∈ S, ∃ l ∈ Ls, ∃ r : ℝ, w = r • l := by
  induction S using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp, by simp⟩
  | @insert w S hw ih =>
    obtain ⟨Ls, hsub, hp, hc⟩ := ih (fun u hu => hS u (Finset.mem_insert_of_mem hu))
    by_cases hex : ∃ l ∈ Ls, ∃ r : ℝ, w = r • l
    · refine ⟨Ls, hsub.trans (Finset.subset_insert _ _), hp, ?_⟩
      intro u hu
      rcases Finset.mem_insert.1 hu with rfl | hu
      · exact hex
      · exact hc u hu
    · push Not at hex
      have hw0 : w ≠ 0 := hS w (Finset.mem_insert_self _ _)
      refine ⟨insert w Ls, Finset.insert_subset_insert _ hsub, ?_, ?_⟩
      · intro b hb b' hb' hne r
        rcases Finset.mem_insert.1 hb with rfl | hbL <;> rcases Finset.mem_insert.1 hb' with rfl | hbL'
        · exact absurd rfl hne
        · intro h
          have hb'0 : b' ≠ 0 := hS b' (Finset.mem_insert_of_mem (hsub hbL'))
          have hr : r ≠ 0 := by rintro rfl; simp at h; exact hb'0 h
          apply hex b' hbL' r⁻¹
          rw [h, smul_smul, inv_mul_cancel₀ hr, one_smul]
        · exact hex b hbL r
        · exact hp b hbL b' hbL' hne r
      · intro u hu
        rcases Finset.mem_insert.1 hu with rfl | hu
        · exact ⟨u, Finset.mem_insert_self _ _, 1, (one_smul _ _).symm⟩
        · obtain ⟨l, hl, r, hr⟩ := hc u hu
          exact ⟨l, Finset.mem_insert_of_mem hl, r, hr⟩

theorem term_generic {k : ℕ} {K : Type} (M : Finset K) (Ls : Finset (A0 k)) (v l : K → A0 k) (r : K → ℝ)
    (hl : ∀ a ∈ M, l a ∈ Ls) (hv : ∀ a ∈ M, v a = r a • l a) (hinj : Set.InjOn l M)
    (c : ℂ) (x : A0 k) (hx : ∀ a ∈ M, ⟪x, v a⟫_ℝ ≠ 0) :
    c * ((∏ a ∈ M, (r a : ℂ))⁻¹ * ∏ l' ∈ Ls \ M.image l, (⟪x, l'⟫_ℝ : ℂ)) =
      (∏ l' ∈ Ls, (⟪x, l'⟫_ℝ : ℂ)) * (c * ∏ a ∈ M, (⟪x, v a⟫_ℝ : ℂ)⁻¹) := by
  have h1 : ∏ a ∈ M, (⟪x, v a⟫_ℝ : ℂ) = (∏ a ∈ M, (r a : ℂ)) * ∏ l' ∈ M.image l, (⟪x, l'⟫_ℝ : ℂ) := by
    rw [Finset.prod_image (fun a ha b hb h => hinj ha hb h), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a ha => ?_
    rw [hv a ha, real_inner_smul_right]; push_cast; ring
  have hsub : M.image l ⊆ Ls := by
    intro y hy; obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hy; exact hl a ha
  have hne : ∏ a ∈ M, (⟪x, v a⟫_ℝ : ℂ) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun a ha => by exact_mod_cast hx a ha
  rw [h1] at hne
  have hR : ∏ a ∈ M, (r a : ℂ) ≠ 0 := left_ne_zero_of_mul hne
  have hI : ∏ l' ∈ M.image l, (⟪x, l'⟫_ℝ : ℂ) ≠ 0 := right_ne_zero_of_mul hne
  rw [Finset.prod_inv_distrib, h1, ← Finset.prod_sdiff hsub]
  field_simp

theorem term_residue {k : ℕ} {K : Type} [DecidableEq K] (M : Finset K) (Ls : Finset (A0 k)) (v l : K → A0 k) (r : K → ℝ)
    (hl : ∀ a ∈ M, l a ∈ Ls) (hv : ∀ a ∈ M, v a = r a • l a) (hr : ∀ a ∈ M, r a ≠ 0)
    (hinj : Set.InjOn l M) (hLs : ∀ b ∈ Ls, ∀ b' ∈ Ls, b ≠ b' → ∀ t : ℝ, b' ≠ t • b)
    (c : ℂ) (l0 : A0 k) (hl0 : l0 ∈ Ls) (hl00 : l0 ≠ 0) (x : A0 k) (hx0 : ⟪x, l0⟫_ℝ = 0)
    (hx : ∀ l' ∈ Ls.erase l0, ⟪x, l'⟫_ℝ ≠ 0) :
    c * ((∏ a ∈ M, (r a : ℂ))⁻¹ * ∏ l' ∈ Ls \ M.image l, (⟪x, l'⟫_ℝ : ℂ)) =
      ((⟪l0, l0⟫_ℝ : ℂ) * ∏ l' ∈ Ls.erase l0, (⟪x, l'⟫_ℝ : ℂ)) *
        ∑ a ∈ M.filter (fun a => ∃ t : ℝ, v a = t • l0),
          c * ((⟪v a, l0⟫_ℝ : ℂ)⁻¹ * ∏ a' ∈ M.erase a, (⟪x, v a'⟫_ℝ : ℂ)⁻¹) := by
  have hsub : M.image l ⊆ Ls := by
    intro y hy; obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hy; exact hl a ha
  have hfilt : ∀ a ∈ M, (∃ t : ℝ, v a = t • l0) ↔ l a = l0 := by
    intro a ha; constructor
    · rintro ⟨t, ht⟩; by_contra hne
      apply hLs l0 hl0 (l a) (hl a ha) (Ne.symm hne) ((r a)⁻¹ * t)
      rw [← smul_smul, ← ht, hv a ha, smul_smul, inv_mul_cancel₀ (hr a ha), one_smul]
    · intro h; exact ⟨r a, by rw [hv a ha, h]⟩
  by_cases hmem : l0 ∈ M.image l
  · obtain ⟨a0, ha0, hla0⟩ := Finset.mem_image.1 hmem
    have hF : M.filter (fun a => ∃ t : ℝ, v a = t • l0) = {a0} := by
      ext a; simp only [Finset.mem_filter, Finset.mem_singleton]; constructor
      · rintro ⟨ha, h⟩; exact hinj ha ha0 (((hfilt a ha).1 h).trans hla0.symm)
      · rintro rfl; exact ⟨ha0, (hfilt a ha0).2 hla0⟩
    rw [hF, Finset.sum_singleton]
    have himg : (M.erase a0).image l = (M.image l).erase l0 := by
      ext y; simp only [Finset.mem_image, Finset.mem_erase]; constructor
      · rintro ⟨a, ⟨hne, ha⟩, rfl⟩
        exact ⟨fun h => hne (hinj ha ha0 (h.trans hla0.symm)), a, ha, rfl⟩
      · rintro ⟨hy, a, ha, rfl⟩
        exact ⟨a, ⟨fun h => hy (h ▸ hla0), ha⟩, rfl⟩
    have h1 : ∏ a ∈ M.erase a0, (⟪x, v a⟫_ℝ : ℂ) =
        (∏ a ∈ M.erase a0, (r a : ℂ)) * ∏ l' ∈ (M.image l).erase l0, (⟪x, l'⟫_ℝ : ℂ) := by
      rw [← himg, Finset.prod_image (fun a ha b hb h =>
        hinj (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hb) h), ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun a ha => ?_
      rw [hv a (Finset.mem_of_mem_erase ha), real_inner_smul_right]; push_cast; ring
    have hset : (Ls.erase l0) \ ((M.image l).erase l0) = Ls \ M.image l := by
      ext y; by_cases hy : y = l0
      · subst hy; simp [hmem]
      · simp [hy]
    have hsplit : ∏ l' ∈ Ls.erase l0, (⟪x, l'⟫_ℝ : ℂ) =
        (∏ l' ∈ Ls \ M.image l, (⟪x, l'⟫_ℝ : ℂ)) * ∏ l' ∈ (M.image l).erase l0, (⟪x, l'⟫_ℝ : ℂ) := by
      rw [← Finset.prod_sdiff (Finset.erase_subset_erase l0 hsub), hset]
    have hR : ∏ a ∈ M, (r a : ℂ) = r a0 * ∏ a ∈ M.erase a0, (r a : ℂ) :=
      (Finset.mul_prod_erase M _ ha0).symm
    have hva0 : ⟪v a0, l0⟫_ℝ = r a0 * ⟪l0, l0⟫_ℝ := by rw [hv a0 ha0, hla0, real_inner_smul_left]
    have hll : (⟪l0, l0⟫_ℝ : ℂ) ≠ 0 := by
      rw [Ne, Complex.ofReal_eq_zero]; exact fun h => hl00 (inner_self_eq_zero.1 h)
    have hra0 : (r a0 : ℂ) ≠ 0 := by exact_mod_cast hr a0 ha0
    have hRe : ∏ a ∈ M.erase a0, (r a : ℂ) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun a ha => by exact_mod_cast hr a (Finset.mem_of_mem_erase ha)
    have hIe : ∏ l' ∈ (M.image l).erase l0, (⟪x, l'⟫_ℝ : ℂ) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun y hy => by
        exact_mod_cast hx y (Finset.erase_subset_erase l0 hsub hy)
    rw [Finset.prod_inv_distrib, h1, hsplit, hR, hva0]
    push_cast
    field_simp
  · have hF : M.filter (fun a => ∃ t : ℝ, v a = t • l0) = ∅ := by
      ext a; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro ha h; exact hmem (Finset.mem_image.2 ⟨a, ha, (hfilt a ha).1 h⟩)
    rw [hF, Finset.sum_empty, mul_zero,
      Finset.prod_eq_zero (Finset.mem_sdiff.2 ⟨hl0, hmem⟩) (by simp [hx0]), mul_zero, mul_zero]

end GlobalTheory.ExtRes

namespace GlobalTheory

theorem smooth_extension_of_residues_cancel :
    ∀ {k : ℕ} {J K : Type} [DecidableEq K] (s : Finset J) (m : J → Finset K) (v : J → K → A0 k) (g : J → A0 k → ℂ),
  (∀ j ∈ s, ContDiff ℝ ∞ (g j)) → (∀ j ∈ s, ∀ a ∈ m j, v j a ≠ 0) →
  (∀ j ∈ s, ∀ a ∈ m j, ∀ a' ∈ m j, a ≠ a' → ∀ r : ℝ, v j a' ≠ r • v j a) →
  (∀ b : A0 k, b ≠ 0 → ∀ x : A0 k, ⟪x, b⟫_ℝ = 0 → (∀ j ∈ s, ∀ a ∈ m j, (∀ r : ℝ, v j a ≠ r • b) → ⟪x, v j a⟫_ℝ ≠ 0) →
    ∑ j ∈ s, ∑ a ∈ (m j).filter (fun a => ∃ r : ℝ, v j a = r • b),
      g j x * ((⟪v j a, b⟫_ℝ : ℂ)⁻¹ * ∏ a' ∈ (m j).erase a, (⟪x, v j a'⟫_ℝ : ℂ)⁻¹) = 0) →
  ∃ F : A0 k → ℂ, ContDiff ℝ ∞ F ∧ ∀ x, (∀ j ∈ s, ∀ a ∈ m j, ⟪x, v j a⟫_ℝ ≠ 0) →
    F x = ∑ j ∈ s, g j x * ∏ a ∈ m j, (⟪x, v j a⟫_ℝ : ℂ)⁻¹ := by
  intro k J K _ s m v g hg hv0 hnp hres
  set S : Finset (A0 k) := s.biUnion (fun j => (m j).image (v j)) with hS
  have memS : ∀ w, w ∈ S ↔ ∃ j ∈ s, ∃ a ∈ m j, v j a = w := by
    intro w; simp [hS]
  have hS0 : ∀ w ∈ S, w ≠ 0 := by
    intro w hw
    obtain ⟨j, hj, a, ha, rfl⟩ := (memS w).1 hw
    exact hv0 j hj a ha
  obtain ⟨Ls, hsub, hp, hc⟩ := ExtRes.exists_line_reps S hS0
  have hc' : ∀ j ∈ s, ∀ a ∈ m j, ∃ l ∈ Ls, ∃ r : ℝ, v j a = r • l :=
    fun j hj a ha => hc _ ((memS _).2 ⟨j, hj, a, ha, rfl⟩)
  choose! l hl r hr using hc'
  have hr0 : ∀ j ∈ s, ∀ a ∈ m j, r j a ≠ 0 := by
    intro j hj a ha h
    apply hv0 j hj a ha
    rw [hr j hj a ha, h, zero_smul]
  have hinj : ∀ j ∈ s, Set.InjOn (l j) (m j) := by
    intro j hj a ha a' ha' h
    by_contra hne
    apply hnp j hj a ha a' ha' hne (r j a' * (r j a)⁻¹)
    rw [hr j hj a ha, hr j hj a' ha', h, smul_smul, mul_assoc, inv_mul_cancel₀ (hr0 j hj a ha), mul_one]
  have hL0 : ∀ b ∈ Ls, b ≠ 0 := fun b hb => hS0 b (hsub hb)
  let N : A0 k → ℂ := fun x => ∑ j ∈ s,
    g j x * ((∏ a ∈ m j, (r j a : ℂ))⁻¹ * ∏ l' ∈ Ls \ (m j).image (l j), (⟪x, l'⟫_ℝ : ℂ))
  have hN : ContDiff ℝ ∞ N := by
    refine ContDiff.sum fun j hj => (hg j hj).mul (contDiff_const.mul (contDiff_prod fun l' _ => ?_))
    exact Complex.ofRealCLM.contDiff.comp (contDiff_id.inner ℝ contDiff_const)
  have hvan : ∀ b ∈ Ls, ∀ x, ⟪x, b⟫_ℝ = 0 → N x = 0 := by
    intro l0 hl0
    refine GlobalTheory.T.continuous_vanishing_hyperplane_extend l0 (Ls.erase l0) N hN.continuous ?_ ?_
    · intro b' hb'
      exact hp l0 hl0 b' (Finset.mem_of_mem_erase hb') (Finset.ne_of_mem_erase hb').symm
    · intro x hx0 hx
      have h1 := hres l0 (hL0 l0 hl0) x hx0 (by
        intro j hj a ha hne
        have hla : l j a ≠ l0 := fun h => hne (r j a) (by rw [hr j hj a ha, h])
        rw [hr j hj a ha, real_inner_smul_right]
        exact mul_ne_zero (hr0 j hj a ha) (hx _ (Finset.mem_erase.2 ⟨hla, hl j hj a ha⟩)))
      have h2 : N x = ((⟪l0, l0⟫_ℝ : ℂ) * ∏ l' ∈ Ls.erase l0, (⟪x, l'⟫_ℝ : ℂ)) *
          ∑ j ∈ s, ∑ a ∈ (m j).filter (fun a => ∃ t : ℝ, v j a = t • l0),
            g j x * ((⟪v j a, l0⟫_ℝ : ℂ)⁻¹ * ∏ a' ∈ (m j).erase a, (⟪x, v j a'⟫_ℝ : ℂ)⁻¹) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        exact ExtRes.term_residue (m j) Ls (v j) (l j) (r j) (hl j hj) (hr j hj) (hr0 j hj) (hinj j hj) hp
          (g j x) l0 hl0 (hL0 l0 hl0) x hx0 hx
      rw [h2, h1, mul_zero]
  obtain ⟨F, hF, hNF⟩ := GlobalTheory.T.smooth_vanishing_hyperplanes_factor Ls N hL0 hp hN hvan
  refine ⟨F, hF, fun x hx => ?_⟩
  have hne : (∏ b ∈ Ls, (⟪x, b⟫_ℝ : ℂ)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun b hb => ?_
    obtain ⟨j, hj, a, ha, rfl⟩ := (memS b).1 (hsub hb)
    exact_mod_cast hx j hj a ha
  apply mul_left_cancel₀ hne
  rw [← hNF x, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  exact ExtRes.term_generic (m j) Ls (v j) (l j) (r j) (hl j hj) (hr j hj) (hinj j hj) (g j x) x (hx j hj)

end GlobalTheory
