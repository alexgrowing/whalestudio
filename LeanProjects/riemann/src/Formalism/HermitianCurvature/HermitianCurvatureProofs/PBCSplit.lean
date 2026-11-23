import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCLim

namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

open Classical

variable {H : Type} {f : ℕ}

structure GermData (Y : Finset H) (U P Q : Fin f → H × ℂ → H × ℂ → ℂ) (hat : Fin f → ℂ → H → H → ℂ) : Prop where
  blk : ∀ v (Xs : Finset ℂ), (∀ x ∈ Xs, x ≠ 0) → KB.BlockPSD (Y ×ˢ Xs) (Y ×ˢ Xs) (U v) (P v) (Q v)
  bd : ∃ B : ℝ, 0 ≤ B ∧ ∀ v, ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → ‖U v (h, x) (h, x)‖ ≤ B ∧ ‖Q v (h, x) (h, x)‖ ≤ B
  limQ : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ∀ σ : ℂ,
    Tendsto (fun x => Q v (h, x) (h', x + σ)) (cocompact ℂ) (𝓝 (hat v σ h h'))
  limP : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ∀ σ : ℂ,
    Tendsto (fun x => P v (h, x) (h', x + σ)) (cocompact ℂ) (𝓝 (hat v σ h h'))
  limPc : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ∀ σ : ℂ,
    Tendsto (fun x => conj (P v (h', x + σ) (h, x))) (cocompact ℂ) (𝓝 (hat v σ h h'))

section

variable {Y : Finset H} {U P Q : Fin f → H × ℂ → H × ℂ → ℂ} {hat : Fin f → ℂ → H → H → ℂ}

private lemma norm_apply_sq_le_mul_of_psdOn {α : Type} {T : Finset α} {k : α → α → ℂ} (hk : TB.PSDOn T k) {a b : α}
    (ha : a ∈ T) (hb : b ∈ T) : ‖k a b‖ ^ 2 ≤ ‖k a a‖ * ‖k b b‖ := by

  have hs := (hk.submatrix ![(⟨a, ha⟩ : T), ⟨b, hb⟩]).det_nonneg
  rw [Matrix.det_fin_two] at hs
  simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] at hs
  have hba : k b a = conj (k a b) := by
    have := congrFun (congrFun hk.isHermitian ⟨b, hb⟩) ⟨a, ha⟩
    simpa [Matrix.conjTranspose_apply] using this.symm
  have hda : 0 ≤ k a a := by
    have := (hk.submatrix ![(⟨a, ha⟩ : T)]).det_nonneg
    rw [Matrix.det_fin_one] at this
    simpa using this
  have hdb : 0 ≤ k b b := by
    have := (hk.submatrix ![(⟨b, hb⟩ : T)]).det_nonneg
    rw [Matrix.det_fin_one] at this
    simpa using this
  rw [hba, Complex.mul_conj] at hs
  obtain ⟨hs1, -⟩ := Complex.le_def.mp hs
  obtain ⟨ha1, ha2⟩ := Complex.le_def.mp hda
  obtain ⟨hb1, hb2⟩ := Complex.le_def.mp hdb
  simp only [Complex.zero_re, Complex.zero_im, Complex.sub_re, Complex.mul_re, Complex.ofReal_re] at hs1 ha1 ha2 hb1 hb2
  have na : ‖k a a‖ = (k a a).re := by
    rw [← Complex.re_add_im (k a a), ← ha2]; simp [abs_of_nonneg ha1]
  have nb : ‖k b b‖ = (k b b).re := by
    rw [← Complex.re_add_im (k b b), ← hb2]; simp [abs_of_nonneg hb1]
  rw [na, nb, ← Complex.normSq_eq_norm_sq]
  rw [← ha2, ← hb2] at hs1
  linarith

private lemma entry_lemma_2 (hG : GermData Y U P Q hat) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ v, ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → ‖U v (h, x) (h, x)‖ ≤ B ∧ ‖Q v (h, x) (h, x)‖ ≤ B)
    (v : Fin f) {h h' : H} (hh : h ∈ Y) (hh' : h' ∈ Y) {z z' : ℂ} (hz : z ≠ 0) (hz' : z' ≠ 0) :
    ‖U v (h, z) (h', z')‖ ≤ B ∧ ‖P v (h, z) (h', z')‖ ≤ B ∧ ‖Q v (h, z) (h', z')‖ ≤ B := by
  have hk := hG.blk v {z, z'} (by simp [hz, hz'])
  have hp : ((h, z) : H × ℂ) ∈ Y ×ˢ ({z, z'} : Finset ℂ) := by simp [hh]
  have hq : ((h', z') : H × ℂ) ∈ Y ×ˢ ({z, z'} : Finset ℂ) := by simp [hh']
  obtain ⟨hU1, hQ1⟩ := hB v h hh z hz
  obtain ⟨hU2, hQ2⟩ := hB v h' hh' z' hz'
  have e1 : ‖U v (h, z) (h', z')‖ ^ 2 ≤ ‖U v (h, z) (h, z)‖ * ‖U v (h', z') (h', z')‖ :=
    norm_apply_sq_le_mul_of_psdOn hk (a := Sum.inl (h, z)) (b := Sum.inl (h', z')) (by simp [hp]) (by simp [hq])
  have e2 : ‖P v (h, z) (h', z')‖ ^ 2 ≤ ‖U v (h, z) (h, z)‖ * ‖Q v (h', z') (h', z')‖ :=
    norm_apply_sq_le_mul_of_psdOn hk (a := Sum.inl (h, z)) (b := Sum.inr (h', z')) (by simp [hp]) (by simp [hq])
  have e3 : ‖Q v (h, z) (h', z')‖ ^ 2 ≤ ‖Q v (h, z) (h, z)‖ * ‖Q v (h', z') (h', z')‖ :=
    norm_apply_sq_le_mul_of_psdOn hk (a := Sum.inr (h, z)) (b := Sum.inr (h', z')) (by simp [hp]) (by simp [hq])
  have m1 := mul_le_mul hU1 hU2 (norm_nonneg _) hB0
  have m2 := mul_le_mul hU1 hQ2 (norm_nonneg _) hB0
  have m3 := mul_le_mul hQ1 hQ2 (norm_nonneg _) hB0
  have n1 := norm_nonneg (U v (h, z) (h', z'))
  have n2 := norm_nonneg (P v (h, z) (h', z'))
  have n3 := norm_nonneg (Q v (h, z) (h', z'))
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem GermData.phiG_bdd (hG : GermData Y U P Q hat) (κ : H → H → ℂ) :
    ∃ C : ℝ, ∀ x x' : crystallineComparison.V f, ‖phiG Y κ U x x'‖ ≤ C ∧ ‖phiG Y κ P x x'‖ ≤ C ∧ ‖phiG Y κ Q x x'‖ ≤ C := by
  obtain ⟨B, hB0, hB⟩ := hG.bd
  have hC : 0 ≤ (∑ h ∈ Y, ∑ h' ∈ Y, ‖κ h h'‖) * B ^ f := by positivity
  refine ⟨(∑ h ∈ Y, ∑ h' ∈ Y, ‖κ h h'‖) * B ^ f, fun x x' => ?_⟩
  unfold phiG
  by_cases hg : Good x ∧ Good x'
  · simp only [if_pos hg]
    have hE := fun v h (hh : h ∈ Y) h' (hh' : h' ∈ Y) => entry_lemma_2 hG hB0 hB v hh hh' (hg.1 v) (hg.2 v)
    exact ⟨phi_bound Y κ U B hB0 x x' fun v h hh h' hh' => (hE v h hh h' hh').1,
      phi_bound Y κ P B hB0 x x' fun v h hh h' hh' => (hE v h hh h' hh').2.1,
      phi_bound Y κ Q B hB0 x x' fun v h hh h' hh' => (hE v h hh h' hh').2.2⟩
  · simp only [if_neg hg, norm_zero]
    exact ⟨hC, hC, hC⟩

theorem GermData.phiRG_bdd (hG : GermData Y U P Q hat) (κ : H → H → ℂ) :
    ∃ C : ℝ, ∀ x x' : crystallineComparison.V f, ‖phiRG Y κ U P Q x x'‖ ≤ C := by
  obtain ⟨C, hC⟩ := hG.phiG_bdd κ
  refine ⟨4 * C, fun x x' => ?_⟩
  have hr : phiRG Y κ U P Q x x' =
      phiG Y κ U x x' - phiG Y κ P x x' - conj (phiG Y κ P x' x) + phiG Y κ Q x x' := by
    rw [phiG_split Y κ U P Q x x']; ring
  rw [hr]
  obtain ⟨a1, a2, a3⟩ := hC x x'
  obtain ⟨-, b2, -⟩ := hC x' x
  have c2 : ‖conj (phiG Y κ P x' x)‖ ≤ C := by rw [Complex.norm_conj]; exact b2
  calc _ ≤ ‖phiG Y κ U x x'‖ + ‖phiG Y κ P x x'‖ + ‖conj (phiG Y κ P x' x)‖ + ‖phiG Y κ Q x x'‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
        exact norm_sub_le _ _
    _ ≤ 4 * C := by linarith

variable (Λ : AddSubgroup (crystallineComparison.V f)) (LIM : (Λ → ℂ) → ℂ)

def A0 (Y : Finset H) (κ : H → H → ℂ) (U P Q : Fin f → H × ℂ → H × ℂ → ℂ) (τ : crystallineComparison.V f) : ℂ :=
  LIM fun x : Λ => phiRG Y κ U P Q (x : crystallineComparison.V f) ((x : crystallineComparison.V f) + τ)

private lemma lim_eq_of_tendsto_atInfAll (hL : crystallineComparison.IsMeanInf Λ LIM) {g : Λ → ℂ} (hg : crystallineComparison.Bdd g) {c : ℂ}
    (ht : Tendsto g (comap (fun x : Λ => (x : crystallineComparison.V f)) (crystallineComparison.atInfAll f)) (𝓝 c)) : LIM g = c := by
  obtain ⟨⟨hadd, hsmul, -, hone, -⟩, hinf⟩ := hL
  obtain ⟨B, hB⟩ := hg
  have h1 : crystallineComparison.Bdd (fun _ : Λ => (1 : ℂ)) := ⟨1, fun _ => by simp⟩
  have hc : crystallineComparison.Bdd ((-c) • fun _ : Λ => (1 : ℂ)) := ⟨‖c‖, fun _ => by simp⟩
  have hgc : crystallineComparison.Bdd (g + (-c) • fun _ : Λ => (1 : ℂ)) :=
    ⟨B + ‖c‖, fun x => (norm_add_le _ _).trans (add_le_add (hB x) (by simp))⟩
  have ht' : Tendsto (g + (-c) • fun _ : Λ => (1 : ℂ)) (comap (fun x : Λ => (x : crystallineComparison.V f)) (crystallineComparison.atInfAll f)) (𝓝 0) := by
    have := ht.add_const (-c)
    simp only [add_neg_cancel] at this
    convert this using 1
    funext x; simp
  have h0 := hinf _ hgc ht'
  rw [hadd _ _ ⟨B, hB⟩ hc, hsmul _ _ h1, hone] at h0
  linear_combination h0

theorem mean_split (hG : GermData Y U P Q hat) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (hL : crystallineComparison.IsMeanInf Λ LIM)
    (σ : crystallineComparison.V f) :
    LIM (fun x : Λ => phiG Y κ U (x : crystallineComparison.V f) ((x : crystallineComparison.V f) + σ)) = Hh Y κ hat σ + A0 Λ LIM Y κ U P Q σ := by
  obtain ⟨CG, hCG⟩ := hG.phiG_bdd κ
  obtain ⟨CR, hCR⟩ := hG.phiRG_bdd κ
  obtain ⟨hadd, hsmul, -, -, -⟩ := hL.1
  have bR : crystallineComparison.Bdd (fun x : Λ => phiRG Y κ U P Q (x : crystallineComparison.V f) ((x : crystallineComparison.V f) + σ)) := ⟨CR, fun _ => hCR _ _⟩
  have bP : crystallineComparison.Bdd (fun x : Λ => phiG Y κ P (x : crystallineComparison.V f) ((x : crystallineComparison.V f) + σ)) := ⟨CG, fun _ => (hCG _ _).2.1⟩
  have bPc : crystallineComparison.Bdd (fun x : Λ => conj (phiG Y κ P ((x : crystallineComparison.V f) + σ) (x : crystallineComparison.V f))) :=
    ⟨CG, fun _ => by rw [Complex.norm_conj]; exact (hCG _ _).2.1⟩
  have bQ : crystallineComparison.Bdd (fun x : Λ => phiG Y κ Q (x : crystallineComparison.V f) ((x : crystallineComparison.V f) + σ)) := ⟨CG, fun _ => (hCG _ _).2.2⟩
  have badd : ∀ {g h : Λ → ℂ}, crystallineComparison.Bdd g → crystallineComparison.Bdd h → crystallineComparison.Bdd (g + h) := by
    rintro g h ⟨B1, h1⟩ ⟨B2, h2⟩
    exact ⟨B1 + B2, fun x => (norm_add_le _ _).trans (add_le_add (h1 x) (h2 x))⟩
  have bQ' : crystallineComparison.Bdd ((-1 : ℂ) • fun x : Λ => phiG Y κ Q (x : crystallineComparison.V f) ((x : crystallineComparison.V f) + σ)) := by
    obtain ⟨B, hB⟩ := bQ; exact ⟨B, fun x => by simpa using hB x⟩
  have hsplit : (fun x : Λ => phiG Y κ U (x : crystallineComparison.V f) ((x : crystallineComparison.V f) + σ)) =
      (fun x : Λ => phiRG Y κ U P Q (x : crystallineComparison.V f) ((x : crystallineComparison.V f) + σ)) +
        (fun x : Λ => phiG Y κ P (x : crystallineComparison.V f) ((x : crystallineComparison.V f) + σ)) +
        (fun x : Λ => conj (phiG Y κ P ((x : crystallineComparison.V f) + σ) (x : crystallineComparison.V f))) +
        (-1 : ℂ) • (fun x : Λ => phiG Y κ Q (x : crystallineComparison.V f) ((x : crystallineComparison.V f) + σ)) := by
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [phiG_split Y κ U P Q]; ring
  have lP := lim_eq_of_tendsto_atInfAll Λ LIM hL bP ((phiG_tendsto Y κ P hat hG.limP σ).comp tendsto_comap)
  have lPc := lim_eq_of_tendsto_atInfAll Λ LIM hL bPc ((phiG_conj_tendsto Y κ hκ P hat hG.limPc σ).comp tendsto_comap)
  have lQ := lim_eq_of_tendsto_atInfAll Λ LIM hL bQ ((phiG_tendsto Y κ Q hat hG.limQ σ).comp tendsto_comap)
  rw [hsplit, hadd _ _ (badd (badd bR bP) bPc) bQ', hadd _ _ (badd bR bP) bPc, hadd _ _ bR bP, hsmul _ _ bQ,
    lP, lPc, lQ]
  simp only [A0]
  ring

theorem limit_average_translate_eq (hG : GermData Y U P Q hat) (κ : H → H → ℂ) (hL : crystallineComparison.IsMean LIM) {σ σ' : crystallineComparison.V f}
    (hσ' : σ' ∈ Λ) :
    A0 Λ LIM Y κ U P Q (σ - σ') =
      LIM (fun x : Λ => phiRG Y κ U P Q ((x : crystallineComparison.V f) + σ') ((x : crystallineComparison.V f) + σ)) := by
  obtain ⟨CR, hCR⟩ := hG.phiRG_bdd κ
  have hb : crystallineComparison.Bdd (fun x : Λ => phiRG Y κ U P Q (x : crystallineComparison.V f) ((x : crystallineComparison.V f) + (σ - σ'))) :=
    ⟨CR, fun _ => hCR _ _⟩
  have ht := hL.2.2.2.2 _ ⟨σ', hσ'⟩ hb
  simp only [A0]
  rw [← ht]
  congr 1
  funext x
  simp only [AddSubgroup.coe_add, AddSubgroup.coe_mk]
  rw [show (x : crystallineComparison.V f) + σ' + (σ - σ') = (x : crystallineComparison.V f) + σ by abel]

private lemma bdd_finset_sum {β ι : Type} (s : Finset ι) (g : ι → β → ℂ) (hg : ∀ i ∈ s, crystallineComparison.Bdd (g i)) :
    crystallineComparison.Bdd (fun x => ∑ i ∈ s, g i x) := by
  choose! B hB using hg
  exact ⟨∑ i ∈ s, B i, fun x => (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => hB i hi x)⟩

private lemma lim_finset_sum_of_isMean (hL : crystallineComparison.IsMean LIM) {ι : Type} (s : Finset ι) (g : ι → Λ → ℂ)
    (hg : ∀ i ∈ s, crystallineComparison.Bdd (g i)) : LIM (fun x => ∑ i ∈ s, g i x) = ∑ i ∈ s, LIM (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have e : (fun _ : Λ => (0 : ℂ)) = (0 : ℂ) • (fun _ : Λ => (1 : ℂ)) := by funext; simp
    simp only [Finset.sum_empty]
    rw [e, hL.2.1 _ _ ⟨1, fun _ => by simp⟩, zero_mul]
  | insert i s hi ih =>
    have hs : ∀ j ∈ s, crystallineComparison.Bdd (g j) := fun j hj => hg j (Finset.mem_insert_of_mem hj)
    have e : (fun x => ∑ j ∈ insert i s, g j x) = g i + fun x => ∑ j ∈ s, g j x := by
      funext x; simp [Finset.sum_insert hi]
    rw [e, Finset.sum_insert hi, hL.1 _ _ (hg i (Finset.mem_insert_self _ _)) (bdd_finset_sum s g hs), ih hs]

theorem limit_average_positive_definite (hG : GermData Y U P Q hat) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (hL : crystallineComparison.IsMean LIM)
    (S : Finset (crystallineComparison.V f)) (hS : ∀ σ ∈ S, σ ∈ Λ) (c : crystallineComparison.V f → ℂ) :
    0 ≤ (∑ σ ∈ S, ∑ σ' ∈ S, A0 Λ LIM Y κ U P Q (σ - σ') * c σ * conj (c σ')).re := by
  classical
  have qf : ∀ X : crystallineComparison.V f, 0 ≤ ∑ σ ∈ S, ∑ σ' ∈ S, phiRG Y κ U P Q (X + σ') (X + σ) * c σ * conj (c σ') := by
    intro X
    have hinj : Set.InjOn (fun σ => X + σ) S := fun a _ b _ h => add_left_cancel h
    have h := (phiRG_psd Y κ hκ U P Q hG.blk (S.image fun σ => X + σ)).dotProduct_mulVec_nonneg
      (fun t => c ((t : crystallineComparison.V f) - X))
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Matrix.of_apply, Finset.mul_sum] at h
    rw [Finset.sum_coe_sort (S.image fun σ => X + σ) (fun i => ∑ j : ↥(S.image fun σ => X + σ),
      star (c (i - X)) * (phiRG Y κ U P Q i j * c (j - X)))] at h
    rw [Finset.sum_image hinj] at h
    have e : ∀ x ∈ S, (∑ j : ↥(S.image fun σ => X + σ),
        star (c (X + x - X)) * (phiRG Y κ U P Q (X + x) ↑j * c (↑j - X))) =
        ∑ σ ∈ S, phiRG Y κ U P Q (X + x) (X + σ) * c σ * conj (c x) := by
      intro x _
      rw [Finset.sum_coe_sort (S.image fun σ => X + σ)
        (fun j => star (c (X + x - X)) * (phiRG Y κ U P Q (X + x) j * c (j - X))), Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun σ _ => ?_
      simp only [add_sub_cancel_left, Complex.star_def]
      ring
    rw [Finset.sum_congr rfl e, Finset.sum_comm] at h
    exact h
  obtain ⟨CR, hCR⟩ := hG.phiRG_bdd κ
  have hb : ∀ σ σ' : crystallineComparison.V f, crystallineComparison.Bdd (fun x : Λ =>
      phiRG Y κ U P Q ((x : crystallineComparison.V f) + σ') ((x : crystallineComparison.V f) + σ) * c σ * conj (c σ')) := fun σ σ' =>
    ⟨CR * ‖c σ‖ * ‖c σ'‖, fun x => by
      rw [norm_mul, norm_mul, Complex.norm_conj]
      gcongr
      exact hCR _ _⟩
  have e1 : ∀ σ ∈ S, ∀ σ' ∈ S, A0 Λ LIM Y κ U P Q (σ - σ') * c σ * conj (c σ') =
      LIM (fun x : Λ => phiRG Y κ U P Q ((x : crystallineComparison.V f) + σ') ((x : crystallineComparison.V f) + σ) * c σ * conj (c σ')) := by
    intro σ _ σ' hσ'
    have hb0 : crystallineComparison.Bdd (fun x : Λ => phiRG Y κ U P Q ((x : crystallineComparison.V f) + σ') ((x : crystallineComparison.V f) + σ)) :=
      ⟨CR, fun _ => hCR _ _⟩
    rw [limit_average_translate_eq Λ LIM hG κ hL (hS σ' hσ'), mul_assoc, mul_comm, ← hL.2.1 _ _ hb0]
    congr 1
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl fun σ hσ => Finset.sum_congr rfl (e1 σ hσ)]
  rw [Finset.sum_congr rfl fun σ _ => (lim_finset_sum_of_isMean Λ LIM hL S _ fun σ' _ => hb σ σ').symm]
  rw [← lim_finset_sum_of_isMean Λ LIM hL S _ fun σ _ => bdd_finset_sum S _ fun σ' _ => hb σ σ']
  refine (hL.2.2.1 _ (bdd_finset_sum S _ fun σ _ => bdd_finset_sum S _ fun σ' _ => hb σ σ') fun x => ?_).1
  have := Complex.le_def.mp (qf x)
  simp only [Complex.zero_re, Complex.zero_im] at this
  exact ⟨this.1, this.2.symm⟩

end

end

end Formalism.FourierDecayAlt.P.PBC
