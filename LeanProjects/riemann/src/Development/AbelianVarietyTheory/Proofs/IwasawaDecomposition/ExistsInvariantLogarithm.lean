import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SCoordStatementPf
import ReciprocityTheory.SemistableReduction.ShareDetA

noncomputable section

open NumberField Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul mat hermC sgn)
open ReciprocityTheory.ChartRestriction.G
open scoped ComplexOrder

namespace GlobalTheory.FrameLog

theorem exists_log {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] {S : Set V} (ho : IsOpen S)
    (hs : StarConvex ℝ 0 S) (hne : S.Nonempty) {F : V → ℂ} (hF : DifferentiableOn ℂ F S) (h0 : ∀ w ∈ S, F w ≠ 0) :
    ∃ L : V → ℂ, DifferentiableOn ℂ L S ∧ ∀ w ∈ S, Complex.exp (L w) = F w := by
  have := hs.contractibleSpace hne
  have hsc : IsSimplyConnected S := (inferInstance : SimplyConnectedSpace S)
  obtain ⟨L, hLc, hL⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsc ho hF.continuousOn
    (by rintro ⟨w, hw, h⟩; exact h0 w hw h)
  refine ⟨L, fun w hw => ?_, fun w hw => hL hw⟩
  have hn := ho.mem_nhds hw
  have hc : ContinuousAt (fun z => (L z - L w).im) w :=
    Complex.continuous_im.continuousAt.comp ((hLc.continuousAt hn).sub continuousAt_const)
  have h1 : ∀ᶠ z in 𝓝 w, (L z - L w).im ∈ Set.Ioo (-Real.pi) Real.pi :=
    hc.eventually (isOpen_Ioo.mem_nhds (by simp [Real.pi_pos]))
  have h2 : L =ᶠ[𝓝 w] fun z => L w + Complex.log (F z / F w) := by
    filter_upwards [h1, hn] with z hz hzS
    rw [← hL hzS, ← hL hw, Function.comp, Function.comp, ← Complex.exp_sub, Complex.log_exp hz.1 hz.2.le]
    ring
  refine (DifferentiableAt.congr_of_eventuallyEq ?_ h2).differentiableWithinAt
  have h3 : DifferentiableAt ℂ (fun z => F z / F w) w := by
    simp only [div_eq_mul_inv]
    exact (hF.differentiableAt hn).mul_const _
  refine DifferentiableAt.const_add _ (DifferentiableAt.comp (g := Complex.log) w (Complex.differentiableAt_log ?_) h3)
  simp [div_self (h0 w hw)]

theorem block_induction {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (K : Matrix (α ⊕ β) (α ⊕ β) ℂ → Prop) (hmul : ∀ g h, K g → K h → K (g * h))
    (hd : ∀ d : α ⊕ β → ℂ, (∀ i, d i ≠ 0) → K (diagonal d))
    (hl : ∀ i j c, i ≠ j → K (transvection (Sum.inl i) (Sum.inl j) c))
    (hr : ∀ i j c, i ≠ j → K (transvection (Sum.inr i) (Sum.inr j) c))
    (hu : ∀ B, K (fromBlocks 1 B 0 1)) (A : Matrix α α ℂ) (B : Matrix α β ℂ) (D : Matrix β β ℂ)
    (hA : A.det ≠ 0) (hD : D.det ≠ 0) : K (fromBlocks A B 0 D) := by
  have h1 : K (fromBlocks A 0 0 1) := by
    refine diagonal_transvection_induction_of_det_ne_zero (fun A => K (fromBlocks A 0 0 1)) A hA
      (fun d hd' => ?_) (fun t => ?_) fun A B _ _ kA kB => ?_
    · rw [det_diagonal] at hd'
      rw [← diagonal_one, fromBlocks_diagonal]
      refine hd _ ?_
      rintro (i | i)
      · exact Finset.prod_ne_zero_iff.1 hd' i (Finset.mem_univ i)
      · simp
    · convert hl t.i t.j t.c t.hij using 1
      ext (a | a) (b | b) <;> simp [TransvectionStruct.toMatrix, transvection, one_apply, single_apply]
    · simpa [fromBlocks_multiply] using hmul _ _ kA kB
  have h2 : K (fromBlocks 1 0 0 D) := by
    refine diagonal_transvection_induction_of_det_ne_zero (fun D => K (fromBlocks 1 0 0 D)) D hD
      (fun d hd' => ?_) (fun t => ?_) fun A B _ _ kA kB => ?_
    · rw [det_diagonal] at hd'
      rw [← diagonal_one, fromBlocks_diagonal]
      refine hd _ ?_
      rintro (i | i)
      · simp
      · exact Finset.prod_ne_zero_iff.1 hd' i (Finset.mem_univ i)
    · convert hr t.i t.j t.c t.hij using 1
      ext (a | a) (b | b) <;> simp [TransvectionStruct.toMatrix, transvection, one_apply, single_apply]
    · simpa [fromBlocks_multiply] using hmul _ _ kA kB
  have h3 := hmul _ _ h2 (hmul _ _ (hu B) h1)
  simpa [fromBlocks_multiply] using h3

variable {N : ℕ}

def Par (p : ℕ) (g : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  g.det ≠ 0 ∧ ∀ a c : Fin N, (c : ℕ) < p → ¬ (a : ℕ) < p → g a c = 0

theorem Par.mul {p : ℕ} {g h : Matrix (Fin N) (Fin N) ℂ} (hg : Par p g) (hh : Par p h) : Par p (g * h) := by
  refine ⟨by rw [det_mul]; exact mul_ne_zero hg.1 hh.1, fun a c hc ha => ?_⟩
  rw [mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : (k : ℕ) < p
  · rw [hg.2 a k hk ha, zero_mul]
  · rw [hh.2 k c hc hk, mul_zero]

theorem par_of_upper {p : ℕ} {b : Matrix (Fin N) (Fin N) ℂ} (hd : b.det ≠ 0) (hb : ∀ a c, c < a → b a c = 0) :
    Par p b := ⟨hd, fun a c hc ha => hb a c (by rw [Fin.lt_def]; omega)⟩

theorem par_transvection {p : ℕ} {i j : Fin N} (hij : i ≠ j) (h : (j : ℕ) < p → (i : ℕ) < p) (t : ℂ) :
    Par p (transvection i j t) := by
  refine ⟨by rw [det_transvection_of_ne _ _ hij]; exact one_ne_zero, fun a c hc ha => ?_⟩
  have : a ≠ c := by rintro rfl; exact ha hc
  rw [transvection, Matrix.add_apply, one_apply_ne this, single_apply_of_ne, add_zero]
  rintro ⟨rfl, rfl⟩
  exact ha (h hc)

theorem transvection_upper {i j : Fin N} (hij : i < j) (t : ℂ) (a c : Fin N) (h : c < a) :
    transvection i j t a c = 0 := by
  rw [transvection, Matrix.add_apply, one_apply_ne h.ne', single_apply_of_ne, add_zero]
  rintro ⟨rfl, rfl⟩
  exact absurd h (not_lt.2 hij.le)

theorem transvection_factor {i j : Fin N} (hij : i ≠ j) {t : ℂ} (ht : t ≠ 0) :
    transvection i j t * transvection j i (-t⁻¹) * (1 + single j j (t⁻¹ - 1) + single i i (t - 1)) =
      transvection j i (-1 : ℂ) * transvection i j 1 * transvection j i (-1) * transvection i j (-t⁻¹) := by
  have hji := hij.symm
  simp only [transvection, mul_add, add_mul, Matrix.mul_one, Matrix.one_mul, single_mul_single_same,
    single_mul_single_of_ne _ _ _ _ hij, single_mul_single_of_ne _ _ _ _ hji, Matrix.zero_mul, add_zero]
  ext a c
  simp only [Matrix.add_apply, single_apply]
  split_ifs <;> simp_all <;> field_simp <;> ring

section Keeps

open scoped Matrix.Norms.Elementwise

variable {p : ℕ} {Ω : Set (Matrix (Fin N) (Fin N) ℂ)} {f : Matrix (Fin N) (Fin N) ℂ → ℂ}

theorem keeps_lower (hf : DifferentiableOn ℂ f Ω) (hΩ : ∀ m ∈ Ω, ∀ g, Par p g → m * g ∈ Ω)
    (hB : ∀ m ∈ Ω, ∀ b : Matrix (Fin N) (Fin N) ℂ, b.det ≠ 0 → (∀ a c, c < a → b a c = 0) → f (m * b) = f m)
    {i j : Fin N} (hji : j < i) (h : (j : ℕ) < p → (i : ℕ) < p) (t : ℂ) {m : Matrix (Fin N) (Fin N) ℂ} (hm : m ∈ Ω) :
    f (m * transvection i j t) = f m := by
  have hij : i ≠ j := hji.ne'
  have hL : ∀ s, Par p (transvection i j s) := par_transvection hij h
  have hU : ∀ s, Par p (transvection j i s) := par_transvection hij.symm fun h' => lt_trans hji h'
  have hdiff : ∀ m ∈ Ω, Differentiable ℂ fun s : ℂ => f (m * transvection i j s) := fun m hm => by
    have h1 : Differentiable ℂ fun s : ℂ => m * transvection i j s := by
      have : (fun s : ℂ => m * transvection i j s) = fun s => m + s • (m * single i j 1) := by
        funext s
        rw [transvection, mul_add, Matrix.mul_one, ← Matrix.mul_smul, smul_single, smul_eq_mul, mul_one]
      rw [this]
      fun_prop
    rw [← differentiableOn_univ]
    exact hf.comp h1.differentiableOn fun s _ => hΩ m hm _ (hL s)
  set w := transvection j i (-1 : ℂ) * transvection i j 1 * transvection j i (-1) with hw
  have hmw : m * w ∈ Ω := hΩ m hm _ (((hU _).mul (hL _)).mul (hU _))
  have key : ∀ s : ℂ, s ≠ 0 → f (m * transvection i j s) = f (m * w * transvection i j (-s⁻¹)) := fun s hs => by
    have e := transvection_factor hij hs
    have h1 := hΩ m hm _ (hL s)
    have h2 := hΩ _ h1 _ (hU (-s⁻¹))
    rw [Matrix.mul_assoc m w, hw, ← e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hB _ h2, hB _ h1 _ (hU _).1
      (transvection_upper hji _)]
    · have e' := congrArg det e
      simp only [det_mul, det_transvection_of_ne _ _ hij, det_transvection_of_ne _ _ hij.symm, one_mul] at e'
      rw [e']
      exact one_ne_zero
    · intro a c hca
      simp only [Matrix.add_apply, one_apply_ne hca.ne']
      rw [single_apply_of_ne, single_apply_of_ne, add_zero, add_zero] <;>
      · rintro ⟨h1, h2⟩
        exact hca.ne (h2.symm.trans h1)
  have hlim : Tendsto (fun s : ℂ => f (m * transvection i j s)) (cocompact ℂ)
      (𝓝 (f (m * w * transvection i j (-0)))) := by
    have h1 : Tendsto (fun s : ℂ => -s⁻¹) (cocompact ℂ) (𝓝 (-0)) := by
      rw [← Metric.cobounded_eq_cocompact]
      exact tendsto_inv₀_cobounded.neg
    refine (((hdiff _ hmw).continuous.tendsto _).comp h1).congr' ?_
    filter_upwards [(isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact] with s hs
    exact (key s hs).symm
  have h1 := (hdiff m hm).apply_eq_of_tendsto_cocompact t hlim
  have h2 := (hdiff m hm).apply_eq_of_tendsto_cocompact 0 hlim
  rw [h1, ← h2, transvection_zero, Matrix.mul_one]

theorem keeps_par (hf : DifferentiableOn ℂ f Ω) (hΩ : ∀ m ∈ Ω, ∀ g, Par p g → m * g ∈ Ω)
    (hB : ∀ m ∈ Ω, ∀ b : Matrix (Fin N) (Fin N) ℂ, b.det ≠ 0 → (∀ a c, c < a → b a c = 0) → f (m * b) = f m)
    {g : Matrix (Fin N) (Fin N) ℂ} (hg : Par p g) : ∀ m ∈ Ω, f (m * g) = f m := by
  let σ := Equiv.sumCompl fun a : Fin N => (a : ℕ) < p
  let K : Matrix (Fin N) (Fin N) ℂ → Prop := fun g => Par p g ∧ ∀ m ∈ Ω, f (m * g) = f m
  have Kup : ∀ b : Matrix (Fin N) (Fin N) ℂ, b.det ≠ 0 → (∀ a c, c < a → b a c = 0) → K b := fun b h1 h2 =>
    ⟨par_of_upper h1 h2, fun m hm => hB m hm b h1 h2⟩
  have Ktr : ∀ (i j : Fin N) (t : ℂ), i ≠ j → ((j : ℕ) < p → (i : ℕ) < p) → K (transvection i j t) :=
    fun i j t hij h => by
      rcases lt_or_gt_of_ne hij with h' | h'
      · exact Kup _ (par_transvection hij h t).1 (transvection_upper h' t)
      · exact ⟨par_transvection hij h t, fun m hm => keeps_lower hf hΩ hB h' h t hm⟩
  have htr : ∀ i j t, (transvection i j (t : ℂ)).submatrix σ.symm σ.symm = transvection (σ i) (σ j) t := by
    intro i j t
    ext a c
    simp [transvection, one_apply, single_apply, Equiv.eq_symm_apply]
  have h21 : (g.submatrix σ σ).toBlocks₂₁ = 0 := by
    ext a c
    exact hg.2 _ _ c.2 a.2
  have hblk : g.submatrix σ σ = fromBlocks (g.submatrix σ σ).toBlocks₁₁ (g.submatrix σ σ).toBlocks₁₂ 0
      (g.submatrix σ σ).toBlocks₂₂ := by
    rw [← h21, fromBlocks_toBlocks]
  have hdet := hg.1
  rw [← det_submatrix_equiv_self σ, hblk, det_fromBlocks_zero₂₁] at hdet
  have key := block_induction (fun M => K (M.submatrix σ.symm σ.symm)) (fun g h kg kh => ?_) (fun d hd => ?_)
    (fun i j c hij => ?_) (fun i j c hij => ?_) (fun B => ?_) _ (g.submatrix σ σ).toBlocks₁₂ _
    (left_ne_zero_of_mul hdet) (right_ne_zero_of_mul hdet)
  · rw [← hblk, submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id] at key
    exact key.2
  · rw [← submatrix_mul_equiv g h σ.symm σ.symm σ.symm]
    exact ⟨kg.1.mul kh.1, fun m hm => by rw [← Matrix.mul_assoc, kh.2 _ (hΩ m hm _ kg.1), kg.2 m hm]⟩
  · refine Kup _ ?_ fun a c hca => ?_
    · rw [det_submatrix_equiv_self, det_diagonal]
      exact Finset.prod_ne_zero_iff.2 fun i _ => hd i
    · exact diagonal_apply_ne _ fun h => hca.ne' (σ.symm.injective h)
  · rw [htr]
    exact Ktr _ _ _ (fun h => hij (Sum.inl_injective (σ.injective h))) fun _ => i.2
  · rw [htr]
    exact Ktr _ _ _ (fun h => hij (Sum.inr_injective (σ.injective h))) fun h => absurd h j.2
  · refine Kup _ ?_ fun a c hca => ?_
    · rw [det_submatrix_equiv_self, det_fromBlocks_zero₂₁]
      simp
    · obtain ⟨a, rfl⟩ := σ.surjective a
      obtain ⟨c, rfl⟩ := σ.surjective c
      rw [submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      rcases a with a | a <;> rcases c with c | c
      · exact one_apply_ne fun h => hca.ne' (by rw [h])
      · exact absurd (lt_trans (show ((c : Fin N) : ℕ) < (a : Fin N) from hca) a.2) c.2
      · rfl
      · exact one_apply_ne fun h => hca.ne' (by rw [h])

end Keeps

section Ring

variable {A : Type} [Ring A] {e y m b m' : A}

theorem comm_inv (he : e * e = e) (h1 : (e * y * e + (1 - e)) * m = 1) (h2 : m * (e * y * e + (1 - e)) = 1) :
    e * m = m * e := by
  have h : (e * y * e + (1 - e)) * e = e * (e * y * e + (1 - e)) := by
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, mul_assoc, he]
    rw [← mul_assoc e e, he]
  calc e * m = m * ((e * y * e + (1 - e)) * e) * m := by rw [← mul_assoc m, h2, one_mul]
    _ = m * e := by rw [h, mul_assoc, mul_assoc, h1, mul_one]

theorem proj_mul_inv (he : e * e = e) (h1 : (e * y * e + (1 - e)) * m = 1) : e * y * e * m = e := by
  have h : e * (e * y * e + (1 - e)) = e * y * e := by
    simp only [mul_add, mul_sub, mul_one, he, ← mul_assoc, sub_self, add_zero]
  rw [← h, mul_assoc, h1, mul_one]

theorem graph_eq (he : e * e = e) (h1 : (e * y * e + (1 - e)) * m = 1) (h2 : m * (e * y * e + (1 - e)) = 1) :
    (1 + (1 - e) * ((1 - e) * y * m * e) * e) * e = y * (e * m) := by
  have h3 := proj_mul_inv he h1
  have h4 := comm_inv he h1 h2
  have h5 : (1 - e) * (1 - e) = 1 - e := by simp only [mul_sub, sub_mul, one_mul, mul_one, he, sub_self, sub_zero]
  have h6 : e * y * m * e = e := by rw [mul_assoc, ← h4, ← mul_assoc, h3]
  rw [h4, add_mul, one_mul]
  simp only [← mul_assoc, h5]
  rw [mul_assoc _ e e, he, mul_assoc _ e e, he]
  simp only [sub_mul, one_mul, h6]
  abel

theorem graph_inv (he : e * e = e) (h1 : (e * y * e + (1 - e)) * m = 1) (h2 : m * (e * y * e + (1 - e)) = 1)
    (h1' : (e * (y * b) * e + (1 - e)) * m' = 1) (h2' : m' * (e * (y * b) * e + (1 - e)) = 1)
    (hb : (1 - e) * b * e = 0) : (1 - e) * (y * b) * m' * e = (1 - e) * y * m * e := by
  have hb' : b * e = e * (b * e) := by
    rw [sub_mul, sub_mul, one_mul, sub_eq_zero] at hb
    rw [← mul_assoc, ← hb]
  have h3 := proj_mul_inv he h1'
  have h4 := comm_inv he h1' h2'
  have h : (e * y * e + (1 - e)) * e = e * y * e := by
    simp only [add_mul, sub_mul, one_mul, mul_assoc, he, sub_self, add_zero]
  have h5 : b * (m' * e) = m * e := by
    calc b * (m' * e) = m * ((e * y * e + (1 - e)) * e) * (b * e) * m' := by
          rw [← mul_assoc m, h2, one_mul, ← hb', ← h4, mul_assoc]
      _ = m * (e * (y * b) * e * m') := by
          rw [h, mul_assoc m, mul_assoc _ e (b * e), ← hb']
          simp only [mul_assoc]
      _ = m * e := by rw [h3]
  simp only [mul_assoc, h5]

end Ring

def pr (N p : ℕ) : Matrix (Fin N) (Fin N) ℂ := diagonal fun a => if (a : ℕ) < p then 1 else 0

theorem pr_mul_pr (p : ℕ) : pr N p * pr N p = pr N p := by
  rw [pr, diagonal_mul_diagonal]
  congr 1
  funext a
  split_ifs <;> simp

theorem one_sub_pr (p : ℕ) : 1 - pr N p = diagonal fun a : Fin N => if (a : ℕ) < p then 0 else 1 := by
  rw [pr, ← diagonal_one, diagonal_sub]
  congr 1
  funext a
  split_ifs <;> simp

theorem cut_apply (p : ℕ) (g : Matrix (Fin N) (Fin N) ℂ) (a c : Fin N) :
    ((1 - pr N p) * g * pr N p) a c = if (c : ℕ) < p ∧ ¬ (a : ℕ) < p then g a c else 0 := by
  rw [one_sub_pr, pr, mul_diagonal, diagonal_mul]
  by_cases ha : (a : ℕ) < p <;> by_cases hc : (c : ℕ) < p <;> simp [ha, hc]

theorem par_iff {p : ℕ} {g : Matrix (Fin N) (Fin N) ℂ} :
    Par p g ↔ g.det ≠ 0 ∧ (1 - pr N p) * g * pr N p = 0 := by
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h a c hc ha => ?_⟩
  · ext a c
    rw [cut_apply]
    split_ifs with h'
    · exact h a c h'.1 h'.2
    · rfl
  · have := congrFun (congrFun h a) c
    rwa [cut_apply, if_pos ⟨hc, ha⟩] at this

theorem det_one_add_cut (p : ℕ) (W : Matrix (Fin N) (Fin N) ℂ) : (1 + (1 - pr N p) * W * pr N p).det ≠ 0 := by
  have h : pr N p * (1 - pr N p) = 0 := by rw [mul_sub, pr_mul_pr, Matrix.mul_one, sub_self]
  have h1 : (1 - pr N p) * W * pr N p * ((1 - pr N p) * W * pr N p) = 0 := by
    rw [Matrix.mul_assoc _ (pr N p), ← Matrix.mul_assoc (pr N p), ← Matrix.mul_assoc (pr N p), h]
    simp
  have h2 : (1 + (1 - pr N p) * W * pr N p) * (1 - (1 - pr N p) * W * pr N p) = 1 := by
    rw [add_mul, mul_sub ((1 - pr N p) * W * pr N p), h1]
    simp
  exact (isUnit_det_of_right_inverse h2).ne_zero

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (X : Data E N)

def Good (τ : X.Ψ) (m : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  m.det ≠ 0 ∧ ∀ v : Fin N → ℂ, v ≠ 0 → (∀ a : Fin N, ¬ (a : ℕ) < X.p0 → v a = 0) →
    0 < (hermC τ.1 X.Gm (m *ᵥ v) (m *ᵥ v)).re

theorem mulVec_eq_sum_colP (x : Frame X.Ψ N) (τ : X.Ψ) (v : Fin N → ℂ)
    (hv : ∀ a : Fin N, ¬ (a : ℕ) < X.p0 → v a = 0) :
    mat x τ *ᵥ v = ∑ a : Fin X.p0, v (Fin.castLE X.p0_le a) • X.colP x τ a := by
  rw [Data.mulVec_eq_sum_col]
  symm
  refine Finset.sum_of_injOn (Fin.castLE X.p0_le) (Fin.castLE_injective _).injOn (fun _ _ => Finset.mem_univ _)
    (fun a _ ha => ?_) fun _ _ => rfl
  rw [hv a, zero_smul]
  intro h
  exact ha ⟨⟨a, h⟩, by simp, rfl⟩

theorem mem_dom_iff_good {x : Frame X.Ψ N} : x ∈ X.dom ↔ ∀ τ, Good X τ (mat x τ) := by
  refine ⟨fun hx τ => ⟨(hx τ).1, fun v hv0 hv => ?_⟩, fun h =>
    ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.mem_dom_of_gramPos X fun τ => ⟨(h τ).1, ?_⟩⟩
  · rw [mulVec_eq_sum_colP X x τ v hv, ReciprocityTheory.ChartRestriction.G.FD.hermC_quad]
    refine ReciprocityTheory.ChartRestriction.G.FD.quad_re_pos (X.gramPos_posDef hx τ) fun h0 => hv0 (funext fun a => ?_)
    by_cases ha : (a : ℕ) < X.p0
    · exact congrFun h0 ⟨a, ha⟩
    · exact hv a ha
  · refine PosDef.of_dotProduct_mulVec_pos (X.gramPos_isHermitian x τ) fun c hc => ?_
    let v : Fin N → ℂ := fun a => if ha : (a : ℕ) < X.p0 then star (c ⟨a, ha⟩) else 0
    have hv : ∀ a : Fin N, ¬ (a : ℕ) < X.p0 → v a = 0 := fun a ha => dif_neg ha
    have hvc : ∀ a : Fin X.p0, v (Fin.castLE X.p0_le a) = star (c a) := fun a => dif_pos a.2
    have hv0 : v ≠ 0 := fun h0 => hc (funext fun a => by simpa [h0] using (hvc a).symm)
    have e : star c ⬝ᵥ X.gramPos x τ *ᵥ c = hermC τ.1 X.Gm (mat x τ *ᵥ v) (mat x τ *ᵥ v) := by
      rw [mulVec_eq_sum_colP X x τ v hv, ReciprocityTheory.ChartRestriction.G.FD.hermC_quad]
      simp [hvc, dotProduct, mulVec, Finset.mul_sum, mul_assoc, Data.gramPos_apply]
    rw [e, Complex.pos_iff]
    exact ⟨(h τ).2 v hv0 hv, (Complex.conj_eq_iff_im.1 (FD.hermC_conj τ.1 X.Gm_herm _ _)).symm⟩

theorem Good.mul_par {τ : X.Ψ} {m g : Matrix (Fin N) (Fin N) ℂ} (hm : Good X τ m) (hg : Par X.p0 g) :
    Good X τ (m * g) := by
  refine ⟨by rw [det_mul]; exact mul_ne_zero hm.1 hg.1, fun v hv0 hv => ?_⟩
  rw [← mulVec_mulVec]
  refine hm.2 _ (fun h => hg.1 (exists_mulVec_eq_zero_iff.1 ⟨v, hv0, h⟩)) fun a ha => ?_
  rw [mulVec, dotProduct]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hc : (c : ℕ) < X.p0
  · simp [hg.2 a c hc ha]
  · simp [hv c hc]

variable {X}

theorem quad_eq {τ : X.Ψ} {P : Matrix (Fin N) (Fin N) ℂ}
    (hP : FD.gram τ.1 X.Gm P = diagonal fun a : Fin N => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) (c : Fin N → ℂ) :
    (hermC τ.1 X.Gm (P *ᵥ c) (P *ᵥ c)).re = ∑ i : Fin N, sgn X.p0 i * Complex.normSq (c i) := by
  have hPij : ∀ i j, hermC τ.1 X.Gm (FD.col P i) (FD.col P j) = if i = j then ((sgn X.p0 i : ℝ) : ℂ) else 0 := by
    intro i j
    have := congrFun (congrFun hP i) j
    simpa only [FD.gram, of_apply, diagonal_apply] using this
  rw [Data.mulVec_eq_sum_col, ReciprocityTheory.ChartRestriction.G.FD.hermC_quad, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [hPij]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [mul_right_comm, Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re, mul_comm]

theorem quad_cut {τ : X.Ψ} {P : Matrix (Fin N) (Fin N) ℂ}
    (hP : FD.gram τ.1 X.Gm P = diagonal fun a : Fin N => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) (W : Matrix (Fin N) (Fin N) ℂ)
    (t : ℝ) {v : Fin N → ℂ} (hv : ∀ a : Fin N, ¬ (a : ℕ) < X.p0 → v a = 0) :
    (hermC τ.1 X.Gm ((P * (1 + (1 - pr N X.p0) * (t • W) * pr N X.p0)) *ᵥ v)
      ((P * (1 + (1 - pr N X.p0) * (t • W) * pr N X.p0)) *ᵥ v)).re =
      ∑ i, Complex.normSq (v i) - t ^ 2 * ∑ i, Complex.normSq ((((1 - pr N X.p0) * W * pr N X.p0) *ᵥ v) i) := by
  rw [← mulVec_mulVec, quad_eq hP, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, add_mulVec, one_mulVec, smul_mulVec, Pi.add_apply, Pi.smul_apply]
  by_cases hi : (i : ℕ) < X.p0
  · have : (((1 - pr N X.p0) * W * pr N X.p0) *ᵥ v) i = 0 := by
      rw [mulVec, dotProduct]
      exact Finset.sum_eq_zero fun c _ => by simp [cut_apply, hi]
    simp [this, sgn, hi]
  · simp [hv i hi, sgn, hi, sq]

theorem good_smul {τ : X.Ψ} {P : Matrix (Fin N) (Fin N) ℂ}
    (hP : FD.gram τ.1 X.Gm P = diagonal fun a : Fin N => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) {W : Matrix (Fin N) (Fin N) ℂ}
    (h : Good X τ (P * (1 + (1 - pr N X.p0) * W * pr N X.p0))) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    Good X τ (P * (1 + (1 - pr N X.p0) * (t • W) * pr N X.p0)) := by
  refine ⟨?_, fun v hv0 hv => ?_⟩
  · have := h.1
    rw [det_mul] at this ⊢
    exact mul_ne_zero (left_ne_zero_of_mul this) (det_one_add_cut _ _)
  · have h2 := h.2 v hv0 hv
    have h3 := quad_cut hP W 1 hv
    rw [one_smul] at h3
    rw [h3] at h2
    rw [quad_cut hP W t hv]
    have h4 : 0 ≤ ∑ i, Complex.normSq ((((1 - pr N X.p0) * W * pr N X.p0) *ᵥ v) i) :=
      Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
    have h5 : t ^ 2 ≤ 1 := by nlinarith
    nlinarith

theorem det_block_ne_zero {τ : X.Ψ} {P : Matrix (Fin N) (Fin N) ℂ}
    (hP : FD.gram τ.1 X.Gm P = diagonal fun a : Fin N => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) {y : Matrix (Fin N) (Fin N) ℂ}
    (h : Good X τ (P * y)) : (pr N X.p0 * y * pr N X.p0 + (1 - pr N X.p0)).det ≠ 0 := by
  intro hd
  obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_iff.2 hd
  rw [add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, one_sub_pr] at hv
  have h1 : ∀ a : Fin N, ¬ (a : ℕ) < X.p0 → v a = 0 := fun a ha => by
    have := congrFun hv a
    rw [Pi.add_apply, mulVec_diagonal, pr, mulVec_diagonal] at this
    simpa [ha] using this
  have h2 : pr N X.p0 *ᵥ v = v := by
    funext a
    by_cases ha : (a : ℕ) < X.p0
    · simp [pr, mulVec_diagonal, ha]
    · simp [pr, mulVec_diagonal, ha, h1 a ha]
  rw [h2] at hv
  have h3 : ∀ a : Fin N, (a : ℕ) < X.p0 → (y *ᵥ v) a = 0 := fun a ha => by
    have := congrFun hv a
    rw [Pi.add_apply, mulVec_diagonal, pr, mulVec_diagonal] at this
    simpa [ha] using this
  have h4 := h.2 v hv0 h1
  rw [← mulVec_mulVec, quad_eq hP] at h4
  refine absurd h4 (not_lt.2 (Finset.sum_nonpos fun i _ => ?_))
  by_cases hi : (i : ℕ) < X.p0
  · simp [h3 i hi]
  · simp [sgn, hi, Complex.normSq_nonneg]

def graph (p : ℕ) (y : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (1 - pr N p) * y * (pr N p * y * pr N p + (1 - pr N p))⁻¹ * pr N p

theorem exists_par_graph {p : ℕ} {y : Matrix (Fin N) (Fin N) ℂ} (hy : y.det ≠ 0)
    (h : (pr N p * y * pr N p + (1 - pr N p)).det ≠ 0) :
    ∃ g, Par p g ∧ y * g = 1 + (1 - pr N p) * graph p y * pr N p := by
  have h1 := mul_nonsing_inv _ h.isUnit
  have h2 := nonsing_inv_mul _ h.isUnit
  refine ⟨y⁻¹ * (1 + (1 - pr N p) * graph p y * pr N p), par_iff.2 ⟨?_, ?_⟩, ?_⟩
  · rw [det_mul, det_nonsing_inv, Ring.inverse_eq_inv']
    exact mul_ne_zero (inv_ne_zero hy) (det_one_add_cut _ _)
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, graph, graph_eq (pr_mul_pr p) h1 h2, ← Matrix.mul_assoc y⁻¹,
      nonsing_inv_mul _ hy.isUnit, Matrix.one_mul, ← Matrix.mul_assoc, sub_mul, pr_mul_pr]
    simp
  · rw [← Matrix.mul_assoc, mul_nonsing_inv _ hy.isUnit, Matrix.one_mul]

theorem graph_mul_par {p : ℕ} {y b : Matrix (Fin N) (Fin N) ℂ} (hb : Par p b)
    (h : (pr N p * y * pr N p + (1 - pr N p)).det ≠ 0) (h' : (pr N p * (y * b) * pr N p + (1 - pr N p)).det ≠ 0) :
    graph p (y * b) = graph p y :=
  graph_inv (pr_mul_pr p) (mul_nonsing_inv _ h.isUnit) (nonsing_inv_mul _ h.isUnit) (mul_nonsing_inv _ h'.isUnit)
    (nonsing_inv_mul _ h'.isUnit) (par_iff.1 hb).2

section Hol

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {U : Set V} {M M' : V → Matrix (Fin N) (Fin N) ℂ}

def HolOn (M : V → Matrix (Fin N) (Fin N) ℂ) (U : Set V) : Prop := ∀ i j, DifferentiableOn ℂ (fun x => M x i j) U

theorem HolOn.const (A : Matrix (Fin N) (Fin N) ℂ) : HolOn (fun _ => A) U := fun _ _ => differentiableOn_const _

theorem HolOn.add (h : HolOn M U) (h' : HolOn M' U) : HolOn (fun x => M x + M' x) U := fun i j => (h i j).add (h' i j)

theorem HolOn.mul (h : HolOn M U) (h' : HolOn M' U) : HolOn (fun x => M x * M' x) U := fun i j => by
  simp only [mul_apply]
  exact DifferentiableOn.fun_sum fun k _ => (h i k).mul (h' k j)

theorem HolOn.inv (hM : HolOn M U) (hu : ∀ x ∈ U, (M x).det ≠ 0) : HolOn (fun x => (M x)⁻¹) U := fun i j => by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, adjugate_apply]
  refine ((ReciprocityTheory.MultiplicativeHeights.differentiableOn_det_of hM).inv hu).mul
    (ReciprocityTheory.MultiplicativeHeights.differentiableOn_det_of
      (F := fun k l x => (M x).updateRow j (Pi.single i 1) k l) fun k l => ?_)
  simp only [updateRow_apply]
  split_ifs
  · exact differentiableOn_const _
  · exact hM k l

end Hol

theorem holOn_mat (τ : X.Ψ) (U : Set (Frame X.Ψ N)) : HolOn (fun x : Frame X.Ψ N => mat x τ) U := fun i j => by
  have : Differentiable ℂ fun x : Frame X.Ψ N => x τ i j := by fun_prop
  exact this.differentiableOn

theorem rmul_mem {x g : Frame X.Ψ N} (hx : x ∈ X.dom) (hg : ∀ τ, Par X.p0 (mat g τ)) : rmul x g ∈ X.dom :=
  (mem_dom_iff_good X).2 fun τ => ((mem_dom_iff_good X).1 hx τ).mul_par X (hg τ)

def ofMat (m : X.Ψ → Matrix (Fin N) (Fin N) ℂ) : Frame X.Ψ N := fun τ i j => m τ i j

theorem mat_ofMat (m : X.Ψ → Matrix (Fin N) (Fin N) ℂ) (τ : X.Ψ) : mat (ofMat m) τ = m τ := rfl

theorem mat_rmul (x b : Frame X.Ψ N) (τ : X.Ψ) : mat (rmul x b) τ = mat x τ * mat b τ := rfl

theorem frame_ext {x y : Frame X.Ψ N} (h : ∀ τ, mat x τ = mat y τ) : x = y := funext h

open scoped Matrix.Norms.Elementwise in
theorem update_par {R : Frame X.Ψ N → ℂ} (hR : DifferentiableOn ℂ R X.dom)
    (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ N, R (rmul x b) = R x) [DecidableEq X.Ψ] {x : Frame X.Ψ N} (hx : x ∈ X.dom)
    (τ : X.Ψ) {g : Matrix (Fin N) (Fin N) ℂ} (hg : Par X.p0 g) :
    R (ofMat fun ρ => if ρ = τ then mat x τ * g else mat x ρ) = R x := by
  have hgood : ∀ m : Matrix (Fin N) (Fin N) ℂ, Good X τ m →
      (ofMat fun ρ => if ρ = τ then m else mat x ρ) ∈ X.dom := fun m hm =>
    (mem_dom_iff_good X).2 fun ρ => by
      rw [mat_ofMat]
      split_ifs with h
      · rwa [h]
      · exact (mem_dom_iff_good X).1 hx ρ
  have hd : Differentiable ℂ fun m : Matrix (Fin N) (Fin N) ℂ =>
      (ofMat fun ρ => if ρ = τ then m else mat x ρ) := by
    refine differentiable_pi.2 fun ρ => ?_
    change Differentiable ℂ fun m : Matrix (Fin N) (Fin N) ℂ => if ρ = τ then m else mat x ρ
    by_cases h : ρ = τ
    · simp only [if_pos h]
      exact differentiable_id
    · simp only [if_neg h]
      exact differentiable_const _
  have key := keeps_par (p := X.p0) (Ω := {m | Good X τ m})
    (f := fun m => R (ofMat fun ρ => if ρ = τ then m else mat x ρ))
    (hR.comp hd.differentiableOn fun m hm => hgood m hm)
    (fun m hm g hg => Good.mul_par X hm hg) (fun m hm b hd hb => ?_) hg _ ((mem_dom_iff_good X).1 hx τ)
  · refine key.trans (congrArg R (frame_ext fun ρ => ?_))
    rw [mat_ofMat]
    split_ifs with h
    · rw [h]
    · rfl
  · rw [← hB _ (hgood m hm) (ofMat fun ρ => if ρ = τ then b else 1) fun ρ => ?_]
    · refine congrArg R (frame_ext fun ρ => ?_)
      simp only [mat_rmul, mat_ofMat]
      split_ifs <;> simp
    · rw [mat_ofMat]
      by_cases h : ρ = τ
      · simp only [ofMat, if_pos h]
        exact ⟨hd, hb⟩
      · simp only [ofMat, if_neg h]
        exact ⟨by simp, fun a c hca => one_apply_ne hca.ne'⟩

theorem rmul_par {R : Frame X.Ψ N → ℂ} (hR : DifferentiableOn ℂ R X.dom)
    (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ N, R (rmul x b) = R x) {x g : Frame X.Ψ N} (hx : x ∈ X.dom)
    (hg : ∀ τ, Par X.p0 (mat g τ)) : R (rmul x g) = R x := by
  classical
  have key : ∀ s : Finset X.Ψ, R (ofMat fun ρ => if ρ ∈ s then mat x ρ * mat g ρ else mat x ρ) = R x := fun s => by
    induction s using Finset.induction_on with
    | empty => exact congrArg R (frame_ext fun ρ => by simp [mat_ofMat])
    | insert τ s hτ ih =>
      have hs : (ofMat fun ρ => if ρ ∈ s then mat x ρ * mat g ρ else mat x ρ) ∈ X.dom :=
        (mem_dom_iff_good X).2 fun ρ => by
          rw [mat_ofMat]
          split_ifs with h
          · exact (mem_dom_iff_good X).1 (rmul_mem hx hg) ρ
          · exact (mem_dom_iff_good X).1 hx ρ
      rw [← ih, ← update_par hR hB hs τ (hg τ)]
      refine congrArg R (frame_ext fun ρ => ?_)
      simp only [mat_ofMat]
      by_cases h : ρ = τ
      · subst h
        simp [hτ]
      · simp [h]
  rw [← key Finset.univ]
  exact congrArg R (frame_ext fun ρ => by simp [mat_ofMat, mat_rmul])

theorem exists_invariant_log : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N)
    (R : Frame X.Ψ N → ℂ), DifferentiableOn ℂ R X.dom → (∀ x ∈ X.dom, R x ≠ 0) →
    (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ N, R (rmul x b) = R x) → ∃ L : Frame X.Ψ N → ℂ, DifferentiableOn ℂ L X.dom ∧
      (∀ x ∈ X.dom, Complex.exp (L x) = R x) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ N, L (rmul x b) = L x) := by
  intro E _ _ _ N X R hR h0 hB
  rcases X.dom.eq_empty_or_nonempty with he | ⟨x₀, hx₀⟩
  · exact ⟨0, differentiableOn_const _, by simp [he], by simp⟩
  choose P hPd hP using X.signature
  let n : Frame X.Ψ N → Frame X.Ψ N := fun W τ =>
    (P τ * (1 + (1 - pr N X.p0) * mat W τ * pr N X.p0) : Matrix (Fin N) (Fin N) ℂ)
  let Z : Frame X.Ψ N → Frame X.Ψ N := fun x τ => graph X.p0 ((P τ)⁻¹ * mat x τ)
  have hn : Differentiable ℂ n := by
    rw [← differentiableOn_univ]
    exact differentiableOn_pi.2 fun τ => differentiableOn_pi.2 fun i => differentiableOn_pi.2 fun j =>
      (HolOn.const _).mul ((HolOn.const _).add (((HolOn.const _).mul (holOn_mat τ _)).mul (HolOn.const _))) i j
  have hPP : ∀ τ (m : Matrix (Fin N) (Fin N) ℂ), P τ * ((P τ)⁻¹ * m) = m := fun τ m => by
    rw [← Matrix.mul_assoc, mul_nonsing_inv _ (hPd τ).isUnit, Matrix.one_mul]
  have hblk : ∀ x ∈ X.dom, ∀ τ,
      (pr N X.p0 * ((P τ)⁻¹ * mat x τ) * pr N X.p0 + (1 - pr N X.p0)).det ≠ 0 := fun x hx τ =>
    det_block_ne_zero (hP τ) (by rw [hPP]; exact (mem_dom_iff_good X).1 hx τ)
  have hZ : DifferentiableOn ℂ Z X.dom :=
    differentiableOn_pi.2 fun τ => differentiableOn_pi.2 fun i => differentiableOn_pi.2 fun j =>
      (((HolOn.const _).mul ((HolOn.const _).mul (holOn_mat τ _))).mul
        (((((HolOn.const _).mul ((HolOn.const _).mul (holOn_mat τ _))).mul (HolOn.const _)).add
          (HolOn.const _)).inv fun x hx => hblk x hx τ)).mul (HolOn.const _) i j
  have hnZ : ∀ x ∈ X.dom, ∃ g : Frame X.Ψ N, (∀ τ, Par X.p0 (mat g τ)) ∧ n (Z x) = rmul x g := fun x hx => by
    have := fun τ => exists_par_graph (p := X.p0) (y := (P τ)⁻¹ * mat x τ) (by
      rw [det_mul, det_nonsing_inv, Ring.inverse_eq_inv']
      exact mul_ne_zero (inv_ne_zero (hPd τ)) (hx τ).1) (hblk x hx τ)
    choose g hg hg' using this
    refine ⟨g, hg, funext fun τ => ?_⟩
    change P τ * (1 + (1 - pr N X.p0) * graph X.p0 ((P τ)⁻¹ * mat x τ) * pr N X.p0) = mat x τ * g τ
    rw [← hg', Matrix.mul_assoc, hPP]
  have hZS : ∀ x ∈ X.dom, Z x ∈ n ⁻¹' X.dom := fun x hx => by
    obtain ⟨g, hg, e⟩ := hnZ x hx
    rw [Set.mem_preimage, e]
    exact rmul_mem hx hg
  have hstar : StarConvex ℝ 0 (n ⁻¹' X.dom) := by
    rw [starConvex_zero_iff]
    intro W hW t h0 h1
    exact (mem_dom_iff_good X).2 fun τ => good_smul (hP τ) ((mem_dom_iff_good X).1 hW τ) h0 h1
  obtain ⟨L, hL, hLe⟩ := exists_log ((AR.Up.SchubertCoordinates.isOpen_dom X).preimage hn.continuous) hstar
    ⟨_, hZS x₀ hx₀⟩ (F := R ∘ n) (hR.comp hn.differentiableOn fun _ h => h) fun W hW => h0 _ hW
  refine ⟨L ∘ Z, hL.comp hZ hZS, fun x hx => ?_, fun x hx b hb => ?_⟩
  · obtain ⟨g, hg, e⟩ := hnZ x hx
    rw [Function.comp, hLe _ (hZS x hx), Function.comp, e, rmul_par hR hB hx hg]
  · have hb' : ∀ τ, Par X.p0 (mat b τ) := fun τ => par_of_upper (hb τ).1 (hb τ).2
    refine congrArg L (funext fun τ => ?_)
    have h1 := hblk _ (rmul_mem hx hb') τ
    change graph X.p0 ((P τ)⁻¹ * (mat x τ * mat b τ)) = graph X.p0 ((P τ)⁻¹ * mat x τ)
    change (pr N X.p0 * ((P τ)⁻¹ * (mat x τ * mat b τ)) * pr N X.p0 + (1 - pr N X.p0)).det ≠ 0 at h1
    rw [← Matrix.mul_assoc (P τ)⁻¹] at h1 ⊢
    exact graph_mul_par (hb' τ) (hblk x hx τ) h1

end GlobalTheory.FrameLog
