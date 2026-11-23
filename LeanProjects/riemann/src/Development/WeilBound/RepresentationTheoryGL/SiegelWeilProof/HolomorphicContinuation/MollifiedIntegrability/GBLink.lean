import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsGainBSt

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.WR.K.GB

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def hermL (n : ℕ) : (Fin n → Fin n → ℝ) →L[ℝ] Mc n :=
  LinearMap.toContinuousLinearMap
    { toFun := herm
      map_add' := fun x y => by
        ext i j; simp only [herm, Pi.add_apply, Matrix.add_apply]; push_cast; ring
      map_smul' := fun c x => by
        ext i j; simp only [herm, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, RingHom.id_apply]
        rw [Complex.real_smul]; push_cast; ring }

theorem hermL_apply (x : Fin n → Fin n → ℝ) : hermL n x = herm x := rfl

theorem vkl_re (k l a b : Fin n) :
    (vkl k l a b).re = (if a = k ∧ b = l then 1 / 2 else 0) + (if a = l ∧ b = k then 1 / 2 else 0) := by
  unfold vkl; split_ifs <;> simp

theorem vkl_im (k l a b : Fin n) :
    (vkl k l a b).im = (if a = k ∧ b = l then 1 / 2 else 0) + (if a = l ∧ b = k then -1 / 2 else 0) := by
  unfold vkl; split_ifs <;> simp

theorem herm_re_im_vkl (k l : Fin n) :
    herm (fun a b => (vkl k l a b).re) + Complex.I • herm (fun a b => (vkl k l a b).im) =
      Matrix.single l k (1 : ℂ) := by
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.single_apply]
  unfold herm
  dsimp only
  rw [vkl_re, vkl_re, vkl_im, vkl_im]
  have e1 : (if j = k ∧ i = l then (1 / 2 : ℝ) else 0) = 1 / 2 * (if i = l ∧ j = k then 1 else 0) := by
    split_ifs <;> first | (exfalso; tauto) | norm_num
  have e2 : (if j = l ∧ i = k then (1 / 2 : ℝ) else 0) = 1 / 2 * (if i = k ∧ j = l then 1 else 0) := by
    split_ifs <;> first | (exfalso; tauto) | norm_num
  have e3 : (if i = k ∧ j = l then (1 / 2 : ℝ) else 0) = 1 / 2 * (if i = k ∧ j = l then 1 else 0) := by
    split_ifs <;> first | (exfalso; tauto) | norm_num
  have e4 : (if i = l ∧ j = k then (1 / 2 : ℝ) else 0) = 1 / 2 * (if i = l ∧ j = k then 1 else 0) := by
    split_ifs <;> first | (exfalso; tauto) | norm_num
  have e5 : (if i = l ∧ j = k then (-1 / 2 : ℝ) else 0) = -1 / 2 * (if i = l ∧ j = k then 1 else 0) := by
    split_ifs <;> first | (exfalso; tauto) | norm_num
  have e6 : (if j = l ∧ i = k then (-1 / 2 : ℝ) else 0) = -1 / 2 * (if i = k ∧ j = l then 1 else 0) := by
    split_ifs <;> first | (exfalso; tauto) | norm_num
  have e7 : (if l = i ∧ k = j then (1 : ℂ) else 0) = (((if i = l ∧ j = k then (1 : ℝ) else 0) : ℝ) : ℂ) := by
    by_cases h : i = l ∧ j = k
    · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩]; simp
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩)]; simp
  rw [e1, e2, e3, e4, e5, e6, e7]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

variable {F G : Mc n → ℂ} {U : Set (Mc n)}

theorem dkl_comp_herm (k l : Fin n) (y : Fin n → Fin n → ℝ) (hd : DifferentiableAt ℂ G (herm y)) :
    Dkl k l (fun y => G (herm y)) y = cpart l k G (herm y) := by
  have hG : HasFDerivAt G ((fderiv ℂ G (herm y)).restrictScalars ℝ) (herm y) :=
    hd.hasFDerivAt.restrictScalars ℝ
  have hc : HasFDerivAt (fun y => G (herm y)) (((fderiv ℂ G (herm y)).restrictScalars ℝ).comp (hermL n)) y :=
    hG.comp y (hermL n).hasFDerivAt
  unfold Dkl dirC cpart
  rw [hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars', hermL_apply]
  rw [← herm_re_im_vkl k l, map_add, map_smul, smul_eq_mul]

theorem cpart_contDiffOn (i j : Fin n) (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) :
    ContDiffOn ℂ (⊤ : ℕ∞) (cpart i j F) U := by
  have h := hF.fderiv_of_isOpen hU (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by norm_cast)
  exact h.clm_apply contDiffOn_const

theorem differentiableAt_of_cdo (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) {b : Mc n} (hb : b ∈ U) :
    DifferentiableAt ℂ F b :=
  ((hF.contDiffAt (hU.mem_nhds hb)).differentiableAt (by norm_cast))

theorem foldr_herm (τ : Fin n → Fin n) (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) (hh : ∀ y, herm y ∈ U)
    (L : List (Fin n)) :
    L.foldr (fun k g => Dkl k (τ k) g) (fun y => F (herm y)) =
        (fun y => (L.foldr (fun k g => cpart (τ k) k g) F) (herm y)) ∧
      ContDiffOn ℂ (⊤ : ℕ∞) (L.foldr (fun k g => cpart (τ k) k g) F) U := by
  induction L with
  | nil => exact ⟨rfl, hF⟩
  | cons a L ih =>
    refine ⟨?_, cpart_contDiffOn _ _ hU ih.2⟩
    simp only [List.foldr_cons]
    rw [ih.1]
    funext y
    exact dkl_comp_herm a (τ a) y (differentiableAt_of_cdo hU ih.2 (hh y))

theorem deltaC_contDiffOn (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) :
    ContDiffOn ℂ (⊤ : ℕ∞) (DeltaC F) U := by
  have : DeltaC F = fun b => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      (List.finRange n).foldr (fun k g => cpart (σ k) k g) F b := by
    funext b; simp [DeltaC, Finset.sum_apply]
  rw [this]
  refine ContDiffOn.sum fun σ _ => ContDiffOn.const_smul _ ?_
  have key : ∀ L : List (Fin n), ContDiffOn ℂ (⊤ : ℕ∞) (L.foldr (fun k g => cpart (σ k) k g) F) U := by
    intro L; induction L with
    | nil => exact hF
    | cons a L ih => exact cpart_contDiffOn _ _ hU ih
  exact key _

theorem delta_herm (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) (hh : ∀ y, herm y ∈ U) :
    Delta (fun y => F (herm y)) = fun y => DeltaC F (herm y) := by
  funext y
  simp only [Delta, DeltaC, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [(foldr_herm σ hU hF hh _).1]

theorem iterate_herm (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) (hh : ∀ y, herm y ∈ U) (N : ℕ) :
    (Delta^[N] (fun y => F (herm y))) = (fun y => (DeltaC^[N] F) (herm y)) ∧
      ContDiffOn ℂ (⊤ : ℕ∞) (DeltaC^[N] F) U := by
  induction N with
  | zero => exact ⟨rfl, hF⟩
  | succ N ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih.1]
    exact ⟨delta_herm hU ih.2 hh, deltaC_contDiffOn hU ih.2⟩

theorem eqOn_cpart (i j : Fin n) (hU : IsOpen U) {H H' : Mc n → ℂ} (h : Set.EqOn H H' U) :
    Set.EqOn (cpart i j H) (cpart i j H') U := fun b hb => by
  have : H =ᶠ[nhds b] H' := Filter.eventuallyEq_of_mem (hU.mem_nhds hb) h
  simp only [cpart, this.fderiv_eq]

theorem eqOn_word (L : List (Fin n × Fin n)) (hU : IsOpen U) {H H' : Mc n → ℂ} (h : Set.EqOn H H' U) :
    Set.EqOn (word L H) (word L H') U := by
  induction L with
  | nil => exact h
  | cons a L ih => exact eqOn_cpart a.1 a.2 hU ih

theorem word_contDiffOn (L : List (Fin n × Fin n)) (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) :
    ContDiffOn ℂ (⊤ : ℕ∞) (word L F) U := by
  induction L with
  | nil => exact hF
  | cons a L ih => exact cpart_contDiffOn _ _ hU ih

theorem cpart_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → Mc n → ℂ) (i j : Fin n) (hU : IsOpen U)
    (hf : ∀ t, ContDiffOn ℂ (⊤ : ℕ∞) (f t) U) :
    Set.EqOn (cpart i j (fun x => ∑ t ∈ s, c t * f t x)) (fun x => ∑ t ∈ s, c t * cpart i j (f t) x) U := by
  intro b hb
  have hd : ∀ t ∈ s, DifferentiableAt ℂ (fun x => c t * f t x) b := fun t _ =>
    (differentiableAt_of_cdo hU (hf t) hb).const_mul (c t)
  simp only [cpart]
  have hs : HasFDerivAt (fun x => ∑ t ∈ s, c t * f t x) (∑ t ∈ s, fderiv ℂ (fun x => c t * f t x) b) b :=
    HasFDerivAt.fun_sum (fun t ht => (hd t ht).hasFDerivAt)
  rw [hs.fderiv, _root_.sum_apply]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 : HasFDerivAt (fun x => c t * f t x) (c t • fderiv ℂ (f t) b) b :=
    (differentiableAt_of_cdo hU (hf t) hb).hasFDerivAt.const_mul (c t)
  rw [h1.fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem word_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → Mc n → ℂ) (L : List (Fin n × Fin n))
    (hU : IsOpen U) (hf : ∀ t, ContDiffOn ℂ (⊤ : ℕ∞) (f t) U) :
    Set.EqOn (word L (fun x => ∑ t ∈ s, c t * f t x)) (fun x => ∑ t ∈ s, c t * word L (f t) x) U := by
  induction L with
  | nil => intro b _; rfl
  | cons a L ih =>
    intro b hb
    have h1 := eqOn_cpart a.1 a.2 hU ih hb
    simp only [word, List.foldr_cons] at h1 ⊢
    rw [h1]
    exact cpart_sum s c (fun t => word L (f t)) a.1 a.2 hU (fun t => word_contDiffOn L hU (hf t)) hb

theorem word_append (L₁ L₂ : List (Fin n × Fin n)) (H : Mc n → ℂ) :
    word (L₁ ++ L₂) H = word L₁ (word L₂ H) := by
  simp [word, List.foldr_append]

def blk (σ : Equiv.Perm (Fin n)) : List (Fin n × Fin n) := (List.finRange n).map fun k => (σ k, k)

theorem deltaC_eq_word (H : Mc n → ℂ) :
    DeltaC H = fun b => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * word (blk σ) H b := by
  funext b
  simp only [DeltaC, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, word, blk, List.foldr_map]

theorem flat_succ {N : ℕ} (τ : Fin (N + 1) → Equiv.Perm (Fin n)) :
    (List.finRange (N + 1)).flatMap (fun j => blk (τ j)) =
      blk (τ 0) ++ (List.finRange N).flatMap (fun j => blk (τ j.succ)) := by
  rw [List.finRange_succ, List.flatMap_cons, List.flatMap_map]

theorem deltaC_iter_word (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) (N : ℕ) :
    Set.EqOn (DeltaC^[N] F) (fun b => ∑ τ : Fin N → Equiv.Perm (Fin n),
      ((∏ j, (Equiv.Perm.sign (τ j) : ℤ) : ℤ) : ℂ) *
        word ((List.finRange N).flatMap fun j => blk (τ j)) F b) U := by
  induction N with
  | zero => intro b _; simp [word]
  | succ N ih =>
    intro b hb
    rw [Function.iterate_succ_apply', deltaC_eq_word]
    dsimp only
    have step : ∀ σ : Equiv.Perm (Fin n), word (blk σ) (DeltaC^[N] F) b =
        ∑ τ : Fin N → Equiv.Perm (Fin n), ((∏ j, (Equiv.Perm.sign (τ j) : ℤ) : ℤ) : ℂ) *
          word (blk σ ++ (List.finRange N).flatMap fun j => blk (τ j)) F b := by
      intro σ
      rw [eqOn_word (blk σ) hU ih hb]
      have hw := word_sum (Finset.univ : Finset (Fin N → Equiv.Perm (Fin n)))
        (fun τ => ((∏ j, (Equiv.Perm.sign (τ j) : ℤ) : ℤ) : ℂ))
        (fun τ => word ((List.finRange N).flatMap fun j => blk (τ j)) F) (blk σ) hU
        (fun τ => word_contDiffOn _ hU hF) hb
      rw [hw]
      simp only [word_append]
    simp only [step, Finset.mul_sum]
    rw [← (Fin.consEquiv fun _ => Equiv.Perm (Fin n)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
    simp only [Fin.consEquiv_apply, flat_succ, Fin.cons_zero, Fin.cons_succ, Fin.prod_univ_succ]
    push_cast
    ring

theorem link : Link := by
  intro n F U hU hF hh
  exact ⟨fun N y => by rw [(iterate_herm hU hF hh N).1],
    fun N b hb => (deltaC_iter_word hU hF N hb).trans (by simp only [blk])⟩

end PositivityTheory.Rg.Sw.WR.K.GB
