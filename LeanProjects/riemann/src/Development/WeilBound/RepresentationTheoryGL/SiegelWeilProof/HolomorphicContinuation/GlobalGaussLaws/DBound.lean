import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DetNeOfPosDef

noncomputable section

open Matrix Topology
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.Glob

def famPQ {m n : ℕ} (ε : Fin m → Bool) (t c : ℝ) (e : ℤ) (p q : ℕ) (y : GR n) (X : Fin n → ℝ) (z : ℂ)
    (u : Fin m → Fin n → ℂ) : ℂ :=
  jC e p q y X z * gC ε t c (ptZ y X z Complex.I) (ptZ y X z (-Complex.I)) u

namespace DBoundH

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

def EntD (S : Set ℂ) (f : ℂ → Matrix ι ι ℂ) : Prop := ∀ i j, DifferentiableOn ℂ (fun z => f z i j) S

theorem entD_const (S : Set ℂ) (A : Matrix ι ι ℂ) : EntD S (fun _ => A) := fun _ _ => differentiableOn_const _

theorem entD_add {S : Set ℂ} {f g : ℂ → Matrix ι ι ℂ} (hf : EntD S f) (hg : EntD S g) :
    EntD S (fun z => f z + g z) := fun i j => by
  simp only [Matrix.add_apply]
  exact (hf i j).fun_add (hg i j)

theorem entD_mul {S : Set ℂ} {f g : ℂ → Matrix ι ι ℂ} (hf : EntD S f) (hg : EntD S g) :
    EntD S (fun z => f z * g z) := fun i j => by
  simp only [Matrix.mul_apply]
  exact DifferentiableOn.fun_sum fun k _ => (hf i k).mul (hg k j)

theorem det_diff {S : Set ℂ} {f : ℂ → Matrix ι ι ℂ} (hf : EntD S f) :
    DifferentiableOn ℂ (fun z => (f z).det) S := by
  simp only [Matrix.det_apply]
  refine DifferentiableOn.fun_sum fun σ _ => ?_
  simp only [Units.smul_def, zsmul_eq_mul]
  exact (differentiableOn_const _).mul (DifferentiableOn.fun_finsetProd fun i _ => hf _ _)

theorem entD_adjugate {S : Set ℂ} {f : ℂ → Matrix ι ι ℂ} (hf : EntD S f) :
    EntD S (fun z => (f z).adjugate) := fun i j => by
  simp only [Matrix.adjugate_apply]
  refine det_diff (f := fun z => (f z).updateRow j (Pi.single i 1)) (fun a b => ?_)
  by_cases hab : a = j
  · subst hab; simp only [Matrix.updateRow_self]; exact differentiableOn_const _
  · simp only [Matrix.updateRow_ne hab]; exact hf a b

theorem entD_inv {S : Set ℂ} {f : ℂ → Matrix ι ι ℂ} (hf : EntD S f) (h0 : ∀ z ∈ S, (f z).det ≠ 0) :
    EntD S (fun z => (f z)⁻¹) := fun i j => by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact ((det_diff hf).inv h0).mul (entD_adjugate hf i j)

theorem trace_diff {S : Set ℂ} {f : ℂ → Matrix ι ι ℂ} (hf : EntD S f) :
    DifferentiableOn ℂ (fun z => (f z).trace) S := by
  simp only [Matrix.trace, Matrix.diag]
  exact DifferentiableOn.fun_sum fun i _ => hf i i

theorem entD_aC (X : Fin n → ℝ) (S : Set ℂ) : EntD S (aC X) := by
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · by_cases h : i = j
    · subst h
      simpa [aC] using (by fun_prop : Differentiable ℂ (fun z : ℂ => Complex.exp (z * (X i : ℂ)))).differentiableOn
    · simpa [aC, h] using differentiableOn_const (c := (0 : ℂ))
  · simpa [aC] using differentiableOn_const (c := (0 : ℂ))
  · simpa [aC] using differentiableOn_const (c := (0 : ℂ))
  · by_cases h : i = j
    · subst h
      simpa [aC] using (by fun_prop : Differentiable ℂ (fun z : ℂ => Complex.exp (-(z * (X i : ℂ))))).differentiableOn
    · simpa [aC, h] using differentiableOn_const (c := (0 : ℂ))

theorem entD_toBlocks₁₁ {S : Set ℂ} {f : ℂ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ}
    (hf : EntD S f) : EntD S (fun z => (f z).toBlocks₁₁) :=
  fun i j => hf (Sum.inl i) (Sum.inl j)

theorem entD_toBlocks₁₂ {S : Set ℂ} {f : ℂ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ}
    (hf : EntD S f) : EntD S (fun z => (f z).toBlocks₁₂) :=
  fun i j => hf (Sum.inl i) (Sum.inr j)

theorem entD_toBlocks₂₁ {S : Set ℂ} {f : ℂ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ}
    (hf : EntD S f) : EntD S (fun z => (f z).toBlocks₂₁) :=
  fun i j => hf (Sum.inr i) (Sum.inl j)

theorem entD_toBlocks₂₂ {S : Set ℂ} {f : ℂ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ}
    (hf : EntD S f) : EntD S (fun z => (f z).toBlocks₂₂) :=
  fun i j => hf (Sum.inr i) (Sum.inr j)

theorem bigM_diff (y : GR n) (X : Fin n → ℝ) (S : Set ℂ) : EntD S (fun z => mR y * aC X z) :=
  entD_mul (entD_const _ _) (entD_aC X S)

theorem det_aC (X : Fin n → ℝ) (z : ℂ) : (aC X z).det = 1 := by
  unfold aC
  rw [Matrix.det_fromBlocks_zero₂₁, det_diagonal, det_diagonal, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun j _ => by rw [← Complex.exp_add]; simp

theorem det_bigM_ne (y : GR n) (X : Fin n → ℝ) (z : ℂ) : (mR y * aC X z).det ≠ 0 := by
  rw [det_mul, det_aC, mul_one]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 y.1.isUnit).ne_zero

end DBoundH

namespace DBoundH

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem famPQ_holo {m n : ℕ} (ε : Fin m → Bool) (t c : ℝ) (e : ℤ) (p q : ℕ) (X : Fin n → ℝ) (y : GR n)
    (u : Fin m → Fin n → ℂ) : DifferentiableOn ℂ (fun z => famPQ ε t c e p q y X z u) (stripS X) := by
  set S := stripS X
  have hM := bigM_diff y X S
  have hQ : ∀ s : ℂ, EntD S (fun z => (mR y * aC X z).toBlocks₂₁ * (s • 1) + (mR y * aC X z).toBlocks₂₂) :=
    fun s => entD_add (entD_mul (entD_toBlocks₂₁ hM) (entD_const _ _)) (entD_toBlocks₂₂ hM)
  have hP : ∀ s : ℂ, EntD S (fun z => (mR y * aC X z).toBlocks₁₁ * (s • 1) + (mR y * aC X z).toBlocks₁₂) :=
    fun s => entD_add (entD_mul (entD_toBlocks₁₁ hM) (entD_const _ _)) (entD_toBlocks₁₂ hM)
  have hd1 : ∀ z ∈ S, ((mR y * aC X z).toBlocks₂₁ * (Complex.I • 1) + (mR y * aC X z).toBlocks₂₂).det ≠ 0 :=
    fun z hz => (dSieg n y X z hz).2.2.1
  have hd2 : ∀ z ∈ S, ((mR y * aC X z).toBlocks₂₁ * ((-Complex.I) • 1) + (mR y * aC X z).toBlocks₂₂).det ≠ 0 :=
    fun z hz => (dSieg n y X z hz).2.2.2
  have hZ1 : EntD S (fun z => ptZ y X z Complex.I) := entD_mul (hP _) (entD_inv (hQ _) hd1)
  have hZ2 : EntD S (fun z => ptZ y X z (-Complex.I)) := entD_mul (hP _) (entD_inv (hQ _) hd2)
  have hj : DifferentiableOn ℂ (fun z => jC e p q y X z) S := by
    unfold jC
    refine (((det_diff hM).zpow (Or.inl fun z _ => det_bigM_ne y X z)).mul
      ((det_diff (hQ _)).zpow (Or.inl fun z hz => hd1 z hz))).mul ((det_diff (hQ _)).zpow (Or.inl fun z hz => hd2 z hz))
  have hg : DifferentiableOn ℂ (fun z => gC ε t c (ptZ y X z Complex.I) (ptZ y X z (-Complex.I)) u) S := by
    unfold gC
    refine DifferentiableOn.cexp ?_
    exact ((trace_diff (entD_mul hZ1 (entD_const _ _))).const_mul _).sub
      ((trace_diff (entD_mul hZ2 (entD_const _ _))).const_mul _)
  exact hj.mul hg

variable {n : ℕ} {T : Type} [TopologicalSpace T]

def EntC (S : Set T) (f : T → Matrix ι ι ℂ) : Prop := ∀ i j, ContinuousOn (fun x => f x i j) S

omit [Fintype ι] [DecidableEq ι] in
theorem entC_const (S : Set T) (A : Matrix ι ι ℂ) : EntC S (fun _ => A) := fun _ _ => continuousOn_const

omit [Fintype ι] [DecidableEq ι] in
theorem entC_add {S : Set T} {f g : T → Matrix ι ι ℂ} (hf : EntC S f) (hg : EntC S g) :
    EntC S (fun z => f z + g z) := fun i j => by
  simp only [Matrix.add_apply]
  exact (hf i j).add (hg i j)

omit [DecidableEq ι] in
theorem entC_mul {S : Set T} {f g : T → Matrix ι ι ℂ} (hf : EntC S f) (hg : EntC S g) :
    EntC S (fun z => f z * g z) := fun i j => by
  simp only [Matrix.mul_apply]
  exact continuousOn_finset_sum _ fun k _ => (hf i k).mul (hg k j)

theorem det_cont {S : Set T} {f : T → Matrix ι ι ℂ} (hf : EntC S f) :
    ContinuousOn (fun z => (f z).det) S := by
  simp only [Matrix.det_apply]
  refine continuousOn_finset_sum _ fun σ _ => ?_
  simp only [Units.smul_def, zsmul_eq_mul]
  exact continuousOn_const.mul (continuousOn_finset_prod _ fun i _ => hf _ _)

theorem entC_adjugate {S : Set T} {f : T → Matrix ι ι ℂ} (hf : EntC S f) :
    EntC S (fun z => (f z).adjugate) := fun i j => by
  simp only [Matrix.adjugate_apply]
  refine det_cont (f := fun z => (f z).updateRow j (Pi.single i 1)) (fun a b => ?_)
  by_cases hab : a = j
  · subst hab; simp only [Matrix.updateRow_self]; exact continuousOn_const
  · simp only [Matrix.updateRow_ne hab]; exact hf a b

theorem entC_inv {S : Set T} {f : T → Matrix ι ι ℂ} (hf : EntC S f) (h0 : ∀ z ∈ S, (f z).det ≠ 0) :
    EntC S (fun z => (f z)⁻¹) := fun i j => by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact ((det_cont hf).inv₀ h0).mul (entC_adjugate hf i j)

omit [DecidableEq ι] in
theorem trace_cont {S : Set T} {f : T → Matrix ι ι ℂ} (hf : EntC S f) :
    ContinuousOn (fun z => (f z).trace) S := by
  simp only [Matrix.trace, Matrix.diag]
  exact continuousOn_finset_sum _ fun i _ => hf i i

theorem mR_cont : Continuous fun y : GR n => mR y :=
  Units.continuous_val.comp continuous_subtype_val

theorem gramB_cont {m : ℕ} (ε : Fin m → Bool) (b : Bool) (i j : Fin n) :
    Continuous fun u : Fin m → Fin n → ℂ => gramB ε b u i j := by
  unfold gramB evX
  exact (MvPolynomial.continuous_eval _).comp (continuous_pi fun k => by
    split_ifs
    · exact continuous_star.comp ((continuous_apply _).comp (continuous_apply _))
    · exact (continuous_apply _).comp (continuous_apply _))

theorem famPQ_cont {m : ℕ} (ε : Fin m → Bool) (t c : ℝ) (e : ℤ) (p q : ℕ) (X : Fin n → ℝ) :
    ContinuousOn (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => famPQ ε t c e p q p'.1 X p'.2.1 p'.2.2)
      (Set.univ ×ˢ (stripS X ×ˢ Set.univ)) := by
  set S : Set (GR n × ℂ × (Fin m → Fin n → ℂ)) := Set.univ ×ˢ (stripS X ×ˢ Set.univ) with hS
  have hzS : ∀ p' ∈ S, p'.2.1 ∈ stripS X := fun p' hp => hp.2.1
  have hY : EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => mR p'.1) := fun i j =>
    (((continuous_apply j).comp ((continuous_apply i).comp mR_cont)).comp continuous_fst).continuousOn
  have hA : EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => aC X p'.2.1) := by
    intro i j
    have := (entD_aC X Set.univ i j).continuousOn
    exact (this.comp_continuous (continuous_fst.comp continuous_snd) (fun _ => Set.mem_univ _)).continuousOn
  have hM : EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => mR p'.1 * aC X p'.2.1) := entC_mul hY hA
  have hM' : ∀ i j, ContinuousOn (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => (mR p'.1 * aC X p'.2.1) i j) S := hM
  have projected_block_lower_sum : EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => (mR p'.1 * aC X p'.2.1).toBlocks₂₁) :=
    fun i j => hM' (Sum.inr i) (Sum.inl j)
  have lowerDiagonalBlockAsGL : EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => (mR p'.1 * aC X p'.2.1).toBlocks₂₂) :=
    fun i j => hM' (Sum.inr i) (Sum.inr j)
  have upper_block_rank_one_update : EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => (mR p'.1 * aC X p'.2.1).toBlocks₁₁) :=
    fun i j => hM' (Sum.inl i) (Sum.inl j)
  have projected_block_upper_sum : EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => (mR p'.1 * aC X p'.2.1).toBlocks₁₂) :=
    fun i j => hM' (Sum.inl i) (Sum.inr j)
  have hQ : ∀ s : ℂ, EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) =>
      (mR p'.1 * aC X p'.2.1).toBlocks₂₁ * (s • 1) + (mR p'.1 * aC X p'.2.1).toBlocks₂₂) :=
    fun s => entC_add (entC_mul projected_block_lower_sum (entC_const _ _)) lowerDiagonalBlockAsGL
  have hP : ∀ s : ℂ, EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) =>
      (mR p'.1 * aC X p'.2.1).toBlocks₁₁ * (s • 1) + (mR p'.1 * aC X p'.2.1).toBlocks₁₂) :=
    fun s => entC_add (entC_mul upper_block_rank_one_update (entC_const _ _)) projected_block_upper_sum
  have hd1 : ∀ p' ∈ S, ((mR p'.1 * aC X p'.2.1).toBlocks₂₁ * (Complex.I • 1) + (mR p'.1 * aC X p'.2.1).toBlocks₂₂).det ≠ 0 :=
    fun p' hp => (dSieg n p'.1 X p'.2.1 (hzS p' hp)).2.2.1
  have hd2 : ∀ p' ∈ S, ((mR p'.1 * aC X p'.2.1).toBlocks₂₁ * ((-Complex.I) • 1) + (mR p'.1 * aC X p'.2.1).toBlocks₂₂).det ≠ 0 :=
    fun p' hp => (dSieg n p'.1 X p'.2.1 (hzS p' hp)).2.2.2
  have hZ1 : EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => ptZ p'.1 X p'.2.1 Complex.I) :=
    entC_mul (hP _) (entC_inv (hQ _) hd1)
  have hZ2 : EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => ptZ p'.1 X p'.2.1 (-Complex.I)) :=
    entC_mul (hP _) (entC_inv (hQ _) hd2)
  have hG : ∀ b : Bool, EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => gramB (epsT t ε) b p'.2.2) := fun b i j =>
    ((gramB_cont (epsT t ε) b i j).comp (continuous_snd.comp continuous_snd)).continuousOn
  have hj : ContinuousOn (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => jC e p q p'.1 X p'.2.1) S := by
    unfold jC
    exact (((det_cont hM).zpow₀ _ fun p' _ => Or.inl (det_bigM_ne p'.1 X p'.2.1)).mul
      ((det_cont (hQ _)).zpow₀ _ fun p' hp => Or.inl (hd1 p' hp))).mul
      ((det_cont (hQ _)).zpow₀ _ fun p' hp => Or.inl (hd2 p' hp))
  have hg : ContinuousOn (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) =>
      gC ε t c (ptZ p'.1 X p'.2.1 Complex.I) (ptZ p'.1 X p'.2.1 (-Complex.I)) p'.2.2) S := by
    unfold gC
    refine ContinuousOn.cexp ?_
    exact (continuousOn_const.mul (trace_cont (entC_mul hZ1 (hG true)))).sub
      (continuousOn_const.mul (trace_cont (entC_mul hZ2 (hG false))))
  exact hj.mul hg

end DBoundH

end PositivityTheory.Rg.Sw.Glob
