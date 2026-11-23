import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardToMultisetEqDegree
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DifferentiablePolyDeriv
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MulConjTransposeEqOneOfOrthonormal

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum.Minor

open ReciprocityTheory.ChartRestriction.G Matrix

abbrev Incr (a d : ℕ) : Type := {s : Fin a → Fin d // StrictMono s}

noncomputable def toIncr {a d : ℕ} (S : Set.powersetCard (Fin d) a) : Incr a d :=
  ⟨GlobalTheory.subsetEnum S, (S.1.orderEmbOfFin S.2).strictMono⟩

theorem toIncr_bijective {a d : ℕ} : Function.Bijective (toIncr (a := a) (d := d)) := by
  constructor
  · intro S S' h
    have h1 : GlobalTheory.subsetEnum S = GlobalTheory.subsetEnum S' := congrArg Subtype.val h
    have h2 : (S.1 : Set (Fin d)) = S'.1 := by
      rw [← GlobalTheory.range_subsetEnum S, ← GlobalTheory.range_subsetEnum S', h1]
    exact Subtype.ext (Finset.coe_injective h2)
  · intro s
    have hc : (Finset.univ.image s.1).card = a := by
      rw [Finset.card_image_of_injective _ s.2.injective]; simp
    refine ⟨⟨Finset.univ.image s.1, hc⟩, Subtype.ext ?_⟩
    exact (Finset.orderEmbOfFin_unique hc (fun x => by simp) s.2).symm

theorem det_submatrix_mul {R l o : Type*} [CommRing R] {a d : ℕ}
    (A : Matrix l (Fin d) R) (B : Matrix (Fin d) o R) (r : Fin a → l) (c : Fin a → o) :
    ((A * B).submatrix r c).det = ∑ s : Incr a d, (A.submatrix r s.1).det * (B.submatrix s.1 c).det := by
  rw [GlobalTheory.det_submatrix_mul_eq_sum_minors]
  exact Fintype.sum_bijective toIncr toIncr_bijective _ _ fun S => rfl

theorem det_submatrix_one {a d : ℕ} (s s' : Incr a d) :
    ((1 : Matrix (Fin d) (Fin d) ℂ).submatrix s.1 s'.1).det = if s = s' then 1 else 0 := by
  obtain ⟨I, rfl⟩ := toIncr_bijective.2 s
  obtain ⟨J, rfl⟩ := toIncr_bijective.2 s'
  split_ifs with h
  · rw [← h, submatrix_one _ (toIncr I).2.injective, det_one]
  · have h' : I ≠ J := fun e => h (by rw [e])
    obtain ⟨x, hxI, hxJ⟩ := (Set.powersetCard.exists_mem_notMem_iff_ne I J).mp h'
    have h1 : x ∈ Set.range (GlobalTheory.subsetEnum I) := by rw [GlobalTheory.range_subsetEnum]; exact hxI
    have h2 : x ∉ Set.range (GlobalTheory.subsetEnum J) := by rw [GlobalTheory.range_subsetEnum]; exact hxJ
    obtain ⟨i, rfl⟩ := h1
    exact det_eq_zero_of_row_eq_zero i fun j => one_apply_ne fun e => h2 ⟨j, e.symm⟩

theorem minors_orth {a d : ℕ} {u : Matrix (Fin d) (Fin d) ℂ} (hu : u ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (s' s'' : Incr a d) :
    ∑ s : Incr a d, (u.submatrix s'.1 s.1).det * star (u.submatrix s''.1 s.1).det = if s' = s'' then 1 else 0 := by
  rw [← det_submatrix_one, ← (Matrix.mem_unitaryGroup_iff.1 hu), det_submatrix_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← det_conjTranspose, conjTranspose_submatrix, star_eq_conjTranspose]

theorem sum_norm_sq_eq {ι : Type*} [Fintype ι] (K : ι → ι → ℂ)
    (hK : ∀ i j, ∑ t, K i t * star (K j t) = if i = j then 1 else 0) (v : ι → ℂ) :
    ∑ t, ‖∑ i, K i t * v i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  apply Complex.ofReal_injective
  have h (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [Complex.ofReal_sum, h, star_sum, star_mul', Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  have : ∀ j, ∑ t, K i t * v i * (star (K j t) * star (v j)) = (if i = j then 1 else 0) * (v i * star (v j)) := by
    intro j
    rw [← hK, Finset.sum_mul]
    exact Finset.sum_congr rfl fun t _ => by ring
  simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem prod_prod_sum {R T S : Type*} [CommSemiring R] [Fintype T] [DecidableEq T] [Fintype S] (n : T → ℕ)
    (f : ∀ τ, Fin (n τ) → S → R) :
    ∏ τ, ∏ j, ∑ s, f τ j s = ∑ t : ∀ τ, Fin (n τ) → S, ∏ τ, ∏ j, f τ j (t τ j) := by
  simp only [Fintype.prod_sum]

theorem polyDeriv_subst {σ κ W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [Fintype κ] {F : W → ℂ}
    (hF : ContDiff ℂ (⊤ : ℕ∞) F) (s : σ → κ → ℂ)
    (j : σ → κ → σ) (Φ : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ)
    (hΦ : ∀ l, Φ (MvPolynomial.X l) = ∑ k, MvPolynomial.C (s l k) * MvPolynomial.X (j l k))
    (u : σ → W) (P : MvPolynomial σ ℂ) (x : W) :
    I2.polyDeriv (Φ P) u F x = I2.polyDeriv P (fun l => ∑ k, s l k • u (j l k)) F x := by
  induction P using MvPolynomial.induction_on generalizing x with
  | C a =>
    have h : (MvPolynomial.C a : MvPolynomial σ ℂ) = a • MvPolynomial.monomial 0 1 := by
      simp [MvPolynomial.smul_eq_C_mul]
    rw [MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, h]
    simp [I2.polyDeriv_smul, I2.polyDeriv_monomial_one, I2.pdTerm_eq_itD,
      -MvPolynomial.monomial_zero']
  | add P Q hP hQ => simp only [map_add, I2.polyDeriv_add, hP, hQ]
  | mul_X P l hP =>
    rw [map_mul, hΦ, Finset.mul_sum, I2.jof_polyDeriv_sum, GlobalTheory.ThFr.polyDeriv_mul_X hF, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_left_comm, MvPolynomial.C_mul', I2.polyDeriv_smul, GlobalTheory.ThFr.polyDeriv_mul_X hF, funext hP]
    simp

variable {D : D7} {a d : ℕ}

theorem applyAt0_eq (P : MvPolynomial (GL3Theta.Idx D a d) ℂ) (G : VC D a d → ℂ) :
    GL3Theta.applyAt0 D P G = I2.polyDeriv P (coordV D) G 0 := by
  unfold GL3Theta.applyAt0 I2.polyDeriv taylor
  refine Finset.sum_congr rfl fun α _ => ?_
  have h : (α.prod fun _ n => (n.factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  rw [mul_assoc, mul_div_cancel₀ _ h]
  rfl

theorem applyAt0_comp {κ : Type} [Fintype κ] {G : VC D a d → ℂ} (hG : Differentiable ℂ G)
    (A : VC D a d →ₗ[ℂ] VC D a d) (s : GL3Theta.Idx D a d → κ → ℂ) (j : GL3Theta.Idx D a d → κ → GL3Theta.Idx D a d)
    (hA : ∀ l, A (coordV D l) = ∑ k, s l k • coordV D (j l k)) (P : MvPolynomial (GL3Theta.Idx D a d) ℂ) :
    GL3Theta.applyAt0 D P (fun z => G (A z)) = GL3Theta.applyAt0 D
      (MvPolynomial.aeval (fun l => ∑ k, MvPolynomial.C (s l k) * (MvPolynomial.X (j l k) : MvPolynomial _ ℂ)) P) G := by
  have hG' : ContDiff ℂ (⊤ : ℕ∞) G := contDiff_infty.2 fun k => I2.contDiff_of_differentiable_fd hG k
  rw [applyAt0_eq, applyAt0_eq, polyDeriv_subst hG' s j _ (fun l => MvPolynomial.aeval_X _ l)]
  have h := GlobalTheory.Jet.polyDeriv_comp_clm P (coordV D) hG (LinearMap.toContinuousLinearMap A) 0
  rw [map_zero] at h
  refine h.trans ?_
  congr 1
  funext l
  exact hA l

def mulR (u : D.what₂.Tau → Matrix (Fin a) (Fin a) ℂ) : VC D a d →ₗ[ℂ] VC D a d where
  toFun z := fun τ i j => ∑ k, z τ i k * u τ k j
  map_add' x y := by
    funext τ i j
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    funext τ i j
    simp [Finset.mul_sum, mul_assoc]

def mulL (u : D.what₂.Tau → Matrix (Fin d) (Fin d) ℂ) : VC D a d →ₗ[ℂ] VC D a d where
  toFun z := fun τ i j => ∑ k, u τ i k * z τ k j
  map_add' x y := by
    funext τ i j
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext τ i j
    simp [Finset.mul_sum, mul_left_comm]

theorem mulR_coordV (u : D.what₂.Tau → Matrix (Fin a) (Fin a) ℂ) (l : GL3Theta.Idx D a d) :
    mulR u (coordV D l) = ∑ k, u l.1 l.2.2 k • coordV D (l.1, l.2.1, k) := by
  obtain ⟨τ, i, j⟩ := l
  funext τ' i' j'
  by_cases h1 : τ' = τ <;> by_cases h2 : i' = i <;>
    simp [mulR, coordV, Finset.sum_apply, h1, h2]

theorem mulL_coordV (u : D.what₂.Tau → Matrix (Fin d) (Fin d) ℂ) (l : GL3Theta.Idx D a d) :
    mulL u (coordV D l) = ∑ k, u l.1 k l.2.1 • coordV D (l.1, k, l.2.2) := by
  obtain ⟨τ, i, j⟩ := l
  funext τ' i' j'
  by_cases h1 : τ' = τ <;> by_cases h2 : j' = j <;>
    simp [mulL, coordV, Finset.sum_apply, h1, h2]

theorem applyAt0_minorPol_mulR {n : D.what₂.Tau → ℕ} {G : VC D a d → ℂ} (hG : Differentiable ℂ G)
    (u : D.what₂.Tau → Matrix (Fin a) (Fin a) ℂ) (t : Tup D a d n) :
    GL3Theta.applyAt0 D (minorPol D t) (fun z => G (mulR u z)) =
      (∏ τ, (u τ).det ^ n τ) * GL3Theta.applyAt0 D (minorPol D t) G := by
  rw [applyAt0_comp hG (mulR u) (fun l k => u l.1 l.2.2 k) (fun l k => (l.1, l.2.1, k)) (mulR_coordV u),
    applyAt0_eq, applyAt0_eq, ← I2.polyDeriv_smul]
  congr 1
  unfold minorPol
  rw [map_prod, MvPolynomial.smul_eq_C_mul, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_prod, map_pow, ← Fin.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [AlgHom.map_det, RingHom.map_det, mul_comm, ← det_transpose (RingHom.mapMatrix _ _), ← det_mul]
  congr 1
  ext1 i i'
  simp [Matrix.mul_apply, mul_comm]

theorem applyAt0_minorPol_mulL {n : D.what₂.Tau → ℕ} {G : VC D a d → ℂ} (hG : Differentiable ℂ G)
    (u : D.what₂.Tau → Matrix (Fin d) (Fin d) ℂ) (t : Tup D a d n) :
    GL3Theta.applyAt0 D (minorPol D t) (fun z => G (mulL u z)) =
      ∑ t' : Tup D a d n, (∏ τ, ∏ j, ((u τ).submatrix (t' τ j).1 (t τ j).1).det) *
        GL3Theta.applyAt0 D (minorPol D t') G := by
  rw [applyAt0_comp hG (mulL u) (fun l k => u l.1 k l.2.1) (fun l k => (l.1, k, l.2.2)) (mulL_coordV u)]
  simp only [applyAt0_eq, ← I2.polyDeriv_smul]
  rw [← I2.jof_polyDeriv_sum]
  congr 1
  unfold minorPol
  simp only [MvPolynomial.smul_eq_C_mul, map_prod, ← Finset.prod_mul_distrib]
  rw [← prod_prod_sum n (fun τ j (s : Incr a d) => MvPolynomial.C ((u τ).submatrix s.1 (t τ j).1).det *
    (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, s.1 i, i') : MvPolynomial (GL3Theta.Idx D a d) ℂ)).det)]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun j _ => ?_
  have h := det_submatrix_mul ((u τ)ᵀ.map (MvPolynomial.C : ℂ →+* MvPolynomial (GL3Theta.Idx D a d) ℂ))
    (Matrix.of fun (i : Fin d) (i' : Fin a) => (MvPolynomial.X (τ, i, i') : MvPolynomial (GL3Theta.Idx D a d) ℂ))
    (t τ j).1 id
  rw [AlgHom.map_det]
  refine Eq.trans ?_ (h.trans (Finset.sum_congr rfl fun s _ => ?_))
  · congr 1
    ext1 i i'
    simp [Matrix.mul_apply]
  · rw [RingHom.map_det, ← det_transpose (RingHom.mapMatrix _ _)]
    rfl

end GlobalTheory.NormSum.Minor

open GlobalTheory.NormSum.Minor ReciprocityTheory.ChartRestriction.G in

theorem GlobalTheory.NormSum.applyAt0_minorPol_linear : ∀ (D : D7) (a d : ℕ) (n : D.what₂.Tau → ℕ) (G : VC D a d → ℂ), Differentiable ℂ G → (∀ (u : D.what₂.Tau → Matrix (Fin a) (Fin a) ℂ) (t : Tup D a d n), GL3Theta.applyAt0 D (minorPol D t) (fun z => G (fun τ => (Matrix.of (z τ) * u τ : Matrix _ _ ℂ))) = (∏ τ, (u τ).det ^ n τ) * GL3Theta.applyAt0 D (minorPol D t) G) ∧ (∀ (u : D.what₂.Tau → Matrix (Fin d) (Fin d) ℂ), (∀ τ, u τ ∈ Matrix.unitaryGroup (Fin d) ℂ) → ∑ t : Tup D a d n, ‖GL3Theta.applyAt0 D (minorPol D t) (fun z => G (fun τ => (u τ * Matrix.of (z τ) : Matrix _ _ ℂ)))‖ ^ 2 = ∑ t : Tup D a d n, ‖GL3Theta.applyAt0 D (minorPol D t) G‖ ^ 2) ∧ (∀ (c : ℂ) P, GL3Theta.applyAt0 D P (c • G) = c * GL3Theta.applyAt0 D P G) ∧ ∀ G' P, Differentiable ℂ G' → GL3Theta.applyAt0 D P (G + G') = GL3Theta.applyAt0 D P G + GL3Theta.applyAt0 D P G' := by
  intro D a d n G hG
  refine ⟨fun u t => applyAt0_minorPol_mulR hG u t, fun u hu => ?_, fun c P => ?_, fun G' P hG' => ?_⟩
  · refine Eq.trans (Finset.sum_congr rfl fun t _ => ?_) (sum_norm_sq_eq
      (fun t' t : Tup D a d n => ∏ τ, ∏ j, ((u τ).submatrix (t' τ j).1 (t τ j).1).det) (fun t' t'' => ?_) _)
    · rw [← applyAt0_minorPol_mulL hG u t]
      rfl
    · simp only [star_prod, ← Finset.prod_mul_distrib]
      rw [← prod_prod_sum n (fun τ j (s : Incr a d) => ((u τ).submatrix (t' τ j).1 s.1).det *
        star ((u τ).submatrix (t'' τ j).1 s.1).det)]
      simp only [fun τ => minors_orth (a := a) (hu τ)]
      split_ifs with h
      · simp [h]
      · obtain ⟨τ, hτ⟩ := Function.ne_iff.1 h
        obtain ⟨j, hj⟩ := Function.ne_iff.1 hτ
        exact Finset.prod_eq_zero (Finset.mem_univ τ) (Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj))
  · rw [applyAt0_eq, applyAt0_eq, GlobalTheory.Jet.polyDeriv_smul_fun P _ hG]
  · rw [applyAt0_eq, applyAt0_eq, applyAt0_eq, GlobalTheory.Jet.polyDeriv_add_fun P _ hG hG']
