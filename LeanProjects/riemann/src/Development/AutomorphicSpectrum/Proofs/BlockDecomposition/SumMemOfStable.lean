import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff

noncomputable section

open Matrix Finset
open scoped InnerProductSpace

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount.InjHw

variable {n : ℕ}

theorem exp_mem_unitary (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (s : ℝ) :
    NormedSpace.exp ((s : ℂ) • X) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose]
  have h : ((s : ℂ) • X)ᴴ = -((s : ℂ) • X) := by
    rw [conjTranspose_smul, hX]
    simp
  have hc : Commute ((s : ℂ) • X) (-((s : ℂ) • X)) := (Commute.refl _).neg_right
  rw [h, ← Matrix.exp_add_of_commute _ _ hc]
  simp

theorem single_conjT (a b : Fin n) (c : ℂ) :
    (Matrix.single a b c : Matrix (Fin n) (Fin n) ℂ)ᴴ = Matrix.single b a (star c) := by
  ext i j
  simp only [conjTranspose_apply, Matrix.single_apply]
  by_cases h : a = j ∧ b = i
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
  · rw [if_neg h, if_neg (fun hh => h ⟨hh.2, hh.1⟩)]
    simp

theorem single_negI (a b : Fin n) (c : ℂ) :
    (Matrix.single a b (-c) : Matrix (Fin n) (Fin n) ℂ) = -Matrix.single a b c := by
  ext i j
  simp only [Matrix.neg_apply, Matrix.single_apply]
  split_ifs <;> simp

def expU (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (s : ℝ) : Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨NormedSpace.exp ((s : ℂ) • X), exp_mem_unitary X hX s⟩

section V

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)} {Kf : Fin n → Fin n → Module.End ℂ V}

theorem deriv_expU (h : IsDerivK σ Kf) (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (w : V) :
    HasDerivAt (fun s : ℝ => σ (expU X hX s) w) (∑ a, ∑ b, X a b • Kf a b w) 0 := by
  obtain ⟨S, _, hw, _, _, hd⟩ := h.2 w
  exact hd X (expU X hX) (fun _ => rfl) w hw

theorem sum_mem_of_stable (h : IsDerivK σ Kf) (R : Submodule ℂ V) [FiniteDimensional ℂ R]
    (hR : ∀ k, ∀ w ∈ R, σ k w ∈ R) (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) {w : V} (hw : w ∈ R) :
    ∑ a, ∑ b, X a b • Kf a b w ∈ R := by
  have hd := deriv_expU h X hX w
  have hcl : IsClosed (R : Set V) := Submodule.closed_of_finiteDimensional R
  have ht := hasDerivAt_iff_tendsto_slope_zero.1 hd
  refine hcl.mem_of_tendsto ht (Filter.Eventually.of_forall fun s => ?_)
  have : s⁻¹ • (σ (expU X hX (0 + s)) w - σ (expU X hX 0) w) ∈ R.restrictScalars ℝ :=
    Submodule.smul_mem _ _ (sub_mem (hR _ _ hw) (hR _ _ hw))
  exact this

theorem sum_single (w : V) (a b : Fin n) (c : ℂ) :
    ∑ x, ∑ y, (Matrix.single a b c : Matrix (Fin n) (Fin n) ℂ) x y • Kf x y w = c • Kf a b w := by
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro y _ hy
    rw [Matrix.single_apply, if_neg (fun hh => hy hh.2.symm), zero_smul]
  · simp
  · intro x _ hx
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [Matrix.single_apply, if_neg (fun hh => hx hh.1.symm), zero_smul]
  · simp

theorem entry_mem (h : IsDerivK σ Kf) (R : Submodule ℂ V) [FiniteDimensional ℂ R]
    (hR : ∀ k, ∀ w ∈ R, σ k w ∈ R) (a b : Fin n) {w : V} (hw : w ∈ R) : Kf a b w ∈ R := by
  have h1 : (Matrix.single a b (1 : ℂ) - Matrix.single b a 1)ᴴ = -(Matrix.single a b (1 : ℂ) - Matrix.single b a 1) := by
    rw [conjTranspose_sub, single_conjT, single_conjT, star_one, neg_sub]
  have h2 : (Matrix.single a b Complex.I + Matrix.single b a Complex.I)ᴴ =
      -(Matrix.single a b Complex.I + Matrix.single b a Complex.I) := by
    rw [conjTranspose_add, single_conjT, single_conjT, Complex.star_def, Complex.conj_I, single_negI, single_negI, neg_add,
      add_comm]
  have m1 := sum_mem_of_stable h R hR _ h1 hw
  have m2 := sum_mem_of_stable h R hR _ h2 hw
  have e1 : ∑ x, ∑ y, (Matrix.single a b (1 : ℂ) - Matrix.single b a 1 : Matrix (Fin n) (Fin n) ℂ) x y • Kf x y w =
      Kf a b w - Kf b a w := by
    simp only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, sum_single, one_smul]
  have e2 : ∑ x, ∑ y, (Matrix.single a b Complex.I + Matrix.single b a Complex.I : Matrix (Fin n) (Fin n) ℂ) x y • Kf x y w =
      Complex.I • Kf a b w + Complex.I • Kf b a w := by
    simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib, sum_single]
  rw [e1] at m1
  rw [e2] at m2
  have m3 := R.smul_mem (-Complex.I) m2
  have m4 := R.smul_mem (1 / 2 : ℂ) (R.add_mem m1 m3)
  have e3 : (1 / 2 : ℂ) • (Kf a b w - Kf b a w + -Complex.I • (Complex.I • Kf a b w + Complex.I • Kf b a w)) = Kf a b w := by
    rw [smul_add (-Complex.I), smul_smul, smul_smul]
    have : -Complex.I * Complex.I = 1 := by simp
    rw [this, one_smul, one_smul, sub_add_add_cancel, ← two_smul ℂ, smul_smul]
    norm_num
  rwa [e3] at m4

theorem weight_of_torus (h : IsDerivK σ Kf) (μ : Fin n → ℤ) {v : V}
    (hv : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → σ k v = (∏ a, z a ^ μ a) • v)
    (a : Fin n) : Kf a a v = ((μ a : ℝ) : ℂ) • v := by
  have hX : (Matrix.single a a Complex.I)ᴴ = -(Matrix.single a a Complex.I) := by
    rw [single_conjT, Complex.star_def, Complex.conj_I, single_negI]
  have hd := deriv_expU (Kf := Kf) h _ hX v
  rw [sum_single] at hd
  have hk : ∀ s : ℝ, (expU _ hX s).1 = diagonal (fun c => if c = a then Complex.exp (s * Complex.I) else 1) := by
    intro s
    have e : (s : ℂ) • (Matrix.single a a Complex.I : Matrix (Fin n) (Fin n) ℂ) =
        diagonal (fun c => if c = a then (s : ℂ) * Complex.I else 0) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        by_cases hc : i = a
        · subst hc
          simp
        · simp [Matrix.single_apply, hc, Ne.symm hc]
      · rw [Matrix.diagonal_apply_ne _ hij, Matrix.smul_apply, Matrix.single_apply,
          if_neg (fun hh => hij (hh.1.symm.trans hh.2)), smul_zero]
    show NormedSpace.exp _ = _
    rw [e, Matrix.exp_diagonal]
    congr 1
    funext c
    split_ifs with hc <;> simp [hc, Complex.exp_eq_exp_ℂ]
  have hf : (fun s : ℝ => σ (expU _ hX s) v) =
      fun s : ℝ => Complex.exp ((s : ℂ) * (Complex.I * ((μ a : ℝ) : ℂ))) • v := by
    funext s
    rw [hv _ _ (hk s), Finset.prod_eq_single a]
    · simp only [if_true]
      rw [← Complex.exp_int_mul]
      congr 2
      push_cast
      ring
    · intro c _ hc
      simp [hc]
    · simp
  rw [hf] at hd
  have h2 : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * (Complex.I * ((μ a : ℝ) : ℂ))) • v)
      ((Complex.I * ((μ a : ℝ) : ℂ)) • v) 0 := by
    have h3 : HasDerivAt (fun y : ℂ => Complex.exp (y * (Complex.I * ((μ a : ℝ) : ℂ))))
        (Complex.exp ((0 : ℂ) * (Complex.I * ((μ a : ℝ) : ℂ))) * (1 * (Complex.I * ((μ a : ℝ) : ℂ)))) 0 :=
      ((hasDerivAt_id (0 : ℂ)).mul_const _).cexp
    have h4 := (h3.comp_ofReal).smul_const v
    simpa using h4
  have e := hd.unique h2
  calc Kf a a v = (-Complex.I) • (Complex.I • Kf a a v) := by rw [smul_smul]; simp
    _ = ((μ a : ℝ) : ℂ) • v := by rw [e, smul_smul, ← mul_assoc]; simp

end V

section Main

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem gl_kF {E1 E2 : Fin n → Fin n → Module.End ℂ V} (h : IsPair E1 E2) : Formalism.REAL.GlRel (kF E1 E2) := by
  intro a b c d
  have h1 := h.gl1 a b c d
  have h2 := h.gl2 a b c d
  have c1 := h.comm a b c d
  have c2 := h.comm c d a b
  have e : kF E1 E2 a b * kF E1 E2 c d - kF E1 E2 c d * kF E1 E2 a b =
      (E1 a b * E1 c d - E1 c d * E1 a b) + (E2 a b * E2 c d - E2 c d * E2 a b) := by
    simp only [kF, add_mul, mul_add]
    rw [c1, c2]
    abel
  rw [e, h1, h2]
  simp only [kF]
  split_ifs <;> abel

theorem weight_shift {K : Fin n → Fin n → Module.End ℂ V} (hg : Formalism.REAL.GlRel K) (μ : Fin n → ℤ) {v : V}
    (hv : ∀ c, K c c v = ((μ c : ℝ) : ℂ) • v) {a b : Fin n} (hab : a ≠ b) (c : Fin n) :
    K c c (K a b v) =
      (((μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0) : ℤ) : ℝ) : ℂ) • K a b v := by
  have e : K c c (K a b v) = K a b (K c c v) +
      ((if c = a then K c b else 0) - (if b = c then K a c else 0)) v := by
    rw [← hg c c a b]
    simp [Module.End.mul_apply]
  rw [e, hv c, map_smul]
  by_cases h1 : c = a
  · subst h1
    have h2 : ¬ b = c := fun h => hab h.symm
    have h3 : ¬ c = b := hab
    simp only [↓reduceIte, h2, h3, LinearMap.sub_apply, LinearMap.zero_apply]
    push_cast
    module
  · by_cases h2 : c = b
    · subst h2
      simp only [↓reduceIte, h1, LinearMap.sub_apply, LinearMap.zero_apply]
      push_cast
      module
    · have h3 : ¬ b = c := fun h => h2 h.symm
      simp only [↓reduceIte, h1, h2, h3, sub_zero, LinearMap.zero_apply, add_zero]

def jt (K : Fin n → Fin n → Module.End ℂ V) (χ : Fin n → ℂ) : Submodule ℂ V :=
  ⨅ c, (K c c).maxGenEigenspace (χ c)

theorem mem_jt {K : Fin n → Fin n → Module.End ℂ V} {χ : Fin n → ℂ} {v : V} (hv : ∀ c, K c c v = χ c • v) :
    v ∈ jt K χ := by
  refine (Submodule.mem_iInf _).2 fun c => ?_
  rw [Module.End.mem_maxGenEigenspace]
  exact ⟨1, by simp [hv c]⟩

theorem jt_indep {K : Fin n → Fin n → Module.End ℂ V} (hg : Formalism.REAL.GlRel K) : iSupIndep (jt K) := by
  have hc : ∀ i j, Commute (K i i) (K j j) := by
    intro i j
    have h := hg i i j j
    by_cases hij : i = j
    · subst hij
      exact Commute.refl _
    · have h' : ¬ j = i := fun h => hij h.symm
      rw [if_neg hij, if_neg h', sub_zero] at h
      exact sub_eq_zero.1 h
  exact Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun c => K c c)
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) φ)

def wtC (μ : Fin n → ℤ) : Fin n → ℂ := fun a => ((μ a : ℝ) : ℂ)

theorem wtC_injective : Function.Injective (wtC (n := n)) := by
  intro x y h
  funext c
  have := congrFun h c
  simpa [wtC] using this

end Main

end GlobalTheory.CompanionTheory.RealCount.InjHw
