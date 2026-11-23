import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

theorem isDerivedOn_trivial {n : ℕ} (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] :
    IsURepOn (UJset ε) (fun _ : Matrix (Fin n) (Fin n) ℂ => (1 : H →L[ℂ] H)) ∧
      IsDerivedOn ε (fun _ : Matrix (Fin n) (Fin n) ℂ => (1 : H →L[ℂ] H)) ⊤ (fun _ _ => 0) := by

  refine ⟨⟨⟨rfl, fun a _ b _ => ?_⟩, fun g _ v => ?_, fun v => continuousOn_const⟩, ⟨?_, ?_, ?_⟩⟩
  · ext v
    simp
  · simp
  · intro a b c d
    simp
  · intro k _ v _
    exact Submodule.mem_top
  · intro X _ v
    have h1 : ((actM (fun _ _ => (0 : Module.End ℂ (⊤ : Submodule ℂ H))) X v : (⊤ : Submodule ℂ H)) : H) = 0 := by
      simp [actM]
    rw [h1]
    simp only [ContinuousLinearMap.one_apply]
    exact hasDerivAt_const _ _

abbrev EH (n : ℕ) := EuclideanSpace ℂ (Fin n)

def rsM {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (⊤ : Submodule ℂ (EH n)) :=
  ((toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A : EH n →L[ℂ] EH n) : EH n →ₗ[ℂ] EH n).restrict
    (p := ⊤) (q := ⊤) (fun _ _ => Submodule.mem_top)

theorem rsM_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (v : (⊤ : Submodule ℂ (EH n))) :
    ((rsM A v : (⊤ : Submodule ℂ (EH n))) : EH n) = toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A v := rfl

theorem rsM_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : rsM A * rsM B = rsM (A * B) := by

  apply LinearMap.ext
  intro v
  apply Subtype.ext
  show toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A (toEuclideanCLM (n := Fin n) (𝕜 := ℂ) B (v : EH n)) = toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (A * B) (v : EH n)
  rw [map_mul]
  rfl

theorem rsM_sub {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : rsM A - rsM B = rsM (A - B) := by

  apply LinearMap.ext
  intro v
  apply Subtype.ext
  show toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A (v : EH n) - toEuclideanCLM (n := Fin n) (𝕜 := ℂ) B (v : EH n) = toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (A - B) (v : EH n)
  rw [map_sub]
  rfl

theorem rsM_zero {n : ℕ} : rsM (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by

  apply LinearMap.ext
  intro v
  apply Subtype.ext
  show toEuclideanCLM (n := Fin n) (𝕜 := ℂ) 0 (v : EH n) = (0 : EH n)
  rw [map_zero]
  rfl

theorem rsM_neg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : rsM (-A) = -rsM A := by

  apply LinearMap.ext
  intro v
  apply Subtype.ext
  show toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (-A) (v : EH n) = -toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A (v : EH n)
  rw [map_neg]
  rfl

theorem rsM_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : rsM A + rsM B = rsM (A + B) := by

  apply LinearMap.ext
  intro v
  apply Subtype.ext
  show toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A (v : EH n) + toEuclideanCLM (n := Fin n) (𝕜 := ℂ) B (v : EH n) = toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (A + B) (v : EH n)
  rw [map_add]
  rfl

theorem rsM_smul {n : ℕ} (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) : c • rsM A = rsM (c • A) := by

  apply LinearMap.ext
  intro v
  apply Subtype.ext
  show c • toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A (v : EH n) = toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (c • A) (v : EH n)
  rw [map_smul]
  rfl

def rsL (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (⊤ : Submodule ℂ (EH n)) where
  toFun := rsM
  map_add' A B := (rsM_add A B).symm
  map_smul' c A := (rsM_smul c A).symm

theorem actM_rsM {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    actM (fun a b => rsM (single a b (1 : ℂ))) X = rsM X := by

  have h1 : ∀ a b, X a b • rsM (single a b (1 : ℂ)) = rsL n (X a b • single a b (1 : ℂ)) :=
    fun a b => rsM_smul _ _
  have h2 : ∑ a, ∑ b, X a b • single a b (1 : ℂ) = X := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single i (fun c _ hc => by simp [hc]) (by simp),
      Finset.sum_eq_single j (fun c _ hc => by simp [hc]) (by simp)]
    simp
  unfold actM
  simp only [h1, ← map_sum, h2]
  rfl

private lemma ss_lemma {n : ℕ} (a b c d : Fin n) :
    single a b (1 : ℂ) * single c d 1 = if b = c then single a d 1 else 0 := by
  split_ifs with h
  · subst h
    simp [Matrix.single_mul_single_same]
  · ext i j
    simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero (fun x _ => ?_)
    split_ifs with h1 h2 <;> simp_all

theorem glRep_rsM (n : ℕ) : IsGlRep (fun a b : Fin n => rsM (single a b (1 : ℂ))) := by

  intro a b c d
  simp only
  rw [rsM_mul, rsM_mul, rsM_sub, ss_lemma, ss_lemma]
  split_ifs <;> simp only [sub_zero, zero_sub, sub_self, rsM_zero, rsM_neg, rsM_sub]

theorem toE_unitary {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (hg : g ∈ UJset (fun _ : Fin n => true))
    (v : EH n) : ‖toEuclideanCLM (n := Fin n) (𝕜 := ℂ) g v‖ = ‖v‖ := by

  have hJ : Jm (fun _ : Fin n => true) = 1 := by
    simp [Jm]
  have hg' : gᴴ * g = 1 := by
    have h0 : gᴴ * Jm (fun _ : Fin n => true) * g = Jm (fun _ : Fin n => true) := hg
    rw [hJ, Matrix.mul_one] at h0
    exact h0
  have hg2 : g * gᴴ = 1 := mul_eq_one_comm.mp hg'
  have hu : toEuclideanCLM (n := Fin n) (𝕜 := ℂ) g ∈ unitary (EH n →L[ℂ] EH n) := by
    rw [Unitary.mem_iff]
    constructor
    · rw [← map_star, ← map_mul, Matrix.star_eq_conjTranspose, hg', map_one]
    · rw [← map_star, ← map_mul, Matrix.star_eq_conjTranspose, hg2, map_one]
  exact ContinuousLinearMap.norm_map_of_mem_unitary hu v

theorem toE_continuous (n : ℕ) : Continuous (toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) := by

  let f : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (EH n →L[ℂ] EH n) :=
    { toFun := toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
      map_add' := map_add _
      map_smul' := map_smul _ }
  exact f.continuous_of_finiteDimensional

theorem toE_exp {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (NormedSpace.exp X) =
      NormedSpace.exp (toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X) := by

  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  exact NormedSpace.map_exp _ (toE_continuous n) X

theorem toE_deriv {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (v : EH n) :
    HasDerivAt (fun t : ℝ => toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (NormedSpace.exp ((t : ℂ) • X)) v)
      (toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X v) 0 := by

  have h2 : HasDerivAt (fun s : ℂ => NormedSpace.exp (s • toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X))
      (NormedSpace.exp ((0 : ℂ) • toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X) * toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X) 0 :=
    hasDerivAt_exp_smul_const (toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X) 0
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  have h3 : HasDerivAt (fun s : ℂ => NormedSpace.exp (s • toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X) v) (toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X v) 0 := by
    have h4 := (ContinuousLinearMap.apply ℂ (EH n) v).hasFDerivAt.comp_hasDerivAt (0 : ℂ) h2
    exact h4
  have hid : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have h3' : HasDerivAt (fun s : ℂ => (NormedSpace.exp (s • toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X)) v) (toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X v)
      ((fun t : ℝ => (t : ℂ)) 0) := by
    simpa using h3
  have h6 := h3'.scomp (0 : ℝ) hid
  simp only [one_smul] at h6
  have hfun : (fun t : ℝ => toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (NormedSpace.exp ((t : ℂ) • X)) v) =
      ((fun s : ℂ => (NormedSpace.exp (s • toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X)) v) ∘ Complex.ofReal) := by
    funext t
    simp only [Function.comp_apply]
    rw [toE_exp, map_smul]
  rw [hfun]
  exact h6

theorem isDerivedOn_natural (n : ℕ) :
    ∃ (σ : Matrix (Fin n) (Fin n) ℂ → (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)))
      (E : Fin n → Fin n → Module.End ℂ (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin n)))),
      IsURepOn (UJset (fun _ : Fin n => true)) σ ∧ IsDerivedOn (fun _ => true) σ ⊤ E ∧
        ∀ a b, E a b ≠ 0 := by

  refine ⟨toEuclideanCLM (n := Fin n) (𝕜 := ℂ), fun a b => rsM (single a b (1 : ℂ)), ⟨⟨map_one _, fun a _ b _ => ?_⟩, fun g hg v => toE_unitary g hg v,
    fun v => ?_⟩, ⟨glRep_rsM n, fun _ _ v _ => Submodule.mem_top, fun X _ v => ?_⟩, fun a b => ?_⟩
  · rw [map_mul]
    rfl
  · exact ((ContinuousLinearMap.apply ℂ (EH n) v).continuous.comp (toE_continuous n)).continuousOn
  · rw [actM_rsM, rsM_apply]
    exact toE_deriv X v
  · intro h
    have h1 : toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (single a b (1 : ℂ)) = 0 := by
      ext1 v
      have := congrArg (fun f : Module.End ℂ (⊤ : Submodule ℂ (EH n)) =>
        ((f ⟨v, Submodule.mem_top⟩ : (⊤ : Submodule ℂ (EH n))) : EH n)) h
      simpa [rsM_apply] using this
    have h2 : single a b (1 : ℂ) = 0 := (map_eq_zero_iff _ (toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).injective).mp h1
    have h3 := congrFun (congrFun h2 a) b
    simp at h3

end ReciprocityTheory.ChartRestriction.DS
