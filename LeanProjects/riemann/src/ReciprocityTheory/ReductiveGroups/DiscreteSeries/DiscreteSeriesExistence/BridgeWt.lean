import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bridge

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def bwtDiag (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun a => (θ a : ℂ) * Complex.I

theorem bwtDiag_inG (ε : Fin n → Bool) (θ : Fin n → ℝ) : inG ε (bwtDiag θ) := by
  show (bwtDiag θ)ᴴ * Jm ε + Jm ε * bwtDiag θ = 0
  rw [bwtDiag, Jm, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, ← Matrix.diagonal_zero]
  congr 1
  funext a
  simp only [Pi.add_apply, Pi.star_apply, Complex.star_def, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  ring

theorem bwt_exp (θ : Fin n → ℝ) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • bwtDiag θ) =
      Matrix.diagonal (fun a => Complex.exp (((t * θ a : ℝ) : ℂ) * Complex.I)) := by
  have h : (t : ℂ) • bwtDiag θ = Matrix.diagonal (fun a => (t : ℂ) * ((θ a : ℂ) * Complex.I)) := by
    rw [bwtDiag]
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal_apply, h]
  rw [h, Matrix.exp_diagonal]
  congr 1
  funext a
  rw [Pi.exp_def]
  dsimp only
  rw [← Complex.exp_eq_exp_ℂ]
  congr 1
  push_cast
  ring

theorem bwt_diag_mem_Kset (ε : Fin n → Bool) (θ : Fin n → ℝ) :
    Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    simp only [Pi.star_apply, Complex.star_def]
    rw [← Complex.exp_conj, ← Complex.exp_add]
    simp
  · rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    ring

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem bwt_actM_diag (E : Fin n → Fin n → Module.End ℂ M) (d : Fin n → ℂ) :
    actM E (Matrix.diagonal d) = ∑ a, d a • E a a := by
  simp [actM, Matrix.diagonal_apply, ite_smul]

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem bwt_actM_apply (θ : Fin n → ℝ) (v : D) :
    ((actM E (bwtDiag θ) v : D) : H) = ∑ a, ((θ a : ℂ) * Complex.I) • ((E a a v : D) : H) := by
  rw [bwtDiag, bwt_actM_diag]
  simp

private theorem exp_smul_bwtDiag_mem_UJset (ε : Fin n → Bool) (θ : Fin n → ℝ) (s : ℝ) :
    NormedSpace.exp ((s : ℂ) • bwtDiag θ) ∈ UJset ε := by
  have hK := bwt_diag_mem_Kset ε (fun a => s * θ a)
  obtain ⟨hu, hc⟩ := hK
  rw [bwt_exp]
  have hu' := Matrix.mem_unitaryGroup_iff'.1 hu
  have hJJ : Jm ε = Formalism.REAL.Jm ε := rfl
  show inUJ ε _
  unfold inUJ
  rw [hJJ, Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose, hu',
    Matrix.one_mul]

private theorem apply_one_eq_exp_smul_of_hasDerivAt_smul {F : ℝ → H} {c : ℂ} (hF : ∀ s, HasDerivAt F (c • F s) s) :
    F 1 = Complex.exp c • F 0 := by
  have hG : ∀ s : ℝ, HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * -c) • F t) 0 s := by
    intro s
    have h1 := (((hasDerivAt_id' s).ofReal_comp).mul_const (-c)).cexp
    refine (h1.smul (hF s)).congr_deriv ?_
    rw [smul_smul, ← add_smul]
    simp
  have hconst := is_const_of_deriv_eq_zero (fun s => (hG s).differentiableAt)
    (fun s => (hG s).deriv) 1 0
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, neg_zero,
    Complex.exp_zero, one_smul] at hconst
  rw [← hconst, smul_smul, ← Complex.exp_add]
  simp

private theorem hasDerivAt_of_shift_of_hasDerivAt_zero {G : ℝ → H} {L : H} (T : ℝ → (H →L[ℂ] H))
    (hG0 : HasDerivAt G L 0) (hshift : ∀ s t, G (s + t) = T s (G t)) (s : ℝ) :
    HasDerivAt G (T s L) s := by
  have h1 := ((T s).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hG0
  have h2 : HasDerivAt (fun t => G (s + t)) (T s L) 0 := by
    convert h1 using 1 <;> first | rfl | (funext t; exact hshift s t)
  have h3 : HasDerivAt (fun t => G (s + t)) (T s L) (s - s) := by rwa [sub_self]
  have h4 := HasDerivAt.scomp (h := fun x : ℝ => x - s) s h3 ((hasDerivAt_id' s).sub_const s)
  convert h4 using 1 <;> first | (funext x; simp) | simp

theorem isWtOn_iff (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (v : D) (μ : Fin n → ℝ) :
    Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ μ (v : H) ↔ ∀ a, E a a v = ((μ a : ℝ) : ℂ) • v := by
  constructor
  · intro hw a
    have hder := hD.deriv _ (bwtDiag_inG ε (Pi.single a 1)) v
    have hfun : (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • bwtDiag (Pi.single a 1))) (v : H)) =
        fun t : ℝ => Complex.exp ((t : ℂ) * ((μ a : ℂ) * Complex.I)) • (v : H) := by
      funext t
      have h := hw (fun b => t * (Pi.single a (1 : ℝ) : Fin n → ℝ) b) (bwt_diag_mem_Kset ε _)
      rw [bwt_exp, h]
      congr 2
      simp [Pi.single_apply] <;> ring
    rw [hfun, bwt_actM_apply] at hder
    have hexp : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * ((μ a : ℂ) * Complex.I)) • (v : H))
        (((μ a : ℂ) * Complex.I) • (v : H)) 0 := by
      have := ((((hasDerivAt_id' (0 : ℝ)).ofReal_comp).mul_const
        ((μ a : ℂ) * Complex.I)).cexp).smul_const (v : H)
      convert this using 1
      simp
    have heq := hder.unique hexp
    rw [Finset.sum_eq_single a (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)] at heq
    simp only [Pi.single_eq_same, Complex.ofReal_one, one_mul] at heq
    apply Subtype.ext
    have h2 : Complex.I • ((E a a v : D) : H) = Complex.I • (((μ a : ℝ) : ℂ) • (v : H)) := by
      rw [heq, smul_smul, mul_comm]
    exact smul_right_injective H Complex.I_ne_zero h2
  · intro hE θ _
    have hlam : ((actM E (bwtDiag θ) v : D) : H) =
        (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • (v : H) := by
      rw [bwt_actM_apply]
      have hterm : ∀ a, ((θ a : ℂ) * Complex.I) • ((E a a v : D) : H) =
          (((θ a : ℂ) * Complex.I) * (μ a : ℂ)) • (v : H) := by
        intro a
        rw [hE a, Submodule.coe_smul, smul_smul]
      rw [Finset.sum_congr rfl fun a _ => hterm a, ← Finset.sum_smul]
      congr 1
      push_cast
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => by ring
    have h0 := hD.deriv _ (bwtDiag_inG ε θ) v
    rw [hlam] at h0
    have hshift : ∀ s t : ℝ, σ (NormedSpace.exp (((s + t : ℝ) : ℂ) • bwtDiag θ)) (v : H) =
        σ (NormedSpace.exp ((s : ℂ) • bwtDiag θ)) (σ (NormedSpace.exp ((t : ℂ) • bwtDiag θ)) (v : H)) := by
      intro s t
      have hmul : NormedSpace.exp (((s + t : ℝ) : ℂ) • bwtDiag θ) =
          NormedSpace.exp ((s : ℂ) • bwtDiag θ) * NormedSpace.exp ((t : ℂ) • bwtDiag θ) := by
        rw [Complex.ofReal_add, add_smul]
        exact Matrix.exp_add_of_commute _ _ (((Commute.refl (bwtDiag θ)).smul_left _).smul_right _)
      rw [hmul, hσ.1.2 _ (exp_smul_bwtDiag_mem_UJset ε θ s) _ (exp_smul_bwtDiag_mem_UJset ε θ t)]
      rfl
    have hF : ∀ s : ℝ, HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • bwtDiag θ)) (v : H))
        ((((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) •
          σ (NormedSpace.exp ((s : ℂ) • bwtDiag θ)) (v : H)) s := by
      intro s
      have := hasDerivAt_of_shift_of_hasDerivAt_zero (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • bwtDiag θ))) h0 hshift s
      rwa [map_smul] at this
    have hode := apply_one_eq_exp_smul_of_hasDerivAt_smul hF
    have e1 : NormedSpace.exp (((1 : ℝ) : ℂ) • bwtDiag θ) =
        Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) := by
      rw [bwt_exp]
      simp
    have e0 : NormedSpace.exp (((0 : ℝ) : ℂ) • bwtDiag θ) = 1 := by simp
    rw [e1, e0, hσ.1.1] at hode
    simpa using hode

end Rep

end ReciprocityTheory.ChartRestriction.DS
