import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.FromHCA
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

section Alg

variable {k : ℕ}

lemma fh_Jm_allPos : Jm (fun _ : Fin k => true) = 1 := by
  ext i j
  simp [Jm, Matrix.diagonal, Matrix.one_apply]

lemma fh_decomp (Z : Matrix (Fin k) (Fin k) ℂ) : ∃ Z₁ Z₂ : Matrix (Fin k) (Fin k) ℂ,
    inK (fun _ : Fin k => true) Z₁ ∧ inK (fun _ : Fin k => true) Z₂ ∧ Z = Z₁ + Complex.I • Z₂ := by
  have hJ : Jm (fun _ : Fin k => true) = 1 := fh_Jm_allPos
  have hh : star (1 / 2 : ℂ) = 1 / 2 := by simp
  have hi : star (-(Complex.I / 2)) = Complex.I / 2 := by
    simp [Complex.star_def, Complex.conj_I, neg_div]
  refine ⟨(1 / 2 : ℂ) • (Z - Zᴴ), (-(Complex.I / 2)) • (Z + Zᴴ), ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · simp only [inG, hJ, Matrix.mul_one, Matrix.one_mul]
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose, hh]
    module
  · rw [hJ, Matrix.mul_one, Matrix.one_mul]
  · simp only [inG, hJ, Matrix.mul_one, Matrix.one_mul]
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, hi]
    module
  · rw [hJ, Matrix.mul_one, Matrix.one_mul]
  · have hI : Complex.I * (-(Complex.I / 2)) = 1 / 2 := by
      rw [mul_neg, mul_div_assoc', Complex.I_mul_I]
      ring
    rw [smul_smul, hI]
    module

lemma fh_diag_conj (d : Fin k → ℂ) (a b : Fin k) :
    Matrix.diagonal d * Matrix.single a b 1 * star (Matrix.diagonal d) =
      (d a * star (d b)) • Matrix.single a b 1 := by
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simp [smul_eq_mul]
  · simp

lemma fh_not_cdom {Λ : Fin k → ℝ} {a b : Fin k} (hab : a < b) :
    ¬ Formalism.MainNotions.S.CDom (fun _ : Fin k => true) (Λ + Pi.single a 1 - Pi.single b 1) Λ := by
  rintro ⟨c, hc, hsum⟩
  let f : (Fin k → ℝ) →ₗ[ℝ] ℝ := ∑ i : Fin k, ((i : ℕ) : ℝ) • LinearMap.proj i
  have hf : ∀ x, f x = ∑ i : Fin k, ((i : ℕ) : ℝ) * x i := fun x => by simp [f]
  have hs : ∀ j : Fin k, f (Pi.single j 1) = ((j : ℕ) : ℝ) := fun j => by
    rw [hf]
    simp [Pi.single_apply]
  have hL : Λ - (Λ + Pi.single a 1 - Pi.single b 1) = Pi.single b 1 - Pi.single a 1 := by abel
  have h1 := congrArg f hsum
  rw [hL, map_sub, hs, hs] at h1
  simp only [map_sum, map_smul, Formalism.REAL.root, map_sub, hs, smul_eq_mul] at h1
  have hneg : ∑ x : Fin k, ∑ y : Fin k, (c x y : ℝ) * (((x : ℕ) : ℝ) - ((y : ℕ) : ℝ)) ≤ 0 := by
    refine Finset.sum_nonpos fun x _ => Finset.sum_nonpos fun y _ => ?_
    by_cases h0 : c x y = 0
    · simp [h0]
    · have hxy : ((x : ℕ) : ℝ) < ((y : ℕ) : ℝ) := Nat.cast_lt.mpr (hc x y h0).1
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have hab' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := Nat.cast_lt.mpr hab
  linarith

end Alg

section Tau

variable {k : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma fh_unitary (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H))
    (hU : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k)) π) (g : KG (fun _ : Fin k => true)) :
    π (toMK g) ∈ unitary (H →L[ℂ] H) := by
  have hmem : toMK g ∈ Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k) := g.1.2
  have hiso := hU.2.1 _ hmem
  have hmul : ∀ a b : KG (fun _ : Fin k => true), π (toMK (a * b)) = π (toMK a) * π (toMK b) :=
    fun a b => hU.1.2 _ a.1.2 _ b.1.2
  have hone : π (toMK (1 : KG (fun _ : Fin k => true))) = 1 := hU.1.1
  have hTR : π (toMK g) * π (toMK g⁻¹) = 1 := by rw [← hmul, mul_inv_cancel, hone]
  have h1 : star (π (toMK g)) * π (toMK g) = 1 := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp hiso
  have hstar : star (π (toMK g)) = π (toMK g⁻¹) := by
    calc star (π (toMK g)) = star (π (toMK g)) * (π (toMK g) * π (toMK g⁻¹)) := by rw [hTR, mul_one]
      _ = π (toMK g⁻¹) := by rw [← mul_assoc, h1, one_mul]
  exact Unitary.mem_iff.mpr ⟨h1, by rw [hstar, hTR]⟩

def fhTau (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H))
    (hU : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k)) π) :
    KG (fun _ : Fin k => true) →* unitary (H →L[ℂ] H) where
  toFun g := ⟨π (toMK g), fh_unitary π hU g⟩
  map_one' := Subtype.ext hU.1.1
  map_mul' a b := Subtype.ext (hU.1.2 _ (a : UJ (fun _ : Fin k => true)).2 _ (b : UJ (fun _ : Fin k => true)).2)

lemma fhTau_coe (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H))
    (hU : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k)) π) (g : KG (fun _ : Fin k => true)) :
    ((fhTau π hU g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) = π (toMK g) := rfl

lemma fhTau_cont [FiniteDimensional ℂ H] (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H))
    (hU : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k)) π) : Continuous (fhTau π hU) := by
  apply continuous_induced_rng.2
  change Continuous fun g : KG (fun _ : Fin k => true) => π (toMK g)
  rw [continuous_clm_apply]
  intro v
  have hc : Continuous fun g : KG (fun _ : Fin k => true) => toMK g :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  exact (hU.2.2 v).comp_continuous hc (fun g => g.1.2)

end Tau

section Der

variable {k : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (τ : KG (fun _ : Fin k => true) →* unitary (H →L[ℂ] H))
  (dτ : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] (H →L[ℂ] H))
  (hder : ∀ X, inK (fun _ : Fin k => true) X → ∀ γ : ℝ → KG (fun _ : Fin k => true),
    (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      HasDerivAt (fun t => ((τ (γ t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H)) (dτ X) 0)
  (σ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H))
  (hσ : ∀ g : KG (fun _ : Fin k => true), σ (toMK g) = ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H))

include hder in
lemma fh_conj (g : KG (fun _ : Fin k => true)) {Y : Matrix (Fin k) (Fin k) ℂ}
    (hY : inK (fun _ : Fin k => true) Y) :
    ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) * dτ Y * star ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) =
      dτ (toMK g * Y * star (toMK g)) := by
  have hJ : Jm (fun _ : Fin k => true) = 1 := fh_Jm_allPos
  obtain ⟨-, hγ, -⟩ := kcurve_spec (fun _ : Fin k => true) hY
  have hKs : toMK g ∈ Formalism.REAL.Kset (fun _ : Fin k => true) := g.2
  have hun : star (toMK g) * toMK g = 1 := Matrix.mem_unitaryGroup_iff'.mp hKs.1
  have hinv : toMK g * toMK g⁻¹ = 1 := by exact Units.mul_inv g.1.1
  have hg : star (toMK g) = toMK g⁻¹ := by
    calc star (toMK g) = star (toMK g) * (toMK g * toMK g⁻¹) := by rw [hinv, Matrix.mul_one]
      _ = toMK g⁻¹ := by rw [← Matrix.mul_assoc, hun, Matrix.one_mul]
  have hc : inK (fun _ : Fin k => true) (toMK g * Y * star (toMK g)) := by
    obtain ⟨h1, -⟩ := hY
    simp only [inG, hJ, Matrix.mul_one, Matrix.one_mul] at h1
    refine ⟨?_, by rw [hJ, Matrix.mul_one, Matrix.one_mul]⟩
    simp only [inG, hJ, Matrix.mul_one, Matrix.one_mul]
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc, ← Matrix.add_mul, ← Matrix.mul_add, h1,
      Matrix.mul_zero, Matrix.zero_mul]
  have hδ : ∀ t : ℝ, toMK (g * kcurve (fun _ : Fin k => true) Y t * g⁻¹) =
      NormedSpace.exp ((t : ℂ) • (toMK g * Y * star (toMK g))) := by
    intro t
    have e := Matrix.exp_units_conj g.1.1 ((t : ℂ) • Y)
    calc toMK (g * kcurve (fun _ : Fin k => true) Y t * g⁻¹)
        = toMK g * NormedSpace.exp ((t : ℂ) • Y) * toMK g⁻¹ := by rw [← hγ t]; rfl
      _ = NormedSpace.exp ((t : ℂ) • (toMK g * Y * star (toMK g))) := by
        rw [hg, ← Matrix.smul_mul, ← Matrix.mul_smul]
        exact e.symm
  have hU' : ((τ g⁻¹ : unitary (H →L[ℂ] H)) : H →L[ℂ] H) = star ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) := by
    rw [map_inv, ← Unitary.star_eq_inv, Unitary.coe_star]
  have hd1 := hder _ hc (fun t => g * kcurve (fun _ : Fin k => true) Y t * g⁻¹) hδ
  have h0 := hder Y hY _ hγ
  have heq : (fun t => ((τ (g * kcurve (fun _ : Fin k => true) Y t * g⁻¹) : unitary (H →L[ℂ] H)) : H →L[ℂ] H)) =
      fun t => ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) *
        ((τ (kcurve (fun _ : Fin k => true) Y t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) *
        star ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) := by
    funext t
    rw [map_mul, map_mul, ← hU']
    rfl
  have hd2 := (h0.const_mul ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H)).mul_const
    (star ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H))
  rw [← heq] at hd2
  exact hd2.unique hd1

include hder in
lemma fh_conj_all (g : KG (fun _ : Fin k => true)) (Z : Matrix (Fin k) (Fin k) ℂ) :
    ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) * dτ Z * star ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) =
      dτ (toMK g * Z * star (toMK g)) := by
  obtain ⟨Z₁, Z₂, h1, h2, rfl⟩ := fh_decomp Z
  rw [map_add, map_smul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, fh_conj τ dτ hder g h1,
    fh_conj τ dτ hder g h2, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, map_add,
    map_smul]

include hder hσ in
lemma fh_dτ_of_wt {μ : Fin k → ℝ} {v : H}
    (hv : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (fun _ : Fin k => true)) σ μ v) (a : Fin k) :
    dτ (Matrix.single a a 1) v = ((μ a : ℝ) : ℂ) • v := by
  have hJ : Jm (fun _ : Fin k => true) = 1 := fh_Jm_allPos
  have hX : inK (fun _ : Fin k => true) (Complex.I • Matrix.single a a 1) := by
    refine ⟨?_, by rw [hJ, Matrix.mul_one, Matrix.one_mul]⟩
    simp only [inG, hJ, Matrix.mul_one, Matrix.one_mul]
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_single, star_one]
    simp [Complex.star_def, Complex.conj_I]
  obtain ⟨-, hγ, -⟩ := kcurve_spec (fun _ : Fin k => true) hX
  have hd1 := hder _ hX _ hγ
  have hd2 : HasDerivAt
      (fun t => ((τ (kcurve (fun _ : Fin k => true) (Complex.I • Matrix.single a a 1) t) :
        unitary (H →L[ℂ] H)) : H →L[ℂ] H) v) (dτ (Complex.I • Matrix.single a a 1) v) 0 :=
    ((ContinuousLinearMap.apply ℂ H v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd1
  let θ : ℝ → Fin k → ℝ := fun t b => if b = a then t else 0
  have hdiag : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • (Complex.I • Matrix.single a a (1 : ℂ))) =
      Matrix.diagonal (fun b => Complex.exp (((θ t b : ℝ) : ℂ) * Complex.I)) := by
    intro t
    have e1 : (t : ℂ) • (Complex.I • Matrix.single a a (1 : ℂ)) =
        Matrix.diagonal (fun b => ((θ t b : ℝ) : ℂ) * Complex.I) := by
      ext i j
      rcases eq_or_ne i j with rfl | hij
      · by_cases hia : i = a
        · subst hia
          simp [θ, Matrix.diagonal_apply, Matrix.single_apply, mul_comm]
        · simp [θ, Matrix.diagonal_apply, Matrix.single_apply, hia, Ne.symm hia]
      · simp [θ, Matrix.diagonal_apply, Matrix.single_apply, hij]
        rintro rfl rfl
        exact absurd rfl hij
    rw [e1, Matrix.exp_diagonal, Pi.exp_def, Complex.exp_eq_exp_ℂ]
  have hval : ∀ t : ℝ, ((τ (kcurve (fun _ : Fin k => true) (Complex.I • Matrix.single a a 1) t) :
      unitary (H →L[ℂ] H)) : H →L[ℂ] H) v = Complex.exp (((μ a * t : ℝ) : ℂ) * Complex.I) • v := by
    intro t
    have hm : Matrix.diagonal (fun b => Complex.exp (((θ t b : ℝ) : ℂ) * Complex.I)) ∈
        Formalism.REAL.Kset (fun _ : Fin k => true) := by
      rw [← hdiag t, ← hγ t]
      exact (kcurve (fun _ : Fin k => true) (Complex.I • Matrix.single a a 1) t).2
    rw [← hσ, hγ t, hdiag t, hv (θ t) hm]
    congr 3
    simp [θ]
  have hd3 : HasDerivAt (fun t : ℝ => Complex.exp (((μ a * t : ℝ) : ℂ) * Complex.I) • v)
      ((Complex.exp (((μ a * 0 : ℝ) : ℂ) * Complex.I) * (((μ a * 1 : ℝ) : ℂ) * Complex.I)) • v) 0 :=
    ((((hasDerivAt_id (0 : ℝ)).const_mul (μ a)).ofReal_comp.mul_const Complex.I).cexp).smul_const v
  have hfun : (fun t => ((τ (kcurve (fun _ : Fin k => true) (Complex.I • Matrix.single a a 1) t) :
      unitary (H →L[ℂ] H)) : H →L[ℂ] H) v) =
      fun t : ℝ => Complex.exp (((μ a * t : ℝ) : ℂ) * Complex.I) • v := funext hval
  rw [hfun] at hd2
  have hu := hd2.unique hd3
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, mul_one] at hu
  rw [map_smul, ContinuousLinearMap.smul_apply, mul_comm, mul_smul] at hu
  exact smul_right_injective H Complex.I_ne_zero hu

include hder hσ in
lemma fh_hw {Λ : Fin k → ℝ}
    (hK5 : ∀ (μ : Fin k → ℝ) (v : H), v ∈ (⊤ : Submodule ℂ H) → v ≠ 0 →
      Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (fun _ : Fin k => true)) σ μ v → Formalism.MainNotions.S.CDom (fun _ : Fin k => true) μ Λ)
    {w : H} (hw : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (fun _ : Fin k => true)) σ Λ w) (a b : Fin k) (hab : a < b) :
    dτ (Matrix.single a b 1) w = 0 := by
  have hJ : Jm (fun _ : Fin k => true) = 1 := fh_Jm_allPos
  by_contra hne
  refine fh_not_cdom hab (hK5 _ (dτ (Matrix.single a b 1) w) Submodule.mem_top hne ?_)
  intro θ hθ
  set d : Fin k → ℂ := fun c => Complex.exp ((θ c : ℂ) * Complex.I) with hd
  have hD1 : star (Matrix.diagonal d) * Matrix.diagonal d = 1 := Matrix.mem_unitaryGroup_iff'.mp hθ.1
  have hD2 : Matrix.diagonal d * star (Matrix.diagonal d) = 1 := Matrix.mem_unitaryGroup_iff.mp hθ.1
  let u0 : (Matrix (Fin k) (Fin k) ℂ)ˣ := ⟨Matrix.diagonal d, star (Matrix.diagonal d), hD2, hD1⟩
  have huJ : u0 ∈ UJ (fun _ : Fin k => true) := by
    show (Matrix.diagonal d)ᴴ * Jm (fun _ : Fin k => true) * Matrix.diagonal d = Jm (fun _ : Fin k => true)
    rw [hJ, Matrix.mul_one, ← Matrix.star_eq_conjTranspose, hD1]
  let g0 : UJ (fun _ : Fin k => true) := ⟨u0, huJ⟩
  let g : KG (fun _ : Fin k => true) := ⟨g0, hθ⟩
  have hg : toMK g = Matrix.diagonal d := rfl
  have hU1 : star ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) * ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) = 1 :=
    Unitary.star_mul_self_of_mem (τ g).2
  have hcomm : ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) * dτ (Matrix.single a b 1) =
      dτ (toMK g * Matrix.single a b 1 * star (toMK g)) * ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) := by
    rw [← fh_conj_all τ dτ hder g, mul_assoc _ (star _) _, hU1, mul_one]
  have h3 : ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) w =
      Complex.exp (((∑ c, Λ c * θ c : ℝ) : ℂ) * Complex.I) • w := by
    rw [← hσ, hg]
    exact hw θ hθ
  have h2 := congrArg (fun T : H →L[ℂ] H => T w) hcomm
  simp only [ContinuousLinearMap.mul_apply] at h2
  rw [hg, fh_diag_conj, h3] at h2
  rw [← hg, hσ, h2, map_smul, LinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_smul]
  congr 1
  have hs : ∑ c, (Λ + Pi.single a 1 - Pi.single b 1 : Fin k → ℝ) c * θ c = (∑ c, Λ c * θ c) + θ a - θ b := by
    simp [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Pi.single_apply]
  have hst : star (d b) = Complex.exp (-((θ b : ℂ) * Complex.I)) := by
    rw [hd, Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring_nf
  rw [hs, hst, hd]
  simp only
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end Der

end ReciprocityTheory.ChartRestriction.DS.HW
