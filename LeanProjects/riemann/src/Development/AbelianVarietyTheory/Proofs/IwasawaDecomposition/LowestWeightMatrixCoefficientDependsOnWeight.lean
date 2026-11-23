import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolRepOfIsTau
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompComplexifiedMaxCompact
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactExponentialSurjective

open Matrix Formalism.MainNotions.S GlobalTheory.JointHarm

noncomputable section

namespace GlobalTheory.JointHarm.Sph

variable {n : ℕ} {ε : Fin n → Bool} {μ : Fin n → ℝ}

theorem entire_eq_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h : ∀ t : ℝ, f t = 0) (z : ℂ) : f z = 0 := by
  have ha : AnalyticOnNhd ℂ f Set.univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  refine ha.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (Set.mem_univ 0) ?_
    (Set.mem_univ z)
  have ht : Filter.Tendsto (fun t : ℝ => (t : ℂ)) (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := Complex.continuous_ofReal.tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ht
  exact ht.frequently (Filter.Eventually.of_forall h).frequently

theorem diag_mem {d : Fin n → ℂ} (hd : ∀ a, d a ≠ 0) : Matrix.diagonal d ∈ GlobalTheory.Dec.KC ε := by
  refine ⟨?_, by simp [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, mul_comm]⟩
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  exact fun a _ => hd a

theorem mul_mem {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ GlobalTheory.Dec.KC ε) (hb : b ∈ GlobalTheory.Dec.KC ε) :
    a * b ∈ GlobalTheory.Dec.KC ε :=
  ⟨ha.1.mul hb.1, by rw [Matrix.mul_assoc, hb.2, ← Matrix.mul_assoc, ha.2, Matrix.mul_assoc]⟩

theorem ct_mem {a : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ GlobalTheory.Dec.KC ε) : aᴴ ∈ GlobalTheory.Dec.KC ε := by
  refine ⟨by simpa [Matrix.star_eq_conjTranspose] using ha.1.star, ?_⟩
  have := congrArg Matrix.conjTranspose ha.2
  simp only [Matrix.conjTranspose_mul, Formalism.REAL.Jm_conjTranspose] at this
  exact this.symm

section One

variable {P : Type} [AddCommGroup P] [Module ℂ P] {B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ}
  {π : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P}

theorem diff_curve (h : IsHolRep ε B π) {c : ℂ → Matrix (Fin n) (Fin n) ℂ}
    (hc : ∀ i j, Differentiable ℂ fun z => c z i j) (hm : ∀ z, c z ∈ GlobalTheory.Dec.KC ε) (x y : P) :
    Differentiable ℂ fun z => B x (π (c z) y) := by
  have h1 : Differentiable ℂ fun z => (fun i j => c z i j : Fin n → Fin n → ℂ) :=
    differentiable_pi.2 fun i => differentiable_pi.2 fun j => hc i j
  have := (h.2.2.2.2 x y).comp (s := Set.univ) h1.differentiableOn (fun z _ => hm z)
  exact differentiableOn_univ.1 this

theorem real_torus (h : IsHolRep ε B π) {x : P} (hx : IsBottom ε π μ x) (s : Fin n → ℝ) :
    π (Matrix.diagonal fun a => Complex.exp (s a : ℂ)) x = Complex.exp ((∑ a, μ a * s a : ℝ) : ℂ) • x := by
  rw [← sub_eq_zero]
  apply h.1
  generalize hw : π (Matrix.diagonal fun a => Complex.exp (s a : ℂ)) x -
    Complex.exp ((∑ a, μ a * s a : ℝ) : ℂ) • x = w
  have hd := diff_curve h (c := fun z => Matrix.diagonal fun a => Complex.exp (z * s a * Complex.I))
    (fun i j => by
      by_cases e : i = j
      · subst e; simp only [Matrix.diagonal_apply_eq]; fun_prop
      · simp only [Matrix.diagonal_apply_ne _ e]; fun_prop)
    (fun z => diag_mem fun a => Complex.exp_ne_zero _) w x
  have h0 := entire_eq_zero (f := fun z => B w (π (Matrix.diagonal fun a => Complex.exp (z * s a * Complex.I)) x) -
      Complex.exp (z * ((∑ a, μ a * s a : ℝ) : ℂ) * Complex.I) * B w x) (hd.sub (by fun_prop))
    (fun t => by
      have := hx.2 (fun a => t * s a)
      have e : (∑ a, μ a * (t * s a)) = t * ∑ a, μ a * s a := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
      rw [e] at this
      simp only [Complex.ofReal_mul] at this
      simp only [this, map_smul, smul_eq_mul, sub_self]) (-Complex.I)
  have e : ∀ u : ℂ, -Complex.I * u * Complex.I = u := fun u => by
    linear_combination (-u) * Complex.I_mul_I
  simp only [e] at h0
  conv_lhs => enter [2]; rw [← hw]
  rw [map_sub, map_smul, smul_eq_mul, h0]

theorem borel {b : Matrix (Fin n) (Fin n) ℂ} (hb : b ∈ GlobalTheory.Dec.KC ε) (hl : GlobalTheory.Dec.IsLo b)
    (hp : ∀ i, b i i = Complex.exp (Real.log (b i i).re : ℝ))
    (h : IsHolRep ε B π) {x : P} (hx : IsBottom ε π μ x) :
    π b x = Complex.exp ((∑ a, μ a * Real.log (b a a).re : ℝ) : ℂ) • x := by
  have hne : ∀ i, b i i ≠ 0 := fun i => by rw [hp i]; exact Complex.exp_ne_zero _
  have hu : Matrix.diagonal (fun a => (b a a)⁻¹) * b ∈ GlobalTheory.Dec.KC ε :=
    mul_mem (diag_mem fun a => inv_ne_zero (hne a)) hb
  have hlu : IsLoUni (Matrix.diagonal (fun a => (b a a)⁻¹) * b) := fun i j =>
    ⟨fun hij => by rw [Matrix.diagonal_mul, hl i j hij, mul_zero],
      fun hij => by subst hij; rw [Matrix.diagonal_mul, inv_mul_cancel₀ (hne i)]⟩
  have e : b = Matrix.diagonal (fun a => Complex.exp (Real.log (b a a).re : ℝ)) *
      (Matrix.diagonal (fun a => (b a a)⁻¹) * b) := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.diagonal_mul, ← hp i, mul_inv_cancel_left₀ (hne i)]
  conv_lhs => rw [e]
  rw [h.2.2.1 _ (diag_mem fun a => Complex.exp_ne_zero _) _ hu, Module.End.mul_apply, hx.1 _ hu hlu,
    real_torus h hx]

end One

open scoped ComplexOrder in

theorem gram {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ GlobalTheory.Dec.KC ε) (μ : Fin n → ℝ) :
    ∃ c : ℂ, ∀ (P : Type) [AddCommGroup P] [Module ℂ P] (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ)
      (π : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P) (x y : P), IsHolRep ε B π → IsBottom ε π μ x →
      IsBottom ε π μ y → B x (π (gᴴ * g) y) = c * B x y := by
  obtain ⟨k, b, hk, hb, hl, hp, rfl⟩ := GlobalTheory.Dec.IwKC.exists_decomp ε hg
  have hp' : ∀ i, b i i = Complex.exp (Real.log (b i i).re : ℝ) := fun i => by
    have := Complex.pos_iff.1 (hp i)
    rw [← Complex.ofReal_exp, Real.exp_log this.1]
    exact Complex.ext rfl (by simpa using this.2.symm)
  refine ⟨star (Complex.exp ((∑ a, μ a * Real.log (b a a).re : ℝ) : ℂ)) *
    Complex.exp ((∑ a, μ a * Real.log (b a a).re : ℝ) : ℂ), fun P _ _ B π x y h hx hy => ?_⟩
  rw [GlobalTheory.Dec.IwKC.gram_unitary_mul hk.1, h.2.2.1 _ (ct_mem hb) _ hb, Module.End.mul_apply,
    ← h.2.2.2.1 _ hb, borel hb hl hp' h hx, borel hb hl hp' h hy]
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, starRingEnd_apply]
  ring

section Exp

open scoped Matrix.Norms.Operator

theorem exp_mem {H : Matrix (Fin n) (Fin n) ℂ} (hJ : H * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * H) (z : ℂ) :
    NormedSpace.exp (z • H) ∈ GlobalTheory.Dec.KC ε := by
  refine ⟨Matrix.isUnit_exp _, ?_⟩
  have : Commute (z • H) (Formalism.REAL.Jm ε) := Commute.smul_left hJ z
  exact this.exp_left.eq

theorem exp_diff (H : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    Differentiable ℂ fun z : ℂ => NormedSpace.exp (z • H) i j := by
  have h1 : Differentiable ℂ fun z : ℂ => NormedSpace.exp (z • H) :=
    fun z => (hasDerivAt_exp_smul_const H z).differentiableAt
  exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)).differentiable.comp h1

theorem exp_gram {H : Matrix (Fin n) (Fin n) ℂ} (hH : Hᴴ = H) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • H) =
      (NormedSpace.exp (((t : ℂ) / 2) • H))ᴴ * NormedSpace.exp (((t : ℂ) / 2) • H) := by
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hH]
  have e : star ((t : ℂ) / 2) = (t : ℂ) / 2 := by simp
  rw [e, ← Matrix.exp_add_of_commute _ _ (Commute.refl _), ← add_smul, add_halves]

end Exp

theorem coeff_eq (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (P : Type) [AddCommGroup P] [Module ℂ P]
    (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ) (π : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P) (P' : Type) [AddCommGroup P']
    [Module ℂ P'] (B' : P' →ₗ⋆[ℂ] P' →ₗ[ℂ] ℂ) (π' : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P') (x y : P)
    (x' y' : P') (h : IsHolRep ε B π) (h' : IsHolRep ε B' π') (hx : IsBottom ε π μ x) (hy : IsBottom ε π μ y)
    (hx' : IsBottom ε π' μ x') (hy' : IsBottom ε π' μ y') :
    ∀ k ∈ Formalism.REAL.Kset ε, B x (π k y) * B' x' y' = B x y * B' x' (π' k y') := by
  intro k hk
  obtain ⟨Y, ⟨hG, hY⟩, rfl, -⟩ := Formalism.REAL.compact_exists_log_bounded ε k hk
  have hs : Yᴴ = -Y := by
    have h1 : (Yᴴ + Y) * Formalism.REAL.Jm ε = 0 := by
      rw [Matrix.add_mul, hY]; exact hG
    have h2 := congrArg (· * Formalism.REAL.Jm ε) h1
    simp only [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one, Matrix.zero_mul] at h2
    exact eq_neg_of_add_eq_zero_left h2
  have hH : ((-Complex.I) • Y)ᴴ = (-Complex.I) • Y := by
    rw [Matrix.conjTranspose_smul, hs]; simp
  have hJ : ((-Complex.I) • Y) * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * ((-Complex.I) • Y) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hY]
  have h0 := entire_eq_zero (f := fun z => B x (π (NormedSpace.exp (z • (-Complex.I) • Y)) y) * B' x' y' -
      B x y * B' x' (π' (NormedSpace.exp (z • (-Complex.I) • Y)) y'))
    (((diff_curve h (exp_diff _) (exp_mem hJ) x y).mul_const _).sub
      ((diff_curve h' (exp_diff _) (exp_mem hJ) x' y').const_mul _))
    (fun t => by
      obtain ⟨c, hc⟩ := gram (exp_mem hJ ((t : ℂ) / 2)) μ
      simp only [exp_gram hH t, hc P B π x y h hx hy, hc P' B' π' x' y' h' hx' hy']
      ring) Complex.I
  have e : Complex.I • (-Complex.I) • Y = Y := by rw [smul_smul]; simp
  simp only [e] at h0
  exact sub_eq_zero.1 h0

end GlobalTheory.JointHarm.Sph

end
