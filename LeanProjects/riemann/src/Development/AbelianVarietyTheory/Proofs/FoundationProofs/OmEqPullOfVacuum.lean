import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalPointsIntegralPointsMembership
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaLatticePointMemThetaLatticeOfAdelic

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.NormSum.RatExtend

variable {D : D7}

section Theta

variable {T : Tor D} {N N' : ℕ}

theorem Hf_add_left (x y w : VC D N N') : Hf D T (x + y) w = Hf D T x w + Hf D T y w := by
  simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]

theorem Hf_smul_left (c : ℂ) (x w : VC D N N') : Hf D T (c • x) w = c * Hf D T x w := by
  simp only [Hf, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, mul_div_assoc]

theorem Hf_conj (x w : VC D N N') : Hf D T w x = (starRingEnd ℂ) (Hf D T x w) := by
  simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal, mul_comm]

theorem Hf_nsmul_left (n : ℕ) (x w : VC D N N') : Hf D T (n • x) w = n * Hf D T x w := by
  rw [← Nat.cast_smul_eq_nsmul ℂ, Hf_smul_left]

theorem Hf_nsmul_right (n : ℕ) (x w : VC D N N') : Hf D T x (n • w) = n * Hf D T x w := by
  rw [Hf_conj, Hf_nsmul_left, map_mul, ← Hf_conj, map_natCast]

theorem qH_nsmul (n : ℕ) (x : VC D N N') : qH D T (n • x) = n ^ 2 * qH D T x := by
  rw [qH, qH, Hf_nsmul_left, Hf_nsmul_right, ← mul_assoc, ← Nat.cast_mul, ← Complex.ofReal_natCast,
    Complex.re_ofReal_mul]
  push_cast; ring

theorem Hf_diff (x : VC D N N') : Differentiable ℂ (fun z : VC D N N' => Hf D T z x) := by
  unfold Hf
  fun_prop

theorem Wd_diff (x : VC D N N') {F : VC D N N' → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ (Wd D T x F) := by
  have h := Hf_diff (T := T) x
  unfold Wd U
  fun_prop

theorem Wd_comm (a x : VC D N N') (m : ℤ) (h : (Hf D T a x).im = m) (F : VC D N N' → ℂ) :
    Wd D T a (Wd D T x F) = Wd D T x (Wd D T a F) := by
  funext z
  have h1 : Hf D T x a = Hf D T a x - 2 * m * Complex.I := by
    rw [Hf_conj a x]
    apply Complex.ext <;> simp [h]
    ring
  have h2 : Complex.exp (-(Real.pi : ℂ) * Hf D T (z + x) a - (Real.pi : ℂ) * Hf D T a a / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T z x - (Real.pi : ℂ) * Hf D T x x / 2) =
      Complex.exp (-(Real.pi : ℂ) * Hf D T (z + a) x - (Real.pi : ℂ) * Hf D T x x / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T z a - (Real.pi : ℂ) * Hf D T a a / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨m, ?_⟩
    rw [Hf_add_left, Hf_add_left, h1]
    ring
  simp only [Wd, U]
  rw [add_right_comm z a x]
  linear_combination (-(wdPh D T a * wdPh D T x * F (z + x + a))) * h2

theorem Wd_add (x : VC D N N') (F G : VC D N N' → ℂ) : Wd D T x (F + G) = Wd D T x F + Wd D T x G := by
  funext z; simp only [Wd, U, Pi.add_apply]; ring

theorem Wd_smul (x : VC D N N') (c : ℂ) (F : VC D N N' → ℂ) : Wd D T x (c • F) = c • Wd D T x F := by
  funext z; simp only [Wd, U, Pi.smul_apply, smul_eq_mul]; ring

theorem TT_add {F G : VC D N N' → ℂ} (hF : F ∈ TT D T N N') (hG : G ∈ TT D T N N') : F + G ∈ TT D T N N' := by
  obtain ⟨d, m, hm, h⟩ := hF
  obtain ⟨d', m', hm', h'⟩ := hG
  refine ⟨d.add d', m * m', by positivity, fun x hx => ?_⟩
  rw [Wd_add]
  congr 1
  · rw [mul_nsmul']; exact h _ (nsmul_mem hx _)
  · rw [mul_nsmul]; exact h' _ (nsmul_mem hx _)

theorem TT_smul (c : ℂ) {F : VC D N N' → ℂ} (hF : F ∈ TT D T N N') : c • F ∈ TT D T N N' := by
  obtain ⟨d, m, hm, h⟩ := hF
  exact ⟨d.const_smul c, m, hm, fun x hx => by rw [Wd_smul, h x hx]⟩

theorem TT_zero : (0 : VC D N N' → ℂ) ∈ TT D T N N' :=
  ⟨differentiable_const 0, 1, one_pos, fun x _ => by funext z; simp [Wd, U]⟩

end Theta

theorem Om_sum {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ} {e0 : VC D N N' → ℂ} (W : WeilO D cc δ N N' e0)
    (g : GA D N) (g' : GA D N') {κ : Type} (s : Finset κ) (r : κ → ℂ) (F : κ → VC D N N' → ℂ)
    (hF : ∀ i, F i ∈ TT D (tor0 D cc δ) N N') :
    (∑ i ∈ s, r i • F i) ∈ TT D (tor0 D cc δ) N N' ∧
      W.Om g g' (∑ i ∈ s, r i • F i) = ∑ i ∈ s, r i • W.Om g g' (F i) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using TT_zero, ?_⟩
    have := W.smul g g' 0 0 TT_zero
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨TT_add (TT_smul _ (hF a)) ih.1, ?_⟩
    rw [W.add g g' _ (TT_smul _ (hF a)) _ ih.1, W.smul g g' _ _ (hF a), ih.2]

theorem exists_nsmul_mem {cc : Ideal (𝓞 D.host.K)} (hc : cc ≠ ⊥) (δ : ℂ) {N N' : ℕ}
    (z : Matrix (Fin N') (Fin N) D.host.E) :
    ∃ n : ℕ, 0 < n ∧ n • pt D (tor0 D cc δ) δ z ∈ La0 D (tor0 D cc δ) N N' := by
  obtain ⟨a, ha0, ha⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger (MovedLattice.inverseHalfDifferent_ne_zero D)
  set b : D.host.E := algebraMap (𝓞 D.host.E) D.host.E a with hb
  have hb0 : b ≠ 0 := by
    rw [hb]; exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).2 ha0
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := D.host.E)
    (Finset.univ.image fun p : Fin N' × Fin N => z p.1 p.2 / b)
  have hA : ∀ i j, IsIntegral ℤ (((y.natAbs * y.natAbs : ℕ) : D.host.E) * (z i j / b)) := by
    intro i j
    have h1 := hy _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))
    have h2 : ((y.natAbs * y.natAbs : ℕ) : D.host.E) = (y : D.host.E) * (y : D.host.E) := by
      rw [← Int.cast_natCast, Int.natAbs_mul_self, Int.cast_mul]
    rw [h2, mul_assoc]
    rw [zsmul_eq_mul] at h1
    exact (isIntegral_algebraMap (R := ℤ) (x := y)).mul h1
  set m : ℕ := y.natAbs * y.natAbs with hm
  have hm0 : 0 < m := by positivity
  have hn0 : 0 < Ideal.absNorm cc := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  refine ⟨Ideal.absNorm cc * m, by positivity, AddSubgroup.subset_closure
    ⟨δ * D.host.φ₀ ((((Ideal.absNorm cc : 𝓞 D.host.K) : D.host.K) : D.host.E)),
      AddSubgroup.subset_closure ⟨_, Ideal.absNorm_mem cc, rfl⟩,
      b • Matrix.of (fun i j => (m : D.host.E) * (z i j / b)),
      Submodule.subset_span ⟨b, ha, _, Submodule.subset_span ?_, rfl⟩, ?_⟩⟩
  · intro x hx i _
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    refine Submodule.sum_mem _ fun j _ => ?_
    exact Submodule.smul_mem _ (⟨_, hA i j⟩ : 𝓞 D.host.E) (hx j trivial)
  · funext τ i j
    have h1 : b * ((m : D.host.E) * (z i j / b)) = m * z i j := by field_simp
    simp only [pt, embV, tor0, Pi.smul_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, h1, map_mul,
      map_natCast, nsmul_eq_mul]
    simp
    ring

theorem emb_conj {a b : ℕ} (γ : Matrix (Fin a) (Fin b) D.host.E) (τ : D.what₂.Tau) :
    ((γ.map D.host.conj).transpose).map (embT D τ) = (γ.map (embT D τ)).conjTranspose := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.transpose_apply]
  exact D.host.conjE_apply (embT D τ) (γ j i)

theorem Hf_eq_trace {T : Tor D} {N N' : ℕ} (z w : VC D N N') :
    Hf D T z w = (∑ τ, (Matrix.of (z τ) * (Matrix.of (w τ)).conjTranspose).trace) / (area T.abelian₂ : ℂ) := by
  simp [Hf, Matrix.trace, Matrix.mul_apply]

def subst {N N' : ℕ} (u : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ) (u' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ)
    (z : VC D N N') : VC D N N' :=
  fun τ => ((u' τ).conjTranspose * Matrix.of (z τ) * u τ : Matrix _ _ ℂ)

theorem Hf_subst {T : Tor D} {N N' : ℕ} {u : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ}
    {u' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ} (hu : ∀ τ, u τ * (u τ).conjTranspose = 1)
    (hu' : ∀ τ, u' τ * (u' τ).conjTranspose = 1) (z w : VC D N N') :
    Hf D T (subst u u' z) (subst u u' w) = Hf D T z w := by
  rw [Hf_eq_trace, Hf_eq_trace]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  change (((u' τ).conjTranspose * Matrix.of (z τ) * u τ) *
    ((u' τ).conjTranspose * Matrix.of (w τ) * u τ).conjTranspose).trace = _
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (u τ), hu, Matrix.one_mul, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc, hu', Matrix.mul_one]

theorem subst_add {N N' : ℕ} (u : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ)
    (u' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) (z w : VC D N N') :
    subst u u' (z + w) = subst u u' z + subst u u' w := by
  funext τ
  change ((u' τ).conjTranspose * (Matrix.of (z τ) + Matrix.of (w τ)) * u τ : Matrix _ _ ℂ) =
    (u' τ).conjTranspose * Matrix.of (z τ) * u τ + (u' τ).conjTranspose * Matrix.of (w τ) * u τ
  rw [Matrix.mul_add, Matrix.add_mul]

theorem pull_Wd {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ} {γ : Matrix (Fin N) (Fin N) D.host.E}
    {γ' : Matrix (Fin N') (Fin N') D.host.E} (h : γ * (γ.map D.host.conj).transpose = 1)
    (h' : γ' * (γ'.map D.host.conj).transpose = 1) (z : Matrix (Fin N') (Fin N) D.host.E) (G : VC D N N' → ℂ) :
    pull D (tor0 D cc δ) γ γ' (Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) G) =
      Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (γ' * z * (γ.map D.host.conj).transpose))
        (pull D (tor0 D cc δ) γ γ' G) := by
  have hu : ∀ τ, γ.map (embT D τ) * (γ.map (embT D τ)).conjTranspose = 1 := fun τ => by
    rw [← emb_conj, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  have hu' : ∀ τ, γ'.map (embT D τ) * (γ'.map (embT D τ)).conjTranspose = 1 := fun τ => by
    rw [← emb_conj, ← Matrix.map_mul, h', Matrix.map_one _ (map_zero _) (map_one _)]
  have hx : pt D (tor0 D cc δ) δ z = subst (fun τ => γ.map (embT D τ)) (fun τ => γ'.map (embT D τ))
      (pt D (tor0 D cc δ) δ (γ' * z * (γ.map D.host.conj).transpose)) := by
    funext τ
    change (δ • z.map (embT D τ) : Matrix _ _ ℂ) = (γ'.map (embT D τ)).conjTranspose *
      (δ • (γ' * z * (γ.map D.host.conj).transpose).map (embT D τ)) * γ.map (embT D τ)
    rw [Matrix.map_mul, Matrix.map_mul, emb_conj, Matrix.mul_smul, Matrix.smul_mul]
    simp only [Matrix.mul_assoc]
    rw [mul_eq_one_comm.1 (hu τ), Matrix.mul_one, ← Matrix.mul_assoc, mul_eq_one_comm.1 (hu' τ), Matrix.one_mul]
  generalize pt D (tor0 D cc δ) δ (γ' * z * (γ.map D.host.conj).transpose) = x at hx
  rw [hx]
  funext w
  change Wd D (tor0 D cc δ) _ G (subst (fun τ => γ.map (embT D τ)) (fun τ => γ'.map (embT D τ)) w) =
    wdPh D (tor0 D cc δ) x * (G (subst (fun τ => γ.map (embT D τ)) (fun τ => γ'.map (embT D τ)) (w + x)) * _)
  simp only [Wd, U, wdPh, qH, Hf_subst hu hu', subst_add]

theorem om_eq_pull_of_vacuum : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), (∀ F ∈ TT D (tor0 D cc δ) N N', ∃ (k : ℕ) (r : Fin k → ℂ) (z : Fin k → Matrix (Fin N') (Fin N) D.host.E), F = ∑ i, r i • Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) e0) → ∀ (W : WeilO D cc δ N N' e0) (γA : GA D N) (γA' : GA D N') (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) (a : ℂ), IsRat D (γA : GL (Fin N) (AE D)) γ → IsRat D (γA' : GL (Fin N') (AE D)) γ' → (W.Om γA γA' e0 = fun z => a * pull D (tor0 D cc δ) γ γ' e0 z) → ∀ F ∈ TT D (tor0 D cc δ) N N', W.Om γA γA' F = fun z => a * pull D (tor0 D cc δ) γ γ' F z := by
  intro D cc δ hC N N' e0 he0 hspan W γA γA' γ γ' a hγ hγ' h0 F hF
  have hSD0 : ∀ N : ℕ, SD D (stdL D N) := by
    intro N
    obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
    rw [← h2]; exact (h1 1).2
  obtain ⟨-, hW, hint, -⟩ := GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hC N N'
    (La0 D (tor0 D cc δ) N N') (Or.inr ⟨_, _, hSD0 _, hSD0 _, rfl⟩)
  have hfix : ∀ x ∈ La0 D (tor0 D cc δ) N N', Wd D (tor0 D cc δ) x e0 = e0 := by
    intro x hx
    rw [hW x hx]; funext z; exact he0.2 x hx z
  have heT : e0 ∈ TT D (tor0 D cc δ) N N' :=
    ⟨he0.1, 1, one_pos, fun x hx => by rw [one_nsmul]; exact hfix x hx⟩
  have hT : ∀ z, Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) e0 ∈ TT D (tor0 D cc δ) N N' := by
    intro z
    obtain ⟨Q, hQ, hz⟩ := exists_nsmul_mem hC.1.1 δ z
    refine ⟨Wd_diff _ he0.1, Q, hQ, fun x hx => ?_⟩
    obtain ⟨m, hm⟩ := hint x hx _ hz
    rw [Hf_nsmul_right, ← Hf_nsmul_left] at hm
    rw [Wd_comm _ _ m hm, hfix _ (nsmul_mem hx _)]
  have hu := (GlobalTheory.NormSum.mem_ratG_intG D N).2.2.2.1 γA γ hγ
  have hu' := (GlobalTheory.NormSum.mem_ratG_intG D N').2.2.2.1 γA' γ' hγ'
  have hinv : (((γA : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) =
      ((γ.map D.host.conj).transpose).map (inc D) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [show ((γA : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) = γ.map (inc D) from hγ,
      ← Matrix.map_mul, hu, Matrix.map_one _ (map_zero _) (map_one _)]
  have key : ∀ z, W.Om γA γA' (Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) e0) =
      a • pull D (tor0 D cc δ) γ γ' (Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) e0) := by
    intro z
    obtain ⟨m, -, hl⟩ := W.lift γA γA' z e0 heT
    rw [hl (γ' * z * (γ.map D.host.conj).transpose), pull_Wd hu hu', ← Wd_smul, h0]
    · rfl
    · intro i j
      refine ⟨0, zero_mem _, ?_⟩
      rw [hinv, show ((γA' : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) = γ'.map (inc D) from hγ',
        Matrix.map_mul, Matrix.map_mul, sub_self, mul_zero]
      rfl
  obtain ⟨k, r, z, rfl⟩ := hspan F hF
  rw [(Om_sum W γA γA' Finset.univ _ _ fun i => hT (z i)).2]
  funext w
  simp only [key, pull, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  erw [Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _

end GlobalTheory.NormSum.RatExtend
