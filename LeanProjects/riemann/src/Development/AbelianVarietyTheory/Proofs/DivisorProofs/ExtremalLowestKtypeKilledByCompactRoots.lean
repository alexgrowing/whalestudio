import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexifiedDerivedActionIsLieActionStatement

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HolDict.BorelK

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Mt n → (H →L[ℂ] H)}

private theorem mem_UJset_of_mem_Kset_divisor {g : Mt n} (hg : g ∈ Formalism.REAL.Kset ε) : g ∈ UJset ε := by
  obtain ⟨hu, hc⟩ := hg
  have hgg : gᴴ * g = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp hu
  show gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε
  rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, hgg, Matrix.one_mul]

theorem inner_rep (hσ : IsURepOn (UJset ε) σ) {g : Mt n} (hg : g ∈ Formalism.REAL.Kset ε) (x y : H) :
    ⟪σ g x, σ g y⟫_ℂ = ⟪x, y⟫_ℂ := by
  have hn : ∀ v : H, ‖σ g v‖ = ‖v‖ := hσ.2.1 g (mem_UJset_of_mem_Kset_divisor hg)
  let L : H →ₗᵢ[ℂ] H := { toLinearMap := (σ g : H →ₗ[ℂ] H), norm_map' := hn }
  exact L.inner_map_map x y

private theorem dRepC_zero_right (Z : Mt n) : dRepC (Formalism.REAL.Jm ε) σ Z (0 : H) = 0 := by
  simp [dRepC, dRep]

private theorem dRepC_zero_left (v : H) : dRepC (Formalism.REAL.Jm ε) σ 0 v = 0 := by
  simp [dRepC, conjH, dRep]

private theorem diagonal_exp_mem_Kset (φ : Fin n → ℝ) :
    Matrix.diagonal (fun b => Complex.exp ((φ b : ℂ) * Complex.I)) ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext b
    rw [Pi.star_apply, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_ofReal,
      Complex.conj_I]
    simp
  · unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext b
    ring

theorem isWtOn_proj (hσ : IsURepOn (UJset ε) σ) (S : Submodule ℂ H) [FiniteDimensional ℂ S] (hS : IsKStableOn ε σ S)
    {μ : Fin n → ℝ} {w : H} (hw : IsWtOn (Formalism.REAL.Kset ε) σ μ w) :
    IsWtOn (Formalism.REAL.Kset ε) σ μ (S.starProjection w) := by
  intro θ hθ
  have hw' := hw θ hθ
  have hSt : ∀ v ∈ S, σ (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) v ∈ S := hS _ hθ
  let f : S →ₗ[ℂ] S := (σ (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) : H →ₗ[ℂ] H).restrict hSt
  have hfi : Function.Injective f := by
    intro x y hxy
    have h1 : σ (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) (x : H) =
        σ (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) (y : H) := congrArg Subtype.val hxy
    have h2 := hσ.2.1 _ (mem_UJset_of_mem_Kset_divisor hθ) ((x : H) - y)
    rw [map_sub, h1, sub_self, norm_zero] at h2
    exact Subtype.ext (sub_eq_zero.mp (norm_eq_zero.mp h2.symm))
  have hfs : Function.Surjective f := LinearMap.injective_iff_surjective.mp hfi
  have key : S.starProjection (σ (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) w) =
      σ (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) (S.starProjection w) := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hSt _ (by rw [Submodule.starProjection_apply]; exact Submodule.coe_mem _))
    intro y hy
    obtain ⟨y', hy'⟩ := hfs ⟨y, hy⟩
    have hy'' : σ (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) (y' : H) = y :=
      congrArg Subtype.val hy'
    rw [← hy'', ← map_sub, inner_rep hσ hθ]
    exact S.starProjection_inner_eq_zero w y' y'.2
  rw [← key, hw', map_smul]

theorem orth_of_not_cdom (hσ : IsURepOn (UJset ε) σ) {Λ μ : Fin n → ℝ} {w : H}
    (hw : IsWtOn (Formalism.REAL.Kset ε) σ μ w) (hμ : ¬ CDom ε μ Λ) :
    ∀ x ∈ sSup {S | IsKTypeOf ε σ Λ S}, ⟪w, x⟫_ℂ = 0 := by
  have hle : sSup {S | IsKTypeOf ε σ Λ S} ≤ (ℂ ∙ w)ᗮ := by
    apply sSup_le
    intro S hS x hx
    obtain ⟨hfd, hst, -, -, hmax⟩ := hS
    haveI := hfd
    have hp := isWtOn_proj hσ S hst hw
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    by_cases h0 : S.starProjection w = 0
    · have h3 := S.starProjection_inner_eq_zero w x hx
      rwa [h0, sub_zero] at h3
    · exact absurd (hmax μ _ (by rw [Submodule.starProjection_apply]; exact Submodule.coe_mem _) h0 hp) hμ
  intro x hx
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hle hx)

theorem stable_sSup {Λ : Fin n → ℝ} : IsKStableOn ε σ (sSup {S | IsKTypeOf ε σ Λ S}) := by
  intro g hg v hv
  have hle : sSup {S | IsKTypeOf ε σ Λ S} ≤
      (sSup {S | IsKTypeOf ε σ Λ S}).comap (σ g : H →ₗ[ℂ] H) := by
    apply sSup_le
    intro S hS x hx
    exact (le_sSup hS : S ≤ sSup {S | IsKTypeOf ε σ Λ S}) (hS.2.1 g hg x hx)
  exact hle hv

private theorem sum_index_mul_root_eq_sub (x y : Fin n) :
    ∑ i : Fin n, ((i : ℕ) : ℝ) * Formalism.REAL.root x y i = ((x : ℕ) : ℝ) - ((y : ℕ) : ℝ) := by
  simp [Formalism.REAL.root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]

theorem not_cdom (Λ : Fin n → ℝ) {a c : Fin n} (h : a < c) :
    ¬ CDom ε (Λ + Formalism.REAL.root a c) Λ := by
  rintro ⟨k, hk, heq⟩
  have key := congrArg (fun x : Fin n → ℝ => ∑ i : Fin n, ((i : ℕ) : ℝ) * x i) heq
  have lhs : ∑ i : Fin n, ((i : ℕ) : ℝ) * (Λ - (Λ + Formalism.REAL.root a c)) i = ((c : ℕ) : ℝ) - ((a : ℕ) : ℝ) := by
    have e : ∀ i, (Λ - (Λ + Formalism.REAL.root a c)) i = -(Formalism.REAL.root a c i) := fun i => by simp
    simp only [e, mul_neg, Finset.sum_neg_distrib, sum_index_mul_root_eq_sub]
    ring
  have rhs : ∑ i : Fin n, ((i : ℕ) : ℝ) * (∑ x, ∑ y, (k x y : ℝ) • Formalism.REAL.root x y) i =
      ∑ x, ∑ y, (k x y : ℝ) * (((x : ℕ) : ℝ) - ((y : ℕ) : ℝ)) := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← sum_index_mul_root_eq_sub, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hle : ∑ x, ∑ y, (k x y : ℝ) * (((x : ℕ) : ℝ) - ((y : ℕ) : ℝ)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro x _
    apply Finset.sum_nonpos
    intro y _
    by_cases h0 : k x y = 0
    · simp [h0]
    · have h1 : (x : ℕ) < (y : ℕ) := (hk x y h0).1
      have h2 : ((x : ℕ) : ℝ) < ((y : ℕ) : ℝ) := by exact_mod_cast h1
      have h3 : (0 : ℝ) ≤ (k x y : ℝ) := Nat.cast_nonneg _
      nlinarith
  have hca : ((a : ℕ) : ℝ) < ((c : ℕ) : ℝ) := by exact_mod_cast (show (a : ℕ) < (c : ℕ) from h)
  rw [lhs, rhs] at key
  linarith

theorem exp_mem_kset {X : Mt n} (h1 : Xᴴ = -X) (h2 : Commute X (Formalism.REAL.Jm ε)) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose,
      Matrix.conjTranspose_smul, h1, star_trivial, smul_neg,
      ← Matrix.exp_add_of_commute (-(t • X)) (t • X) ((Commute.refl _).neg_left), neg_add_cancel]
    exact NormedSpace.exp_zero
  · let U : (Mt n)ˣ := ⟨Formalism.REAL.Jm ε, Formalism.REAL.Jm ε, Formalism.REAL.Jm_mul_self ε, Formalism.REAL.Jm_mul_self ε⟩
    have h3 : Formalism.REAL.Jm ε * (t • X) * Formalism.REAL.Jm ε = t • X := by
      rw [Matrix.mul_smul, Matrix.smul_mul, ← h2.eq, Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one]
    have h4 := Matrix.exp_units_conj U (t • X)
    change NormedSpace.exp (Formalism.REAL.Jm ε * (t • X) * Formalism.REAL.Jm ε) =
      Formalism.REAL.Jm ε * NormedSpace.exp (t • X) * Formalism.REAL.Jm ε at h4
    rw [h3] at h4
    calc NormedSpace.exp (t • X) * Formalism.REAL.Jm ε
        = Formalism.REAL.Jm ε * NormedSpace.exp (t • X) * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [← h4]
      _ = Formalism.REAL.Jm ε * NormedSpace.exp (t • X) := by
        rw [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one]

theorem inner_dRep {S : Submodule ℂ H} (hS : IsKStableOn ε σ S) {w v : H} (hw : ∀ x ∈ S, ⟪w, x⟫_ℂ = 0) (hv : v ∈ S)
    {X : Mt n} (h1 : Xᴴ = -X) (h2 : Commute X (Formalism.REAL.Jm ε)) : ⟪w, dRep σ X v⟫_ℂ = 0 := by
  have hz : ∀ t : ℝ, ⟪w, σ (NormedSpace.exp (t • X)) v⟫_ℂ = 0 :=
    fun t => hw _ (hS _ (exp_mem_kset h1 h2 t) v hv)
  unfold dRep
  by_cases hd : DifferentiableAt ℝ (fun t : ℝ => σ (NormedSpace.exp (t • X)) v) 0
  · have h3 := ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd.hasDerivAt
    have h5 : HasDerivAt (fun _ : ℝ => (0 : ℂ))
        (((innerSL ℂ w).restrictScalars ℝ) (deriv (fun t : ℝ => σ (NormedSpace.exp (t • X)) v) 0)) 0 :=
      h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by simp [hz t])
    have h6 := h5.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
    simpa using h6
  · rw [deriv_zero_of_not_differentiableAt hd, inner_zero_right]

theorem Jm_inv : (Formalism.REAL.Jm ε)⁻¹ = Formalism.REAL.Jm ε := Matrix.inv_eq_left_inv (Formalism.REAL.Jm_mul_self ε)

theorem commute_single {a c : Fin n} (h : ε a = ε c) : Commute (Matrix.single a c (1 : ℂ)) (Formalism.REAL.Jm ε) := by
  show Matrix.single a c (1 : ℂ) * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * Matrix.single a c (1 : ℂ)
  unfold Formalism.REAL.Jm
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.single, Matrix.of_apply]
  by_cases hi : a = i
  · by_cases hj : c = j
    · subst hi hj; simp [h]
    · simp [hj]
  · simp [hi]

private theorem single_ct_lemma (a c : Fin n) : (Matrix.single a c (1 : ℂ))ᴴ = Matrix.single c a 1 := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.single, Matrix.of_apply]
  by_cases h : c = i ∧ a = j
  · rw [if_pos ⟨h.2, h.1⟩, if_pos h, star_one]
  · rw [if_neg (fun h' => h ⟨h'.2, h'.1⟩), if_neg h, star_zero]

theorem conjH_single {a c : Fin n} (h : ε a = ε c) :
    conjH (Formalism.REAL.Jm ε) (Matrix.single a c 1) = -Matrix.single c a 1 := by
  unfold conjH
  rw [Jm_inv, single_ct_lemma, Matrix.mul_assoc, (commute_single h.symm).eq, ← Matrix.mul_assoc,
    Formalism.REAL.Jm_mul_self, Matrix.one_mul]

private theorem star_one_div_two : star (1 / 2 : ℂ) = 1 / 2 := by simp

private theorem star_one_div_two_mul_I : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
  rw [Complex.star_def, map_div₀, map_one, map_mul, Complex.conj_I, map_ofNat, mul_neg, div_neg]

theorem inner_dRepC {S : Submodule ℂ H} (hS : IsKStableOn ε σ S) {w v : H} (hw : ∀ x ∈ S, ⟪w, x⟫_ℂ = 0) (hv : v ∈ S)
    {a c : Fin n} (h : ε a = ε c) : ⟪w, dRepC (Formalism.REAL.Jm ε) σ (Matrix.single a c 1) v⟫_ℂ = 0 := by
  unfold dRepC
  rw [conjH_single h]
  have hc := commute_single (ε := ε) h
  have hc' := commute_single (ε := ε) h.symm
  have k1 : ((1 / 2 : ℂ) • (Matrix.single a c (1 : ℂ) + -Matrix.single c a 1))ᴴ =
      -((1 / 2 : ℂ) • (Matrix.single a c (1 : ℂ) + -Matrix.single c a 1)) := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_neg, single_ct_lemma,
      single_ct_lemma, star_one_div_two, ← smul_neg]
    congr 1
    abel
  have k2 : ((1 / (2 * Complex.I)) • (Matrix.single a c (1 : ℂ) - -Matrix.single c a 1))ᴴ =
      -((1 / (2 * Complex.I)) • (Matrix.single a c (1 : ℂ) - -Matrix.single c a 1)) := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_neg, single_ct_lemma,
      single_ct_lemma, star_one_div_two_mul_I, neg_smul, sub_neg_eq_add, sub_neg_eq_add, add_comm]
  have c1 : Commute ((1 / 2 : ℂ) • (Matrix.single a c (1 : ℂ) + -Matrix.single c a 1)) (Formalism.REAL.Jm ε) :=
    (hc.add_left hc'.neg_left).smul_left _
  have c2 : Commute ((1 / (2 * Complex.I)) • (Matrix.single a c (1 : ℂ) - -Matrix.single c a 1)) (Formalism.REAL.Jm ε) :=
    (hc.sub_left hc'.neg_left).smul_left _
  rw [inner_add_right, inner_smul_right, inner_dRep hS hw hv k1 c1, inner_dRep hS hw hv k2 c2, mul_zero, add_zero]

theorem dRepC_diag (hσ : IsURepOn (UJset ε) σ) {μ : Fin n → ℝ} {v : H} (hv : IsWtOn (Formalism.REAL.Kset ε) σ μ v) (a : Fin n) :
    dRepC (Formalism.REAL.Jm ε) σ (Matrix.single a a 1) v = ((μ a : ℝ) : ℂ) • v := by
  unfold dRepC
  rw [conjH_single rfl]
  have e1 : (1 / 2 : ℂ) • (Matrix.single a a (1 : ℂ) + -Matrix.single a a 1) = 0 := by simp
  have e2 : (1 / (2 * Complex.I)) • (Matrix.single a a (1 : ℂ) - -Matrix.single a a 1) =
      (-Complex.I) • Matrix.single a a 1 := by
    have hc2 : (1 / (2 * Complex.I)) * 2 = -Complex.I := by
      rw [one_div, mul_inv, Complex.inv_I]
      ring
    rw [sub_neg_eq_add, ← two_smul ℂ, smul_smul, hc2]
  rw [e1, e2]
  have d0 : dRep σ (0 : Mt n) v = 0 := by unfold dRep; simp
  rw [d0, zero_add]
  have hskew : ((-Complex.I) • Matrix.single a a (1 : ℂ))ᴴ = -((-Complex.I) • Matrix.single a a (1 : ℂ)) := by
    rw [Matrix.conjTranspose_smul, single_ct_lemma, Complex.star_def, map_neg, Complex.conj_I]
    simp only [neg_smul, neg_neg]
  have hcomm : Commute ((-Complex.I) • Matrix.single a a (1 : ℂ)) (Formalism.REAL.Jm ε) :=
    (commute_single rfl).smul_left _
  have hexp : ∀ t : ℝ, NormedSpace.exp (t • ((-Complex.I) • Matrix.single a a (1 : ℂ))) =
      Matrix.diagonal (fun b => Complex.exp (((if b = a then -t else 0 : ℝ) : ℂ) * Complex.I)) := by
    intro t
    have hs : t • ((-Complex.I) • Matrix.single a a (1 : ℂ)) =
        Matrix.diagonal (fun b => (((if b = a then -t else 0 : ℝ)) : ℂ) * Complex.I) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        rw [Matrix.diagonal_apply_eq]
        by_cases hia : i = a
        · subst hia; simp [Matrix.single, Complex.real_smul] <;> ring
        · simp [Matrix.single, hia, Ne.symm hia]
      · rw [Matrix.diagonal_apply_ne _ hij]
        simp only [Matrix.smul_apply, Matrix.single, Matrix.of_apply]
        rw [if_neg (fun h' => hij (h'.1.symm.trans h'.2))]
        simp
    rw [hs, Matrix.exp_diagonal]
    congr 1
    funext b
    rw [Pi.coe_exp]
    exact (congrFun Complex.exp_eq_exp_ℂ _).symm
  have hvt7 : ∀ t : ℝ, σ (NormedSpace.exp (t • ((-Complex.I) • Matrix.single a a (1 : ℂ)))) v =
      Complex.exp ((((-(μ a * t)) : ℝ) : ℂ) * Complex.I) • v := by
    intro t
    have hm := exp_mem_kset (ε := ε) hskew hcomm t
    rw [hexp t] at hm ⊢
    have hs2 : (∑ b, μ b * (if b = a then -t else 0)) = -(μ a * t) := by
      simp [mul_ite, Finset.sum_ite_eq']
    rw [hv _ hm, hs2]
  unfold dRep
  simp_rw [hvt7]
  have hd : HasDerivAt (fun t : ℝ => Complex.exp ((((-(μ a * t)) : ℝ) : ℂ) * Complex.I) • v) _ 0 :=
    ((((hasDerivAt_id' (0 : ℝ)).const_mul (μ a)).neg.ofReal_comp).mul_const Complex.I).cexp.smul_const v
  rw [hd.deriv, smul_smul]
  congr 1
  first
    | (simp only [mul_zero, neg_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, mul_one,
        Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_one]
       linear_combination (-(μ a : ℂ)) * Complex.I_mul_I)
    | simp [Complex.ext_iff]

theorem det_Jm : (Formalism.REAL.Jm ε).det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (Formalism.REAL.Jm_mul_self ε)
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at h1
  exact zero_ne_one h1

theorem isWtOn_root [CompleteSpace H] (hσ : IsURepOn (UJset ε) σ) {μ : Fin n → ℝ} {v : H}
    (hs : SmoothVec (lieH (Formalism.REAL.Jm ε)) σ v) (hv : IsWtOn (Formalism.REAL.Kset ε) σ μ v) (a c : Fin n) :
    IsWtOn (Formalism.REAL.Kset ε) σ (μ + Formalism.REAL.root a c) (dRepC (Formalism.REAL.Jm ε) σ (Matrix.single a c 1) v) := by
  have h0 : SmoothVec (lieH (Formalism.REAL.Jm ε)) σ (0 : H) := fun k Xs _ => by
    simp only [map_zero]; exact contDiff_const
  obtain ⟨hlin, -, hequiv, -⟩ :=
    GlobalTheory.T.complexifiedDerivedAction_isLieAction n (Formalism.REAL.Jm ε) H σ (Formalism.REAL.Jm_conjTranspose ε) det_Jm hσ v 0 hs h0
  intro θ hθ
  have hg : Matrix.diagonal (fun b => Complex.exp ((θ b : ℂ) * Complex.I)) ∈ Formalism.QuantumDeterminants.UH (Formalism.REAL.Jm ε) :=
    mem_UJset_of_mem_Kset_divisor hθ
  have htinv : (Matrix.diagonal (fun b => Complex.exp ((θ b : ℂ) * Complex.I)))⁻¹ =
      Matrix.diagonal (fun b => Complex.exp (-((θ b : ℂ) * Complex.I))) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext b
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hconj : Matrix.diagonal (fun b => Complex.exp ((θ b : ℂ) * Complex.I)) * Matrix.single a c 1 *
      (Matrix.diagonal (fun b => Complex.exp ((θ b : ℂ) * Complex.I)))⁻¹ =
      (Complex.exp ((θ a : ℂ) * Complex.I) * Complex.exp (-((θ c : ℂ) * Complex.I))) • Matrix.single a c (1 : ℂ) := by
    rw [htinv]
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.smul_apply, Matrix.single, Matrix.of_apply, smul_eq_mul]
    by_cases hij : a = i ∧ c = j
    · obtain ⟨rfl, rfl⟩ := hij
      simp
    · simp [hij]
  rw [hequiv _ hg, hconj, hv θ hθ]
  have s1 : ∀ (α β : ℂ), dRepC (Formalism.REAL.Jm ε) σ (α • Matrix.single a c (1 : ℂ)) (β • v) =
      β • dRepC (Formalism.REAL.Jm ε) σ (α • Matrix.single a c (1 : ℂ)) v := by
    intro α β
    have h1 := (hlin β (α • Matrix.single a c (1 : ℂ)) 0).2.1
    rwa [add_zero, dRepC_zero_right, add_zero] at h1
  have s2 : ∀ α : ℂ, dRepC (Formalism.REAL.Jm ε) σ (α • Matrix.single a c (1 : ℂ)) v =
      α • dRepC (Formalism.REAL.Jm ε) σ (Matrix.single a c (1 : ℂ)) v := by
    intro α
    have h1 := (hlin α (Matrix.single a c (1 : ℂ)) 0).1
    rwa [add_zero, dRepC_zero_left, add_zero] at h1
  have hsum : (∑ b, (μ + Formalism.REAL.root a c) b * θ b) = (∑ b, μ b * θ b) + (θ a - θ c) := by
    simp [Formalism.REAL.root, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Pi.single_apply]
  rw [s1, s2, smul_smul]
  congr 1
  rw [← Complex.exp_add, ← Complex.exp_add, hsum]
  congr 1
  push_cast
  ring

theorem extremal_killed : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mt n → (H →L[ℂ] H)), IsDS ε lam σ → ∀ v ∈ lowKSub ε lam σ, SmoothVec (lieH (Formalism.REAL.Jm ε)) σ v → IsWtOn (Formalism.REAL.Kset ε) σ (fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) v → (∀ a, dRepC (Formalism.REAL.Jm ε) σ (Matrix.single a a 1) v = ((Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a) : ℝ) : ℂ) • v) ∧ ∀ a c : Fin n, ε a = ε c → revNeg ε a < revNeg ε c → dRepC (Formalism.REAL.Jm ε) σ (Matrix.single a c 1) v = 0 := by
  intro n ε lam H _ _ σ hDS v hvL hs hv
  obtain ⟨hC, -, hσ, -⟩ := hDS
  haveI := hC
  refine ⟨fun a => dRepC_diag hσ hv a, ?_⟩
  intro a c hac hlt
  set s := revNeg ε with hs_def
  let P : Mt n := Matrix.of fun i j => if s j = i then (1 : ℂ) else 0
  let Q : Mt n := Matrix.of fun i j => if s i = j then (1 : ℂ) else 0
  have hPQ : Pᴴ = Q := by
    ext i j
    simp only [Matrix.conjTranspose_apply, P, Q, Matrix.of_apply]
    split_ifs <;> simp
  have E1 : ∀ (M : Mt n) (i j : Fin n), (P * M) i j = M (s.symm i) j := by
    intro M i j
    simp [Matrix.mul_apply, P, Equiv.apply_eq_iff_eq_symm_apply]
  have E2 : ∀ (M : Mt n) (i j : Fin n), (M * Q) i j = M i (s.symm j) := by
    intro M i j
    simp [Matrix.mul_apply, Q, Equiv.apply_eq_iff_eq_symm_apply]
  have E3 : ∀ (M : Mt n) (i j : Fin n), (M * P) i j = M i (s j) := by
    intro M i j
    simp [Matrix.mul_apply, P]
  have E4 : ∀ (M : Mt n) (i j : Fin n), (Q * M) i j = M (s i) j := by
    intro M i j
    simp [Matrix.mul_apply, Q]
  have hQP : Q * P = 1 := by
    ext i j
    rw [E4]
    simp only [P, Matrix.of_apply, Matrix.one_apply, s.injective.eq_iff]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  have hPQ1 : P * Q = 1 := by
    ext i j
    rw [E1]
    simp [Q, Matrix.one_apply]
  have hPK : P ∈ Formalism.REAL.Kset ε := by
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, hPQ, hQP]
    · unfold Formalism.REAL.Jm
      ext i j
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      simp only [P, Matrix.of_apply]
      by_cases hij : s j = i
      · subst hij
        simp [hs_def, eps_revNeg]
      · simp [hij]
  have hPU : P ∈ UJset ε := mem_UJset_of_mem_Kset_divisor hPK
  have hPinv : P⁻¹ = Q := by rw [← hPQ]; exact Matrix.inv_eq_left_inv (by rw [hPQ, hQP])
  have hconjP : P * Matrix.single a c (1 : ℂ) * P⁻¹ = Matrix.single (s a) (s c) 1 := by
    rw [hPinv]
    ext i j
    rw [E2, E1]
    simp [Matrix.single, Equiv.eq_symm_apply]
  have hwtP : ∀ (ν : Fin n → ℝ) (x : H), IsWtOn (Formalism.REAL.Kset ε) σ ν x →
      IsWtOn (Formalism.REAL.Kset ε) σ (fun b => ν (s.symm b)) (σ P x) := by
    intro ν x hx θ hθ
    have hD' : Q * Matrix.diagonal (fun b => Complex.exp ((θ b : ℂ) * Complex.I)) * P =
        Matrix.diagonal (fun b => Complex.exp ((θ (s b) : ℂ) * Complex.I)) := by
      ext i j
      rw [E3, E4]
      simp [Matrix.diagonal_apply, s.injective.eq_iff]
    have hmulDP := hσ.1.2 _ (mem_UJset_of_mem_Kset_divisor hθ) P hPU
    have hmulP := hσ.1.2 P hPU (Q * Matrix.diagonal (fun b => Complex.exp ((θ b : ℂ) * Complex.I)) * P)
      (by rw [hD']; exact mem_UJset_of_mem_Kset_divisor (diagonal_exp_mem_Kset _))
    have hPD : P * (Q * Matrix.diagonal (fun b => Complex.exp ((θ b : ℂ) * Complex.I)) * P) =
        Matrix.diagonal (fun b => Complex.exp ((θ b : ℂ) * Complex.I)) * P := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPQ1, Matrix.one_mul]
    have hsumP : ∑ b, ν b * θ (s b) = ∑ b, ν (s.symm b) * θ b := by
      rw [← Equiv.sum_comp s (fun c => ν (s.symm c) * θ c)]
      simp only [Equiv.symm_apply_apply]
    calc σ (Matrix.diagonal fun b => Complex.exp ((θ b : ℂ) * Complex.I)) (σ P x)
        = σ (Matrix.diagonal (fun b => Complex.exp ((θ b : ℂ) * Complex.I)) * P) x := by
          rw [hmulDP]; rfl
      _ = σ P (σ (Q * Matrix.diagonal (fun b => Complex.exp ((θ b : ℂ) * Complex.I)) * P) x) := by
          rw [← hPD, hmulP]; rfl
      _ = Complex.exp (((∑ b, ν (s.symm b) * θ b : ℝ) : ℂ) * Complex.I) • σ P x := by
          rw [hD', hx (fun b => θ (s b)) (diagonal_exp_mem_Kset _), map_smul, hsumP]
  have h0 : SmoothVec (lieH (Formalism.REAL.Jm ε)) σ (0 : H) := fun k Xs _ => by
    simp only [map_zero]; exact contDiff_const
  obtain ⟨-, -, hequiv, -⟩ :=
    GlobalTheory.T.complexifiedDerivedAction_isLieAction n (Formalism.REAL.Jm ε) H σ (Formalism.REAL.Jm_conjTranspose ε) det_Jm hσ v 0 hs h0
  have hw2 := hwtP _ _ (isWtOn_root hσ hs hv a c)
  have hfun : (fun b => ((fun a => Formalism.QuantumDeterminants.lowK ε lam (s a)) + Formalism.REAL.root a c) (s.symm b)) =
      Formalism.QuantumDeterminants.lowK ε lam + Formalism.REAL.root (s a) (s c) := by
    funext b
    simp [Formalism.REAL.root, Pi.single_apply, Equiv.symm_apply_eq]
  rw [hfun] at hw2
  have horth := orth_of_not_cdom hσ hw2 (not_cdom (ε := ε) _ hlt)
  have hPv : σ P v ∈ lowKSub ε lam σ := stable_sSup P hPK v hvL
  have heq : σ P (dRepC (Formalism.REAL.Jm ε) σ (Matrix.single a c 1) v) =
      dRepC (Formalism.REAL.Jm ε) σ (Matrix.single (s a) (s c) 1) (σ P v) := by
    rw [hequiv P hPU, hconjP]
  rw [heq] at horth
  have hε' : ε (s a) = ε (s c) := by simp only [hs_def, eps_revNeg]; exact hac
  have hzero := inner_dRepC (stable_sSup (Λ := Formalism.QuantumDeterminants.lowK ε lam)) horth hPv hε'
  have hD0 := inner_self_eq_zero.mp hzero
  have hPw : σ P (dRepC (Formalism.REAL.Jm ε) σ (Matrix.single a c 1) v) = 0 := heq.trans hD0
  have hn := hσ.2.1 P hPU (dRepC (Formalism.REAL.Jm ε) σ (Matrix.single a c 1) v)
  rw [hPw, norm_zero] at hn
  exact norm_eq_zero.mp hn.symm

end GlobalTheory.HolDict.BorelK
