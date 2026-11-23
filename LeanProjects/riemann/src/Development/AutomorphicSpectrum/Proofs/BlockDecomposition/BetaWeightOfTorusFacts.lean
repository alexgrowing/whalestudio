import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection

noncomputable section

open Finset Matrix

namespace GlobalTheory.CompanionTheory.TorusSymbol

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 PositivityTheory.RgDs.K

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

lemma isOpen_omegaSet (n : ℕ) : IsOpen (OmegaSet n) := by
  have h : OmegaSet n = ⋂ i : Fin n, {z | lead ((i : ℕ) + 1) z ≠ 0} := by
    ext z
    simp [OmegaSet]
  rw [h]
  refine isOpen_iInter_of_finite fun i => ?_
  have hc : Continuous fun z : Matrix (Fin n) (Fin n) ℂ => lead ((i : ℕ) + 1) z := by
    have hi : (i : ℕ) + 1 ≤ n := i.2
    simp only [lead, dif_pos hi]
    exact (continuous_id.matrix_submatrix _ _).matrix_det
  exact isOpen_ne_fun hc continuous_const

lemma differentiableAt_of_mem {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : F ∈ OmF n)
    {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) : DifferentiableAt ℂ F z :=
  (hF.1.contDiffAt ((isOpen_omegaSet n).mem_nhds hz)).differentiableAt (by simp)

lemma lop_add (Y : Matrix (Fin n) (Fin n) ℂ) {F G : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : F ∈ OmF n) (hG : G ∈ OmF n) : lop Y (F + G) = lop Y F + lop Y G := by
  funext z
  by_cases hz : z ∈ OmegaSet n
  · simp only [lop, Pi.add_apply, if_pos hz]
    have h : fderiv ℂ (F + G) z = fderiv ℂ F z + fderiv ℂ G z :=
      ((differentiableAt_of_mem hF hz).hasFDerivAt.add (differentiableAt_of_mem hG hz).hasFDerivAt).fderiv
    rw [h]
    simp only [ContinuousLinearMap.add_apply]
    ring
  · simp [lop, if_neg hz]

lemma lop_smul (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : F ∈ OmF n) : lop Y (s • F) = s • lop Y F := by
  funext z
  by_cases hz : z ∈ OmegaSet n
  · simp only [lop, Pi.smul_apply, if_pos hz]
    have h : fderiv ℂ (s • F) z = s • fderiv ℂ F z :=
      ((differentiableAt_of_mem hF hz).hasFDerivAt.const_smul s).fderiv
    rw [h]
    simp
  · simp [lop, if_neg hz]

lemma lop_sum (Y : Matrix (Fin n) (Fin n) ℂ) {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (Fin n) (Fin n) ℂ → ℂ) (hf : ∀ i, f i ∈ OmF n) :
    lop Y (∑ i ∈ s, f i) = ∑ i ∈ s, lop Y (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    funext z
    by_cases hz : z ∈ OmegaSet n
    · simp [lop, if_pos hz]
    · simp [lop, if_neg hz]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, lop_add Y (hf i) (Submodule.sum_mem _ fun j _ => hf j), ih]

def wtL (c : Fin n) (w : List (Fin n × Fin n)) : ℝ :=
  (w.map fun p => (if p.1 = c then (1 : ℝ) else 0) - (if p.2 = c then 1 else 0)).sum

lemma lw_mem (H : HolFacts) (μ : Fin n → ℤ) (w : List (Fin n × Fin n)) : lw w (PhiO μ) ∈ OmF n := by
  induction w with
  | nil => exact (H n μ).2.2.1
  | cons p w ih => exact (H n μ).1 _ _ ih

lemma lop_lw (H : HolFacts) (μ : Fin n → ℤ) (c : Fin n) (w : List (Fin n × Fin n)) :
    lop (Matrix.single c c 1) (lw w (PhiO μ)) =
      ((((μ c : ℤ) : ℝ) + wtL c w : ℝ) : ℂ) • lw w (PhiO μ) := by
  induction w with
  | nil =>
    have h := (H n μ).2.2.2.1 c
    simpa [wtL, lw] using h
  | cons p w ih =>
    obtain ⟨a, b⟩ := p
    have hF := lw_mem H μ w
    have rel := (H n μ).2.1 (lw w (PhiO μ)) c c a b hF
    have hlw : lw ((a, b) :: w) (PhiO μ) = lop (Matrix.single a b 1) (lw w (PhiO μ)) := rfl
    have hwt : wtL c ((a, b) :: w) =
        ((if a = c then (1 : ℝ) else 0) - (if b = c then 1 else 0)) + wtL c w := by
      simp [wtL]
    rw [ih, lop_smul _ _ hF] at rel
    have rel' : lop (Matrix.single c c 1) (lop (Matrix.single a b 1) (lw w (PhiO μ))) =
        ((((μ c : ℤ) : ℝ) + wtL c w : ℝ) : ℂ) • lop (Matrix.single a b 1) (lw w (PhiO μ)) +
        ((((if a = c then (1 : ℝ) else 0) - (if b = c then 1 else 0) : ℝ)) : ℂ) •
          lop (Matrix.single a b 1) (lw w (PhiO μ)) := by
      rw [sub_eq_iff_eq_add] at rel
      rw [rel, add_comm]
      congr 1
      by_cases h1 : a = c <;> by_cases h2 : b = c
      · subst h1; subst h2; simp
      · subst h1; simp [h2]
      · subst h2; simp [h1, Ne.symm h1]
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
    rw [hlw, rel', hwt, ← add_smul]
    congr 1
    push_cast
    ring

lemma exists_tor (ε : Fin n → Bool) (θ : Fin n → ℝ) : ∃ k : KG ε, toMK k = tor θ := by
  have hH : (tor θ)ᴴ = tor (-θ) := by
    unfold tor
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    simp only [Pi.star_apply, Pi.neg_apply, RCLike.star_def, ← Complex.exp_conj]
    simp
  have hm : ∀ θ : Fin n → ℝ, tor θ * tor (-θ) = 1 := by
    intro θ
    unfold tor
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    rw [← Complex.exp_add]
    simp
  have h1 : tor θ * (tor θ)ᴴ = 1 := by rw [hH, hm]
  have h2 : (tor θ)ᴴ * tor θ = 1 := by
    have := hm (-θ)
    rwa [neg_neg, ← hH] at this
  have hJ : tor θ * Jm ε = Jm ε * tor θ := by
    unfold tor Jm
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    exact mul_comm _ _
  have hUJ : inUJ ε (tor θ) := by
    unfold inUJ
    rw [Matrix.mul_assoc, ← hJ, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hK : tor θ ∈ Kset ε := by
    refine ⟨?_, hJ⟩
    rw [Matrix.mem_unitaryGroup_iff]
    exact h1
  let u : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨tor θ, (tor θ)ᴴ, h1, h2⟩
  let g : UJ ε := ⟨u, hUJ⟩
  exact ⟨⟨g, hK⟩, rfl⟩

lemma inner_op_op {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) (u v : T.V) :
    inner ℂ (T.op k u) (T.op k v) = inner ℂ u v := by
  have hu : star (T.op k) * T.op k = 1 := Unitary.star_mul_self_of_mem (T.τ k).2
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint]
  have : star (T.op k) (T.op k v) = v := by
    have h : (star (T.op k) * T.op k) v = v := by rw [hu]; rfl
    exact h
  rw [this]

lemma wt_eq (hR : RhoTorus) (hT : TorW) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {m : ℕ}
    {η : Fin n → ℝ} {a : AS T m}
    (ha : ∀ (θ : Fin n → ℝ) (k : KG ε), toMK k = tor θ →
      rhoA T m k a = Complex.exp (((∑ c, η c * θ c : ℝ) : ℂ) * Complex.I) • a)
    (x : Wd n m) (hx : inner ℂ T.w (a x) ≠ 0) (c : Fin n) : wtL c (ofW x) = η c - Λ c := by
  by_contra hne
  set v : ℝ := η c - Λ c - wtL c (ofW x) with hv
  have hv0 : v ≠ 0 := fun h => hne (by rw [hv] at h; linarith)
  set t : ℝ := Real.pi / v with ht
  have htv : t * v = Real.pi := by rw [ht]; field_simp
  set θ : Fin n → ℝ := Pi.single c t with hθ
  obtain ⟨k, hk⟩ := exists_tor ε θ
  have h1 : rhoA T m k a x = Complex.exp (((∑ c, η c * θ c : ℝ) : ℂ) * Complex.I) • a x := by
    rw [ha θ k hk]; rfl
  have h2 := hR n ε Λ T m θ k hk a x
  have h3 := hT n ε Λ T θ k hk
  have hS : (∑ i, (θ (x.2 i).1 - θ (x.2 i).2) : ℝ) = t * wtL c (ofW x) := by
    unfold wtL ofW
    rw [List.map_ofFn, List.sum_ofFn, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hθ, Pi.single_apply, Function.comp_apply]
    split_ifs <;> simp
  have hE : (∑ a, η a * θ a : ℝ) = t * η c := by
    simp [hθ, Pi.single_apply, mul_comm]
  have hL : (∑ a, Λ a * θ a : ℝ) = t * Λ c := by
    simp [hθ, Pi.single_apply, mul_comm]
  rw [hS] at h2
  rw [hE] at h1
  rw [hL] at h3
  set E1 : ℂ := Complex.exp (((t * wtL c (ofW x) : ℝ) : ℂ) * Complex.I) with hE1
  set E2 : ℂ := Complex.exp (((t * η c : ℝ) : ℂ) * Complex.I) with hE2
  set E3 : ℂ := Complex.exp (((t * Λ c : ℝ) : ℂ) * Complex.I) with hE3
  have h4 : E1 • T.op k (a x) = E2 • a x := by rw [← h2, h1]
  have h5 : E1 * inner ℂ T.w (a x) = (starRingEnd ℂ) E3 * E2 * inner ℂ T.w (a x) := by
    calc E1 * inner ℂ T.w (a x) = E1 * inner ℂ (T.op k T.w) (T.op k (a x)) := by rw [inner_op_op]
      _ = inner ℂ (T.op k T.w) (E1 • T.op k (a x)) := by rw [inner_smul_right]
      _ = (starRingEnd ℂ) E3 * E2 * inner ℂ T.w (a x) := by
        rw [h4, h3, inner_smul_right, inner_smul_left]; ring
  have h6 : E1 = (starRingEnd ℂ) E3 * E2 := mul_right_cancel₀ hx h5
  have h7 : (starRingEnd ℂ) E3 * E3 = 1 := by
    rw [hE3, ← Complex.exp_conj, ← Complex.exp_add]
    simp
  have h8 : E1 * E3 = E2 := by
    rw [h6]
    calc (starRingEnd ℂ) E3 * E2 * E3 = ((starRingEnd ℂ) E3 * E3) * E2 := by ring
      _ = E2 := by rw [h7, one_mul]
  have h9 : E2 = -(E1 * E3) := by
    have : ((t * η c : ℝ) : ℂ) * Complex.I = ((t * wtL c (ofW x) : ℝ) : ℂ) * Complex.I +
        ((t * Λ c : ℝ) : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I := by
      rw [← htv, hv]
      push_cast
      ring
    rw [hE2, this, Complex.exp_add, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have h10 : E1 * E3 ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
  apply h10
  have h11 : E1 * E3 = -(E1 * E3) := by rw [← h9, h8]
  have h12 : (2 : ℂ) * (E1 * E3) = 0 := by linear_combination h11
  simpa using h12

theorem betaWeight : HolFacts → RhoTorus → TorW → BetaWeight := by
  intro H hR hT n ε Λ T μ m η a ha
  refine ⟨?_, ?_⟩
  · unfold betaF
    exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨ofW x, rfl⟩)
  · intro c
    unfold betaF
    rw [lop_sum _ _ _ fun x => Submodule.smul_mem _ _ (lw_mem H μ (ofW x)), Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [lop_smul _ _ (lw_mem H μ (ofW x)), lop_lw H]
    by_cases hx : inner ℂ T.w (a x) = 0
    · simp [hx]
    · rw [wt_eq hR hT T ha x hx c, smul_comm]
      congr 2
      push_cast
      ring

end GlobalTheory.CompanionTheory.TorusSymbol
