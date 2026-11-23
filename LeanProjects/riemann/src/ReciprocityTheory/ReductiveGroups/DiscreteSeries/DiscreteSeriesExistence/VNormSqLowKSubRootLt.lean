import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeKType
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeExpK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFCoreA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.VogDrop

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem vNormSq_lowK_sub_root_lt {ε : Fin n → Bool} {lam : Fin n → ℝ} (hmono : StrictAnti lam) {a b : Fin n}
    (hab : a < b) (hne : ε a ≠ ε b) :
    Formalism.MainNotions.S.vNormSq ε (Formalism.QuantumDeterminants.lowK ε lam - root a b) < Formalism.MainNotions.S.vNormSq ε (Formalism.QuantumDeterminants.lowK ε lam) := by
  have hab' : a ≠ b := hab.ne
  have hba : ¬ b < a := not_lt.mpr hab.le
  have hrho : ∀ x : Fin n, Formalism.REAL.rhoN ε x + Formalism.REAL.rhoC ε x =
      (∑ c : Fin n, ((if x < c then (1:ℝ) else 0) - (if c < x then 1 else 0))) / 2 := by
    intro x
    have e1 : (∑ c : Fin n, if x < c then (1:ℝ) else 0) =
        (∑ c : Fin n, if x < c ∧ ε c ≠ ε x then (1:ℝ) else 0) +
          ∑ c : Fin n, if x < c ∧ ε c = ε x then (1:ℝ) else 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases h1 : x < c <;> by_cases h2 : ε c = ε x <;> simp [h1, h2]
    have e2 : (∑ c : Fin n, if c < x then (1:ℝ) else 0) =
        (∑ c : Fin n, if c < x ∧ ε c ≠ ε x then (1:ℝ) else 0) +
          ∑ c : Fin n, if c < x ∧ ε c = ε x then (1:ℝ) else 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases h1 : c < x <;> by_cases h2 : ε c = ε x <;> simp [h1, h2]
    unfold Formalism.REAL.rhoN Formalism.REAL.rhoC
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [Finset.sum_sub_distrib, e1, e2]
    ring
  have i1 : ∀ c : Fin n, (if b < c then (1:ℝ) else 0) ≤ if a < c then 1 else 0 := by
    intro c
    split_ifs <;> first | exact absurd (lt_trans hab ‹b < c›) ‹¬a < c› | norm_num
  have i2 : ∀ c : Fin n, (if c < a then (1:ℝ) else 0) ≤ if c < b then 1 else 0 := by
    intro c
    split_ifs <;> first | exact absurd (lt_trans ‹c < a› hab) ‹¬c < b› | norm_num
  have hS : 2 ≤ ∑ c : Fin n, (((if a < c then (1:ℝ) else 0) - (if c < a then 1 else 0)) -
      ((if b < c then 1 else 0) - (if c < b then 1 else 0))) := by
    have hsub := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ ({a, b} : Finset (Fin n)))
      (f := fun c : Fin n => ((if a < c then (1:ℝ) else 0) - (if c < a then 1 else 0)) -
        ((if b < c then 1 else 0) - (if c < b then 1 else 0)))
      (fun c _ _ => by
        try dsimp only
        linarith [i1 c, i2 c])
    rw [Finset.sum_pair hab'] at hsub
    have fa : ((if a < a then (1:ℝ) else 0) - (if a < a then 1 else 0)) -
        ((if b < a then 1 else 0) - (if a < b then 1 else 0)) = 1 := by
      simp [hab, hba]
    have fb : ((if a < b then (1:ℝ) else 0) - (if b < a then 1 else 0)) -
        ((if b < b then 1 else 0) - (if b < b then 1 else 0)) = 1 := by
      simp [hab, hba]
    linarith
  set w : Fin n → ℝ := Formalism.QuantumDeterminants.lowK ε lam + (2:ℝ) • Formalism.REAL.rhoC ε with hw
  have hwx : ∀ x, w x = lam x + (Formalism.REAL.rhoN ε x + Formalism.REAL.rhoC ε x) := by
    intro x
    simp only [hw, Formalism.QuantumDeterminants.lowK, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hgap : 1 < w a - w b := by
    rw [hwx a, hwx b, hrho a, hrho b]
    have hl : lam b < lam a := hmono hab
    rw [Finset.sum_sub_distrib] at hS
    linarith
  have hr : ∀ c, root a b c = (if c = a then (1:ℝ) else 0) - (if c = b then 1 else 0) := by
    intro c
    simp [root, Pi.single_apply]
  have hsum : ∑ c, (root a b c * root a b c - 2 * (w c * root a b c)) = 2 - 2 * (w a - w b) := by
    rw [Fintype.sum_eq_add a b hab']
    · rw [hr a, hr b]
      simp only [if_neg hab', if_neg hab'.symm, eq_self_iff_true, ↓reduceIte]
      ring
    · intro c hc
      rw [hr c]
      simp [hc.1, hc.2]
  have hL : Formalism.MainNotions.S.vNormSq ε (Formalism.QuantumDeterminants.lowK ε lam - root a b) =
      ∑ c, (w c - root a b c) * (w c - root a b c) := by
    unfold Formalism.MainNotions.S.vNormSq Formalism.REAL.nsq Formalism.REAL.dot
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [hw, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hR : Formalism.MainNotions.S.vNormSq ε (Formalism.QuantumDeterminants.lowK ε lam) = ∑ c, w c * w c := by
    unfold Formalism.MainNotions.S.vNormSq Formalism.REAL.nsq Formalism.REAL.dot
    rfl
  have hexp : ∑ c, (w c - root a b c) * (w c - root a b c) =
      ∑ c, w c * w c + (2 - 2 * (w a - w b)) := by
    rw [← hsum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hL, hR, hexp]
  linarith

theorem CDom_lowWt {ε : Fin n → Bool} (μ : Fin n → ℝ) :
    ∀ l : List (Fin n × Fin n), (∀ p ∈ l, IsKLow ε p) → Formalism.MainNotions.S.CDom ε (lowWt μ l) μ
  | [], _ => ⟨fun _ _ => 0, fun a b h => absurd rfl h, by simp [lowWt]⟩
  | p :: l, hl => by
    obtain ⟨c, hc, hsum⟩ := CDom_lowWt μ l fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hp := hl p (List.mem_cons_self ..)
    refine ⟨fun a b => c a b + if a = p.2 ∧ b = p.1 then 1 else 0, fun a b h => ?_, ?_⟩
    · by_cases h' : a = p.2 ∧ b = p.1
      · obtain ⟨rfl, rfl⟩ := h'; exact ⟨hp.1, hp.2.symm⟩
      · dsimp only at h; rw [if_neg h', add_zero] at h; exact hc a b h
    · have e : ∀ a b : Fin n, ((c a b + if a = p.2 ∧ b = p.1 then 1 else 0 : ℕ) : ℝ) • Formalism.REAL.root a b =
          (c a b : ℝ) • Formalism.REAL.root a b + if a = p.2 ∧ b = p.1 then Formalism.REAL.root a b else 0 := by
        intro a b; split_ifs <;> simp [add_smul]
      simp only [e, Finset.sum_add_distrib]
      rw [← hsum]
      have h2 : (∑ a : Fin n, ∑ b : Fin n, if a = p.2 ∧ b = p.1 then Formalism.REAL.root a b else 0) =
          Formalism.REAL.root p.2 p.1 := by
        rw [Finset.sum_eq_single p.2]
        · rw [Finset.sum_eq_single p.1]
          · simp
          · intro b _ hb; simp [hb]
          · simp
        · intro a _ ha; apply Finset.sum_eq_zero; intro b _; simp [ha]
        · simp
      rw [h2]
      ext i
      simp only [lowWt, Formalism.REAL.root, root, Pi.sub_apply, Pi.add_apply]
      ring

section Module

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M}

theorem exists_irr_sub_of_khw (hE : IsGlRep E) (hU : IsInfUnitary ε E) (S : Submodule ℂ M)
    (hSf : FiniteDimensional ℂ S) (hSk : IsKStableSub ε E S) {μ : Fin n → ℝ} {y : M} (hyS : y ∈ S) (hy0 : y ≠ 0)
    (hy : IsKHWVec ε E μ y) : ∃ S' : Submodule ℂ M, S' ≤ S ∧ y ∈ S' ∧ IsKIrrHW ε E μ S' := by
  have hle := kLowSpan_le (E := E) hSk hyS
  have : FiniteDimensional ℂ (kLowSpan ε E y) := Submodule.finiteDimensional_of_le hle
  exact ⟨_, hle, self_mem_kLowSpan y, kLowSpan_kIrrHW hE hU hy hy0 this⟩

theorem weights_le_of_irr_hw (hE : IsGlRep E) (hU : IsInfUnitary ε E) {μ : Fin n → ℝ} {S : Submodule ℂ M}
    (hS : IsKIrrHW ε E μ S) {ν : Fin n → ℝ} {x : M} (hxS : x ∈ S) (hx0 : x ≠ 0)
    (hν : ∀ a, E a a x = ((ν a : ℝ) : ℂ) • x) : Formalism.MainNotions.S.CDom ε ν μ := by
  obtain ⟨w, hwS, hw0, hw⟩ := hS.2.2.2
  have hle := kLowSpan_le (E := E) hS.2.1 hwS
  have heq : kLowSpan ε E w = S := by
    rcases hS.2.2.1 _ hle (kLowSpan_kStable hE hw) with h | h
    · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ self_mem_kLowSpan w)) hw0
    · exact h
  by_contra hno
  have horth : kLowSpan ε E w ≤ (ℂ ∙ x)ᗮ := by
    refine Submodule.span_le.2 ?_
    rintro z ⟨l, hl, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left]
    have hne : lowWt μ l ≠ ν := fun h => hno (h ▸ CDom_lowWt μ l hl)
    obtain ⟨a, ha⟩ := Function.ne_iff.1 hne
    have h1 := hU a a (lowWord E w l) x
    rw [lowWord_wt hE hw.1 l a, hν a, inner_smul_left, inner_smul_right] at h1
    simp only [adjSign, if_true, one_mul, Complex.conj_ofReal] at h1
    have h2 : ((lowWt μ l a : ℂ) - (ν a : ℂ)) * inner ℂ (lowWord E w l) x = 0 := by
      rw [sub_mul, h1, sub_self]
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd (by exact_mod_cast sub_eq_zero.1 h) ha
    · exact h
  have h0 : inner ℂ x x = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.1 (horth (heq ▸ hxS))
  exact hx0 (inner_self_eq_zero.1 h0)

theorem khw_line_of_irr (hE : IsGlRep E) (hU : IsInfUnitary ε E) {μ : Fin n → ℝ} {S : Submodule ℂ M}
    (hS : IsKIrrHW ε E μ S) {x y : M} (hx : x ∈ S) (hy : y ∈ S) (hxw : IsKHWVec ε E μ x)
    (hyw : IsKHWVec ε E μ y) (hy0 : y ≠ 0) : ∃ c : ℂ, x = c • y :=
  khw_line_of_kIrrHW hE hU hS hx hy hxw hyw hy0

end Module

end ReciprocityTheory.ChartRestriction.DS

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

private theorem casGen_inG_entry_of_lt (ε : Fin n → Bool) {a b : Fin n} (h : a < b) (i j : Fin n) :
    star (casGen ε (a, b) j i) * (if ε j then (1:ℂ) else -1) +
      (if ε i then (1:ℂ) else -1) * casGen ε (a, b) i j = 0 := by
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  simp only [casGen, casSg, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.single,
    Matrix.of_apply, smul_eq_mul]
  split_ifs <;> simp_all
  all_goals (split_ifs <;> simp_all)
  all_goals ring

private theorem casGen_inG_entry_of_eq (ε : Fin n → Bool) {a b : Fin n} (h : a = b) (i j : Fin n) :
    star (casGen ε (a, b) j i) * (if ε j then (1:ℂ) else -1) +
      (if ε i then (1:ℂ) else -1) * casGen ε (a, b) i j = 0 := by
  subst h
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  by_cases hij : a = j ∧ a = i
  · obtain ⟨hj, hi⟩ := hij
    rw [← hj, ← hi]
    have e : casGen ε (a, a) a a = Complex.I := by simp [casGen, Matrix.single]
    rw [e, hI]
    ring
  · have hji : ¬(a = i ∧ a = j) := fun h' => hij ⟨h'.2, h'.1⟩
    have e1 : casGen ε (a, a) j i = 0 := by simp [casGen, Matrix.single, hij]
    have e2 : casGen ε (a, a) i j = 0 := by simp [casGen, Matrix.single, hji]
    rw [e1, e2]
    simp

private theorem casGen_inG_entry_of_gt (ε : Fin n → Bool) {a b : Fin n} (h : b < a) (i j : Fin n) :
    star (casGen ε (a, b) j i) * (if ε j then (1:ℂ) else -1) +
      (if ε i then (1:ℂ) else -1) * casGen ε (a, b) i j = 0 := by
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  simp only [casGen, casSg, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.single,
    Matrix.of_apply, smul_eq_mul]
  split_ifs <;> simp_all
  all_goals (split_ifs <;> simp_all)
  all_goals ring

theorem inG_casGen' (ε : Fin n → Bool) (p : Fin n × Fin n) : inG ε (casGen ε p) := by
  obtain ⟨a, b⟩ := p
  unfold inG Jm
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
    Matrix.zero_apply]
  rcases lt_trichotomy a b with h | h | h
  · exact casGen_inG_entry_of_lt ε h i j
  · exact casGen_inG_entry_of_eq ε h i j
  · exact casGen_inG_entry_of_gt ε h i j

section Equiv

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {ε : Fin n → Bool}
  {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)}
  {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)}

private theorem inUJ_exp_of_conjTranspose_Jm_add_Jm_mul_eq_zero {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Yᴴ * Jm ε + Jm ε * Y = 0) :
    inUJ ε (NormedSpace.exp Y) := by
  have hJJ : Jm ε * Jm ε = 1 := by
    unfold Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    by_cases h : ε a <;> simp [h]
  have hYc : Yᴴ = Jm ε * (-Y) * Jm ε := by
    have h1 : Yᴴ * Jm ε = -(Jm ε * Y) := eq_neg_of_add_eq_zero_left hY
    calc Yᴴ = Yᴴ * Jm ε * Jm ε := by rw [mul_assoc, hJJ, mul_one]
      _ = Jm ε * (-Y) * Jm ε := by rw [h1, mul_neg, neg_mul]
  let u : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨Jm ε, Jm ε, hJJ, hJJ⟩
  have hexp : (NormedSpace.exp Y)ᴴ = Jm ε * NormedSpace.exp (-Y) * Jm ε := by
    have e1 := Matrix.exp_conjTranspose Y
    rw [hYc] at e1
    exact e1.symm.trans (Matrix.exp_units_conj u (-Y))
  have h2 : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    have e3 := Matrix.exp_add_of_commute (-Y) Y (Commute.neg_left (Commute.refl Y))
    rw [neg_add_cancel] at e3
    have e4 : NormedSpace.exp (0 : Matrix (Fin n) (Fin n) ℂ) = 1 := NormedSpace.exp_zero
    exact e3.symm.trans e4
  unfold inUJ
  rw [hexp]
  simp only [mul_assoc]
  rw [← mul_assoc (Jm ε) (Jm ε), hJJ, one_mul, h2, mul_one]

private theorem deriv_linearIsometryEquiv_comp_zero {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (U : E ≃ₗᵢ[ℂ] F) (f : ℝ → E) :
    deriv (fun t => U (f t)) 0 = U (deriv f 0) := by
  let L : E →L[ℝ] F := ((U.toContinuousLinearEquiv : E ≃L[ℂ] F) : E →L[ℂ] F).restrictScalars ℝ
  let L' : F →L[ℝ] E := ((U.symm.toContinuousLinearEquiv : F ≃L[ℂ] E) : F →L[ℂ] E).restrictScalars ℝ
  by_cases hd : DifferentiableAt ℝ f 0
  · exact (L.hasFDerivAt.comp_hasDerivAt (0:ℝ) hd.hasDerivAt).deriv
  · have hd' : ¬ DifferentiableAt ℝ (fun t => U (f t)) 0 := by
      intro h
      apply hd
      have h2 : DifferentiableAt ℝ (fun t => U.symm (U (f t))) 0 := L'.differentiableAt.comp (0:ℝ) h
      simpa using h2
    rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hd', map_zero]

theorem dS_map_isometry (U : H₁ ≃ₗᵢ[ℂ] H₂) (hU : ∀ g ∈ UJset ε, ∀ x : H₁, U (σ₁ g x) = σ₂ g (U x))
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (x : H₁) : dS σ₂ X (U x) = U (dS σ₁ X x) := by
  have hg : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ UJset ε := by
    intro t
    have hX' : Xᴴ * Jm ε + Jm ε * X = 0 := hX
    have hs : star (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
    have hY : ((t : ℂ) • X)ᴴ * Jm ε + Jm ε * ((t : ℂ) • X) = 0 := by
      rw [Matrix.conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX', smul_zero]
    exact inUJ_exp_of_conjTranspose_Jm_add_Jm_mul_eq_zero hY
  show deriv (fun t : ℝ => σ₂ (NormedSpace.exp ((t : ℂ) • X)) (U x)) 0 =
    U (deriv (fun t : ℝ => σ₁ (NormedSpace.exp ((t : ℂ) • X)) x) 0)
  have hfun : (fun t : ℝ => σ₂ (NormedSpace.exp ((t : ℂ) • X)) (U x)) =
      fun t : ℝ => U (σ₁ (NormedSpace.exp ((t : ℂ) • X)) x) := by
    funext t
    exact (hU _ (hg t) x).symm
  rw [hfun]
  exact deriv_linearIsometryEquiv_comp_zero U _

theorem dS_casGen_map_isometry (U : H₁ ≃ₗᵢ[ℂ] H₂) (hU : ∀ g ∈ UJset ε, ∀ x : H₁, U (σ₁ g x) = σ₂ g (U x))
    (p : Fin n × Fin n) (x : H₁) : dS σ₂ (casGen ε p) (U x) = U (dS σ₁ (casGen ε p) x) := dS_map_isometry U hU (inG_casGen' ε p) x

theorem casU_map_isometry (U : H₁ ≃ₗᵢ[ℂ] H₂) (hU : ∀ g ∈ UJset ε, ∀ x : H₁, U (σ₁ g x) = σ₂ g (U x))
    (x : H₁) : casU ε σ₂ (U x) = U (casU ε σ₁ x) := by
  unfold casU
  simp only [dS_casGen_map_isometry U hU, map_neg, map_sum, map_smul]

theorem smooth_symm_of_isometry (U : H₁ ≃ₗᵢ[ℂ] H₂) (hU : ∀ g ∈ UJset ε, ∀ x : H₁, U (σ₁ g x) = σ₂ g (U x))
    {v : H₂} (hv : IsSmoothVecU ε σ₂ v) : IsSmoothVecU ε σ₁ (U.symm v) := by
  unfold IsSmoothVecU S7.SmoothOnGV at *
  intro g₀ hg₀
  obtain ⟨V, F, hV, hg₀V, hF, hFeq⟩ := hv g₀ hg₀
  refine ⟨V, fun g => U.symm (F g), hV, hg₀V, ?_, ?_⟩
  · exact (((U.symm.toContinuousLinearEquiv : H₂ ≃L[ℂ] H₁) : H₂ →L[ℂ] H₁).restrictScalars ℝ).contDiff.comp_contDiffOn hF
  · intro g hgV hg
    have h3 : σ₂ g v = F g := hFeq g hgV hg
    show σ₁ g (U.symm v) = U.symm (F g)
    rw [← h3]
    apply U.injective
    rw [hU g hg, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]

end Equiv

theorem casOnSmooth_of_equiv {ε : Fin n → Bool} {lam : Fin n → ℝ}
    {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)}
    {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)}
    (U : H₁ ≃ₗᵢ[ℂ] H₂) (hU : ∀ g ∈ UJset ε, ∀ x : H₁, U (σ₁ g x) = σ₂ g (U x))
    (h₁ : CasOnSmooth ε lam σ₁) : CasOnSmooth ε lam σ₂ := by
  intro v hv
  have h := h₁ (U.symm v) (smooth_symm_of_isometry U hU hv)
  have h2 := casU_map_isometry U hU (U.symm v)
  rw [LinearIsometryEquiv.apply_symm_apply] at h2
  rw [h2, h, map_smul, LinearIsometryEquiv.apply_symm_apply]

end ReciprocityTheory.ChartRestriction.DS
