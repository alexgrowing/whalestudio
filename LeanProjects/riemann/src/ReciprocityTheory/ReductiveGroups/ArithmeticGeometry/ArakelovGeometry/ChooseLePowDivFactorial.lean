import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.SectionModuleEqSpanPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.EqZeroOfSecTraceMulEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ExistsNatMulMemConeRingIntFin

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo Module Filter Asymptotics

variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Fintype κ] {D : ℕ}

theorem prod_div_pow_degree (x : κ → Ω) (j : κ) (m : κ →₀ ℕ) :
    (m.prod fun i k => x i ^ k) / x j ^ (Finsupp.degree m) = m.prod fun i k => (x i / x j) ^ k := by
  simp only [Finsupp.prod, Finsupp.degree, div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  rfl

theorem div_pow_mem_fnField (x : κ → Ω) (j : κ) {n : ℕ} {s : Ω} (hs : s ∈ sec ℤ x n) :
    s / x j ^ n ∈ fnField x := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.sec at hs
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.1 hs
  have hhom := (MvPolynomial.mem_homogeneousSubmodule n p).1 hp
  rw [AlgHom.toLinearMap_apply, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, Finset.sum_div]
  refine sum_mem fun m hm => ?_
  have hdeg : Finsupp.degree m = n := by
    rw [Finsupp.degree_eq_weight_one]
    exact hhom (MvPolynomial.mem_support_iff.1 hm)
  rw [mul_div_assoc]
  refine mul_mem ?_ ?_
  · rw [eq_intCast]
    exact intCast_mem _ _
  · have hprod := prod_div_pow_degree x j m
    rw [hdeg] at hprod
    rw [show (∏ i ∈ m.support, x i ^ m i) = m.prod fun i k => x i ^ k from rfl, hprod]
    exact prod_mem fun i _ => pow_mem (IntermediateField.subset_adjoin ℚ {t : Ω | ∃ i j, t = x i / x j} ⟨i, j, rfl⟩) _

theorem coord_ne_zero_of_free (y : Fin (D + 1) → Ω) (hy : coordIdeal ℤ y = ⊥) (l : Fin (D + 1)) : y l ≠ 0 := by
  intro h0
  have hX : (MvPolynomial.X l : MvPolynomial (Fin (D + 1)) ℤ) ∈ coordIdeal ℤ y := by
    unfold ReciprocityTheory.ChartRestriction.G.Geo.coordIdeal
    rw [RingHom.mem_ker]
    simp [ReciprocityTheory.ChartRestriction.G.Geo.coneMap, h0]
  rw [hy] at hX
  exact MvPolynomial.X_ne_zero l (Ideal.mem_bot.1 hX)

theorem alpha_mem (x : κ → Ω) (e : Fin (D + 1) → κ) {k n δ : ℕ} (ε : Fin δ → Ω)
    (hε : ∀ l, ε l ∈ sec ℤ x k) (P : Fin δ → Ω) (hP : ∀ l, P l ∈ sec ℤ (x ∘ e) n) :
    ∑ l, P l * ε l ∈ sec ℤ x (n + k) := by
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [← sec_mul_sec]
  refine Submodule.mul_mem_mul ?_ (hε l)
  have hl := hP l
  unfold ReciprocityTheory.ChartRestriction.G.Geo.sec at hl ⊢
  obtain ⟨p, hp, hpe⟩ := Submodule.mem_map.1 hl
  refine Submodule.mem_map.2 ⟨MvPolynomial.rename e p, ?_, ?_⟩
  · exact (MvPolynomial.mem_homogeneousSubmodule n _).2
      (((MvPolynomial.mem_homogeneousSubmodule n p).1 hp).rename_isHomogeneous)
  · rw [← hpe]
    simp [MvPolynomial.aeval_rename]

theorem alpha_injective (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e) {n δ : ℕ}
    (ε : Fin δ → Ω) (hli : LinearIndependent (fnField (x ∘ e)) ε) (P : Fin δ → Ω)
    (hP : ∀ l, P l ∈ sec ℤ (x ∘ e) n) (h0 : ∑ l, P l * ε l = 0) : P = 0 := by
  have hx0 : x (e 0) ≠ 0 := coord_ne_zero_of_free (x ∘ e) h.free 0
  rw [Fintype.linearIndependent_iff] at hli
  have hmem : ∀ l, P l / (x ∘ e) 0 ^ n ∈ fnField (x ∘ e) := fun l => div_pow_mem_fnField (x ∘ e) 0 (hP l)
  have hsum : ∑ l, (⟨P l / (x ∘ e) 0 ^ n, hmem l⟩ : fnField (x ∘ e)) • ε l = 0 := by
    have hrw : ∑ l, (⟨P l / (x ∘ e) 0 ^ n, hmem l⟩ : fnField (x ∘ e)) • ε l =
        (∑ l, P l * ε l) / (x ∘ e) 0 ^ n := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [Algebra.smul_def, IntermediateField.algebraMap_apply]
      ring
    rw [hrw, h0, zero_div]
  have hg := hli _ hsum
  funext l
  have h2 : P l / (x ∘ e) 0 ^ n = 0 := congrArg Subtype.val (hg l)
  exact (div_eq_zero_iff.1 h2).resolve_right (pow_ne_zero _ hx0)

theorem secTrace_add (x : κ → Ω) (e : Fin (D + 1) → κ) (_h : IsRatProjFrame x e) (n : ℕ) {s t : Ω}
    (hs : s ∈ sec ℤ x n) (ht : t ∈ sec ℤ x n) :
    secTrace x e n (s + t) = secTrace x e n s + secTrace x e n t := by
  have hs' := div_pow_mem_fnField x (e 0) hs
  have ht' := div_pow_mem_fnField x (e 0) ht
  have hst : (s + t) / x (e 0) ^ n ∈ fnField x := by
    rw [add_div]
    exact add_mem hs' ht'
  unfold secTrace fnTrace
  rw [dif_pos hst, dif_pos hs', dif_pos ht']
  have key : (⟨(s + t) / x (e 0) ^ n, hst⟩ : IntermediateField.extendScalars (fnField_comp_le x e)) =
      ⟨s / x (e 0) ^ n, hs'⟩ + ⟨t / x (e 0) ^ n, ht'⟩ := Subtype.ext (add_div s t _)
  rw [key, map_add]
  push_cast
  ring

instance sec_moduleFinite (x : κ → Ω) (n : ℕ) : Module.Finite ℤ (sec ℤ x n) :=
  Module.Finite.iff_fg.mpr (sec_fg x n)

instance sec_moduleFree (x : κ → Ω) (n : ℕ) : Module.Free ℤ (sec ℤ x n) := inferInstance

theorem finrank_fin_pi (M : Type*) [AddCommGroup M] [Module ℤ M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (δ : ℕ) : finrank ℤ (Fin δ → M) = δ * finrank ℤ M := by
  have h := Module.finrank_pi_fintype (R := ℤ) (M := fun _ : Fin δ => M)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  convert h
  exact Subsingleton.elim _ _

noncomputable def alphaMap (x : κ → Ω) (e : Fin (D + 1) → κ) {k δ : ℕ} (ε : Fin δ → Ω) (hε : ∀ l, ε l ∈ sec ℤ x k)
    (n : ℕ) : (Fin δ → sec ℤ (x ∘ e) n) →ₗ[ℤ] sec ℤ x (n + k) where
  toFun P := ⟨∑ l, (P l : Ω) * ε l, alpha_mem x e ε hε (fun l => P l) (fun l => (P l).2)⟩
  map_add' P Q := by ext; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c P := by ext; simp [Finset.mul_sum, mul_assoc]

theorem le_finrank_sec (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsProjFrame x e) :
    ∃ k : ℕ, ∀ n, projDeg x e * (n + D).choose D ≤ finrank ℤ (sec ℤ x (n + k)) := by
  obtain ⟨k, ε, hε, hli⟩ := exists_indep_sections x e h.isRatProjFrame
  refine ⟨k, fun n => ?_⟩
  have hinj : Function.Injective (alphaMap x e ε hε n) := by
    refine (injective_iff_map_eq_zero _).2 fun P hP => ?_
    have h0 : ∑ l, (P l : Ω) * ε l = 0 := congrArg Subtype.val hP
    have h1 := alpha_injective x e h.isRatProjFrame ε hli (fun l => (P l : Ω)) (fun l => (P l).2) h0
    funext l
    exact Subtype.ext (congrFun h1 l)
  have h2 := LinearMap.finrank_le_finrank_of_injective hinj
  rw [finrank_fin_pi, finrank_sec_free (x ∘ e) h.isRatProjFrame.free n] at h2
  exact h2

noncomputable def betaMap (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsProjFrame x e) {k δ : ℕ} (ε : Fin δ → Ω)
    (hε : ∀ l, ε l ∈ sec ℤ x k) (n : ℕ) : sec ℤ x n →+ (Fin δ → sec ℤ (x ∘ e) (n + k)) :=
  AddMonoidHom.mk' (fun s l => ⟨secTrace x e (n + k) ((s : Ω) * ε l), secTrace_mem x e h (n + k)
      (by rw [← sec_mul_sec]; exact Submodule.mul_mem_mul s.2 (hε l))⟩)
    (fun s t => by
      funext l; ext
      simp only [Submodule.coe_add, add_mul, Pi.add_apply]
      have h1 := Submodule.mul_mem_mul s.2 (hε l)
      have h2 := Submodule.mul_mem_mul t.2 (hε l)
      rw [sec_mul_sec] at h1 h2
      exact secTrace_add x e h.isRatProjFrame (n + k) h1 h2)

theorem finrank_sec_le (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsProjFrame x e) :
    ∃ k : ℕ, ∀ n, finrank ℤ (sec ℤ x n) ≤ projDeg x e * (n + k + D).choose D := by
  obtain ⟨k, ε, hε, hli⟩ := exists_indep_sections x e h.isRatProjFrame
  refine ⟨k, fun n => ?_⟩
  have hinj : Function.Injective (betaMap x e h ε hε n).toIntLinearMap := by
    refine (injective_iff_map_eq_zero _).2 fun s hs => ?_
    have h0 : ∀ l, secTrace x e (n + k) ((s : Ω) * ε l) = 0 := fun l =>
      congrArg Subtype.val (congrFun hs l)
    exact Subtype.ext (eq_zero_of_secTrace_mul_eq_zero x e h.isRatProjFrame ε hε hli n s.2 h0)
  have h2 := LinearMap.finrank_le_finrank_of_injective hinj
  rw [finrank_fin_pi, finrank_sec_free (x ∘ e) h.isRatProjFrame.free (n + k)] at h2
  exact h2

theorem shift_pow_sub_pow_isBigO (D : ℕ) (a : ℝ) :
    (fun n : ℕ => ((n : ℝ) + a) ^ D - (n : ℝ) ^ D) =O[atTop] fun n : ℕ => (n : ℝ) ^ D / (n : ℝ) := by
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · simp
    exact Asymptotics.isBigO_zero _ _
  have key : (fun n : ℕ => ((n : ℝ) + a) ^ D - (n : ℝ) ^ D) =
      ∑ i ∈ Finset.range D, fun n : ℕ => (n : ℝ) ^ i * a ^ (D - i) * (D.choose i : ℝ) := by
    funext n
    rw [Finset.sum_apply, add_pow, Finset.sum_range_succ]
    simp
  rw [key]
  refine Asymptotics.IsBigO.sum fun i hi => ?_
  have hi' : i + 1 ≤ D := Finset.mem_range.1 hi
  refine Asymptotics.IsBigO.of_bound (|a| ^ (D - i) * (D.choose i : ℝ)) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := by linarith
  have hdiv : (n : ℝ) ^ D / n = (n : ℝ) ^ (D - 1) := by
    rw [div_eq_iff hpos.ne', ← pow_succ, Nat.sub_add_cancel hD]
  rw [hdiv]
  simp only [Real.norm_eq_abs, abs_mul, abs_pow, Nat.abs_cast]
  have hle : (n : ℝ) ^ i ≤ (n : ℝ) ^ (D - 1) := pow_le_pow_right₀ hn' (by omega)
  have hc : 0 ≤ |a| ^ (D - i) * (D.choose i : ℝ) := by positivity
  nlinarith

theorem pow_div_factorial_le_choose (m D : ℕ) : ((m : ℝ) ^ D) / (D.factorial : ℝ) ≤ ((m + D).choose D : ℝ) := by
  have h1 : m + D + 1 - D = m + 1 := by omega
  have h2 := Nat.pow_le_choose (α := ℝ) D (m + D)
  rw [h1] at h2
  refine le_trans ?_ h2
  gcongr
  push_cast
  linarith

theorem choose_le_pow_div_factorial (N D : ℕ) : (N.choose D : ℝ) ≤ ((N : ℝ) ^ D) / (D.factorial : ℝ) := by
  exact Nat.choose_le_pow_div (α := ℝ) D N

theorem finrank_sec_asymp (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsProjFrame x e) :
    (fun n : ℕ => (finrank ℤ (sec ℤ x n) : ℝ) - (projDeg x e : ℝ) * (n : ℝ) ^ D / (D.factorial : ℝ))
      =O[atTop] fun n : ℕ => (n : ℝ) ^ D / (n : ℝ) := by
  obtain ⟨k1, hk1⟩ := le_finrank_sec x e h
  obtain ⟨k2, hk2⟩ := finrank_sec_le x e h
  have hup := (shift_pow_sub_pow_isBigO D ((k2 : ℝ) + D)).const_mul_left
    ((projDeg x e : ℝ) / D.factorial)
  have hlo := (shift_pow_sub_pow_isBigO D (-(k1 : ℝ))).const_mul_left
    ((projDeg x e : ℝ) / D.factorial)
  refine Asymptotics.IsBigO.trans ?_ (hup.norm_left.add hlo.norm_left)
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Filter.eventually_ge_atTop k1] with n hn
  have hL : (projDeg x e : ℝ) * (((n - k1 : ℕ) : ℝ) ^ D / D.factorial) ≤ finrank ℤ (sec ℤ x n) := by
    have h1 := hk1 (n - k1)
    rw [Nat.sub_add_cancel hn] at h1
    have h1' : ((projDeg x e * (n - k1 + D).choose D : ℕ) : ℝ) ≤ (finrank ℤ (sec ℤ x n) : ℝ) := by
      exact_mod_cast h1
    push_cast at h1'
    exact le_trans (mul_le_mul_of_nonneg_left (pow_div_factorial_le_choose (n - k1) D) (Nat.cast_nonneg _)) h1'
  have hU : (finrank ℤ (sec ℤ x n) : ℝ) ≤ (projDeg x e : ℝ) * (((n + k2 + D : ℕ) : ℝ) ^ D / D.factorial) := by
    have h1 : ((finrank ℤ (sec ℤ x n) : ℕ) : ℝ) ≤ ((projDeg x e * (n + k2 + D).choose D : ℕ) : ℝ) := by
      exact_mod_cast hk2 n
    push_cast at h1
    exact le_trans h1 (mul_le_mul_of_nonneg_left (choose_le_pow_div_factorial (n + k2 + D) D) (Nat.cast_nonneg _))
  rw [Nat.cast_sub hn] at hL
  push_cast at hU
  rw [one_mul, Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  simp only [Real.norm_eq_abs]
  have eA : (projDeg x e : ℝ) / D.factorial * (((n : ℝ) + ((k2 : ℝ) + D)) ^ D - (n : ℝ) ^ D) =
      (projDeg x e : ℝ) * (((n : ℝ) + k2 + D) ^ D / D.factorial) - (projDeg x e : ℝ) * (n : ℝ) ^ D / D.factorial := by
    ring
  have eB : (projDeg x e : ℝ) / D.factorial * (((n : ℝ) + -(k1 : ℝ)) ^ D - (n : ℝ) ^ D) =
      (projDeg x e : ℝ) * (((n : ℝ) - k1) ^ D / D.factorial) - (projDeg x e : ℝ) * (n : ℝ) ^ D / D.factorial := by
    ring
  have a1 := le_abs_self ((projDeg x e : ℝ) / D.factorial * (((n : ℝ) + ((k2 : ℝ) + D)) ^ D - (n : ℝ) ^ D))
  have a2 := neg_abs_le ((projDeg x e : ℝ) / D.factorial * (((n : ℝ) + -(k1 : ℝ)) ^ D - (n : ℝ) ^ D))
  have a3 := abs_nonneg ((projDeg x e : ℝ) / D.factorial * (((n : ℝ) + ((k2 : ℝ) + D)) ^ D - (n : ℝ) ^ D))
  have a4 := abs_nonneg ((projDeg x e : ℝ) / D.factorial * (((n : ℝ) + -(k1 : ℝ)) ^ D - (n : ℝ) ^ D))
  rw [abs_le]
  constructor <;> linarith

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
