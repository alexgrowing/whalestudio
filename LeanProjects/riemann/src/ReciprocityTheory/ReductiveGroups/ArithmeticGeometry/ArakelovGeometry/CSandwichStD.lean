import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CSandwichStC

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Matrix

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem injective_map_of_int_ker {R r : ℕ} (M : Matrix (Fin R) (Fin r) ℤ)
    (key : ∀ u : Fin r → ℤ, M *ᵥ u = 0 → u = 0) :
    Function.Injective (M.map (Int.cast : ℤ → ℚ)).mulVec := by
  intro v w hvw
  have hd : M.map (Int.cast : ℤ → ℚ) *ᵥ (v - w) = 0 := by
    rw [Matrix.mulVec_sub, hvw, sub_self]
  obtain ⟨⟨c, hc⟩, hcu⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (v - w)
  choose u hu using hcu
  have hu2 : ∀ i, ((u i : ℤ) : ℚ) = (c : ℚ) * (v - w) i := fun i => by
    have := hu i
    simp only [zsmul_eq_mul, algebraMap_int_eq, eq_intCast] at this
    exact this
  have hMu : M *ᵥ u = 0 := by
    funext p
    have h1 := RingHom.map_mulVec (Int.castRingHom ℚ) M u p
    have h2 : (Int.castRingHom ℚ) ∘ u = (c : ℚ) • (v - w) := by
      funext i; simp [hu2 i]
    rw [h2, Matrix.mulVec_smul] at h1
    simp only [Int.coe_castRingHom] at h1
    rw [hd, smul_zero] at h1
    simp only [Pi.zero_apply] at h1 ⊢
    exact_mod_cast h1
  have hu0 := key u hMu
  have hc0 : c ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hc
  funext i
  have := hu2 i
  rw [hu0] at this
  simp only [Pi.zero_apply, Int.cast_zero] at this
  have h3 : (v - w) i = 0 := by
    rcases mul_eq_zero.mp this.symm with h | h
    · exact absurd (by exact_mod_cast h) hc0
    · exact h
  simpa [sub_eq_zero] using h3

theorem exists_cols_det_ne_zero {r : ℕ} {ι : Type} [Finite ι] (u : ι → Fin r → ℤ)
    (hspan : ∀ v : Fin r → ℤ, v ∈ Submodule.span ℤ (Set.range u)) :
    ∃ f : Fin r → ι, (Matrix.of fun p q => u (f q) p).det ≠ 0 := by
  classical
  set uq : ι → Fin r → ℚ := fun i p => (u i p : ℚ) with huq
  have h1 : ∀ v : Fin r → ℤ, (fun p => (v p : ℚ)) ∈ Submodule.span ℚ (Set.range uq) := by
    intro v
    induction hspan v using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero =>
      have h0 : (fun p => ((0 : Fin r → ℤ) p : ℚ)) = 0 := by funext p; simp
      rw [h0]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have : (fun p => ((x + y) p : ℚ)) = (fun p => (x p : ℚ)) + fun p => (y p : ℚ) := by
        funext p; simp
      rw [this]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      have : (fun p => ((a • x) p : ℚ)) = (a : ℚ) • fun p => (x p : ℚ) := by
        funext p; simp
      rw [this]; exact Submodule.smul_mem _ _ hx
  have htop : Submodule.span ℚ (Set.range uq) = ⊤ := by
    refine eq_top_iff.mpr fun v _ => ?_
    have hv : v = ∑ p, v p • (fun q => ((Pi.single p (1 : ℤ) : Fin r → ℤ) q : ℚ)) := by
      funext q
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hv]
    exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (h1 _)
  obtain ⟨κ', a, ha, hsp, hli⟩ := exists_linearIndependent' ℚ uq
  have : Finite κ' := Finite.of_injective a ha
  have : Fintype κ' := Fintype.ofFinite κ'
  have hsp' : ⊤ ≤ Submodule.span ℚ (Set.range (uq ∘ a)) := by rw [hsp, htop]
  have hcard : Fintype.card κ' = r := by
    have := Module.finrank_eq_card_basis (Basis.mk hli hsp')
    simpa using this.symm
  set eq := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ eq, ?_⟩
  have hli2 : LinearIndependent ℚ ((Matrix.of fun p q => u ((a ∘ eq) q) p).map
      (Int.cast : ℤ → ℚ)).col := by
    have : ((Matrix.of fun p q => u ((a ∘ eq) q) p).map (Int.cast : ℤ → ℚ)).col = uq ∘ a ∘ eq := by
      funext q p; simp [Matrix.col, huq]
    rw [this]
    exact hli.comp eq eq.injective
  rw [Matrix.linearIndependent_cols_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
    ← Int.cast_det] at hli2
  exact_mod_cast hli2

theorem adtEnum_injective (D N : ℕ) : Function.Injective (adtEnum D N) := fun _ _ h =>
  (Finset.Nat.antidiagonalTuple (D + 1) N).equivFin.symm.injective (Subtype.ext h)

theorem adtEnum_mem (D N : ℕ) (i : Fin (Finset.Nat.antidiagonalTuple (D + 1) N).card) :
    adtEnum D N i ∈ Finset.Nat.antidiagonalTuple (D + 1) N :=
  ((Finset.Nat.antidiagonalTuple (D + 1) N).equivFin.symm i).2

theorem eq_zero_of_sum_mono {y : Fin (D + 1) → Ω} (hy : coordIdeal ℤ y = ⊥) {N : ℕ}
    (u : Fin (Finset.Nat.antidiagonalTuple (D + 1) N).card → ℤ)
    (h : ∑ i, (u i : Ω) * ∏ t, y t ^ adtEnum D N i t = 0) : u = 0 := by
  classical
  set p : MvPolynomial (Fin (D + 1)) ℤ :=
    ∑ i, monomial (Finsupp.equivFunOnFinite.symm (adtEnum D N i)) (u i) with hp
  have hph : p.IsHomogeneous N := by
    refine IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_monomial _ ?_
    rw [Finsupp.degree_eq_sum]
    have := Finset.Nat.mem_antidiagonalTuple.mp (adtEnum_mem D N i)
    simpa using this
  have hpa : aeval y p = 0 := by
    rw [hp, map_sum, ← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [aeval_monomial, Finsupp.prod_fintype _ _ (by simp)]
    simp [algebraMap_int_eq]
  have hp0 : p = 0 := by
    have := mem_coordIdeal_of_isHomogeneous (o := ℤ) (x := y) hph hpa
    rwa [hy, Ideal.mem_bot] at this
  funext i
  have hc := congrArg (coeff (Finsupp.equivFunOnFinite.symm (adtEnum D N i))) hp0
  rw [hp, coeff_sum, coeff_zero] at hc
  rw [Finset.sum_eq_single i (fun j _ hji => ?_) (by simp)] at hc
  · simpa using hc
  · rw [coeff_monomial, if_neg]
    intro hE
    exact hji (adtEnum_injective D N (by simpa using hE))

theorem norm_monoC_sq_le {N : ℕ} (a : Fin N → ℕ) (w : Fin N → ℂ) :
    ‖monoC a w‖ ^ 2 ≤ sqN w ^ (∑ i, a i) := by
  rw [monoC, norm_prod, ← Finset.prod_pow, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun i _ => by positivity) fun i _ => ?_
  rw [norm_pow, ← pow_mul, mul_comm, pow_mul]
  refine pow_le_pow_left₀ (by positivity) ?_ _
  exact Finset.single_le_sum (f := fun j => ‖w j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)

theorem form_enum_sq_le (D N : ℕ) (c : Fin (Finset.Nat.antidiagonalTuple (D + 1) N).card → ℂ)
    (w : Fin (D + 1) → ℂ) :
    ‖∑ i, c i * monoC (adtEnum D N i) w‖ ^ 2 ≤ ((N + D).choose D : ℝ) * sqN w ^ N *
      ∑ i, ‖c i‖ ^ 2 * monoNormSq (adtEnum D N i) := by
  classical
  set c' : (Fin (D + 1) → ℕ) → ℂ := fun a => if h : a ∈ Finset.Nat.antidiagonalTuple (D + 1) N then
    c ((Finset.Nat.antidiagonalTuple (D + 1) N).equivFin ⟨a, h⟩) else 0 with hc'
  have hci : ∀ i, c' (adtEnum D N i) = c i := fun i => by
    simp only [hc', dif_pos (adtEnum_mem D N i)]
    simp [adtEnum]
  have e1 : ∑ i, c i * monoC (adtEnum D N i) w =
      ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N, c' a * monoC a w := by
    rw [← sum_adtEnum D N (fun a => c' a * monoC a w)]
    simp only [hci]
  have e2 : ∑ i, ‖c i‖ ^ 2 * monoNormSq (adtEnum D N i) =
      ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N, ‖c' a‖ ^ 2 * monoNormSq a := by
    rw [← sum_adtEnum D N (fun a => ‖c' a‖ ^ 2 * monoNormSq a)]
    simp only [hci]
  rw [e1, e2, ← integral_form_sq]
  exact form_sq_le D N c' w

def monoZ {N : ℕ} (a : Fin N → ℕ) : MvPolynomial (Fin N) ℤ :=
  monomial (Finsupp.equivFunOnFinite.symm a) 1

theorem monoZ_isHomogeneous {N d : ℕ} {a : Fin N → ℕ} (ha : ∑ i, a i = d) :
    (monoZ a).IsHomogeneous d := by
  unfold monoZ
  apply isHomogeneous_monomial
  rw [← ha, Finsupp.degree_eq_sum]
  simp

def prodForm (e : Fin (D + 1) → Ix κ) (a : Fin (D + 1) → ℕ) (h : MvPolynomial (Ix κ) ℤ) :
    MvPolynomial (Ix κ) ℤ :=
  rename e (monoZ a) * h

theorem prodForm_isHomogeneous (e : Fin (D + 1) → Ix κ) {a : Fin (D + 1) → ℕ} {N k : ℕ}
    (ha : ∑ i, a i = N) {h : MvPolynomial (Ix κ) ℤ} (hh : h.IsHomogeneous k) :
    (prodForm e a h).IsHomogeneous (N + k) :=
  (monoZ_isHomogeneous ha).rename_isHomogeneous.mul hh

theorem aeval_prodForm (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ) (a : Fin (D + 1) → ℕ)
    (h : MvPolynomial (Ix κ) ℤ) :
    aeval x (prodForm e a h) = (∏ t, (x ∘ e) t ^ a t) * aeval x h := by
  rw [prodForm, map_mul, aeval_rename]
  simp [monoZ, aeval_monomial, Finsupp.prod_fintype]

theorem eval_prodForm (e : Fin (D + 1) → Ix κ) (a : Fin (D + 1) → ℕ) (h : MvPolynomial (Ix κ) ℤ)
    (z : Ix κ → ℂ) :
    eval z (map (Int.castRingHom ℂ) (prodForm e a h)) =
      monoC a (z ∘ e) * eval z (map (Int.castRingHom ℂ) h) := by
  rw [prodForm, map_mul, map_mul, map_rename, eval_rename]
  simp [monoZ, map_monomial, eval_monomial, monoC, Finsupp.prod_fintype]

theorem adtEnum_sum (D N : ℕ) (i : Fin (Finset.Nat.antidiagonalTuple (D + 1) N).card) :
    ∑ t, adtEnum D N i t = N :=
  Finset.Nat.mem_antidiagonalTuple.mp (adtEnum_mem D N i)

theorem exists_crd {x : Ix κ → Ω} {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ}
    (hb : IsSecBasis x n b) :
    ∃ crd : sec ℤ x n →ₗ[ℤ] (Fin r → ℤ),
      (∀ v : sec ℤ x n, ∑ j, (crd v j : Ω) * aeval x (b j) = v) ∧
      ∀ j (h : aeval x (b j) ∈ sec ℤ x n), crd ⟨aeval x (b j), h⟩ = Pi.single j 1 := by
  classical
  set bas := (Basis.span hb.2.1).map (LinearEquiv.ofEq _ _ hb.2.2) with hbas
  have hbj : ∀ j, (bas j : Ω) = aeval x (b j) := fun j => by
    simp [hbas, Basis.span_apply]
  refine ⟨(Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin r)).toLinearMap ∘ₗ bas.repr.toLinearMap,
    fun v => ?_, fun j h => ?_⟩
  · conv_rhs => rw [← bas.sum_repr v]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul, hbj, zsmul_eq_mul]
    rfl
  · have : (⟨aeval x (b j), h⟩ : sec ℤ x n) = bas j := Subtype.ext (hbj j).symm
    rw [this]
    simp

theorem crd_span {x : Ix κ → Ω} {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ}
    {crd : sec ℤ x n →ₗ[ℤ] (Fin r → ℤ)}
    (hcrd : ∀ j (h : aeval x (b j) ∈ sec ℤ x n), crd ⟨aeval x (b j), h⟩ = Pi.single j 1)
    (hb : IsSecBasis x n b) {ι : Type} (w : ι → Ω) (hw : ∀ s, w s ∈ sec ℤ x n)
    (hle : sec ℤ x n ≤ Submodule.span ℤ (Set.range w)) (v : Fin r → ℤ) :
    v ∈ Submodule.span ℤ (Set.range fun s => crd ⟨w s, hw s⟩) := by
  have hsub : Submodule.span ℤ (Set.range w) ≤ sec ℤ x n :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr hw)
  have key : ∀ y (hy : y ∈ Submodule.span ℤ (Set.range w)),
      crd ⟨y, hsub hy⟩ ∈ Submodule.span ℤ (Set.range fun s => crd ⟨w s, hw s⟩) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨s, rfl⟩ := hy
      exact Submodule.subset_span ⟨s, rfl⟩
    | zero =>
      have : (⟨0, hsub (Submodule.zero_mem _)⟩ : sec ℤ x n) = 0 := rfl
      rw [this, map_zero]; exact Submodule.zero_mem _
    | add y₁ y₂ h₁ h₂ ih₁ ih₂ =>
      have : (⟨y₁ + y₂, hsub (Submodule.add_mem _ h₁ h₂)⟩ : sec ℤ x n) =
          ⟨y₁, hsub h₁⟩ + ⟨y₂, hsub h₂⟩ := rfl
      rw [this, map_add]; exact Submodule.add_mem _ ih₁ ih₂
    | smul a y h ih =>
      have : (⟨a • y, hsub (Submodule.smul_mem _ a h)⟩ : sec ℤ x n) = a • ⟨y, hsub h⟩ := rfl
      rw [this, map_smul]; exact Submodule.smul_mem _ _ ih
  have hbm : ∀ j, aeval x (b j) ∈ sec ℤ x n := fun j => hb.2.2 ▸ Submodule.subset_span ⟨j, rfl⟩
  have hv : v = ∑ j, v j • crd ⟨aeval x (b j), hbm j⟩ := by
    simp only [hcrd]
    funext q
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hv]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (key _ (hle (hbm j)))

theorem sq_wgt_le_of_le {m : ConeMetric ℂ (Ix κ)} {n : ℕ} {z : Ix κ → ℂ} (hz : z ≠ 0) {a Y : ℝ}
    (ha : 0 ≤ a) (h : a ≤ Y * m.ρ z ^ n) : a ^ 2 * wgt m n z ≤ Y ^ 2 := by
  have hρ : 0 < m.ρ z ^ n := pow_pos (m.pos z hz) n
  unfold wgt
  have e2 : m.ρ z ^ (2 * n) = (m.ρ z ^ n) ^ 2 := by ring
  rw [e2, mul_inv_le_iff₀ (by positivity)]
  calc a ^ 2 ≤ (Y * m.ρ z ^ n) ^ 2 := pow_le_pow_left₀ ha h 2
    _ = Y ^ 2 * (m.ρ z ^ n) ^ 2 := by ring

theorem sqN_comp_eq {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} {m : ConeMetric ℂ (Ix κ)}
    (hFS : IsPullFS x e m) {z : Ix κ → ℂ} (hz : z ∈ pts (coordIdeal ℤ x)) :
    sqN (z ∘ e) = m.ρ z ^ 2 := by
  rw [hFS z hz, Real.sq_sqrt (Finset.sum_nonneg fun k _ => by positivity)]
  rfl

theorem norm_le_sqrt_of_sq_le {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 ≤ t)
    (h : a ^ 2 ≤ b * t ^ 2) : a ≤ Real.sqrt b * t := by
  calc a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
    _ ≤ Real.sqrt (b * t ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt b * t := by rw [Real.sqrt_mul hb, Real.sqrt_sq ht]

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
