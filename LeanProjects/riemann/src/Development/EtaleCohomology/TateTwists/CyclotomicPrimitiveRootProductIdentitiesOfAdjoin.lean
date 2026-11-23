import Development.EtaleCohomology.TateTwists.PrimitiveRootsOfUnityBasicIdentities

open Polynomial Finset GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.PrimPf

noncomputable def μ (q : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / q)

lemma hμ (q : ℕ) [NeZero q] : IsPrimitiveRoot (μ q) q :=
  Complex.isPrimitiveRoot_exp q (NeZero.ne q)

lemma aeval_cyc {n : ℕ} (hn : 0 < n) {ν : ℂ} (h : IsPrimitiveRoot ν n) :
    aeval ν (cyclotomic n ℤ) = 0 := by
  rw [cyclotomic_eq_minpoly h hn]; exact minpoly.aeval _ _

lemma hom_aeval {S T : Type} [CommRing S] [CommRing T] [Algebra ℤ S] [Algebra ℤ T] (f : S →+* T) (x : S) (p : ℤ[X]) :
    f (aeval x p) = aeval (f x) p := by
  rw [aeval_def, aeval_def, hom_eval₂]; congr 1; exact RingHom.ext_int _ _

abbrev R (q : ℕ) := AdjoinRoot (cyclotomic q ℤ)

noncomputable abbrev θ (q : ℕ) : R q := AdjoinRoot.root (cyclotomic q ℤ)

noncomputable def φ (q : ℕ) [NeZero q] : R q →+* ℂ :=
  AdjoinRoot.lift (algebraMap ℤ ℂ) (μ q) (by rw [← aeval_def]; exact aeval_cyc (NeZero.pos q) (hμ q))

lemma φ_root (q : ℕ) [NeZero q] : φ q (θ q) = μ q := AdjoinRoot.lift_root _

lemma φ_inj (q : ℕ) [NeZero q] : Function.Injective (φ q) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  rw [AdjoinRoot.mk_eq_zero]
  have h : aeval (μ q) p = 0 := by
    rw [φ, AdjoinRoot.lift_mk] at hx; rwa [aeval_def]
  rw [cyclotomic_eq_minpoly (hμ q) (NeZero.pos q)]
  exact minpoly.isIntegrallyClosed_dvd ((hμ q).isIntegral (NeZero.pos q)) h

noncomputable def ψ {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : R q →+* A :=
  AdjoinRoot.lift (algebraMap ℤ A) ζ.1 (by rw [← aeval_def]; exact ζ.2.2)

lemma ψ_root {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : ψ ζ (θ q) = ζ.1 :=
  AdjoinRoot.lift_root _

lemma θ_pow (q : ℕ) [NeZero q] : θ q ^ q = 1 :=
  φ_inj q (by rw [map_pow, φ_root, map_one, (hμ q).pow_eq_one])

lemma root_of_prim {q r a : ℕ} [NeZero q] (hr : 0 < r) (h : IsPrimitiveRoot (μ q ^ a) r) :
    aeval (θ q ^ a) (cyclotomic r ℤ) = 0 :=
  φ_inj q (by rw [hom_aeval (φ q), map_pow, φ_root, map_zero]; exact aeval_cyc hr h)

lemma image_range (q : ℕ) [NeZero q] :
    (range q).image (fun a => μ q ^ a) = nthRootsFinset q (1 : ℂ) := by
  ext x
  rw [mem_image, mem_nthRootsFinset (NeZero.pos q)]
  constructor
  · rintro ⟨a, -, rfl⟩; rw [← pow_mul, mul_comm, pow_mul, (hμ q).pow_eq_one, one_pow]
  · intro hx
    obtain ⟨i, hi, rfl⟩ := (hμ q).eq_pow_of_pow_eq_one hx
    exact ⟨i, mem_range.2 hi, rfl⟩

lemma image_prim (q : ℕ) [NeZero q] :
    ((range q).filter (fun a => Nat.Coprime a q)).image (fun a => μ q ^ a) = primitiveRoots q ℂ := by
  ext x
  rw [mem_image, mem_primitiveRoots (NeZero.pos q)]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact (hμ q).pow_of_coprime a (mem_filter.1 ha).2
  · intro hx
    obtain ⟨i, hi, rfl⟩ := (hμ q).eq_pow_of_pow_eq_one hx.pow_eq_one
    exact ⟨i, mem_filter.2 ⟨mem_range.2 hi, ((hμ q).pow_iff_coprime (NeZero.pos q) i).1 hx⟩, rfl⟩

lemma inj_on (q : ℕ) [NeZero q] (s : Finset ℕ) (hs : s ⊆ range q) :
    Set.InjOn (fun a => μ q ^ a) s := by
  intro i hi j hj h
  exact (hμ q).pow_inj (mem_range.1 (hs hi)) (mem_range.1 (hs hj)) h

lemma C_prod_all (q : ℕ) [NeZero q] :
    ∏ a ∈ range q, (X - C (μ q ^ a)) = (X ^ q - 1 : ℂ[X]) := by
  rw [X_pow_sub_one_eq_prod (NeZero.pos q) (hμ q), ← image_range,
    prod_image (inj_on q _ subset_rfl)]

lemma C_prod_prim (q : ℕ) [NeZero q] :
    ∏ a ∈ (range q).filter (fun a => Nat.Coprime a q), (X - C (μ q ^ a)) = cyclotomic q ℂ := by
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots (hμ q), ← image_prim,
    prod_image (inj_on q _ (filter_subset _ _))]

lemma mapφ_C_prod (q : ℕ) [NeZero q] (s : Finset ℕ) :
    (∏ a ∈ s, (X - C (θ q ^ a))).map (φ q) = ∏ a ∈ s, (X - C (μ q ^ a)) := by
  simp [Polynomial.map_prod, φ_root]

lemma R_prod_all (q : ℕ) [NeZero q] :
    ∏ a ∈ range q, (X - C (θ q ^ a)) = (X ^ q - 1 : (R q)[X]) := by
  apply Polynomial.map_injective _ (φ_inj q)
  rw [mapφ_C_prod, C_prod_all]; simp

lemma R_prod_prim (q : ℕ) [NeZero q] :
    ∏ a ∈ (range q).filter (fun a => Nat.Coprime a q), (X - C (θ q ^ a))
      = (cyclotomic q ℤ).map (algebraMap ℤ (R q)) := by
  apply Polynomial.map_injective _ (φ_inj q)
  rw [mapφ_C_prod, C_prod_prim, Polynomial.map_map, ← map_cyclotomic_int]
  congr 1; exact RingHom.ext_int _ _

lemma C_prod_geom (n : ℕ) [NeZero (n + 1)] :
    ∏ i ∈ range n, (X - C (μ (n + 1) ^ (i + 1))) = ∑ i ∈ range (n + 1), (X ^ i : ℂ[X]) := by
  have h := C_prod_all (n + 1)
  rw [prod_range_succ', pow_zero, ← geom_sum_mul, C_1] at h
  have hne : (X - 1 : ℂ[X]) ≠ 0 := by simpa using X_sub_C_ne_zero (1 : ℂ)
  exact mul_right_cancel₀ hne h

lemma R_prod_geom (n : ℕ) [NeZero (n + 1)] :
    ∏ i ∈ range n, (X - C (θ (n + 1) ^ (i + 1))) = ∑ i ∈ range (n + 1), (X ^ i : (R (n + 1))[X]) := by
  apply Polynomial.map_injective _ (φ_inj (n + 1))
  simp only [Polynomial.map_prod, Polynomial.map_sum, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, map_pow, φ_root, Polynomial.map_pow]
  simpa using C_prod_geom n

lemma eval_prod_ψ {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) (y : A) (s : Finset ℕ) (f : ℕ → ℕ) :
    eval₂ (ψ ζ) y (∏ a ∈ s, (X - C (θ q ^ f a))) = ∏ a ∈ s, (y - ζ.1 ^ f a) := by
  simp [eval₂_finsetProd, eval₂_pow, ψ_root]

lemma eval_prod_ψ0 {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) (y : A) (s : Finset ℕ) :
    eval₂ (ψ ζ) y (∏ a ∈ s, (X - C (θ q ^ a))) = ∏ a ∈ s, (y - ζ.1 ^ a) := by
  simp [eval₂_finsetProd, eval₂_pow, ψ_root]

lemma unit_prod {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) :
    ∏ i ∈ range (q - 1), (1 - ζ.1 ^ (i + 1)) = (q : A) := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos q)).symm⟩
  have h := congrArg (eval₂ (ψ ζ) 1) (R_prod_geom n)
  rw [eval_prod_ψ ζ 1 _ (fun i => i + 1)] at h
  simpa [eval₂_finsetSum] using h

theorem cyclotomic_primitive_root_product_identities_of_adjoin_root : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities := by
  intro q _ A _
  have hq1 : ∀ ζ : Prim q A, ζ.1 ^ q = 1 := fun ζ => by
    rw [← ψ_root, ← map_pow, θ_pow, map_one]
  have hu : ∀ ζ : Prim q A, IsUnit ζ.1 := fun ζ =>
    IsUnit.of_mul_eq_one (ζ.1 ^ (q - 1)) (by
      rw [← pow_succ', Nat.sub_add_cancel (NeZero.pos q), hq1])
  have hmod : ∀ (ζ : Prim q A) (a : ℕ), ζ.1 ^ a = ζ.1 ^ (a % q) := fun ζ a => by
    conv_lhs => rw [← Nat.mod_add_div a q, pow_add, pow_mul, hq1, one_pow, mul_one]
  have hlt : ∀ (ζ : Prim q A) (c d : ℕ), c < d → d < q → IsUnit (ζ.1 ^ c - ζ.1 ^ d) := by
    intro ζ c d hcd hd
    obtain ⟨i, rfl⟩ : ∃ i, d = c + (i + 1) := ⟨d - c - 1, by omega⟩
    have e : ζ.1 ^ c - ζ.1 ^ (c + (i + 1)) = ζ.1 ^ c * (1 - ζ.1 ^ (i + 1)) := by ring
    rw [e]
    refine ((hu ζ).pow c).mul (isUnit_of_dvd_unit ?_ ζ.2.1)
    have hd := dvd_prod_of_mem (fun j => 1 - ζ.1 ^ (j + 1)) (mem_range.2 (show i < q - 1 by omega))
    rw [unit_prod ζ] at hd
    exact hd
  refine ⟨hq1, ?_, ?_, ?_, ?_, ?_⟩
  · intro ζ a ha
    refine ⟨⟨ζ.1 ^ a, ζ.2.1, ?_⟩, rfl⟩
    rw [← ψ_root, ← map_pow, ← hom_aeval (ψ ζ),
      root_of_prim (NeZero.pos q) ((hμ q).pow_of_coprime a ha), map_zero]
  · intro ζ a b hab
    rw [hmod ζ a, hmod ζ b]
    have hne : a % q ≠ b % q := hab
    have ha := Nat.mod_lt a (NeZero.pos q)
    have hb := Nat.mod_lt b (NeZero.pos q)
    rcases lt_or_gt_of_ne hne with h | h
    · exact hlt ζ _ _ h hb
    · have := (hlt ζ _ _ h ha).neg
      rwa [neg_sub] at this
  · intro ζ x hx
    have h := congrArg (eval₂ (ψ ζ) x) (R_prod_all q)
    rw [eval_prod_ψ0] at h
    simpa [hx] using h
  · intro ζ ξ
    have h := congrArg (eval₂ (ψ ζ) ξ.1) (R_prod_prim q)
    rw [eval_prod_ψ0, eval₂_map] at h
    rw [h]
    have e : (ψ ζ).comp (algebraMap ℤ (R q)) = algebraMap ℤ A := RingHom.ext_int _ _
    rw [e, ← aeval_def]; exact ξ.2.2
  · intro r hr ζ
    have hr0 : 0 < r := Nat.pos_of_dvd_of_pos hr (NeZero.pos q)
    have hur : IsUnit (r : A) := by
      obtain ⟨k, hk⟩ := hr
      have := ζ.2.1
      rw [hk, Nat.cast_mul] at this
      exact isUnit_of_mul_isUnit_left this
    refine ⟨⟨ζ.1 ^ (q / r), hur, ?_⟩, rfl⟩
    rw [← ψ_root, ← map_pow, ← hom_aeval (ψ ζ),
      root_of_prim hr0 ((hμ q).pow (NeZero.pos q) (Nat.div_mul_cancel hr).symm), map_zero]

end LateralTheory.EtaleFoundations.PrimPf
