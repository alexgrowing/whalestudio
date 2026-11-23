import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IrreducibleParity.Fv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.CintIdx

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PS

private theorem rescale {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] {p : O} (hp : Irreducible p) {x : K} (hx : x ≠ 0) :
    ∃ s : K, s ≠ 0 ∧ ∃ a b : O, algebraMap O K a = s ^ 2 * x ∧ a * b = p ^ 2 := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective O x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hx
  have hp0 : p ≠ 0 := hp.ne_zero
  have hinj := IsFractionRing.injective O K
  have hP : algebraMap O K p ≠ 0 := (map_ne_zero_iff _ hinj).mpr hp0
  have hB : algebraMap O K b ≠ 0 := (map_ne_zero_iff _ hinj).mpr hb0
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hp
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hp
  set t := (m + n) / 2 with ht
  set r := (m + n) % 2 with hr
  have hN : r + t + t = m + n := by omega
  have hr2 : r ≤ 2 := by omega
  have hO : (↑(u * v) * p ^ r) * (p ^ t * p ^ t) = (↑u * p ^ m) * (↑v * p ^ n) := by
    calc (↑(u * v) * p ^ r) * (p ^ t * p ^ t) = ↑u * ↑v * p ^ (r + t + t) := by
            rw [Units.val_mul]; ring
      _ = (↑u * p ^ m) * (↑v * p ^ n) := by rw [hN]; ring
  have key : algebraMap O K (↑(u * v) * p ^ r) * (algebraMap O K p ^ t * algebraMap O K p ^ t)
      = algebraMap O K (↑u * p ^ m) * algebraMap O K (↑v * p ^ n) := by
    rw [← map_pow, ← map_mul, ← map_mul, ← map_mul, hO]
  refine ⟨algebraMap O K (↑v * p ^ n) / algebraMap O K p ^ t, div_ne_zero hB (pow_ne_zero _ hP),
    ↑(u * v) * p ^ r, ↑(u * v)⁻¹ * p ^ (2 - r), ?_, ?_⟩
  · have hT : algebraMap O K p ^ t * algebraMap O K p ^ t ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hP) (pow_ne_zero _ hP)
    have e : algebraMap O K (↑(u * v) * p ^ r) = algebraMap O K (↑u * p ^ m) * algebraMap O K (↑v * p ^ n)
        / (algebraMap O K p ^ t * algebraMap O K p ^ t) := by
      rw [eq_div_iff hT, key]
    rw [e]
    field_simp
  · calc ↑(u * v) * p ^ r * (↑(u * v)⁻¹ * p ^ (2 - r))
        = (↑(u * v) * ↑(u * v)⁻¹) * p ^ (r + (2 - r)) := by rw [pow_add]; ring
      _ = p ^ 2 := by rw [Units.mul_inv, one_mul, Nat.add_sub_cancel' hr2]

private theorem rescaleE {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] {τ : K} {p : O} (hp : Irreducible p) {c : (Etau K τ)ˣ} (hc : c ∈ Cint O τ) :
    ∃ s : K, s ≠ 0 ∧ IsIntegral O (s • (c : Etau K τ)) ∧
      IsIntegral O ((algebraMap O K p * s⁻¹) • ((c⁻¹ : (Etau K τ)ˣ) : Etau K τ)) := by
  obtain ⟨hc1, hc2⟩ := hc
  have sq : ∀ u : (Etau K τ)ˣ, (u : Etau K τ) * u =
      algebraMap K (Etau K τ) (QuadraticAlgebra.norm (u : Etau K τ)) * quo u := by
    intro u
    rw [QuadraticAlgebra.algebraMap_norm_eq_mul_star]
    have h1 : star (u : Etau K τ) * star ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ) = 1 := by
      rw [← star_mul, Units.inv_mul, star_one]
    unfold quo
    calc (u : Etau K τ) * u = u * u * (star (u : Etau K τ) * star ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ)) := by
          rw [h1, mul_one]
      _ = u * star (u : Etau K τ) * (u * star ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ)) := by ring
  obtain ⟨N, hNd⟩ : ∃ N, N = QuadraticAlgebra.norm (c : Etau K τ) := ⟨_, rfl⟩
  obtain ⟨N', hNd'⟩ : ∃ N', N' = QuadraticAlgebra.norm ((c⁻¹ : (Etau K τ)ˣ) : Etau K τ) := ⟨_, rfl⟩
  have hNN : N * N' = 1 := by
    rw [hNd, hNd', ← map_mul, Units.mul_inv, map_one]
  have hN : N ≠ 0 := left_ne_zero_of_mul_eq_one hNN
  have sqc := sq c
  have sqd := sq c⁻¹
  rw [← hNd] at sqc
  rw [← hNd'] at sqd
  obtain ⟨s, hs, a, b, ha, hab⟩ := rescale hp hN
  have hab' : algebraMap O K a * algebraMap O K b = algebraMap O K p ^ 2 := by
    rw [← map_mul, hab, map_pow]
  refine ⟨s, hs, ?_, ?_⟩
  · apply IsIntegral.of_pow (n := 2) two_pos
    have e : (s • (c : Etau K τ)) ^ 2 = algebraMap O (Etau K τ) a * quo c := by
      calc (s • (c : Etau K τ)) ^ 2 = algebraMap K (Etau K τ) s ^ 2 * ((c : Etau K τ) * c) := by
            rw [Algebra.smul_def]; ring
        _ = algebraMap K (Etau K τ) s ^ 2 * (algebraMap K (Etau K τ) N * quo c) := by rw [sqc]
        _ = algebraMap O (Etau K τ) a * quo c := by
            rw [algebraMap_etau a, ha, map_mul, map_pow]; ring
    rw [e]
    exact (isIntegral_algebraMap).mul hc1
  · apply IsIntegral.of_pow (n := 2) two_pos
    have hk : (algebraMap O K p * s⁻¹) ^ 2 * N' = algebraMap O K b := by
      field_simp
      linear_combination (-N') * hab' + (algebraMap O K b * N') * ha + (algebraMap O K b * s ^ 2) * hNN
    have e : ((algebraMap O K p * s⁻¹) • ((c⁻¹ : (Etau K τ)ˣ) : Etau K τ)) ^ 2
        = algebraMap O (Etau K τ) b * quo c⁻¹ := by
      calc ((algebraMap O K p * s⁻¹) • ((c⁻¹ : (Etau K τ)ˣ) : Etau K τ)) ^ 2
          = algebraMap K (Etau K τ) (algebraMap O K p * s⁻¹) ^ 2
            * (((c⁻¹ : (Etau K τ)ˣ) : Etau K τ) * ((c⁻¹ : (Etau K τ)ˣ) : Etau K τ)) := by
            rw [Algebra.smul_def]; ring
        _ = algebraMap K (Etau K τ) (algebraMap O K p * s⁻¹) ^ 2
            * (algebraMap K (Etau K τ) N' * quo c⁻¹) := by rw [sqd]
        _ = algebraMap O (Etau K τ) b * quo c⁻¹ := by
            rw [algebraMap_etau b, ← hk]
            simp only [map_mul, map_pow]
            ring
    rw [e]
    exact (isIntegral_algebraMap).mul hc2

private theorem cls_smul {K : Type} [Field K] {τ : K} (S : Set (Etau K τ)) {s : K} (hs : s ≠ 0) :
    cls τ ((s • ·) '' S) = cls τ S := by
  ext T
  simp only [cls, Set.mem_setOf_eq, Set.image_image, smul_smul]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u * Units.mk0 s hs, by congr 1⟩
  · rintro ⟨u, rfl⟩
    refine ⟨u * (Units.mk0 s hs)⁻¹, ?_⟩
    congr 1
    funext y
    simp [hs]

private theorem exists_finite_representatives_mod_smul_of_fg {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] {m : O}
    (hq : Finite (O ⧸ Ideal.span {m})) (R : Submodule O M) (hR : R.FG) :
    ∃ F : Set M, F.Finite ∧ ∀ x ∈ R, ∃ y ∈ F, ∃ z ∈ R, x - y = m • z := by
  haveI := hq
  obtain ⟨g, rfl⟩ := hR
  have hsurj := Ideal.Quotient.mk_surjective (I := Ideal.span {m})
  refine ⟨Set.range (fun r : (↥g → O ⧸ Ideal.span {m}) =>
    ∑ i : ↥g, Function.surjInv hsurj (r i) • (i : M)), Set.finite_range _, ?_⟩
  intro x hx
  obtain ⟨f, -, rfl⟩ := (Submodule.mem_span_finset).mp hx
  have hk : ∀ i : ↥g, ∃ k : O, k * m = f i - Function.surjInv hsurj (Ideal.Quotient.mk _ (f i)) := by
    intro i
    apply Ideal.mem_span_singleton'.mp
    apply Ideal.Quotient.eq.mp
    rw [Function.surjInv_eq hsurj]
  choose k hk using hk
  refine ⟨_, ⟨fun i => Ideal.Quotient.mk _ (f i), rfl⟩, ∑ i : ↥g, k i • (i : M), ?_, ?_⟩
  · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span i.2)
  · rw [← Finset.sum_coe_sort g, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sub_smul, ← hk i, smul_smul, mul_comm]

theorem UpperTheory.quadraticTorus_fixedVertices_finite :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → (Fv O τ).Finite := by
  intro O K _ _ _ _ _ Δ τ hL hτ
  haveI := hL.frac
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨c0, hc0, hden⟩ := int_denom hL hτ
  have hm : c0 * p ≠ 0 := mul_ne_zero hc0 hp.ne_zero
  obtain ⟨F, hF, hFR⟩ := exists_finite_representatives_mod_smul_of_fg (finite_quot_span hL hm)
    (Subalgebra.toSubmodule (integralClosure O (Etau K τ))) (intE_fg hL hτ)
  have hmemR : ∀ z, z ∈ Subalgebra.toSubmodule (integralClosure O (Etau K τ)) ↔ IsIntegral O z := by
    intro z
    rw [Subalgebra.mem_toSubmodule, mem_integralClosure_iff]
  let 𝒯 : Set (Set (Etau K τ)) := {T | ∃ M : Submodule O (Etau K τ), T = M ∧
    (∀ z ∈ Subalgebra.toSubmodule (integralClosure O (Etau K τ)), (c0 * p) • z ∈ M) ∧
    M ≤ Subalgebra.toSubmodule (integralClosure O (Etau K τ))}
  have h𝒯 : 𝒯.Finite := by
    apply Set.Finite.of_finite_image (f := fun T => T ∩ F)
    · exact (hF.powerset).subset (by rintro _ ⟨T, -, rfl⟩; exact Set.inter_subset_right)
    · have key : ∀ M M' : Submodule O (Etau K τ),
          (∀ z ∈ Subalgebra.toSubmodule (integralClosure O (Etau K τ)), (c0 * p) • z ∈ M) →
          M ≤ Subalgebra.toSubmodule (integralClosure O (Etau K τ)) →
          (∀ z ∈ Subalgebra.toSubmodule (integralClosure O (Etau K τ)), (c0 * p) • z ∈ M') →
          (M : Set (Etau K τ)) ∩ F = (M' : Set (Etau K τ)) ∩ F → (M : Set (Etau K τ)) ⊆ M' := by
        intro M M' hm1 hR1 hm2 he x hx
        obtain ⟨y, hyF, z, hz, hxy⟩ := hFR x (hR1 hx)
        have hy : y ∈ M := by
          have e : y = x - (c0 * p) • z := by rw [← hxy]; abel
          rw [e]
          exact M.sub_mem hx (hm1 z hz)
        have hy2 : y ∈ (M' : Set (Etau K τ)) ∩ F := by
          rw [← he]
          exact ⟨hy, hyF⟩
        have e : x = y + (c0 * p) • z := by rw [← hxy]; abel
        rw [e]
        exact M'.add_mem hy2.1 (hm2 z hz)
      rintro _ ⟨M1, rfl, h1m, h1R⟩ _ ⟨M2, rfl, h2m, h2R⟩ heq
      have heq' : (M1 : Set (Etau K τ)) ∩ F = (M2 : Set (Etau K τ)) ∩ F := heq
      exact Set.Subset.antisymm (key _ _ h1m h1R h2m heq') (key _ _ h2m h2R h1m heq'.symm)
  apply (h𝒯.image (fun T => cls τ T)).subset
  rintro X ⟨S, hS, hω, ⟨c, hc, hgen⟩, rfl⟩
  obtain ⟨s, hs, hsc, hsd⟩ := rescaleE hp hc
  refine ⟨(s • ·) '' S, ?_, cls_smul S hs⟩
  obtain ⟨g, hg⟩ := hS.fg
  have hcomm : ∀ (o : O) (x : Etau K τ), o • (s • x) = s • (o • x) := by
    intro o x
    simp only [Algebra.smul_def]
    ring
  let M : Submodule O (Etau K τ) :=
    { carrier := (s • ·) '' S
      add_mem' := by
        rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
        refine ⟨u + v, ?_, smul_add s u v⟩
        rw [hg] at hu hv ⊢
        exact Submodule.add_mem _ hu hv
      zero_mem' := ⟨0, by rw [hg]; exact Submodule.zero_mem _, smul_zero s⟩
      smul_mem' := by
        rintro o _ ⟨u, hu, rfl⟩
        refine ⟨o • u, ?_, (hcomm o u).symm⟩
        rw [hg] at hu ⊢
        exact Submodule.smul_mem _ o hu }
  refine ⟨M, rfl, ?_, ?_⟩
  · intro z hz
    have hzi : IsIntegral O z := (hmemR z).mp hz
    have e1 : algebraMap O (Etau K τ) p = (s • (c : Etau K τ)) *
        ((algebraMap O K p * s⁻¹) • ((c⁻¹ : (Etau K τ)ˣ) : Etau K τ)) := by
      rw [smul_mul_smul_comm, Units.mul_inv, algebraMap_etau p, Algebra.algebraMap_eq_smul_one]
      congr 1
      field_simp
    have hy : IsIntegral O (((algebraMap O K p * s⁻¹) • ((c⁻¹ : (Etau K τ)ˣ) : Etau K τ)) * z) :=
      hsd.mul hzi
    obtain ⟨a, b, h1, h2⟩ := hden _ hy
    have e2 : algebraMap O (Etau K τ) c0 *
        (((algebraMap O K p * s⁻¹) • ((c⁻¹ : (Etau K τ)ˣ) : Etau K τ)) * z)
        = algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * ω := by
      rw [algebraMap_etau c0, algebraMap_etau a, algebraMap_etau b]
      ext
      · have h1' := h1
        simp at h1' ⊢
        linear_combination h1'
      · have h2' := h2
        simp at h2' ⊢
        linear_combination h2'
    have e3 : (c0 * p) • z = a • (s • (c : Etau K τ)) + b • (s • (ω * (c : Etau K τ))) := by
      calc (c0 * p) • z = algebraMap O (Etau K τ) c0 * algebraMap O (Etau K τ) p * z := by
            rw [Algebra.smul_def, map_mul]
        _ = (s • (c : Etau K τ)) * (algebraMap O (Etau K τ) c0 *
              (((algebraMap O K p * s⁻¹) • ((c⁻¹ : (Etau K τ)ˣ) : Etau K τ)) * z)) := by
            rw [e1]; ring
        _ = (s • (c : Etau K τ)) * (algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * ω) := by
            rw [e2]
        _ = a • (s • (c : Etau K τ)) + b • (s • (ω * (c : Etau K τ))) := by
            rw [Algebra.smul_def a, Algebra.smul_def b, ← mul_smul_comm]
            ring
    rw [e3]
    have m1 : s • (c : Etau K τ) ∈ M := ⟨_, hgen.1, rfl⟩
    have m2 : s • (ω * (c : Etau K τ)) ∈ M := ⟨_, hω _ hgen.1, rfl⟩
    exact M.add_mem (M.smul_mem a m1) (M.smul_mem b m2)
  · rintro _ ⟨w, hw, rfl⟩
    rw [hmemR]
    have e : s • w = (s • (c : Etau K τ)) * (((c⁻¹ : (Etau K τ)ˣ) : Etau K τ) * w) := by
      rw [smul_mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]
    show IsIntegral O (s • w)
    rw [e]
    exact hsc.mul (hgen.2 w hw)
