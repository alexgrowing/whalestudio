import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClProd
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.RadClMul

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

section

variable {K : Type} [Field K] [NumberField K]

private theorem prod_add (f g : HeightOneSpectrum (𝓞 K) → ℤ) (hf : {v | f v ≠ 0}.Finite)
    (hg : {v | g v ≠ 0}.Finite) :
    ∏ᶠ v, primeCl v ^ (f v + g v) = (∏ᶠ v, primeCl v ^ f v) * ∏ᶠ v, primeCl v ^ g v := by
  rw [← finprod_mul_distrib]
  · exact finprod_congr fun v => zpow_add _ _ _
  · exact hf.subset fun v hv h => hv (by simp [h])
  · exact hg.subset fun v hv h => hv (by simp [h])

private theorem fin_add {f g : HeightOneSpectrum (𝓞 K) → ℤ} (hf : {v | f v ≠ 0}.Finite)
    (hg : {v | g v ≠ 0}.Finite) : {v | f v + g v ≠ 0}.Finite :=
  (hf.union hg).subset fun v hv => by
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
    exact hv (by rw [h.1, h.2, add_zero])

private theorem mem_clSub {S : Set (HeightOneSpectrum (𝓞 K))} {c : ClassGroup (𝓞 K)} (hc : c ∈ clSub S) :
    ∃ g : HeightOneSpectrum (𝓞 K) → ℤ, {v | g v ≠ 0}.Finite ∧ (∀ v ∉ S, g v = 0) ∧
      c = ∏ᶠ v, primeCl v ^ g v := by
  classical
  induction hc using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    refine ⟨fun v => if v = w then 1 else 0, (Set.finite_singleton w).subset fun v hv => ?_,
      fun v hv => if_neg fun (h : v = w) => hv (h ▸ hw), ?_⟩
    · by_contra h
      exact hv (if_neg h)
    · rw [finprod_eq_single _ w fun v hv => by simp [hv]]
      simp
  | one => exact ⟨fun _ => 0, by simp, by simp, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨f, hf, hf', rfl⟩ := hx
    obtain ⟨g, hg, hg', rfl⟩ := hy
    exact ⟨fun v => f v + g v, fin_add hf hg, fun v hv => by simp [hf' v hv, hg' v hv],
      (prod_add f g hf hg).symm⟩
  | inv x _ hx =>
    obtain ⟨f, hf, hf', rfl⟩ := hx
    refine ⟨fun v => -f v, by simpa using hf, fun v hv => by simp [hf' v hv], ?_⟩
    rw [← finprod_inv_distrib]
    exact finprod_congr fun v => (zpow_neg _ _).symm

private theorem exists_ordv (f : HeightOneSpectrum (𝓞 K) → ℤ) (hf : {v | f v ≠ 0}.Finite)
    (h : ∏ᶠ v, primeCl v ^ f v = 1) : ∃ b : Kˣ, ∀ v, ordv v b = f v := by
  obtain ⟨h1, h2, -, -⟩ := clProd K
  set I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
    ∏ᶠ v : HeightOneSpectrum (𝓞 K), (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ f v with hI
  have hI0 : I ≠ 0 := by
    rw [hI]
    refine finprod_induction (fun J => J ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) fun v => ?_
    exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 v.ne_bot)
  have hc : ∀ v, FractionalIdeal.count K v I = f v := fun v =>
    FractionalIdeal.count_finprod K v f (by simpa [Filter.eventually_cofinite] using hf)
  have h3 : ClassGroup.mk K (Units.mk0 I hI0) = 1 := by
    rw [h1, ← h]
    exact finprod_congr fun v => by rw [Units.val_mk0, hc]
  obtain ⟨b, hb⟩ := (FractionalIdeal.isPrincipal_iff _).1 (ClassGroup.mk_eq_one_iff.1 h3)
  rw [Units.val_mk0] at hb
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hI0 (by rw [hb, FractionalIdeal.spanSingleton_zero])
  exact ⟨Units.mk0 b hb0, fun v => by rw [← h2, Units.val_mk0, ← hb, hc]⟩

private theorem mem_unit {S : Set (HeightOneSpectrum (𝓞 K))} {u : Kˣ} :
    u ∈ S.unit K ↔ ∀ v ∉ S, ordv v u = 0 := by
  change (∀ v ∉ S, v.valuation K (u : K) = 1) ↔ _
  refine forall₂_congr fun v _ => ?_
  rw [← HeightOneSpectrum.valuationOfNeZero_eq, ← WithZero.coe_one, WithZero.coe_inj, ordv, neg_eq_zero,
    toAdd_eq_zero]

private theorem ordv_pow (v : HeightOneSpectrum (𝓞 K)) (b : Kˣ) (n : ℕ) : ordv v (b ^ n) = n * ordv v b := by
  simp [ordv]

end

theorem UpperTheory.V.Kum.radClKer :
    ∀ (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ), n ≠ 0 → ∀ a ∈ SelK S n, (radCl n a ∈ clSub S ↔ a ∈ S.unit K ⊔ powK K n) := by
  intro K _ _ S n hn a ha
  constructor
  · intro h
    obtain ⟨g, hg, hg', hc⟩ := mem_clSub (inv_mem h)
    have hf : {v | ordv v a / n ≠ 0}.Finite :=
      ((clProd K).2.2.1 a).subset fun v hv h => hv (by simp [h])
    obtain ⟨b, hb⟩ := exists_ordv (fun v => ordv v a / n + g v) (fin_add hf hg) (by
      rw [prod_add _ _ hf hg, ← hc]
      exact mul_inv_cancel _)
    refine Subgroup.mem_sup.2 ⟨a * (b ^ n)⁻¹, mem_unit.2 fun v hv => ?_, b ^ n, ⟨b, rfl⟩, by simp⟩
    rw [ordv_mul, ordv_inv, ordv_pow, hb, hg' v hv, add_zero, Int.mul_ediv_cancel' (ha v hv), add_neg_cancel]
  · intro h
    obtain ⟨u, hu, _, ⟨b, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 h
    rw [powMonoidHom_apply, (radClMul K S n hn).2.2]
    refine finprod_induction (fun c => c ∈ clSub S) (one_mem _) (fun _ _ => mul_mem) fun v => ?_
    by_cases hv : v ∈ S
    · have h0 : primeCl v ∈ clSub S := Subgroup.subset_closure ⟨v, hv, rfl⟩
      exact zpow_mem h0 _
    · rw [mem_unit.1 hu v hv]
      simp
