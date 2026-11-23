import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CmpPrime

open Polynomial
open scoped Pointwise nonZeroDivisors TensorProduct

private theorem finite_setOf_roots_of_monic_family {Λ F : Type*} [CommRing Λ] [Field F] (ρ : Λ →+* F) {r : ℕ}
    (f : Fin r → Polynomial Λ) (hf : ∀ i, (f i).Monic) :
    {v : Fin r → F | ∀ i, Polynomial.eval₂ ρ (v i) (f i) = 0}.Finite := by
  refine (Set.Finite.pi (t := fun i => {y : F | Polynomial.eval₂ ρ y (f i) = 0}) fun i => ?_).subset ?_
  · have h0 : (f i).map ρ ≠ 0 := ((hf i).map ρ).ne_zero
    refine (Polynomial.finite_setOf_isRoot h0).subset ?_
    intro y hy
    simpa [Polynomial.IsRoot, Polynomial.eval_map] using hy
  · intro v hv i _
    exact hv i

private theorem finite_setOf_nat_polynomial_collision {F : Type*} [Field F] [CharZero F] {r : ℕ} (T : Set (Fin r → F))
    (hT : T.Finite) :
    {s : ℕ | ∃ v ∈ T, ∃ w ∈ T, v ≠ w ∧
      ∑ i, v i * (s : F) ^ (i : ℕ) = ∑ i, w i * (s : F) ^ (i : ℕ)}.Finite := by
  classical
  let P : (Fin r → F) → Polynomial F := fun u => ∑ i, Polynomial.C (u i) * Polynomial.X ^ (i : ℕ)
  have hev : ∀ u (y : F), (P u).eval y = ∑ i, u i * y ^ (i : ℕ) := by
    intro u y
    simp [P, Polynomial.eval_finset_sum]
  have hco : ∀ u (j : Fin r), (P u).coeff j = u j := by
    intro u j
    simp only [P, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      rw [if_neg]
      exact fun h => hij (Fin.ext h).symm
    · simp
  have hsub : {s : ℕ | ∃ v ∈ T, ∃ w ∈ T, v ≠ w ∧
      ∑ i, v i * (s : F) ^ (i : ℕ) = ∑ i, w i * (s : F) ^ (i : ℕ)} ⊆
      ⋃ p ∈ T ×ˢ T, {s : ℕ | p.1 ≠ p.2 ∧ (P (p.1 - p.2)).eval (s : F) = 0} := by
    rintro s ⟨v, hv, w, hw, hne, heq⟩
    simp only [Set.mem_iUnion]
    refine ⟨(v, w), ⟨hv, hw⟩, hne, ?_⟩
    rw [hev]
    simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    rw [heq, sub_self]
  refine Set.Finite.subset ((hT.prod hT).biUnion fun p _ => ?_) hsub
  by_cases hp : p.1 = p.2
  · simp [hp]
  · have h0 : P (p.1 - p.2) ≠ 0 := by
      intro h0
      apply hp
      funext j
      have := hco (p.1 - p.2) j
      rw [h0] at this
      simp only [Polynomial.coeff_zero, Pi.sub_apply] at this
      exact sub_eq_zero.mp this.symm
    refine (Set.Finite.preimage (Nat.cast_injective.injOn)
      (Polynomial.finite_setOf_isRoot h0)).subset ?_
    intro s hs
    exact hs.2

private theorem adjoin_singleton_eq_whole_of_separates_homs {L A Ω : Type*} [Field L] [CharZero L] [CommRing A] [Algebra L A]
    [FiniteDimensional L A] [IsReduced A] [Field Ω] [IsAlgClosed Ω] [Algebra L Ω] (t : A)
    (ht : ∀ φ ψ : A →ₐ[L] Ω, φ t = ψ t → φ = ψ) : Algebra.adjoin L {t} = ⊤ := by
  classical
  have hArt : IsArtinianRing A := isArtinian_of_tower L inferInstance
  letI hF : ∀ m : MaximalSpectrum A, Field (A ⧸ m.asIdeal) :=
    fun m => @Ideal.Quotient.field _ _ m.asIdeal m.isMaximal
  haveI : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  haveI hfd : ∀ m : MaximalSpectrum A, FiniteDimensional L (A ⧸ m.asIdeal) := fun m =>
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ L m.asIdeal).toLinearMap
      Ideal.Quotient.mk_surjective
  let e : A ≃ₐ[L] ((m : MaximalSpectrum A) → A ⧸ m.asIdeal) :=
    (IsArtinianRing.equivPi A).restrictScalars L
  have h1 : Module.finrank L A = ∑ m : MaximalSpectrum A, Module.finrank L (A ⧸ m.asIdeal) :=
    e.toLinearEquiv.finrank_eq.trans (Module.finrank_pi_fintype L)
  have h2 : ∀ m : MaximalSpectrum A,
      Nat.card (A ⧸ m.asIdeal →ₐ[L] Ω) = Module.finrank L (A ⧸ m.asIdeal) := fun m =>
    AlgHom.natCard_of_splits L (A ⧸ m.asIdeal) Ω (fun _ => IsAlgClosed.splits _)
  let g : (Σ m : MaximalSpectrum A, (A ⧸ m.asIdeal →ₐ[L] Ω)) → (A →ₐ[L] Ω) :=
    fun p => p.2.comp (Ideal.Quotient.mkₐ L p.1.asIdeal)
  have hg : Function.Injective g := by
    rintro ⟨m, φ⟩ ⟨m', φ'⟩ h
    have hk : ∀ (n : MaximalSpectrum A) (χ : A ⧸ n.asIdeal →ₐ[L] Ω) (a : A),
        χ.comp (Ideal.Quotient.mkₐ L n.asIdeal) a = 0 ↔ a ∈ n.asIdeal := by
      intro n χ a
      have hinj : Function.Injective χ := χ.toRingHom.injective
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, map_eq_zero_iff χ hinj,
        Ideal.Quotient.eq_zero_iff_mem]
    have hm : m = m' := by
      ext a
      rw [← hk m φ a, ← hk m' φ' a]
      exact Iff.of_eq (congrArg (fun χ : A →ₐ[L] Ω => χ a = 0) h)
    subst hm
    have : φ = φ' := by
      ext y
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact DFunLike.congr_fun h a
    subst this
    rfl
  set S := Algebra.adjoin L {t}
  let res : (A →ₐ[L] Ω) → (S →ₐ[L] Ω) := fun φ => φ.comp S.val
  have hres : Function.Injective res := by
    intro φ ψ h
    apply ht
    exact DFunLike.congr_fun h ⟨t, Algebra.self_mem_adjoin_singleton L t⟩
  have h3 : Module.finrank L A ≤ Module.finrank L S := by
    calc Module.finrank L A = ∑ m : MaximalSpectrum A, Nat.card (A ⧸ m.asIdeal →ₐ[L] Ω) := by
            rw [h1]; exact Finset.sum_congr rfl (fun m _ => (h2 m).symm)
      _ = Nat.card (Σ m : MaximalSpectrum A, (A ⧸ m.asIdeal →ₐ[L] Ω)) := by
            rw [Nat.card_sigma]
      _ ≤ Nat.card (A →ₐ[L] Ω) := Nat.card_le_card_of_injective g hg
      _ ≤ Nat.card (S →ₐ[L] Ω) := Nat.card_le_card_of_injective res hres
      _ ≤ Module.finrank L S := card_algHom_le_finrank L S Ω
  rw [← Algebra.toSubmodule_eq_top]
  exact Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) h3)

private theorem finite_span_mod_and_integral_of_j_dat {O Λ B : Type} [CommRing O] [CommRing Λ] [IsNoetherianRing Λ]
    [CommRing B] [Algebra O Λ] [Algebra O B] (lam : Λ →ₐ[O] B) (J : Ideal B) (M : Type)
    [AddCommGroup M] [Module B M] [Module Λ M] (h : UpperTheory.V.J.Dat lam J M) :
    (∃ (r : ℕ) (b : Fin r → B), ∀ a : B, ∃ c : Fin r → Λ, a - ∑ i, lam (c i) * b i ∈ J) ∧
    (∀ a : B, ∃ f : Polynomial Λ, f.Monic ∧ Polynomial.eval₂ (lam : Λ →+* B) a f ∈ J) := by
  classical
  have hann : ∀ b : B, (∀ m : M, b • m = 0) → b ∈ J := by
    intro b hb
    apply h.rad
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro p ⟨hJp, hp⟩
    exact (h.supp p hp).mpr hJp (Module.mem_annihilator.mpr hb)
  haveI := h.free
  haveI := h.fin
  let F : B → Module.End Λ M := fun b =>
    { toFun := fun m => b • m
      map_add' := smul_add b
      map_smul' := fun c m => by
        simp only [RingHom.id_apply]
        rw [h.hs, h.hs, smul_smul, smul_smul, mul_comm] }
  have hFa : ∀ a b, F (a + b) = F a + F b := fun a b => LinearMap.ext fun m => add_smul a b m
  have hFs : ∀ a b, F (a - b) = F a - F b := fun a b => LinearMap.ext fun m => sub_smul a b m
  have hFm : ∀ a b, F (a * b) = F a * F b := fun a b => LinearMap.ext fun m => mul_smul a b m
  have hF0 : F 0 = 0 := LinearMap.ext fun m => zero_smul B m
  have hF1 : F 1 = 1 := LinearMap.ext fun m => one_smul B m
  have hFl : ∀ (c : Λ) b, F (lam c * b) = c • F b := fun c b => LinearMap.ext fun m => by
    show (lam c * b) • m = c • (b • m)
    rw [h.hs, mul_smul]
  have hFp : ∀ a (k : ℕ), F (a ^ k) = F a ^ k := by
    intro a k
    induction k with
    | zero => simp [hF1]
    | succ k ih => rw [pow_succ, hFm, ih, pow_succ]
  have hJ : ∀ b, F b = 0 → b ∈ J := fun b hb => hann b fun m => LinearMap.congr_fun hb m
  let N : Submodule Λ (Module.End Λ M) :=
    { carrier := Set.range F
      add_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a + b, hFa a b⟩
      zero_mem' := ⟨0, hF0⟩
      smul_mem' := by
        rintro c _ ⟨b, rfl⟩
        exact ⟨lam c * b, hFl c b⟩ }
  haveI : IsNoetherian Λ (Module.End Λ M) := isNoetherian_of_isNoetherianRing_of_finite Λ _
  obtain ⟨r, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian N)
  have hsN : ∀ i, s i ∈ N := fun i => hs ▸ Submodule.subset_span (Set.mem_range_self i)
  choose b hb using hsN
  refine ⟨⟨r, b, fun a => ?_⟩, fun a => ?_⟩
  · have hmem : F a ∈ Submodule.span Λ (Set.range s) := hs.symm ▸ ⟨a, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Λ).mp hmem
    refine ⟨c, hJ _ ?_⟩
    have hsum : ∀ (t : Finset (Fin r)), F (∑ i ∈ t, lam (c i) * b i) = ∑ i ∈ t, c i • s i := by
      intro t
      induction t using Finset.induction_on with
      | empty => simp [hF0]
      | insert j t hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, hFa, ih, hFl, hb]
    rw [hFs, hsum, hc, sub_self]
  · refine ⟨(F a).charpoly, (F a).charpoly_monic, hJ _ ?_⟩
    have hp : ∀ p : Polynomial Λ,
        F (Polynomial.eval₂ (lam : Λ →+* B) a p) = Polynomial.aeval (F a) p := by
      intro p
      induction p using Polynomial.induction_on with
      | C c =>
        rw [Polynomial.eval₂_C, Polynomial.aeval_C]
        refine LinearMap.ext fun m => ?_
        rw [Module.algebraMap_end_apply]
        exact (h.hs c m).symm
      | add p q hp hq => rw [Polynomial.eval₂_add, map_add, hFa, hp, hq]
      | monomial n c _ =>
        rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
        rw [show (lam : Λ →+* B) c = lam c from rfl, hFl, hFp, map_mul, Polynomial.aeval_C, map_pow,
          Polynomial.aeval_X, Algebra.smul_def]
    rw [hp, LinearMap.aeval_self_charpoly]

private theorem finite_setOf_nat_not_primitive_element {Λ R : Type} [CommRing Λ] [IsDomain Λ] [CharZero Λ] [CommRing R]
    [Algebra Λ R] [IsReduced R] [Module.Finite Λ R]
    (htf : ∀ c : Λ, c ≠ 0 → ∀ y : R, algebraMap Λ R c * y = 0 → y = 0)
    {r : ℕ} (b : Fin r → R) (hgen : ∀ y : R, ∃ c : Fin r → Λ, y = ∑ i, algebraMap Λ R (c i) * b i)
    (f : Fin r → Polynomial Λ) (hf : ∀ i, (f i).Monic)
    (hfb : ∀ i, Polynomial.aeval (b i) (f i) = 0) :
    {s : ℕ | ¬ ∀ y : R, ∃ c : Λ, c ≠ 0 ∧ ∃ P : Polynomial Λ,
      algebraMap Λ R c * y = Polynomial.aeval (∑ i : Fin r, (s : R) ^ (i : ℕ) * b i) P}.Finite := by
  classical
  let L := FractionRing Λ
  let A := Localization (Algebra.algebraMapSubmonoid R (nonZeroDivisors Λ))
  let Ω := AlgebraicClosure L
  haveI : CharZero L := charZero_of_injective_algebraMap (IsFractionRing.injective Λ L)
  haveI : Module.Finite L A := Module.Finite.of_isLocalization Λ R (nonZeroDivisors Λ)
  let ι : R →+* A := algebraMap R A
  have hιl : ∀ c : Λ, ι (algebraMap Λ R c) = algebraMap L A (algebraMap Λ L c) := by
    intro c
    rw [← IsScalarTower.algebraMap_apply Λ L A, IsScalarTower.algebraMap_apply Λ R A]
  let ρ : Λ →+* Ω := (algebraMap L Ω).comp (algebraMap Λ L)
  have hχl : ∀ (χ : A →ₐ[L] Ω) (c : Λ), χ (ι (algebraMap Λ R c)) = ρ c := by
    intro χ c
    rw [hιl, AlgHom.commutes]
    rfl
  let T := {v : Fin r → Ω | ∀ i, Polynomial.eval₂ ρ (v i) (f i) = 0}
  have hT : T.Finite := finite_setOf_roots_of_monic_family ρ f hf
  have hv : ∀ χ : A →ₐ[L] Ω, (fun i => χ (ι (b i))) ∈ T := by
    intro χ i
    have h0 := congrArg (fun y => χ (ι y)) (hfb i)
    simp only [map_zero] at h0
    rw [← h0, Polynomial.aeval_def]
    have hc : ((χ : A →+* Ω).comp ι).comp (algebraMap Λ R) = ρ := RingHom.ext (hχl χ)
    rw [← hc]
    exact (Polynomial.hom_eval₂ (f i) (algebraMap Λ R) ((χ : A →+* Ω).comp ι) (b i)).symm
  refine (finite_setOf_nat_polynomial_collision T hT).subset ?_
  intro s hs
  by_contra hnb
  apply hs
  set t : R := ∑ i : Fin r, (s : R) ^ (i : ℕ) * b i with ht
  have hsum : ∀ χ : A →ₐ[L] Ω, χ (ι t) = ∑ i, χ (ι (b i)) * (s : Ω) ^ (i : ℕ) := by
    intro χ
    simp only [ht, map_sum, map_mul, map_pow, map_natCast]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hsep : ∀ φ ψ : A →ₐ[L] Ω, φ (ι t) = ψ (ι t) → φ = ψ := by
    intro φ ψ hφψ
    have htup : (fun i => φ (ι (b i))) = (fun i => ψ (ι (b i))) := by
      by_contra hne
      exact hnb ⟨_, hv φ, _, hv ψ, hne, by rw [← hsum, ← hsum]; exact hφψ⟩
    have hB : ∀ y : R, φ (ι y) = ψ (ι y) := by
      intro y
      obtain ⟨c, rfl⟩ := hgen y
      simp only [map_sum, map_mul, hχl]
      exact Finset.sum_congr rfl fun i _ => by rw [congr_fun htup i]
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid R (nonZeroDivisors Λ))
    ext y
    exact hB y
  have htop := adjoin_singleton_eq_whole_of_separates_homs (L := L) (A := A) (Ω := Ω) (ι t) hsep
  intro y
  have hy : ι y ∈ Algebra.adjoin L {ι t} := htop ▸ Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
  obtain ⟨Q, hQ⟩ := hy
  obtain ⟨d, hd0, hd⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors Λ) Q
  set P := IsLocalization.integerNormalization (nonZeroDivisors Λ) Q with hP
  have hPQ : P.map (algebraMap Λ L) = Polynomial.C (algebraMap Λ L d) * Q := by
    rw [hd, Algebra.smul_def, Polynomial.algebraMap_apply]
  have hkey : ι (algebraMap Λ R d * y - Polynomial.aeval t P) = 0 := by
    have e1 : ι (Polynomial.aeval t P) = Polynomial.aeval (ι t) (P.map (algebraMap Λ L)) := by
      rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_def, Polynomial.aeval_def,
        Polynomial.hom_eval₂]
      congr 1
    rw [map_sub, e1, hPQ, map_mul, map_mul, Polynomial.aeval_C, hιl]
    change _ * ι y - _ * (Polynomial.aeval (ι t)) Q = 0
    rw [← hQ]
    exact sub_self _
  obtain ⟨⟨m, hm⟩, hm0⟩ :=
    (IsLocalization.map_eq_zero_iff (Algebra.algebraMapSubmonoid R (nonZeroDivisors Λ)) A _).mp hkey
  obtain ⟨e, he, rfl⟩ := hm
  refine ⟨d, nonZeroDivisors.ne_zero hd0, P, ?_⟩
  exact sub_eq_zero.mp (htf e (nonZeroDivisors.ne_zero he) _ hm0)

theorem UpperTheory.V.J.primEx :
    UpperTheory.V.J.PrimEx := by
  intro O Λ B K _ _ _ _ _ _ _ _ _ _ _ lam J M _ _ _ h x hx
  classical
  obtain ⟨⟨r, b, hgen⟩, hmon⟩ := finite_span_mod_and_integral_of_j_dat lam J M h
  choose f hfm hfJ using fun i => hmon (b i)
  letI : Algebra Λ (B ⧸ J) := ((Ideal.Quotient.mk J).comp (lam : Λ →+* B)).toAlgebra
  have hmk : ∀ c : Λ, algebraMap Λ (B ⧸ J) c = Ideal.Quotient.mk J (lam c) := fun c => rfl
  haveI : IsReduced (B ⧸ J) := (Ideal.isRadical_iff_quotient_reduced J).mp h.rad
  have hgenR : ∀ y : B ⧸ J, ∃ c : Fin r → Λ,
      y = ∑ i, algebraMap Λ (B ⧸ J) (c i) * Ideal.Quotient.mk J (b i) := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨c, hc⟩ := hgen a
    refine ⟨c, ?_⟩
    rw [Ideal.Quotient.eq.mpr hc, map_sum]
    simp only [map_mul, hmk]
  haveI : Module.Finite Λ (B ⧸ J) := by
    refine ⟨⟨Finset.univ.image (fun i => Ideal.Quotient.mk J (b i)), ?_⟩⟩
    rw [eq_top_iff]
    rintro y -
    obtain ⟨c, rfl⟩ := hgenR y
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have htf : ∀ c : Λ, c ≠ 0 → ∀ y : B ⧸ J, algebraMap Λ (B ⧸ J) c * y = 0 → y = 0 := by
    intro c hc y hy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hmk, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hy
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (h.tf c hc a hy)
  have hfb : ∀ i, Polynomial.aeval (Ideal.Quotient.mk J (b i)) (f i) = 0 := by
    intro i
    rw [Polynomial.aeval_def]
    have := Polynomial.hom_eval₂ (f i) (lam : Λ →+* B) (Ideal.Quotient.mk J) (b i)
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hfJ i)] at this
    exact this.symm
  have hbadR := finite_setOf_nat_not_primitive_element htf (fun i => Ideal.Quotient.mk J (b i)) hgenR f hfm hfb
  let ρK : Λ →+* K := (x : B →+* K).comp (lam : Λ →+* B)
  let TK := {v : Fin r → K | ∀ i, Polynomial.eval₂ ρK (v i) (f i) = 0}
  have hTK : TK.Finite := finite_setOf_roots_of_monic_family ρK f hfm
  obtain ⟨s, hs⟩ := ((hbadR.union (finite_setOf_nat_polynomial_collision TK hTK)).infinite_compl).nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, not_or] at hs
  obtain ⟨hs1, hs2⟩ := hs
  simp only [Set.mem_setOf_eq, not_not] at hs1
  refine ⟨∑ i : Fin r, (s : B) ^ (i : ℕ) * b i, ?_, ?_⟩
  · intro a
    obtain ⟨c, hc, P, hP⟩ := hs1 (Ideal.Quotient.mk J a)
    refine ⟨c, hc, P, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ← hmk, hP, Polynomial.aeval_def,
      Polynomial.hom_eval₂]
    simp only [map_sum, map_mul, map_pow, map_natCast]
    rw [sub_eq_zero]
    rfl
  · intro x' hx' hcomp hxt
    have hv : ∀ χ : B →ₐ[O] K, J ≤ RingHom.ker χ → χ.comp lam = x.comp lam →
        (fun i => χ (b i)) ∈ TK := by
      intro χ hχ hχc i
      have h0 : (χ : B →+* K) (Polynomial.eval₂ (lam : Λ →+* B) (b i) (f i)) = 0 :=
        RingHom.mem_ker.mp (hχ (hfJ i))
      have hρ : (χ : B →+* K).comp (lam : Λ →+* B) = ρK :=
        RingHom.ext fun c => AlgHom.congr_fun hχc c
      rw [Polynomial.hom_eval₂, hρ] at h0
      exact h0
    have hsum : ∀ χ : B →ₐ[O] K,
        χ (∑ i : Fin r, (s : B) ^ (i : ℕ) * b i) = ∑ i, χ (b i) * (s : K) ^ (i : ℕ) := by
      intro χ
      simp only [map_sum, map_mul, map_pow, map_natCast]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have htup : (fun i => x' (b i)) = (fun i => x (b i)) := by
      by_contra hne
      exact hs2 ⟨_, hv x' hx' hcomp, _, hv x hx rfl, hne, by rw [← hsum, ← hsum]; exact hxt⟩
    ext a
    obtain ⟨c, hc⟩ := hgen a
    have e1 : ∀ χ : B →ₐ[O] K, J ≤ RingHom.ker χ →
        χ a = ∑ i, χ (lam (c i)) * χ (b i) := by
      intro χ hχ
      have := RingHom.mem_ker.mp (hχ hc)
      rw [map_sub, sub_eq_zero] at this
      rw [this, map_sum]
      simp only [map_mul]
    rw [e1 x' hx', e1 x hx]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := AlgHom.congr_fun hcomp (c i)
    simp only [AlgHom.comp_apply] at h1
    rw [h1, congr_fun htup i]
