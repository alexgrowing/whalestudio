import Mathlib

namespace UpperTheory.Reformulated.B.Ra5

open Polynomial

private theorem ext_inj {R S K : Type} [CommRing R] [CommRing S] [IsDomain S]
    [Field K] [IsAlgClosed K] (f : R →+* S) (hf : Function.Injective f) (hfi : f.IsIntegral)
    (g : R →+* K) (hg : Function.Injective g) :
    ∃ l : S →+* K, l.comp f = g := by
  haveI : IsDomain R := hf.isDomain f
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R K := g.toAlgebra
  haveI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective _ _).mpr hf
  haveI : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  haveI : Algebra.IsIntegral R S := ⟨hfi⟩
  let l := IsAlgClosed.lift (R := R) (S := S) (M := K)
  exact ⟨(l : S →+* K), RingHom.ext fun x => l.commutes x⟩

private theorem ext_integral {R S K : Type} [CommRing R] [CommRing S] [IsDomain S]
    [Field K] [IsAlgClosed K] (f : R →+* S) (hinj : Function.Injective f) (hfi : f.IsIntegral)
    (y : R →+* K) :
    ∃ ξ : S →+* K, ξ.comp f = y := by
  letI : Algebra R S := f.toAlgebra
  haveI : Algebra.IsIntegral R S := ⟨hfi⟩
  haveI hp : (RingHom.ker y).IsPrime := RingHom.ker_isPrime y
  obtain ⟨Q, -, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := S)
    (RingHom.ker y) (⊥ : Ideal S) (by
      intro x hx
      have h0 : algebraMap R S x = 0 := by simpa using hx
      have hx0 : x = 0 := hinj (h0.trans (map_zero f).symm)
      simp [hx0])
  have hQc' : Q.comap f = RingHom.ker y := hQc
  let q : (R ⧸ Q.comap f) →+* (S ⧸ Q) := Ideal.quotientMap Q f le_rfl
  have hq : Function.Injective q := Ideal.quotientMap_injective
  have hqi : q.IsIntegral := RingHom.IsIntegral.quotient f hfi
  let g : (R ⧸ Q.comap f) →+* K := Ideal.Quotient.lift _ y (fun a ha => by
    have : a ∈ RingHom.ker y := hQc' ▸ ha
    exact this)
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro a
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    intro h
    have hx : x ∈ RingHom.ker y := h
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hQc' ▸ hx)
  obtain ⟨l, hl⟩ := ext_inj q hq hqi g hg
  refine ⟨l.comp (Ideal.Quotient.mk Q), RingHom.ext fun x => ?_⟩
  have h := RingHom.congr_fun hl (Ideal.Quotient.mk _ x)
  exact h

private theorem gen_alg {A B K : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra B A] [Field K] [IsAlgClosed K]
    (hinj : Function.Injective (algebraMap B A)) (t : A) (ht : Algebra.adjoin B {t} = ⊤)
    (f : B[X]) (hf : f ≠ 0) (hft : aeval t f = 0) (y : B →+* K) (hy : y f.leadingCoeff ≠ 0) :
    ∃ ξ : A →+* K, ξ.comp (algebraMap B A) = y := by
  have hc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf
  let M : Submonoid B := Submonoid.powers f.leadingCoeff
  have hM : M ≤ nonZeroDivisors B := powers_le_nonZeroDivisors_of_noZeroDivisors hc
  let M' : Submonoid A := M.map (algebraMap B A)
  have hM' : M' ≤ nonZeroDivisors A := by
    rintro _ ⟨m, hm, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero
      (fun h => nonZeroDivisors.ne_zero (hM hm) (hinj (by simpa using h)))
  haveI : IsDomain (Localization M') := IsLocalization.isDomain_localization hM'
  let φ : Localization M →+* Localization M' :=
    IsLocalization.map (Localization M') (algebraMap B A) M.le_comap_map
  have hφ : ∀ r : B, φ (algebraMap B (Localization M) r) =
      algebraMap A (Localization M') (algebraMap B A r) := fun r => IsLocalization.map_eq _ r
  have h1 : ∀ s : A, φ.IsIntegralElem (algebraMap A (Localization M') s) := by
    intro s
    have hs : s ∈ Algebra.adjoin B {t} := ht ▸ Algebra.mem_top
    induction hs using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact RingHom.isIntegralElem_localization_at_leadingCoeff (algebraMap B A) x f hft M
        (Submonoid.mem_powers _)
    | algebraMap r =>
      rw [← hφ]
      exact RingHom.isIntegralElem_map φ
    | add x y _ _ hx hy =>
      rw [map_add]
      exact RingHom.IsIntegralElem.add φ hx hy
    | mul x y _ _ hx hy =>
      rw [map_mul]
      exact RingHom.IsIntegralElem.mul φ hx hy
  have hint : φ.IsIntegral := by
    intro x
    obtain ⟨⟨s, ⟨_, m, hm, rfl⟩⟩, hx⟩ := IsLocalization.surj M' x
    obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp
      (IsLocalization.map_units (Localization M) (⟨m, hm⟩ : M))
    have hv' : algebraMap A (Localization M') (algebraMap B A m) * φ v = 1 := by
      rw [← hφ, ← map_mul]
      have : algebraMap B (Localization M) m * v = 1 := hv
      rw [this, map_one]
    have hxe : x = algebraMap A (Localization M') s * φ v := by
      rw [← hx, mul_assoc]
      simp only [] at hv' ⊢
      rw [hv', mul_one]
    rw [hxe]
    exact RingHom.IsIntegralElem.mul φ (h1 s) (RingHom.isIntegralElem_map φ)
  have hφi : Function.Injective φ :=
    IsLocalization.map_injective_of_injective M (Localization M) (Localization M') hinj
  let y' : Localization M →+* K := IsLocalization.lift (M := M) (g := y) (by
    rintro ⟨_, n, rfl⟩
    simpa using (isUnit_iff_ne_zero.mpr hy).pow n)
  obtain ⟨ξ, hξ⟩ := ext_integral φ hφi hint y'
  refine ⟨ξ.comp (algebraMap A (Localization M')), RingHom.ext fun r => ?_⟩
  have h := RingHom.congr_fun hξ (algebraMap B (Localization M) r)
  simp only [RingHom.comp_apply, hφ] at h ⊢
  rw [h]
  exact IsLocalization.lift_eq _ r

private theorem one_gen {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra B A] (hinj : Function.Injective (algebraMap B A)) (t : A)
    (ht : Algebra.adjoin B {t} = ⊤) (a : A) (ha : a ≠ 0) :
    ∃ b : B, b ≠ 0 ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (y : B →+* K), y b ≠ 0 →
      ∃ ξ : A →+* K, ξ.comp (algebraMap B A) = y ∧ ξ a ≠ 0 := by
  haveI : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr hinj
  by_cases hta : IsAlgebraic B t
  · have haa : IsAlgebraic B a :=
      Algebra.isAlgebraic_adjoin_singleton_iff.mpr hta a (ht ▸ Algebra.mem_top)
    obtain ⟨f, hf, hft⟩ := hta
    obtain ⟨r, hr, d, hd⟩ := haa.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero ha)
    refine ⟨f.leadingCoeff * r, mul_ne_zero (leadingCoeff_ne_zero.mpr hf) hr,
      fun K _ _ y hy => ?_⟩
    rw [map_mul] at hy
    obtain ⟨ξ, hξ⟩ := gen_alg hinj t ht f hf hft y (left_ne_zero_of_mul hy)
    refine ⟨ξ, hξ, fun h0 => right_ne_zero_of_mul hy ?_⟩
    have h1 := congrArg ξ hd
    rw [map_mul, h0, zero_mul] at h1
    rw [← hξ]
    exact h1
  · have hsurj : Function.Surjective (aeval t : B[X] →ₐ[B] A) := by
      intro x
      have hx : x ∈ Algebra.adjoin B {t} := ht ▸ Algebra.mem_top
      rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
      exact hx
    have hbij : Function.Bijective (aeval t : B[X] →ₐ[B] A) :=
      ⟨transcendental_iff_injective.mp hta, hsurj⟩
    obtain ⟨p, rfl⟩ := hsurj a
    have hp : p ≠ 0 := fun h => ha (by simp [h])
    refine ⟨p.leadingCoeff, leadingCoeff_ne_zero.mpr hp, fun K _ _ y hy => ?_⟩
    have hpm : p.map y ≠ 0 := by
      intro h
      apply hy
      have := congrArg (fun q => q.coeff p.natDegree) h
      simpa [coeff_map] using this
    obtain ⟨r, hr⟩ : ∃ r, (p.map y).eval r ≠ 0 := by
      by_contra! h
      exact hpm (Polynomial.funext (by simpa using h))
    let e := AlgEquiv.ofBijective (aeval t : B[X] →ₐ[B] A) hbij
    refine ⟨(eval₂RingHom y r).comp (e.symm : A →+* B[X]), RingHom.ext fun x => ?_, ?_⟩
    · have : e.symm (algebraMap B A x) = C x := by
        rw [AlgEquiv.symm_apply_eq]
        simp [e]
      simp [this]
    · have : e.symm (aeval t p) = p := e.symm_apply_apply p
      simpa [this, eval_map] using hr

end UpperTheory.Reformulated.B.Ra5

theorem UpperTheory.Reformulated.B.Ra5.main_fin :
    ∀ (A : Type) [inst : CommRing A] [IsDomain A]
    (s : Finset A) (B : Type) [inst_2 : CommRing B] [IsDomain B] [inst_4 : Algebra B A],
    Algebra.adjoin B (↑s : Set A) = ⊤ →
      Function.Injective (⇑(Algebra.algebraMap B A) : B → A) →
        ∀ (a : A),
          a ≠ (0 : A) →
            ∃ (b : B),
              b ≠ (0 : B) ∧
                ∀ (K : Type) [inst_5 : Field K] [IsAlgClosed K] (y : B →+* K),
                  (y : B → K) b ≠ (0 : K) →
                    ∃ (ξ : A →+* K), ξ.comp (Algebra.algebraMap B A) = y ∧ (ξ : A → K) a ≠ (0 : K) := by
  intro A _ _ s
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro B _ _ _ htop hinj a ha
    have hinj' : Function.Injective (algebraMap B A) := hinj
    have hsurj : Function.Surjective (algebraMap B A) := by
      intro x
      have hx : x ∈ (⊥ : Subalgebra B A) := by
        rw [← Algebra.adjoin_empty B A, ← Finset.coe_empty, htop]
        exact Algebra.mem_top
      exact Algebra.mem_bot.mp hx
    obtain ⟨b, rfl⟩ := hsurj a
    let e := RingEquiv.ofBijective (algebraMap B A) ⟨hinj', hsurj⟩
    have hb : b ≠ 0 := fun h => ha (by simp [h])
    refine ⟨b, hb, fun K _ _ y hy => ⟨y.comp (e.symm : A →+* B), ?_, ?_⟩⟩
    · refine RingHom.ext fun x => ?_
      have : e.symm (algebraMap B A x) = x := e.symm_apply_apply x
      exact congrArg y this
    · have : e.symm (algebraMap B A b) = b := e.symm_apply_apply b
      simpa [this] using hy
  | insert t s' hts ih =>
    intro B _ _ _ htop hinj a ha
    have hinj' : Function.Injective (algebraMap B A) := hinj
    rw [Finset.coe_insert, Set.insert_eq, Algebra.adjoin_union_eq_adjoin_adjoin] at htop
    have h1 : Algebra.adjoin (Algebra.adjoin B ({t} : Set A)) (s' : Set A) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : x ∈ Subalgebra.restrictScalars B
          (Algebra.adjoin (Algebra.adjoin B ({t} : Set A)) (s' : Set A)) := htop ▸ Algebra.mem_top
      exact hx
    obtain ⟨b₁, hb₁, h⟩ := ih (Algebra.adjoin B ({t} : Set A)) h1 Subtype.val_injective a ha
    let t₁ : Algebra.adjoin B ({t} : Set A) := ⟨t, Algebra.subset_adjoin rfl⟩
    have ht₁ : Algebra.adjoin B {t₁} = ⊤ := by
      apply Subalgebra.map_injective (f := (Algebra.adjoin B ({t} : Set A)).val)
        Subtype.val_injective
      rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val, Set.image_singleton]
      rfl
    have hinj₁ : Function.Injective (algebraMap B (Algebra.adjoin B ({t} : Set A))) := by
      intro x x' hxx
      exact hinj' (congrArg Subtype.val hxx)
    obtain ⟨b, hb, h2⟩ := one_gen hinj₁ t₁ ht₁ b₁ hb₁
    refine ⟨b, hb, fun K _ _ y hy => ?_⟩
    obtain ⟨ξ₁, h3, h4⟩ := h2 K y hy
    obtain ⟨ξ, h5, h6⟩ := h K ξ₁ h4
    refine ⟨ξ, RingHom.ext fun x => ?_, h6⟩
    have h7 := RingHom.congr_fun h5 (algebraMap B _ x)
    have h8 := RingHom.congr_fun h3 x
    exact h7.trans h8
