import Mathlib

open TensorProduct

namespace GlobalTheory

section Krull

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

theorem localizedModule_mk_one_eq_zero_iff (p : Ideal A) [p.IsPrime] (x : M) :
    (LocalizedModule.mk x 1 : LocalizedModule p.primeCompl M) = 0 ↔ ∃ s ∉ p, s • x = 0 := by
  have := IsLocalizedModule.eq_zero_iff p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl M) (m := x)
  rw [LocalizedModule.mkLinearMap_apply] at this
  rw [this]
  exact ⟨fun ⟨s, hs⟩ ↦ ⟨s.1, s.2, hs⟩, fun ⟨s, hs, h⟩ ↦ ⟨⟨s, hs⟩, h⟩⟩

variable [IsNoetherianRing A] [Module.Finite A M]

theorem exists_smul_eq_zero_of_mem_iInf_pow_smul (I : Ideal A) {x : M}
    (hx : x ∈ (⨅ n : ℕ, I ^ n • ⊤ : Submodule A M)) : ∃ f : A, f - 1 ∈ I ∧ f • x = 0 := by
  obtain ⟨r, hr⟩ := (I.mem_iInf_smul_pow_eq_bot_iff x).1 hx
  refine ⟨1 - r, by simp, ?_⟩
  rw [sub_smul, one_smul, hr, sub_self]

end Krull

section Associated

variable {A : Type*} [CommRing A] [IsNoetherianRing A] {M : Type*} [AddCommGroup M] [Module A M]

theorem eq_zero_of_forall_associatedPrimes_exists_smul_eq_zero {x : M}
    (h : ∀ p ∈ associatedPrimes A M, ∃ s ∉ p, s • x = 0) : x = 0 := by
  by_contra hx
  obtain ⟨p, hp, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A x hx
  obtain ⟨s, hs, hsx⟩ := h p hp
  exact hs (hle (by simpa [Submodule.mem_colon_singleton] using hsx))

end Associated

section Flat

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {M : Type*} [AddCommGroup M] [Module A M]

theorem under_mem_associatedPrimes [Module B M] [IsScalarTower A B M] {q : Ideal B}
    (hq : q ∈ associatedPrimes B M) : q.under A ∈ associatedPrimes A M := by
  obtain ⟨hq', x, hx⟩ := hq
  refine ⟨hq'.under A, x, ?_⟩
  ext a
  rw [Ideal.under_def, Ideal.mem_comap, hx]
  simp only [Ideal.mem_radical_iff, Submodule.mem_colon_singleton, Submodule.mem_bot, ← map_pow,
    algebraMap_smul]

theorem associatedPrimes_subset_of_flat [IsNoetherianRing A] [Module.Flat A M] :
    associatedPrimes A M ⊆ associatedPrimes A A := by
  intro p hp
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hp ⊢
  obtain ⟨hp, x, hx⟩ := hp
  have hmem : ∀ a, a ∈ p ↔ a • x = 0 := fun a ↦ by simp [hx, Submodule.mem_colon_singleton]
  obtain ⟨k, a, y, hy, ha⟩ := Module.Flat.exists_factorization_of_comp_eq_zero_of_free
    (f := p.subtype) (x := LinearMap.toSpanSingleton A M x)
    (by ext ⟨a, ha⟩; simpa using (hmem a).1 ha)
  have hx' : x = y (a 1) := by simpa using congr($hy 1)
  have hk : ∀ r ∈ p, ∀ j, r * a 1 j = 0 := fun r hr j ↦ by
    have : a r = 0 := by simpa using congr($ha ⟨r, hr⟩)
    have h2 : r • a 1 = 0 := by rw [← map_smul, smul_eq_mul, mul_one, this]
    simpa using congr($h2 j)
  refine ⟨hp, ?_⟩
  by_contra hne
  have : ∀ j, ∃ s ∉ p, s * a 1 j = 0 := fun j ↦ by
    by_contra hcon
    push Not at hcon
    refine hne ⟨a 1 j, ?_⟩
    ext r
    simp only [Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_bot]
    exact ⟨fun hr ↦ hk r hr j, fun hr ↦ by_contra fun h ↦ hcon r h hr⟩
  choose s hs hs' using this
  have hprod : (∏ j, s j) ∉ p := p.primeCompl.prod_mem fun j _ ↦ hs j
  refine hprod ((hmem _).2 ?_)
  have : (∏ j, s j) • a 1 = 0 := by
    ext j
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem s (Finset.mem_univ j)
    rw [Finsupp.smul_apply, smul_eq_mul, hc, mul_comm (s j), mul_assoc, hs', mul_zero,
      Finsupp.zero_apply]
  rw [hx', ← map_smul, this, map_zero]

variable [Module B M] [IsScalarTower A B M] [Module.Flat A M]

theorem under_eq_of_mem_associatedPrimes_tensor_quotient (p : Ideal A) [hp : p.IsPrime]
    {q : Ideal B} (hq : q ∈ associatedPrimes B (M ⊗[A] (A ⧸ p))) : q.under A = p := by
  obtain ⟨hq', x, hx⟩ := under_mem_associatedPrimes (A := A) hq
  have key : ∀ a : A, a • x = LinearMap.lTensor M (a • LinearMap.id) x := fun a ↦ by
    rw [LinearMap.lTensor_smul, LinearMap.lTensor_id, LinearMap.smul_apply, LinearMap.id_apply]
  refine le_antisymm (fun a ha ↦ ?_) (fun a ha ↦ ?_)
  · by_contra hap
    rw [hx] at ha
    obtain ⟨n, hn⟩ := ha
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, key] at hn
    have hinj : Function.Injective (a ^ n • LinearMap.id : (A ⧸ p) →ₗ[A] (A ⧸ p)) := by
      rw [injective_iff_map_eq_zero]
      intro z hz
      rw [LinearMap.smul_apply, LinearMap.id_apply, Algebra.smul_def, mul_eq_zero,
        Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at hz
      exact hz.resolve_left fun h ↦ hap (hp.mem_of_pow_mem n h)
    have hx0 : x = 0 := Module.Flat.lTensor_preserves_injective_linearMap _ hinj
      (hn.trans (map_zero _).symm)
    exact hq'.ne_top (by simp [hx, hx0])
  · rw [hx]
    refine Ideal.le_radical ?_
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, key]
    have : (a • LinearMap.id : (A ⧸ p) →ₗ[A] (A ⧸ p)) = 0 := by
      refine LinearMap.ext fun z ↦ ?_
      simp [Algebra.smul_def, Ideal.Quotient.eq_zero_iff_mem.2 ha]
    simp [this]

theorem mem_associatedPrimes_tensor_quotient_under [IsNoetherianRing A] {N : Type*}
    [AddCommGroup N] [Module A N] [hN : Module.Finite A N] {q : Ideal B}
    (hq : q ∈ associatedPrimes B (M ⊗[A] N)) :
    q ∈ associatedPrimes B (M ⊗[A] (A ⧸ q.under A)) := by
  induction hN using IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime A with
  | subsingleton N => simp [associatedPrimes.eq_empty_of_subsingleton] at hq
  | quotient N p e =>
    rw [LinearEquiv.AssociatedPrimes.eq
      (AlgebraTensorModule.congr (LinearEquiv.refl B M) e)] at hq
    rwa [under_eq_of_mem_associatedPrimes_tensor_quotient p.asIdeal hq]
  | exact N₁ N₂ N₃ f g hf hg hfg h₁ h₃ =>
    have hf' : Function.Injective (AlgebraTensorModule.lTensor B M f) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ hf
    have hfg' : Function.Exact (AlgebraTensorModule.lTensor B M f)
        (AlgebraTensorModule.lTensor B M g) := lTensor_exact M hfg hg
    exact (associatedPrimes.subset_union_of_exact hf' hfg' hq).elim h₁ h₃

theorem injective_lTensor_residueField (p : Ideal A) [p.IsPrime] :
    Function.Injective (AlgebraTensorModule.lTensor B M
      (IsScalarTower.toAlgHom A (A ⧸ p) p.ResidueField).toLinearMap) :=
  Module.Flat.lTensor_preserves_injective_linearMap _
    (IsFractionRing.injective (A ⧸ p) p.ResidueField)

theorem associatedPrimes_tensor_residueField (p : Ideal A) [hp : p.IsPrime] :
    associatedPrimes B (M ⊗[A] p.ResidueField) = associatedPrimes B (M ⊗[A] (A ⧸ p)) := by
  refine subset_antisymm ?_
    (associatedPrimes.subset_of_injective (injective_lTensor_residueField p))
  set φ := AlgebraTensorModule.lTensor B M
    (IsScalarTower.toAlgHom A (A ⧸ p) p.ResidueField).toLinearMap with hφ
  have hinj : Function.Injective φ := injective_lTensor_residueField p
  have hsurj : ∀ x : M ⊗[A] p.ResidueField, ∃ r ∉ p, ∃ y, φ y = r • x := fun x ↦ by
    induction x with
    | zero => exact ⟨1, (Ideal.ne_top_iff_one p).1 hp.ne_top, 0, by simp⟩
    | tmul m c =>
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A ⧸ p) c
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      have hb0 := nonZeroDivisors.ne_zero hb
      refine ⟨b, fun h ↦ hb0 (Ideal.Quotient.eq_zero_iff_mem.2 h), m ⊗ₜ a, ?_⟩
      have : algebraMap (A ⧸ p) p.ResidueField (Ideal.Quotient.mk p b) ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective (A ⧸ p) p.ResidueField)).2 hb0
      rw [← tmul_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply A (A ⧸ p) p.ResidueField,
        Ideal.Quotient.algebraMap_eq, mul_div_cancel₀ _ this]
      simp [hφ]
    | add x y hx hy =>
      obtain ⟨r, hr, x', hx'⟩ := hx
      obtain ⟨s, hs, y', hy'⟩ := hy
      refine ⟨r * s, p.primeCompl.mul_mem hr hs, s • x' + r • y', ?_⟩
      rw [map_add, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, hx', hy', smul_add,
        smul_smul, smul_smul, mul_comm s r]
  have hreg : ∀ r ∉ p, ∀ x : M ⊗[A] p.ResidueField, r • x = 0 → x = 0 := fun r hr x hx ↦ by
    have h1 : Function.Injective (r • LinearMap.id : p.ResidueField →ₗ[A] p.ResidueField) := by
      rw [injective_iff_map_eq_zero]
      intro z hz
      simpa [Algebra.smul_def, hr] using hz
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := M) _ h1 (by simpa using hx)
  rintro q ⟨hq, x, hx⟩
  obtain ⟨r, hr, y, hy⟩ := hsurj x
  refine ⟨hq, y, ?_⟩
  rw [hx]
  congr 1
  ext b
  simp only [Submodule.mem_colon_singleton, Submodule.mem_bot]
  rw [← map_eq_zero_iff φ hinj, map_smul, hy, smul_comm]
  exact ⟨fun h ↦ by rw [h, smul_zero], hreg r hr _⟩

theorem mem_associatedPrimes_iff_of_flat_module [IsNoetherianRing A] (q : Ideal B) [q.IsPrime] :
    q ∈ associatedPrimes B M ↔ q.under A ∈ associatedPrimes A A ∧
      q ∈ associatedPrimes B (M ⊗[A] (q.under A).ResidueField) := by
  rw [associatedPrimes_tensor_residueField]
  have e := LinearEquiv.AssociatedPrimes.eq (AlgebraTensorModule.rid A B M)
  constructor
  · intro hq
    refine ⟨associatedPrimes_subset_of_flat (under_mem_associatedPrimes hq), ?_⟩
    rw [← e] at hq
    exact mem_associatedPrimes_tensor_quotient_under hq
  · rintro ⟨hp, hq⟩
    obtain ⟨-, f, hf⟩ := (isAssociatedPrime_iff_exists_injective_linearMap _ _).1 hp
    have hf' : Function.Injective (AlgebraTensorModule.lTensor B M f) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ hf
    rw [← e]
    exact associatedPrimes.subset_of_injective hf' hq

theorem mem_associatedPrimes_tensor_residueField_iff (p : Ideal A) [p.IsPrime] (q : Ideal B) :
    q ∈ associatedPrimes B (B ⊗[A] p.ResidueField) ↔
      ∃ Q ∈ associatedPrimes (p.Fiber B) (p.Fiber B),
        Q.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] p.Fiber B) = q := by
  let e := Algebra.TensorProduct.comm A B p.ResidueField
  have key : ∀ (b : B) (x : B ⊗[A] p.ResidueField),
      (Algebra.TensorProduct.includeRight : B →ₐ[A] p.Fiber B) b ∈
        ((⊥ : Submodule (p.Fiber B) (p.Fiber B)).colon {e x}).radical ↔
      b ∈ ((⊥ : Submodule B (B ⊗[A] p.ResidueField)).colon {x}).radical := fun b x ↦ by
    simp only [Ideal.mem_radical_iff, Submodule.mem_colon_singleton, Submodule.mem_bot, ← map_pow]
    refine exists_congr fun n ↦ ?_
    rw [← map_eq_zero_iff e e.injective, Algebra.smul_def (b ^ n) x, map_mul]
    rfl
  constructor
  · rintro ⟨hq, x, hx⟩
    refine ⟨((⊥ : Submodule (p.Fiber B) (p.Fiber B)).colon {e x}).radical, ⟨⟨?_, ?_⟩, e x, rfl⟩, ?_⟩
    · rw [Ideal.ne_top_iff_one, ← map_one (Algebra.TensorProduct.includeRight :
        B →ₐ[A] p.Fiber B), key, ← hx, ← Ideal.ne_top_iff_one]
      exact hq.ne_top
    · have aux : ∀ y : p.Fiber B, ∃ u : p.Fiber B, IsUnit u ∧ ∃ b : B,
          u * y = (Algebra.TensorProduct.includeRight : B →ₐ[A] p.Fiber B) b := fun y ↦ by
        obtain ⟨r, hr, s, h⟩ := Ideal.Fiber.exists_smul_eq_one_tmul p y
        refine ⟨algebraMap A _ r, ?_, s, by rw [← Algebra.smul_def, h]; rfl⟩
        rw [IsScalarTower.algebraMap_apply A p.ResidueField (p.Fiber B)]
        exact (IsUnit.mk0 _ (by simpa using hr)).map _
      intro y z hyz
      obtain ⟨u, hu, b, hb⟩ := aux y
      obtain ⟨u', hu', b', hb'⟩ := aux z
      rw [← Ideal.unit_mul_mem_iff_mem _ (x := y) hu, ← Ideal.unit_mul_mem_iff_mem _ (x := z) hu',
        hb, hb', key, key, ← hx]
      refine hq.mem_or_mem ?_
      rw [hx, ← key, map_mul, ← hb, ← hb', mul_mul_mul_comm]
      exact Ideal.mul_mem_left _ _ hyz
    · ext b
      rw [Ideal.mem_comap, key, hx]
  · rintro ⟨Q, ⟨hQ, x, hx⟩, rfl⟩
    obtain ⟨x, rfl⟩ := e.surjective x
    refine ⟨Ideal.comap_isPrime _ _, x, ?_⟩
    ext b
    rw [Ideal.mem_comap, ← key, ← hx]

variable [Module.Flat A B]

theorem mem_associatedPrimes_iff_of_flat [IsNoetherianRing A] (q : Ideal B) [q.IsPrime] :
    q ∈ associatedPrimes B B ↔ q.under A ∈ associatedPrimes A A ∧
      ∃ Q ∈ associatedPrimes ((q.under A).Fiber B) ((q.under A).Fiber B),
        Q.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] (q.under A).Fiber B) = q := by
  rw [mem_associatedPrimes_iff_of_flat_module (A := A),
    mem_associatedPrimes_tensor_residueField_iff]

theorem ker_includeRight_fiber (p : Ideal A) [p.IsPrime] :
    RingHom.ker (Algebra.TensorProduct.includeRight : B →ₐ[A] p.Fiber B) =
      p.map (algebraMap A B) := by
  ext b
  rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem,
    ← map_eq_zero_iff _ (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B p).injective,
    Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk,
    ← map_eq_zero_iff _ (injective_lTensor_residueField (B := B) (M := B) p),
    ← map_eq_zero_iff _ (Algebra.TensorProduct.comm A p.ResidueField B).injective]
  simp

theorem mem_associatedPrimes_iff_eq_map_of_flat [IsNoetherianRing A] (q : Ideal B) [hq : q.IsPrime]
    [NoZeroDivisors ((q.under A).Fiber B)] :
    q ∈ associatedPrimes B B ↔ q.under A ∈ associatedPrimes A A ∧
      q = (q.under A).map (algebraMap A B) := by
  rw [mem_associatedPrimes_iff_of_flat (A := A), and_congr_right_iff,
    ← ker_includeRight_fiber (q.under A)]
  intro _
  constructor
  · rintro ⟨Q, ⟨hQ, x, hx⟩, h⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hQ.ne_top (by simp [hx])
    have : Q = ⊥ := by
      rw [eq_bot_iff, hx]
      rintro y ⟨n, hn⟩
      simp only [Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_bot, mul_eq_zero, hx0,
        or_false] at hn
      exact eq_zero_of_pow_eq_zero hn
    rw [RingHom.ker_eq_comap_bot, ← this, h]
  · intro h
    have : Nontrivial ((q.under A).Fiber B) := by
      refine ⟨1, 0, fun h1 ↦ hq.ne_top ?_⟩
      rw [Ideal.eq_top_iff_one, h, RingHom.mem_ker, map_one, h1]
    have := NoZeroDivisors.to_isDomain ((q.under A).Fiber B)
    refine ⟨⊥, ⟨Ideal.isPrime_bot, 1, ?_⟩, by rw [← RingHom.ker_eq_comap_bot, ← h]⟩
    rw [eq_comm, eq_bot_iff]
    rintro y ⟨n, hn⟩
    simp only [Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_bot, mul_one] at hn
    exact eq_zero_of_pow_eq_zero hn

theorem mem_associatedPrimes_iff_generic_of_flat [IsNoetherianRing A] (q : Ideal B)
    [hq : q.IsPrime] [NoZeroDivisors ((q.under A).Fiber B)] :
    q ∈ associatedPrimes B B ↔ q.under A ∈ associatedPrimes A A ∧
      ∀ q' : Ideal B, q'.IsPrime → q'.under A = q.under A → q ≤ q' := by
  rw [mem_associatedPrimes_iff_eq_map_of_flat (A := A), and_congr_right_iff]
  intro _
  constructor
  · intro h q' _ h'
    rw [h, Ideal.map_le_iff_le_comap, ← h']
  · intro h
    have hle : (q.under A).map (algebraMap A B) ≤ q := Ideal.map_comap_le
    have : Nontrivial ((q.under A).Fiber B) := by
      refine ⟨1, 0, fun h1 ↦ hq.ne_top ?_⟩
      rw [Ideal.eq_top_iff_one]
      refine hle ?_
      rw [← ker_includeRight_fiber, RingHom.mem_ker, map_one, h1]
    have := NoZeroDivisors.to_isDomain ((q.under A).Fiber B)
    refine le_antisymm (h _ ?_ ?_) hle
    · rw [← ker_includeRight_fiber]
      exact RingHom.ker_isPrime _
    · exact le_antisymm (Ideal.comap_mono hle) Ideal.le_comap_map

theorem eq_zero_of_flat_of_forall_fiber [IsNoetherianRing A] [IsNoetherianRing B]
    {L : Type*} [AddCommGroup L] [Module B L] [Module.Flat B L]
    (hfib : ∀ p : PrimeSpectrum A, p.asIdeal ∈ associatedPrimes A A →
      NoZeroDivisors (p.asIdeal.Fiber B)) {x : L}
    (hx : ∀ q : PrimeSpectrum B, q.asIdeal.under A ∈ associatedPrimes A A →
      ∃ q' : PrimeSpectrum B, q'.asIdeal.under A = q.asIdeal.under A ∧
        (LocalizedModule.mk x 1 : LocalizedModule q'.asIdeal.primeCompl L) = 0) : x = 0 := by
  refine eq_zero_of_forall_associatedPrimes_exists_smul_eq_zero (A := B) fun q hq ↦ ?_
  have hqB := associatedPrimes_subset_of_flat hq
  haveI := hqB.isPrime
  have hp := ((mem_associatedPrimes_iff_of_flat (A := A) q).1 hqB).1
  haveI := hfib ⟨q.under A, inferInstance⟩ hp
  obtain ⟨q', h1, h2⟩ := hx ⟨q, inferInstance⟩ hp
  obtain ⟨s, hs, h⟩ := (localizedModule_mk_one_eq_zero_iff q'.asIdeal x).1 h2
  exact ⟨s, fun hsq ↦ hs (((mem_associatedPrimes_iff_generic_of_flat (A := A) q).1 hqB).2
    q'.asIdeal q'.2 h1 hsq), h⟩

end Flat

section Symbolic

variable {R : Type*} [CommRing R]

noncomputable def symbolicPower (P : Ideal R) [P.IsPrime] (m : ℕ) : Ideal R :=
  (IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ m).comap
    (algebraMap R (Localization.AtPrime P))

open IsLocalRing in

theorem exists_sup_maximalIdeal_pow_stable [IsNoetherianRing R] [IsLocalRing R]
    (J : ℕ → Ideal R) (hJ : Antitone J) (k : ℕ) :
    ∃ m, ∀ m' ≥ m, J m' ⊔ maximalIdeal R ^ k = J m ⊔ maximalIdeal R ^ k := by
  have hdim : Ring.KrullDimLE 0 (R ⧸ maximalIdeal R ^ k) := by
    rw [Ring.krullDimLE_zero_iff]
    intro Q hQ
    have h1 : maximalIdeal R ^ k ≤ Q.comap (Ideal.Quotient.mk (maximalIdeal R ^ k)) :=
      fun x hx ↦ by simp [Ideal.Quotient.eq_zero_iff_mem.2 hx]
    have h2 : maximalIdeal R = Q.comap (Ideal.Quotient.mk (maximalIdeal R ^ k)) :=
      (maximalIdeal.isMaximal R).eq_of_le (Ideal.IsPrime.ne_top inferInstance)
        (Ideal.IsPrime.le_of_pow_le h1)
    have h3 : (Q.comap (Ideal.Quotient.mk (maximalIdeal R ^ k))).IsMaximal :=
      h2 ▸ maximalIdeal.isMaximal R
    have h4 := Ideal.IsMaximal.map_of_surjective_of_ker_le
      (f := Ideal.Quotient.mk (maximalIdeal R ^ k)) Ideal.Quotient.mk_surjective
      (m := Q.comap (Ideal.Quotient.mk (maximalIdeal R ^ k))) (by simpa using h1)
    rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h4
  have hart : IsArtinianRing (R ⧸ maximalIdeal R ^ k) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  obtain ⟨m, hm⟩ := monotone_stabilizes_iff_artinian.2 hart
    ⟨fun n ↦ OrderDual.toDual ((J n).map (Ideal.Quotient.mk (maximalIdeal R ^ k))),
      fun a b hab ↦ Ideal.map_mono (hJ hab)⟩
  refine ⟨m, fun m' hm' ↦ ?_⟩
  have h : (J m).map (Ideal.Quotient.mk (maximalIdeal R ^ k)) =
      (J m').map (Ideal.Quotient.mk (maximalIdeal R ^ k)) := hm m' hm'
  have := congrArg (Ideal.comap (Ideal.Quotient.mk (maximalIdeal R ^ k))) h
  simpa [Ideal.comap_map_quotientMk, sup_comm] using this.symm

open IsLocalRing in

theorem exists_le_maximalIdeal_pow_of_iInf_eq_bot [IsNoetherianRing R] [IsLocalRing R]
    [IsPrecomplete (maximalIdeal R) R] (J : ℕ → Ideal R) (hJ : Antitone J) (h0 : ⨅ m, J m = ⊥)
    (k : ℕ) : ∃ m, J m ≤ maximalIdeal R ^ k := by
  set 𝔪 := maximalIdeal R
  choose s hs using exists_sup_maximalIdeal_pow_stable J hJ
  let B : ℕ → Ideal R := fun k ↦ J (s k) ⊔ 𝔪 ^ k
  have hB : ∀ k m, B k ≤ J m ⊔ 𝔪 ^ k := fun k m ↦ by
    rw [show B k = _ from (hs k (max m (s k)) (le_max_right _ _)).symm]
    exact sup_le_sup_right (hJ (le_max_left _ _)) _
  have step : ∀ k, ∀ x ∈ B k, ∃ y ∈ B (k + 1), x - y ∈ 𝔪 ^ k := fun k x hx ↦ by
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hB k (s (k + 1)) hx)
    exact ⟨y, Ideal.mem_sup_left hy, by simpa using hz⟩
  choose! g hg hg' using step
  refine ⟨s k, fun x hx ↦ ?_⟩
  let f : ℕ → R := fun n ↦ Nat.rec x (fun n y ↦ g (k + n) y) n
  have hf : ∀ n, f n ∈ B (k + n) := fun n ↦ by
    induction n with
    | zero => exact Ideal.mem_sup_left hx
    | succ n ih => exact hg _ _ ih
  have hf' : ∀ n d, f n - f (n + d) ∈ 𝔪 ^ (k + n) := fun n d ↦ by
    induction d with
    | zero => simp
    | succ d ih =>
      have h1 : f (n + d) - f (n + d + 1) ∈ 𝔪 ^ (k + n) :=
        Ideal.pow_le_pow_right (by omega) (hg' _ _ (hf (n + d)))
      simpa [add_assoc] using (𝔪 ^ (k + n)).add_mem ih h1
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := 𝔪) f fun {m n} hmn ↦ by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    exact Ideal.pow_le_pow_right (by omega) (hf' m d)
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hL
  have hL0 : L = 0 := by
    rw [← Ideal.mem_bot, ← h0, Submodule.mem_iInf]
    intro m
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Submodule.mem_bot R,
      ← Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := R ⧸ J m) 𝔪
        (maximalIdeal.isMaximal R).ne_top, Submodule.mem_iInf]
    intro n
    obtain ⟨y, hy, z, hz, e⟩ := Submodule.mem_sup.1 (hB (k + n) m (hf n))
    have hz' : z - (f n - L) ∈ 𝔪 ^ n :=
      (𝔪 ^ n).sub_mem (Ideal.pow_le_pow_right (by omega) hz) (hL n)
    have : Ideal.Quotient.mk (J m) L = (z - (f n - L)) • (1 : R ⧸ J m) := by
      rw [← Algebra.algebraMap_eq_smul_one, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq, ← e]
      convert hy using 1
      ring
    rw [this]
    exact Submodule.smul_mem_smul hz' trivial
  have h1 := hf' 0 k
  have h2 := hL k
  rw [hL0, sub_zero] at h2
  have h3 : x - f k ∈ 𝔪 ^ k := by simpa [f] using h1
  simpa using (𝔪 ^ k).add_mem h3 h2

end Symbolic

section Extension

variable {R : Type*} [CommRing R] {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]

variable (v : Valuation R Γ₀) (I : Ideal R) {π : Γ₀}

end Extension

section LocalExtension

open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

section Multiplicative

variable {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]

end Multiplicative

section Additive

variable {Γ : Type*} [LinearOrderedAddCommMonoidWithTop Γ]

end Additive

end LocalExtension

universe u v w

end GlobalTheory
