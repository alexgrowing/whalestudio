import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.FiniteAlgIdem

open Polynomial

theorem isCoprime_multiset_prod_left {R : Type} [CommRing R] (s : Multiset R) (y : R)
    (h : ∀ x ∈ s, IsCoprime x y) : IsCoprime s.prod y := by
  induction s using Multiset.induction_on with
  | empty => exact isCoprime_one_left
  | cons a s ih =>
    rw [Multiset.prod_cons]
    exact (h a (Multiset.mem_cons_self a s)).mul_left
      (ih fun x hx => h x (Multiset.mem_cons_of_mem hx))

theorem monic_eq_prod_X_sub_C {L : Type} [Field L] [IsAlgClosed L] {v : Valuation L NNReal}
    {O : Type} [CommRing O] [Algebra O L] (hv : v.Integers O) (f : O[X]) (hf : f.Monic) :
    ∃ r : Multiset O, f = (r.map fun x => X - C x).prod := by
  classical
  have hinj : Function.Injective (algebraMap O L) := hv.hom_inj
  have hs : (f.map (algebraMap O L)).Splits := IsAlgClosed.splits _
  have hm : (f.map (algebraMap O L)).Monic := hf.map _
  have hroot : ∀ x ∈ (f.map (algebraMap O L)).roots, ∃ y, algebraMap O L y = x := by
    intro x hx
    have hint : IsIntegral O x := ⟨f, hf, by
      rw [← Polynomial.eval_map]
      exact (Polynomial.mem_roots hm.ne_zero).1 hx⟩
    exact hv.exists_of_le_one ((Valuation.mem_integer_iff _ _).1 (hv.mem_of_integral hint))
  refine ⟨(f.map (algebraMap O L)).roots.map (Function.invFun (algebraMap O L)), ?_⟩
  apply Polynomial.map_injective _ hinj
  conv_lhs => rw [hs.eq_prod_roots_of_monic hm]
  rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro x hx
  simp [Function.invFun_eq (hroot x hx)]

theorem exists_prod_sub_eq_zero {L : Type} [Field L] [IsAlgClosed L] {v : Valuation L NNReal}
    {O : Type} [CommRing O] [Algebra O L] (hv : v.Integers O) {A : Type} [CommRing A]
    [Algebra O A] [Algebra.IsIntegral O A] (a : A) :
    ∃ r : Multiset O, (r.map fun x => a - algebraMap O A x).prod = 0 := by
  obtain ⟨f, hf, hfa⟩ := Algebra.IsIntegral.isIntegral (R := O) a
  obtain ⟨r, hr⟩ := monic_eq_prod_X_sub_C hv f hf
  refine ⟨r, ?_⟩
  have h : aeval a f = 0 := hfa
  rw [hr, map_multiset_prod, Multiset.map_map] at h
  simpa [Function.comp_def] using h

theorem exists_mem_eq {O : Type} [CommRing O] {A K : Type} [CommRing A] [Algebra O A]
    [CommRing K] [IsDomain K] [Algebra O K] (c : A →ₐ[O] K) {a : A} {r : Multiset O}
    (hr : (r.map fun x => a - algebraMap O A x).prod = 0) :
    ∃ x ∈ r, c a = algebraMap O K x := by
  have h := congrArg c hr
  rw [map_multiset_prod, Multiset.map_map, map_zero, Multiset.prod_eq_zero_iff] at h
  obtain ⟨x, hx, hx0⟩ := Multiset.mem_map.1 h
  refine ⟨x, hx, ?_⟩
  simp only [Function.comp_apply, map_sub, AlgHom.commutes] at hx0
  exact sub_eq_zero.1 hx0

open Classical in

theorem exists_idempotent {O : Type} [CommRing O] [IsLocalRing O] {A : Type} [CommRing A]
    [Algebra O A] {a : A} {r : Multiset O} (hr : (r.map fun x => a - algebraMap O A x).prod = 0)
    (ρ : IsLocalRing.ResidueField O) :
    ∃ e : A, IsIdempotentElem e ∧ ∀ c : A →ₐ[O] IsLocalRing.ResidueField O,
      c e = if c a = ρ then 1 else 0 := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : O[X],
      g = ((r.filter fun x => IsLocalRing.residue O x = ρ).map fun x => X - C x).prod := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : O[X],
      h = ((r.filter fun x => ¬ IsLocalRing.residue O x = ρ).map fun x => X - C x).prod :=
    ⟨_, rfl⟩
  have hgh : g * h = (r.map fun x => X - C x).prod := by
    rw [hg, hh, ← Multiset.prod_add, ← Multiset.map_add, Multiset.filter_add_not]
  have hcop : IsCoprime g h := by
    rw [hg]
    apply isCoprime_multiset_prod_left
    intro p hp
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hp
    rw [hh]
    apply IsCoprime.symm
    apply isCoprime_multiset_prod_left
    intro q hq
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hq
    apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).1
    rw [map_sub, (Multiset.mem_filter.1 hx).2, sub_ne_zero]
    exact (Multiset.mem_filter.1 hy).2
  obtain ⟨u, w, huw⟩ := hcop
  have hF : aeval a (g * h) = 0 := by
    rw [hgh, map_multiset_prod, Multiset.map_map]
    simpa [Function.comp_def] using hr
  refine ⟨aeval a (w * h), ?_, ?_⟩
  · have key : w * h * (w * h) = w * h - u * w * (g * h) := by
      linear_combination (w * h) * huw
    show aeval a (w * h) * aeval a (w * h) = aeval a (w * h)
    rw [← map_mul, key, map_sub, map_mul (aeval a) (u * w), hF, mul_zero, sub_zero]
  · intro c
    rw [← Polynomial.aeval_algHom_apply]
    obtain ⟨x, hx, hcx⟩ := exists_mem_eq c hr
    rw [IsLocalRing.ResidueField.algebraMap_eq] at hcx
    have h1 := congrArg (aeval (c a)) huw
    rw [map_add, map_mul, map_mul, map_one] at h1
    by_cases hρ : IsLocalRing.residue O x = ρ
    · have hg0 : aeval (c a) g = 0 := by
        rw [hg, map_multiset_prod, Multiset.map_map]
        apply Multiset.prod_eq_zero
        refine Multiset.mem_map.2 ⟨x, Multiset.mem_filter.2 ⟨hx, hρ⟩, ?_⟩
        simp [hcx]
      rw [if_pos (hcx.trans hρ), map_mul]
      rw [hg0, mul_zero, zero_add] at h1
      exact h1
    · have hh0 : aeval (c a) h = 0 := by
        rw [hh, map_multiset_prod, Multiset.map_map]
        apply Multiset.prod_eq_zero
        refine Multiset.mem_map.2 ⟨x, Multiset.mem_filter.2 ⟨hx, hρ⟩, ?_⟩
        simp [hcx]
      rw [if_neg (show ¬ c a = ρ by rwa [hcx]), map_mul, hh0, mul_zero]

end GlobalTheory.FiniteAlgIdem

namespace GlobalTheory.FiniteAlgIdem

theorem idempotent_eq_zero {L : Type} [Field L] [IsAlgClosed L] {v : Valuation L NNReal}
    {O : Type} [CommRing O] [Algebra O L] [IsLocalRing O] (hv : v.Integers O) {A : Type}
    [CommRing A] [Algebra O A] [Algebra.IsIntegral O A] {s : A} (hs : IsIdempotentElem s)
    (h : ∀ c : A →ₐ[O] IsLocalRing.ResidueField O, c s = 0) : s = 0 := by
  by_contra hne
  have hI : Ideal.span {1 - s} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    apply hne
    have h0 : (1 - s) * s = 0 := by rw [sub_mul, one_mul, hs.eq, sub_self]
    exact hu.mul_right_eq_zero.1 h0
  obtain ⟨M, hM, hsM⟩ := Ideal.exists_le_maximal _ hI
  let ψ : O →ₐ[O] A ⧸ M := Algebra.ofId O (A ⧸ M)
  have hψ : Function.Surjective ψ := by
    intro b
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨r, hr⟩ := exists_prod_sub_eq_zero hv b
    obtain ⟨x, -, hbx⟩ := exists_mem_eq (Ideal.Quotient.mkₐ O M) hr
    exact ⟨x, by rw [Algebra.ofId_apply, ← hbx]; rfl⟩
  have hker : ∀ y ∈ RingHom.ker ψ, (Algebra.ofId O (IsLocalRing.ResidueField O)) y = 0 := by
    intro y hy
    have hne : RingHom.ker ψ ≠ ⊤ := by
      rw [Ne, Ideal.eq_top_iff_one, RingHom.mem_ker, map_one]
      exact one_ne_zero
    rw [Algebra.ofId_apply, IsLocalRing.ResidueField.algebraMap_eq,
      IsLocalRing.residue_eq_zero_iff]
    exact IsLocalRing.le_maximalIdeal hne hy
  let c : A →ₐ[O] IsLocalRing.ResidueField O :=
    (Ideal.Quotient.liftₐ (RingHom.ker ψ) (Algebra.ofId O _) hker).comp
      ((Ideal.quotientKerAlgEquivOfSurjective hψ).symm.toAlgHom.comp (Ideal.Quotient.mkₐ O M))
  have hm : Ideal.Quotient.mkₐ O M (1 - s) = 0 := by
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hsM (Ideal.mem_span_singleton_self _)
  have h1 : c (1 - s) = 0 := by
    simp only [c, AlgHom.comp_apply, hm, map_zero]
  rw [map_sub, map_one, h c, sub_zero] at h1
  exact one_ne_zero h1

theorem finite_and_idempotents {L : Type} [Field L] [IsAlgClosed L] {v : Valuation L NNReal}
    {O : Type} [CommRing O] [Algebra O L] [IsLocalRing O] (hv : v.Integers O) (A : Type)
    [CommRing A] [Algebra O A] [Module.Finite O A] :
    Finite (A →ₐ[O] IsLocalRing.ResidueField O) ∧
      ∃ e : (A →ₐ[O] IsLocalRing.ResidueField O) → A, (∀ c, IsIdempotentElem (e c)) ∧
        (∀ c c', c ≠ c' → e c * e c' = 0) ∧ (∑ᶠ c, e c) = 1 ∧
        ∀ c c' : A →ₐ[O] IsLocalRing.ResidueField O, c' (e c) = 1 ↔ c = c' := by
  classical
  haveI : Algebra.IsIntegral O A := Algebra.IsIntegral.of_finite O A
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := O) (M := A)
  choose r hr using fun a : A => exists_prod_sub_eq_zero hv a
  choose E hEi hEc using fun (a : A) (ρ : IsLocalRing.ResidueField O) =>
    exists_idempotent (hr a) ρ
  have hsep : ∀ c c' : A →ₐ[O] IsLocalRing.ResidueField O,
      (∀ j ∈ S, c' j = c j) → c' = c := by
    intro c c' hcc
    apply AlgHom.toLinearMap_injective
    exact LinearMap.ext_on hS fun x hx => hcc x hx
  let e : (A →ₐ[O] IsLocalRing.ResidueField O) → A := fun c => ∏ j ∈ S, E j (c j)
  have hec : ∀ c c' : A →ₐ[O] IsLocalRing.ResidueField O,
      c' (e c) = if c = c' then 1 else 0 := by
    intro c c'
    simp only [e, map_prod, hEc]
    by_cases hcc : c = c'
    · subst hcc
      rw [if_pos rfl, Finset.prod_boole, if_pos (fun j _ => rfl)]
    · rw [if_neg hcc, Finset.prod_boole, if_neg (fun hh => hcc (hsep c c' hh).symm)]
  have hei : ∀ c, IsIdempotentElem (e c) := fun c =>
    Finset.prod_induction _ IsIdempotentElem (fun _ _ ha hb => ha.mul hb)
      IsIdempotentElem.one (fun j _ => hEi _ _)
  have hort : ∀ c c', c ≠ c' → e c * e c' = 0 := by
    intro c c' hne
    apply idempotent_eq_zero hv ((hei c).mul (hei c'))
    intro c''
    rw [map_mul, hec, hec]
    split_ifs with h1 h2 <;> simp_all
  have hfin : Finite (A →ₐ[O] IsLocalRing.ResidueField O) := by
    let T : S → Finset (IsLocalRing.ResidueField O) := fun j =>
      ((r j).map (algebraMap O (IsLocalRing.ResidueField O))).toFinset
    let F : (A →ₐ[O] IsLocalRing.ResidueField O) → (∀ j : S, T j) := fun c j =>
      ⟨c j, by
        obtain ⟨x, hx, hcx⟩ := exists_mem_eq c (hr j)
        simp only [T, Multiset.mem_toFinset, Multiset.mem_map]
        exact ⟨x, hx, hcx.symm⟩⟩
    refine Finite.of_injective F ?_
    intro c c' hcc
    exact hsep c' c fun j hj => congrArg Subtype.val (congrFun hcc ⟨j, hj⟩)
  refine ⟨hfin, e, hei, hort, ?_, ?_⟩
  · haveI := hfin
    letI := Fintype.ofFinite (A →ₐ[O] IsLocalRing.ResidueField O)
    rw [finsum_eq_sum_of_fintype]
    have horth : OrthogonalIdempotents e := ⟨hei, fun c c' h => hort c c' h⟩
    have hsum := horth.isIdempotentElem_sum (s := Finset.univ)
    have h0 := idempotent_eq_zero hv hsum.one_sub (fun c'' => by
      rw [map_sub, map_one, map_sum]
      simp [hec])
    exact (sub_eq_zero.1 h0).symm
  · intro c c'
    rw [hec]
    split_ifs with h <;> simp [h]

end GlobalTheory.FiniteAlgIdem

theorem GlobalTheory.FiniteAlgIdem.idempotents_at_residue_points :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O →
    ∀ (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A],
    Finite (A →ₐ[O] IsLocalRing.ResidueField O) ∧
    ∃ e : (A →ₐ[O] IsLocalRing.ResidueField O) → A, (∀ c, IsIdempotentElem (e c)) ∧
    (∀ c c', c ≠ c' → e c * e c' = 0) ∧ (∑ᶠ c, e c) = 1 ∧
    ∀ c c' : A →ₐ[O] IsLocalRing.ResidueField O, c' (e c) = 1 ↔ c = c' := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ hv A _ _ _
  exact GlobalTheory.FiniteAlgIdem.finite_and_idempotents hv A
