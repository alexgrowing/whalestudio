import Mathlib

open IsLocalRing

private theorem exists_field_lift {R S F K L : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Field F] [Field K] [Field L] (c : F →+* K) (d : F →+* L) (a : R →+* F) (b : S →+* K)
    (hab : b.comp (algebraMap R S) = c.comp a)
    {ι : Type} (u : ι → S) (f : ι → Polynomial R) (hu : Algebra.adjoin R (Set.range u) = ⊤)
    (hf : ∀ i, (f i).Monic ∧ Polynomial.aeval (u i) (f i) = 0 ∧
      ((f i).map (d.comp a)).Splits) :
    ∃ ψ : S →+* L, ψ.comp (algebraMap R S) = d.comp a ∧
      RingHom.ker ψ = RingHom.ker b := by
  letI : Algebra F K := c.toAlgebra
  letI : Algebra F L := d.toAlgebra
  change b.comp (algebraMap R S) = (algebraMap F K).comp a at hab
  have hab' : ∀ r, b (algebraMap R S r) = algebraMap F K (a r) := fun r => RingHom.congr_fun hab r
  have hT : ∀ s ∈ Set.range (fun i => b (u i)),
      IsIntegral F s ∧ ((minpoly F s).map (algebraMap F L)).Splits := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨h1, h2, h3⟩ := hf i
    have h4 : Polynomial.aeval (b (u i)) ((f i).map a) = 0 := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← hab, ← Polynomial.hom_eval₂,
        ← Polynomial.aeval_def, h2, map_zero]
    refine ⟨⟨_, h1.map a, h4⟩, ?_⟩
    rw [← Polynomial.map_map] at h3
    exact h3.of_dvd ((h1.map a).map _).ne_zero (Polynomial.map_dvd _ (minpoly.dvd F _ h4))
  obtain ⟨φ⟩ := IntermediateField.nonempty_algHom_adjoin_of_splits hT
  have hmem : ∀ s : S, b s ∈ IntermediateField.adjoin F (Set.range (fun i => b (u i))) := by
    intro s
    have hs : s ∈ Algebra.adjoin R (Set.range u) := hu ▸ Algebra.mem_top
    induction hs using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
    | algebraMap r => rw [hab']; exact IntermediateField.algebraMap_mem _ _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz
  let b' : S →+* IntermediateField.adjoin F (Set.range (fun i => b (u i))) :=
    b.codRestrict _ hmem
  refine ⟨φ.toRingHom.comp b', ?_, ?_⟩
  · ext r
    have : b' (algebraMap R S r) = algebraMap F _ (a r) := Subtype.ext (hab' r)
    change φ (b' (algebraMap R S r)) = algebraMap F L (a r)
    rw [this, AlgHom.commutes]
  · ext s
    rw [RingHom.mem_ker, RingHom.mem_ker]
    change φ (b' s) = 0 ↔ _
    rw [map_eq_zero_iff φ φ.toRingHom.injective]
    exact Subtype.ext_iff

theorem UpperTheory.V.AlgebraTools.exists_lift_ker_eq :
    ∀ (R S A : Type) [CommRing R] [CommRing S] [CommRing A] [IsDomain A] [Algebra R S] (x : R →+* A)
      (ι : Type) (u : ι → S) (f : ι → Polynomial R), Algebra.adjoin R (Set.range u) = ⊤ →
      (∀ i, (f i).Monic ∧ Polynomial.aeval (u i) (f i) = 0 ∧ ((f i).map x).Splits) →
      ∀ P : Ideal S, P.IsPrime → P.comap (algebraMap R S) = RingHom.ker x →
      ∃ x' : S →+* A, x'.comp (algebraMap R S) = x ∧ RingHom.ker x' = P := by
  intro R S A _ _ _ _ _ x ι u f hu hf P hP hPx
  haveI : (RingHom.ker x).IsPrime := RingHom.ker_isPrime x
  let j : A →+* FractionRing A := algebraMap A (FractionRing A)
  have hj : Function.Injective j := IsFractionRing.injective A (FractionRing A)
  let b : S →+* FractionRing (S ⧸ P) :=
    (algebraMap (S ⧸ P) (FractionRing (S ⧸ P))).comp (Ideal.Quotient.mk P)
  have hb : RingHom.ker b = P := by
    ext s
    rw [RingHom.mem_ker]
    change algebraMap (S ⧸ P) (FractionRing (S ⧸ P)) (Ideal.Quotient.mk P s) = 0 ↔ _
    rw [map_eq_zero_iff _ (IsFractionRing.injective (S ⧸ P) (FractionRing (S ⧸ P))),
      Ideal.Quotient.eq_zero_iff_mem]
  have hkb : RingHom.ker (b.comp (algebraMap R S)) = RingHom.ker x := by
    rw [← RingHom.comap_ker, hb, hPx]
  have hkj : RingHom.ker (j.comp x) = RingHom.ker x := by
    rw [← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot j).1 hj]
    rfl
  let g₁ : R ⧸ RingHom.ker x →+* FractionRing (S ⧸ P) :=
    Ideal.Quotient.lift _ (b.comp (algebraMap R S)) (fun r hr => by
      rw [← hkb] at hr; exact hr)
  let g₂ : R ⧸ RingHom.ker x →+* FractionRing A :=
    Ideal.Quotient.lift _ (j.comp x) (fun r hr => by rw [← hkj] at hr; exact hr)
  have hg₁ : Function.Injective g₁ := RingHom.lift_injective_of_ker_le_ideal _ _ hkb.le
  have hg₂ : Function.Injective g₂ := RingHom.lift_injective_of_ker_le_ideal _ _ hkj.le
  let F := FractionRing (R ⧸ RingHom.ker x)
  let a : R →+* F := (algebraMap (R ⧸ RingHom.ker x) F).comp (Ideal.Quotient.mk _)
  obtain ⟨c, h1⟩ : ∃ c : F →+* FractionRing (S ⧸ P), b.comp (algebraMap R S) = c.comp a :=
    ⟨IsFractionRing.lift hg₁, RingHom.ext fun r =>
      ((IsFractionRing.lift_algebraMap (K := F) hg₁ (Ideal.Quotient.mk _ r)).trans
        (Ideal.Quotient.lift_mk _ _ _)).symm⟩
  obtain ⟨d, h2⟩ : ∃ d : F →+* FractionRing A, d.comp a = j.comp x :=
    ⟨IsFractionRing.lift hg₂, RingHom.ext fun r =>
      ((IsFractionRing.lift_algebraMap (K := F) hg₂ (Ideal.Quotient.mk _ r)).trans
        (Ideal.Quotient.lift_mk _ _ _))⟩
  obtain ⟨ψ, hψ1, hψ2⟩ := exists_field_lift c d a b h1 u f hu (fun i =>
    ⟨(hf i).1, (hf i).2.1, by rw [h2, ← Polynomial.map_map]; exact (hf i).2.2.map j⟩)
  rw [h2] at hψ1
  rw [hb] at hψ2
  have hmem : ∀ s : S, ψ s ∈ j.range := by
    intro s
    have hs : s ∈ Algebra.adjoin R (Set.range u) := hu ▸ Algebra.mem_top
    induction hs using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      obtain ⟨hm, h0, hsp⟩ := hf i
      have h4 : Polynomial.eval₂ j (ψ (u i)) ((f i).map x) = 0 := by
        rw [Polynomial.eval₂_map, ← hψ1, ← Polynomial.hom_eval₂,
          ← Polynomial.aeval_def, h0, map_zero]
      rw [hsp.eq_prod_roots_of_monic (hm.map x), Polynomial.eval₂_multiset_prod,
        Multiset.prod_eq_zero_iff, Multiset.map_map, Multiset.mem_map] at h4
      obtain ⟨c, -, hc⟩ := h4
      refine ⟨c, ?_⟩
      simp only [Function.comp_apply, Polynomial.eval₂_sub, Polynomial.eval₂_X,
        Polynomial.eval₂_C] at hc
      exact (sub_eq_zero.1 hc).symm
    | algebraMap r => exact ⟨x r, (RingHom.congr_fun hψ1 r).symm⟩
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz
  choose g hg using hmem
  let x' : S →+* A :=
    { toFun := g
      map_one' := hj (by rw [hg, map_one, map_one])
      map_mul' := fun s t => hj (by rw [map_mul, hg, hg, hg, map_mul])
      map_zero' := hj (by rw [hg, map_zero, map_zero])
      map_add' := fun s t => hj (by rw [map_add, hg, hg, hg, map_add]) }
  refine ⟨x', ?_, ?_⟩
  · ext r
    exact hj ((hg _).trans (RingHom.congr_fun hψ1 r))
  · ext s
    rw [← hψ2, RingHom.mem_ker, RingHom.mem_ker, ← hg, map_eq_zero_iff j hj]
    rfl
