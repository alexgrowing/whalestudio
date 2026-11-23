import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.LiftSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.TpSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DTrCoeff
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
open IsLocalRing Filter UpperTheory.V UpperTheory.V.Th UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev

private theorem cnt (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    (c : O) (hc : c ≠ 0) (D0 C : ℕ) : ∃ m : ℕ, ∀ (ι : Type) [Fintype ι] (Y : Type) [AddCommGroup Y] [Module O Y]
      (Φ : (ι → O) →ₗ[O] Y) (S : Set Y), Fintype.card ι = D0 + 1 →
      (∀ t, Φ t = 0 → ∀ a, c * t a ∈ maximalIdeal O ^ m) → (∀ t, Φ t ∈ S) → S.Finite →
      ¬ S.ncard ≤ Nat.card (ResidueField O) ^ (m * D0 + C) := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨v, e, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  refine ⟨v + (v * D0 + C + 1), fun ι _ Y _ _ Φ S hι hker hS hfin hle => ?_⟩
  set k := v * D0 + C + 1 with hk
  have hcard : Nat.card (O ⧸ maximalIdeal O ^ k) = Nat.card (ResidueField O) ^ k :=
    cardQuot_pow_of_prime (IsDiscreteValuationRing.not_a_field O)
  choose s hs using Ideal.Quotient.mk_surjective (I := maximalIdeal O ^ k)
  let f : (ι → O ⧸ maximalIdeal O ^ k) → S := fun t => ⟨Φ fun a => s (t a), hS _⟩
  have hf : Function.Injective f := fun t t' h => by
    have h1 : Φ ((fun a => s (t a)) - fun a => s (t' a)) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact congrArg Subtype.val h
    funext a
    have h2 := hker _ h1 a
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton, pow_add, mul_assoc,
      Units.dvd_mul_left, mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero)] at h2
    rw [← hs (t a), ← hs (t' a), Ideal.Quotient.eq, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    exact h2
  haveI := hfin.to_subtype
  have h3 := (Nat.card_le_card_of_injective f hf).trans (le_of_eq_of_le (Nat.card_coe_set_eq S) hle)
  rw [Nat.card_fun, hcard, Nat.card_eq_fintype_card (α := ι), hι, ← pow_mul,
    Nat.pow_le_pow_iff_right Finite.one_lt_card] at h3
  nlinarith

section Tr

variable {n : ℕ} {R G : Type} [CommRing R] [Group G]

private theorem tr_lin (D : GDet n R G) (hn : 1 ≤ n) : ∃ t : MonoidAlgebra R G →ₗ[R] R, ∀ z, D.tr z = t z := by
  obtain ⟨t, ht⟩ := (UpperTheory.V.CA.d_tr D.toDet).1 hn
  exact ⟨t, fun z => ((UpperTheory.V.CA.d_toDet D z).2.2.1.symm.trans (ht z).symm)⟩

private theorem comap_tr {H : Type} [Group H] (D : GDet n R H) (φ : G →* H)
    (z : MonoidAlgebra R G) : (D.comap φ).tr z = D.tr (MonoidAlgebra.mapDomainRingHom R φ z) := by
  have hc : (D.comap φ).chi z = D.chi (MonoidAlgebra.mapDomainRingHom R φ z) := by
    change D.D _ (MonoidAlgebra.mapDomainRingHom (Polynomial R) φ _) = D.D _ _
    congr 1
    rw [map_sub]
    congr 1
    · simp
    · induction z using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | single g r => simp
  simp only [GDet.tr, GDet.lam, hc]

private theorem map_tr {S : Type} [CommRing S] (D : GDet n R G) (f : R →+* S) (z : MonoidAlgebra R G) :
    f (D.tr z) = (D.map f).tr (MonoidAlgebra.mapRingHom G f z) :=
  (((UpperTheory.V.CA.d_gmap D).2.2.1 f z).2 1).symm

private theorem ofRep_comap' {H : Type} [Group H] (ρ : G →* Matrix (Fin n) (Fin n) R) (φ : H →* G) :
    (GDet.ofRep ρ).comap φ = GDet.ofRep (ρ.comp φ) := by
  ext B _ _ z
  change (GDet.repAlg ρ B (MonoidAlgebra.mapDomainRingHom B φ z)).det = (GDet.repAlg (ρ.comp φ) B z).det
  congr 1
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single g r => simp [GDet.repAlg]

private theorem mapRingHom_single_mul_partial_charpoly {S : Type} [CommRing S] (f : R →+* S) (E : ℕ) (ph ta : G) (u : Fin n → R) (i : Fin n) :
    MonoidAlgebra.mapRingHom G f (twoPowerModulus E ph ta u i 0) = twoPowerModulus E ph ta (fun k => f (u k)) i 0 := by
  have hs : ∀ (g : G) (c : R), MonoidAlgebra.mapRingHom G f (MonoidAlgebra.single g c) =
      MonoidAlgebra.single g (f c) := fun g c => by simp
  simp only [twoPowerModulus, map_mul, map_pow, map_sub, map_one, map_list_prod, List.map_ofFn, hs, map_zero]
  congr 4
  funext k
  by_cases hk : k = i
  · simp only [Function.comp_apply, if_pos hk, map_one]
  · simp only [Function.comp_apply, if_neg hk, map_sub, hs, map_one]

private theorem mapDomain_partial_charpoly_power_zero {H : Type} [Group H] (φ : G →* H) (E : ℕ) (ph ta : G) (u : Fin n → R) (i : Fin n)
    (h : φ ta = 1) : MonoidAlgebra.mapDomainRingHom R φ (twoPowerModulus E ph ta u i 0) = 0 := by
  have hs : MonoidAlgebra.mapDomainRingHom R φ (MonoidAlgebra.single ta 1) = 1 := by
    simp [h, MonoidAlgebra.one_def]
  simp only [twoPowerModulus, map_mul, map_sub, map_one, hs, MonoidAlgebra.single_zero, map_zero, sub_self, mul_zero]

private theorem kill_tr {O X : Type} [CommRing O] [Algebra O R] [AddCommGroup X] [Module O X] (D : GDet n R G)
    (hn : 1 ≤ n) (δ : R →ₗ[O] X) (h : ∀ g, δ (D.tr (MonoidAlgebra.single g 1)) = 0) (z : MonoidAlgebra O G) :
    δ (D.tr (MonoidAlgebra.mapRingHom G (algebraMap O R) z)) = 0 := by
  obtain ⟨t, ht⟩ := tr_lin D hn
  simp only [ht] at h ⊢
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb, add_zero]
  | single g a =>
    have : MonoidAlgebra.mapRingHom G (algebraMap O R) (MonoidAlgebra.single g a) =
        algebraMap O R a • MonoidAlgebra.single g (1 : R) := by
      rw [MonoidAlgebra.mapRingHom_single, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rw [this, map_smul, algebraMap_smul, map_smul, h, smul_zero]

end Tr

section Der

variable {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup X] [Module O X] {x : R →ₐ[O] O}

private theorem der_one {δ : R →ₗ[O] X} (h : IsDer x δ) : δ 1 = 0 := by
  have := h 1 1
  simpa using this

private theorem der_sum {ι : Type} [Fintype ι] (d : ι → R →ₗ[O] X) (h : ∀ a, IsDer x (d a)) (t : ι → O) :
    IsDer x (∑ a, t a • d a) := fun a b => by
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, h _ a b, smul_add, Finset.sum_add_distrib, Finset.smul_sum,
    smul_smul, mul_comm]

private theorem der_smul {δ : R →ₗ[O] X} (h : IsDer x δ) (c : O) : IsDer x (c • δ) := fun a b => by
  simp only [LinearMap.smul_apply, h a b, smul_add, smul_smul, mul_comm]

private theorem der_wt {δ : R →ₗ[O] X} (h : IsDer x δ) (c : O) (a : R) : δ (algebraMap O R c * a - 1) = c • δ a := by
  rw [map_sub, der_one h, sub_zero, ← Algebra.smul_def, map_smul]

end Der

theorem UpperTheory.V.Th.count :
    Count := by
  intro l _ L G0 T n O _ _ _ _ _ r B _ _ _ u J D b y x al hl hn had ⟨E, hA⟩ hgen hu hJ hEt hPL hEig ⟨C, hB⟩ δ0 hδ0 hw g0
  classical
  by_contra hd
  haveI : Finite (ResidueField O) := IsCoef.finite
  choose A hA using hA
  obtain ⟨c1, hc1, h1⟩ := coc l L G0 n O y hl hn
  obtain ⟨c2, hc2, h2⟩ := trPsi l L G0 n O y hn
  obtain ⟨c3, hc3, h3⟩ := split l L G0 T n O r B u J D b y x al E hn hgen hu hJ hEt hPL hEig
  set d := δ0 (u.D.tr (MonoidAlgebra.single g0 1)) with hdd
  obtain ⟨m, hm⟩ := cnt O (c1 * c2 * c3 * d) (mul_ne_zero (mul_ne_zero (mul_ne_zero hc1 hc2) hc3) hd) (D + n * T.q) C
  obtain ⟨N, ⟨hfin, hle⟩, h3N⟩ := ((hB m).and (h3 m)).exists
  obtain ⟨α, hα⟩ := h3N (A N) (hA N)
  clear hA
  generalize A N = A at hα
  choose δ hδ hδw hδq using hα
  have hIp : ∀ w, A.rN.Ip w = (T.GN N).frame.Iu w := fun w => by
    refine inf_eq_left.2 (le_iInf fun i => ?_)
    rintro _ ⟨g, hg, rfl⟩
    have e : (T.h N).p₀ ((T.GN N).φu w g) = G0.φu w g := Subtype.ext ((T.h N).φu w g)
    have hm : G0.φu w g ∈ r.Ip w := by
      rw [had.2 w]
      exact ⟨g, hg, rfl⟩
    rw [MonoidHom.mem_ker, A.compat.1 i, MonoidHom.comp_apply, e]
    exact (Subgroup.mem_iInf.1 hm.2) i
  have hmaps : A.p.Maps (x.comp A.β).toRingHom (GDet.ofRep (mat (y.ρ.comp (T.h N).p₀))) y.ψ := by
    refine ⟨?_, fun v i => ?_⟩
    · have e1 : A.p.D.map (x.comp A.β).toRingHom = (A.p.D.map A.β.toRingHom).map x.toRingHom := rfl
      have e2 : (u.D.comap (T.h N).p₀).map x.toRingHom = (u.D.map x.toRingHom).comap (T.h N).p₀ := rfl
      rw [e1, A.β_pair.1, e2, hu.1, ofRep_comap']
      rfl
    · rw [← hu.2 v i, ← A.β_pair.2 v i]
      rfl
  have hβtr : ∀ z, A.β (A.p.D.tr z) =
      u.D.tr (MonoidAlgebra.mapDomainRingHom B (T.h N).p₀ (MonoidAlgebra.mapRingHom _ A.β.toRingHom z)) := fun z => by
    rw [← comap_tr, ← A.β_pair.1]
    exact map_tr A.p.D A.β.toRingHom z
  let δs : A.R →ₗ[O] Om O m := Algebra.linearMap O (Om O m) ∘ₗ δ0 ∘ₗ A.β.toLinearMap
  have hδs_apply : ∀ a, δs a = algebraMap O (Om O m) (δ0 (A.β a)) := fun _ => rfl
  have hδs : IsDer (x.comp A.β) δs := fun a a' => by
    simp only [hδs_apply, map_mul, hδ0 _ _, map_add, smul_eq_mul, AlgHom.comp_apply, Algebra.smul_def]
  let ι := Option (Fin D ⊕ Fin T.q × Fin n)
  let e : ι → A.R →ₗ[O] Om O m := fun a => a.elim δs δ
  have he : ∀ a, IsDer (x.comp A.β) (e a) := fun a => by
    cases a
    · exact hδs
    · exact hδ _
  let Φ : (ι → O) →ₗ[O] ((T.GN N).G₀ → Om O m) :=
    Fintype.linearCombination O fun a g => c1 • e a (A.p.D.tr (MonoidAlgebra.single g 1))
  have hΦ : ∀ t g, Φ t g = c1 • (∑ a, t a • e a) (A.p.D.tr (MonoidAlgebra.single g 1)) := fun t g => by
    simp only [Φ, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, Finset.smul_sum, smul_comm c1]
  have hev : ∀ (t : ι → O) z, (∑ a, t a • e a) z = t none • δs z + ∑ a, t (some a) • δ a z := fun t z => by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    exact Fintype.sum_option _
  have hmem : ∀ a : O, a • (1 : Om O m) = 0 ↔ a ∈ maximalIdeal O ^ m := fun a => by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact Ideal.Quotient.eq_zero_iff_mem
  refine hm ι _ Φ _ (by simp [ι, mul_comm]) (fun t ht => ?_) (fun t => ?_) hfin hle
  swap
  · obtain ⟨z, hz, hz'⟩ := h1 _ (T.h N) A.rN A.R A.p _ hIp hmaps m _ (der_sum e he t)
    exact ⟨z, hz, funext fun g => (hz' g).trans (hΦ t g).symm⟩
  have hk : ∀ g, (c1 • ∑ a, t a • e a) (A.p.D.tr (MonoidAlgebra.single g 1)) = 0 := fun g =>
    (hΦ t g).symm.trans (congrFun ht g)
  have hder := der_smul (der_sum e he t) c1
  have hsome : ∀ a, (c1 * c2 * c3 * t (some a)) • (1 : Om O m) = 0 := by
    rintro (k | ⟨j, i⟩)
    · have k1 := h2 _ (T.h N) A.rN A.R A.p _ hmaps _ _ hder hk (b.wt.v k) (b.wt.i k) (b.wt.γ k)
      have k2 : c2 • (c1 • ∑ a, t a • e a) (algebraMap (abelian₂ O Empty D) A.R (MvPowerSeries.X (.inr k))) = 0 := by
        rw [A.segmentWeightExponent, der_wt hder, smul_comm, k1, smul_zero]
      have k3 : δs (algebraMap (abelian₂ O Empty D) A.R (MvPowerSeries.X (.inr k))) = 0 := by
        have k4 : A.β (A.p.ψ (b.wt.v k) (b.wt.i k) (b.wt.γ k) : A.Rˣ) = (u.ψ (b.wt.v k) (b.wt.i k) (b.wt.γ k) : Bˣ) := by
          rw [← A.β_pair.2]
          rfl
        rw [A.segmentWeightExponent, der_wt hδs, hδs_apply, k4, hw, map_zero, smul_zero]
      rw [LinearMap.smul_apply, hev, k3] at k2
      simp only [hδw, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, zero_add] at k2
      simp only [Algebra.algebraMap_eq_smul_one, smul_smul] at k2
      rw [← k2]
      congr 1
      ring
    · have k1 := kill_tr A.p.D hn _ hk (twoPowerModulus E (T.ph N j) (T.ta N j) (α j) i 0)
      rw [mapRingHom_single_mul_partial_charpoly] at k1
      have k3 : δs (A.p.D.tr (twoPowerModulus E (T.ph N j) (T.ta N j) (fun k => algebraMap O A.R (α j k)) i 0)) = 0 := by
        obtain ⟨τ, hτ⟩ := tr_lin u.D hn
        rw [hδs_apply, hβtr, mapRingHom_single_mul_partial_charpoly, mapDomain_partial_charpoly_power_zero _ _ _ _ _ _ (Subtype.ext (T.ta_ker N j)), hτ, map_zero, map_zero, map_zero]
      rw [LinearMap.smul_apply, hev, k3] at k1
      simp only [hδq, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, zero_add] at k1
      simp only [Algebra.algebraMap_eq_smul_one, smul_smul] at k1
      have : c1 * c2 * c3 * t (some (.inr (j, i))) = c2 * (c1 * (t (some (.inr (j, i))) * c3)) := by ring
      rw [this, mul_smul, k1, smul_zero]
  rintro (_ | a)
  · obtain ⟨g', hg'⟩ := (T.h N).surj g0
    have hη : g' ∈ (T.GN N).η.ker := by
      rw [MonoidHom.mem_ker, ← (T.h N).η, hg']
      exact g0.2
    have e0 : (T.h N).p₀ ⟨g', hη⟩ = g0 := Subtype.ext hg'
    have k1 := hk ⟨g', hη⟩
    have k3 : δs (A.p.D.tr (MonoidAlgebra.single ⟨g', hη⟩ 1)) = d • (1 : Om O m) := by
      rw [hδs_apply, hβtr, MonoidAlgebra.mapRingHom_single, map_one, MonoidAlgebra.mapDomainRingHom_apply,
        MonoidAlgebra.mapDomain_single, e0, Algebra.algebraMap_eq_smul_one]
    rw [LinearMap.smul_apply, hev, k3] at k1
    have k4 := congrArg (fun w => (c2 * c3) • w) k1
    have k5 : ∀ a (w : Om O m), (c2 * c3) • c1 • t (some a) • w = 0 := fun a w => by
      have : (c2 * c3) • c1 • t (some a) • w = ((c1 * c2 * c3 * t (some a)) • (1 : Om O m)) * w := by
        rw [smul_mul_assoc, one_mul, smul_smul, smul_smul]
        congr 1
        ring
      rw [this, hsome, zero_mul]
    simp only [smul_add, Finset.smul_sum, k5, Finset.sum_const_zero, add_zero, smul_zero] at k4
    rw [← hmem, ← k4]
    simp only [smul_smul]
    congr 1
    ring
  · rw [← hmem]
    have : c1 * c2 * c3 * d * t (some a) = d * (c1 * c2 * c3 * t (some a)) := by ring
    rw [this, mul_smul, hsome, smul_zero]
