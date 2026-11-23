import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Torsor
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
import Development.AutomorphicArithmetic.Foundations.SubgroupJ.SubJ
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsGenLev
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.UPel.HT.EtLev GlobalTheory.crystallineComparison UpperTheory.SubgroupJ UpperTheory.D3

private theorem eq_zero_or_of_mul_eq_zero_of_add_reg {A : Type} [CommRing A] [IsLocalRing A] [IsIntegrallyClosed A]
    {a b : A} (hab : a * b = 0) (hreg : a + b ∈ nonZeroDivisors A) : a = 0 ∨ b = 0 := by
  let F := FractionRing A
  have hinj : Function.Injective (algebraMap A F) := IsLocalization.injective F le_rfl
  let e : F := IsLocalization.mk' F a (⟨a + b, hreg⟩ : nonZeroDivisors A)
  have hu : IsUnit (algebraMap A F (a + b)) := IsLocalization.map_units F (⟨a + b, hreg⟩ : nonZeroDivisors A)
  have he : e * algebraMap A F (a + b) = algebraMap A F a := IsLocalization.mk'_spec F a ⟨a + b, hreg⟩
  have hidem : e * e = e := by
    apply hu.mul_right_cancel
    apply hu.mul_right_cancel
    have h2 : algebraMap A F a * algebraMap A F (a + b) = algebraMap A F a * algebraMap A F a := by
      rw [← map_mul, ← map_mul, mul_add, hab, add_zero]
    calc e * e * algebraMap A F (a + b) * algebraMap A F (a + b)
        = (e * algebraMap A F (a + b)) * (e * algebraMap A F (a + b)) := by ring
      _ = algebraMap A F a * algebraMap A F a := by rw [he]
      _ = algebraMap A F a * algebraMap A F (a + b) := h2.symm
      _ = e * algebraMap A F (a + b) * algebraMap A F (a + b) := by rw [he]
  have hint : IsIntegral A e := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub (by simp)
    · simp [Polynomial.eval₂_sub, pow_two, hidem]
  obtain ⟨c, hc⟩ := IsIntegrallyClosedIn.isIntegral_iff.1 hint
  have hcc : c * c = c := hinj (by rw [map_mul, hc, hidem])
  have hca : c * (a + b) = a := hinj (by rw [map_mul, hc, he])
  have h01 : c = 0 ∨ c = 1 := by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self c with h | h
    · right
      exact h.mul_left_cancel (by rw [hcc, _root_.mul_one])
    · left
      have : (1 - c) * c = 0 := by rw [sub_mul, _root_.one_mul, hcc, sub_self]
      exact h.mul_right_eq_zero.1 this
  rcases h01 with rfl | rfl
  · left
    simpa using hca.symm
  · right
    simpa using hca

private theorem isDomain_of_isReduced_of_isIntegrallyClosed (A : Type) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsReduced A] [IsIntegrallyClosed A] : IsDomain A := by
  classical
  by_contra hdom
  have hbot : ¬ (⊥ : Ideal A).IsPrime := fun h => hdom (IsDomain.of_bot_isPrime A)
  have hfin : (minimalPrimes A).Finite := minimalPrimes.finite_of_isNoetherianRing A
  have hzero : ∀ x : A, (∀ Q ∈ minimalPrimes A, x ∈ Q) → x = 0 := fun x hx => by
    have : x ∈ (⊥ : Ideal A).radical := by
      rw [← Ideal.sInf_minimalPrimes]
      exact (Submodule.mem_sInf).2 hx
    obtain ⟨n, hn⟩ := this
    exact (IsNilpotent.eq_zero ⟨n, by simpa using hn⟩)
  obtain ⟨P, hP, -⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A)) (J := IsLocalRing.maximalIdeal A) bot_le
  have hPp : P.IsPrime := Ideal.minimalPrimes_isPrime hP
  have hprime : ∀ Q ∈ minimalPrimes A, Q.IsPrime := fun Q hQ => Ideal.minimalPrimes_isPrime hQ
  have hle : ∀ Q ∈ minimalPrimes A, ∀ Q' ∈ minimalPrimes A, Q ≤ Q' → Q = Q' := fun Q hQ Q' hQ' h =>
    le_antisymm h (hQ'.2 hQ.1 h)
  let T : Finset (Ideal A) := hfin.toFinset.erase P
  have hT : ∀ Q ∈ T, Q ∈ minimalPrimes A ∧ Q ≠ P := fun Q hQ => by
    have := Finset.mem_erase.1 hQ
    exact ⟨hfin.mem_toFinset.1 this.2, this.1⟩
  have hTm : ∀ Q ∈ minimalPrimes A, Q ≠ P → Q ∈ T := fun Q hQ h =>
    Finset.mem_erase.2 ⟨h, hfin.mem_toFinset.2 hQ⟩

  obtain ⟨a, haP, ha⟩ : ∃ a ∈ P, a ∉ ⋃ i ∈ (↑(insert ⊥ T) : Set (Ideal A)), (i : Set A) := by
    by_contra hcon
    push_neg at hcon
    have hsub : (P : Set A) ⊆ ⋃ i ∈ (↑(insert ⊥ T) : Set (Ideal A)), ((id i : Ideal A) : Set A) := hcon
    obtain ⟨Q, hQ, hPQ⟩ := (Ideal.subset_union_prime (⊥ : Ideal A) (⊥ : Ideal A)
      (fun i hi h1 _ => (hT i ((Finset.mem_insert.1 hi).resolve_left h1)).1 |> hprime i)).1 hsub
    rcases Finset.mem_insert.1 hQ with rfl | hQ
    · exact hbot ((le_bot_iff.1 hPQ) ▸ hPp)
    · exact (hT Q hQ).2 (hle P hP Q (hT Q hQ).1 hPQ).symm
  have ha0 : a ≠ 0 := fun h => ha (by
    simp only [Set.mem_iUnion]
    exact ⟨⊥, by simp, by simp [h]⟩)
  have haT : ∀ Q ∈ T, a ∉ Q := fun Q hQ h => ha (by
    simp only [Set.mem_iUnion]
    exact ⟨Q, by simp [hQ], h⟩)

  obtain ⟨b, hbT, hbP⟩ : ∃ b ∈ T.inf id, b ∉ P := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨Q, hQ, hQP⟩ := (Ideal.IsPrime.inf_le' hPp).1 (show T.inf id ≤ P from hcon)
    exact (hT Q hQ).2 (hle Q (hT Q hQ).1 P hP hQP)
  have hbT' : ∀ Q ∈ T, b ∈ Q := fun Q hQ => by
    have := Finset.inf_le (f := id) hQ
    exact this hbT
  have hab : a * b = 0 := hzero _ fun Q hQ => by
    by_cases h : Q = P
    · exact h ▸ Ideal.mul_mem_right _ _ haP
    · exact Ideal.mul_mem_left _ _ (hbT' Q (hTm Q hQ h))
  have hreg : a + b ∈ nonZeroDivisors A := by
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    refine hzero x fun Q hQ => ?_
    have hQp := hprime Q hQ
    have hx' : x * (a + b) ∈ Q := hx ▸ Q.zero_mem
    refine (hQp.mem_or_mem hx').resolve_right fun hs => ?_
    by_cases h : Q = P
    · subst h
      exact hbP ((Q.add_mem_iff_right haP).1 hs)
    · have hm := hTm Q hQ h
      exact haT Q hm ((Q.add_mem_iff_left (hbT' Q hm)).1 hs)
  rcases eq_zero_or_of_mul_eq_zero_of_add_reg hab hreg with h | h
  · exact ha0 h
  · exact hbP (h ▸ P.zero_mem)

private theorem isLocalization_away_uniformizer (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K] {ϖ : O} (hϖ : Irreducible ϖ) : IsLocalization.Away ϖ K := by
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hne : ϖ ≠ 0 := hϖ.ne_zero
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    exact (IsUnit.mk0 _ ((map_ne_zero_iff _ hinj).2 hne)).pow n |>.map (RingHom.id K) |> fun h => by simpa using h
  · intro z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) z
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
    refine ⟨⟨a * ↑u⁻¹, ⟨ϖ ^ n, n, rfl⟩⟩, ?_⟩
    have h1 : algebraMap O K (↑u) * algebraMap O K (↑u⁻¹ : O) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have h2 : algebraMap O K (↑u) ≠ 0 := fun h => by simp [h] at h1
    have h3 : algebraMap O K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hne
    simp only [map_mul, map_pow]
    field_simp
    rw [_root_.mul_assoc, h1, _root_.mul_one]
  · intro x y h
    exact ⟨1, by rw [hinj h]⟩

private theorem isReduced_of_flat_of_fib {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K] {W : Scheme.{0}} (f : W ⟶ Sp O) [Flat f]
    [IsReduced (fib K f)] : IsReduced W := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  haveI := isLocalization_away_uniformizer O K hϖ
  haveI he : IsOpenImmersion (spMap (algebraMap O K)) := IsOpenImmersion.of_isLocalization ϖ
  let j : fib K f ⟶ W := pullback.fst f (spMap (algebraMap O K))
  haveI : IsOpenImmersion j := inferInstance
  have hrange : Set.range j = f ⁻¹' (PrimeSpectrum.basicOpen ϖ : Set (PrimeSpectrum O)) := by
    have h1 : Set.range (spMap (algebraMap O K)) = (PrimeSpectrum.basicOpen ϖ : Set (PrimeSpectrum O)) :=
      PrimeSpectrum.localization_away_comap_range K ϖ
    rw [← h1]
    exact Scheme.Pullback.range_fst f (spMap (algebraMap O K))
  let r : Γ(Sp O, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom ϖ
  have hr : r ∈ nonZeroDivisors Γ(Sp O, ⊤) := by
    rw [mem_nonZeroDivisors_iff_left]
    intro a ha
    let e := (Scheme.ΓSpecIso (CommRingCat.of O)).commRingCatIsoToRingEquiv
    have hre : e r = ϖ := e.apply_symm_apply ϖ
    refine e.injective ?_
    have : ϖ * e a = 0 := by rw [← hre, mul_comm, ← map_mul, mul_comm, ha, map_zero]
    rw [map_zero]
    exact (mul_eq_zero.1 this).resolve_left hϖ.ne_zero
  have haff : ∀ V : W.Opens, IsAffineOpen V → ∀ g : Γ(W, V), IsNilpotent g → g = 0 := by
    intro V hV g hg
    let q : Γ(W, V) := (f.appLE ⊤ V le_top).hom r
    let U := W.basicOpen q
    let ρ : Γ(W, V) →+* Γ(W, U) := (W.presheaf.map (homOfLE (W.basicOpen_le q)).op).hom
    letI : Algebra Γ(W, V) Γ(W, U) := ρ.toAlgebra
    haveI : IsLocalization.Away q Γ(W, U) := hV.isLocalization_basicOpen q
    have hUr : Set.range U.ι ⊆ Set.range j := by
      rw [Scheme.Opens.range_ι, hrange]
      intro x hx
      have h2 : U = V ⊓ f ⁻¹ᵁ (Sp O).basicOpen r := Scheme.basicOpen_appLE f V ⊤ le_top r
      have h3 : x ∈ f ⁻¹ᵁ (Sp O).basicOpen r := by
        have : x ∈ U := hx
        rw [h2] at this
        exact this.2
      have h4 : (Sp O).basicOpen r = PrimeSpectrum.basicOpen ϖ :=
        basicOpen_eq_of_affine (R := CommRingCat.of O) ϖ
      rw [h4] at h3
      exact h3
    let i' : U.toScheme ⟶ fib K f := IsOpenImmersion.lift j U.ι hUr
    haveI : IsOpenImmersion (i' ≫ j) := by
      rw [IsOpenImmersion.lift_fac]
      infer_instance
    haveI : IsOpenImmersion i' := IsOpenImmersion.of_comp i' j
    haveI : IsReduced U.toScheme := isReduced_of_isOpenImmersion i'
    haveI : _root_.IsReduced Γ(W, U) :=
      isReduced_of_injective (U.topIso.inv.hom) (U.topIso.commRingCatIsoToRingEquiv.symm.injective)
    have h0 : algebraMap Γ(W, V) Γ(W, U) g = 0 := (hg.map (algebraMap Γ(W, V) Γ(W, U))).eq_zero
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers q) _ g).1 h0
    have hk' : q ^ k * g = 0 := hk
    have hfl : (f.appLE ⊤ V le_top).hom.Flat :=
      HasRingHomProperty.appLE (P := @Flat) f inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
    have hq : ∀ y : Γ(W, V), q * y = 0 → y = 0 := fun y hy => by
      letI := (f.appLE ⊤ V le_top).hom.toAlgebra
      haveI : Module.Flat Γ(Sp O, ⊤) Γ(W, V) := hfl
      have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Γ(W, V)) hr
      refine hreg ?_
      simp only [Algebra.smul_def, mul_zero]
      exact hy
    clear hk h0
    induction k with
    | zero => simpa using hk'
    | succ k ih => exact ih (hq _ (by rw [pow_succ', _root_.mul_assoc] at hk'; exact hk'))
  refine ⟨fun U => ⟨fun s hs => ?_⟩⟩
  refine W.sheaf.eq_of_locally_eq' (fun V : {V : W.affineOpens // V.1 ≤ U} => V.1.1) U
    (fun V => homOfLE V.2) ?_ s 0 fun V => ?_
  · intro y hy
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hVU⟩, hyV⟩
  · rw [map_zero]
    exact haff V.1.1 V.1.2 _ (hs.map _)

theorem UpperTheory.finite_flat_cover_model_integral :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O K k : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Field K] [Field k] [Algebra O K] [IsFractionRing O K] [Algebra O k], Function.Surjective (algebraMap O k) → RingHom.ker (algebraMap O k) = IsLocalRing.maximalIdeal O → ∀ (b : Base D O) (N : ℕ) (M : Model b N) (W : Scheme.{0}) (π : W ⟶ M.X), IsFinite π → Flat (π ≫ M.s) → (∀ y : W, IsIntegrallyClosed (W.presheaf.stalk y)) → Etale (fibMap K (π ≫ M.s) M.s π rfl) → ∀ y : W, IsDomain (W.presheaf.stalk y) := by
  intro p _ D O K k _ _ _ _ _ _ _ _ _ _ _ b N M W π hπ hfl hic het y
  haveI := M.smooth
  haveI : Smooth M.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) M.s
  haveI := hπ
  haveI := hfl
  haveI := het
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (π ≫ M.s)
  haveI : IsReduced (fib K (π ≫ M.s)) := GlobalTheory.isReduced_of_smooth_of_isReduced
    (fibMap K (π ≫ M.s) M.s π rfl ≫ pullback.snd M.s (spMap (algebraMap O K)))
  haveI : IsReduced W := isReduced_of_flat_of_fib (K := K) (π ≫ M.s)
  haveI := hic y
  exact isDomain_of_isReduced_of_isIntegrallyClosed _
