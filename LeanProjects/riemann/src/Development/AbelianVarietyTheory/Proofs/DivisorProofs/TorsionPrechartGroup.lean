import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMapComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomCompEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionChartRangeInjectiveEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveEmbeddingMinimalPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatAlgebraicTensorChartRingStatement
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff.ChartGrp

theorem sepext : ∀ (R : Type) [CommRing R] (G : Over (Sp R)), IsSeparated G.hom → ∀ (B L : Type) [CommRing B] [IsDomain B] [Field L] [Algebra R B] [Algebra R L] (em : B →ₐ[R] L), Function.Injective em → ∀ x y : SpAlg R B ⟶ G, spOver em ≫ x = spOver em ≫ y → x = y := by
  intro R _ G hsep B L _ _ _ _ _ em hem x y h
  haveI := hsep
  have hdom : IsDominant (spMap (em : B →+* L)) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      intro a ha
      have h0 : em a = 0 := ha
      rw [show a = 0 from hem (h0.trans (map_zero em).symm)]; exact zero_mem _)⟩
  have h' := congrArg Over.Hom.left h
  rw [Over.comp_left, Over.comp_left] at h'
  exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Sp B) G.hom ((Over.w x).trans (Over.w y).symm)
      (spMap (em : B →+* L)) h')

theorem genmem : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) (W : G.left.Opens) (B L : Type) [CommRing B] [IsDomain B] [Field L] [Algebra R B] [Algebra R L] (em : B →ₐ[R] L), Function.Injective em → ∀ z : SpAlg R B ⟶ G, (Set.range z.left ∩ (W : Set G.left)).Nonempty → Set.range (spOver em ≫ z).left ⊆ W := by
  intro R _ G W B L _ _ _ _ _ em hem z hne
  obtain ⟨_, ⟨x, rfl⟩, hy⟩ := hne
  rintro _ ⟨t, rfl⟩
  let t' : PrimeSpectrum L := t
  let x' : PrimeSpectrum B := x
  have hbot : (PrimeSpectrum.comap (em : B →+* L) t').asIdeal = ⊥ := by
    show Ideal.comap _ t'.asIdeal = ⊥
    rw [show t'.asIdeal = ⊥ from Ideal.eq_bot_of_prime _]
    exact Ideal.comap_bot_of_injective _ hem
  have hsp : PrimeSpectrum.comap (em : B →+* L) t' ⤳ x' :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (by
      show (PrimeSpectrum.comap (em : B →+* L) t').asIdeal ≤ x'.asIdeal
      rw [hbot]; exact bot_le)
  exact (hsp.map z.left.continuous).mem_open W.isOpen hy

theorem mincover : ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D] (G : Over (Sp R)) (W : G.left.Opens) (u : SpAlg R D ⟶ G), (∀ P ∈ minimalPrimes D, Set.range (spOver (Ideal.Quotient.mkₐ R P) ≫ u).left ⊆ W) → Set.range u.left ⊆ W := by
  intro R D _ _ _ G W u h
  rintro _ ⟨x0, rfl⟩
  let x : PrimeSpectrum D := x0
  obtain ⟨P, hP, hle⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := x.asIdeal) bot_le
  have hPp : P.IsPrime := hP.1.1
  have hsurj : Function.Surjective (Ideal.Quotient.mk P) := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (Ideal.Quotient.mk P) ≤ x.asIdeal := by rw [Ideal.mk_ker]; exact hle
  let y : PrimeSpectrum (D ⧸ P) := ⟨x.asIdeal.map (Ideal.Quotient.mk P), Ideal.map_isPrime_of_surjective hsurj hker⟩
  have hy : PrimeSpectrum.comap (Ideal.Quotient.mk P) y = x := PrimeSpectrum.ext ((Ideal.comap_map_of_surjective' _ hsurj _).trans (sup_eq_left.2 hker))
  have := h P hP ⟨y, rfl⟩
  have e : (spOver (Ideal.Quotient.mkₐ R P)).left y = x0 := hy
  rw [Over.comp_left] at this
  rw [← e]; exact this

end GlobalTheory.GroupBplus.Aff.ChartGrp

namespace GlobalTheory.GroupBplus.Aff.ChartGrp

theorem liftRr : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (N : ℕ) (q : PrimeSpectrum R) (c : PreChart G N q) (φ : c.C →ₐ[R] K), ∃ φ' : c.C →ₐ[R] Localization.Away c.r, (c.toK K).comp φ' = φ := by
  intro R K _ _ _ _ _ _ G _ _ N q c φ
  have hr0 := c.r_ne_zero
  letI : Algebra (Localization.Away c.r) K := (c.toK K).toRingHom.toAlgebra
  haveI : IsScalarTower R (Localization.Away c.r) K :=
    IsScalarTower.of_algebraMap_eq fun x => ((c.toK K).commutes x).symm
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors hr0
  haveI : IsDomain (Localization.Away c.r) := IsLocalization.isDomain_localization hle
  haveI : IsIntegrallyClosed (Localization.Away c.r) := isIntegrallyClosed_of_isLocalization _ _ hle
  haveI : IsFractionRing (Localization.Away c.r) K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers c.r) (Localization.Away c.r) K
  haveI : Algebra.IsIntegral (Localization.Away c.r) c.C := Algebra.IsIntegral.of_finite _ _
  let φ' : c.C →ₐ[Localization.Away c.r] K :=
    { φ with
      commutes' := fun x => by
        haveI := IsLocalization.algHom_subsingleton (R := R) (M := Submonoid.powers c.r)
          (S := Localization.Away c.r) (P := K)
        have h := congrArg (fun g : Localization.Away c.r →ₐ[R] K => g x)
          (Subsingleton.elim (φ.comp (IsScalarTower.toAlgHom R (Localization.Away c.r) c.C))
            (IsScalarTower.toAlgHom R (Localization.Away c.r) K))
        simpa using h }
  obtain ⟨g, hg⟩ := GlobalTheory.GroupBplus.exists_algHom_comp_eq φ'
  refine ⟨g.restrictScalars R, ?_⟩
  ext a
  have h := congrArg (fun f : c.C →ₐ[Localization.Away c.r] K => f a) hg
  exact h

theorem fibmeets : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (N : ℕ) (q : PrimeSpectrum R) (c : PreChart G N q) (z : Tors G N (Localization.Away c.r)), (Set.range z.1.left ∩ (c.W : Set G.left)).Nonempty := by
  intro R _ G _ _ N q c z
  have hdisj : Disjoint (Submonoid.powers c.r : Set R) q.asIdeal := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ h
    exact c.hr (q.isPrime.mem_of_pow_mem n h)
  let q' : Ideal (Localization.Away c.r) := q.asIdeal.map (algebraMap R (Localization.Away c.r))
  haveI hq' : q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers c.r) _ q.asIdeal q.isPrime hdisj
  let k := q'.ResidueField
  letI : Algebra R k := ((algebraMap (Localization.Away c.r) k).comp (algebraMap R (Localization.Away c.r))).toAlgebra
  haveI : IsScalarTower R (Localization.Away c.r) k := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hker : RingHom.ker (algebraMap R k) = q.asIdeal := by
    ext x
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply R (Localization.Away c.r) k,
      ← RingHom.mem_ker, Ideal.ker_algebraMap_residueField]
    have e := IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers c.r) (Localization.Away c.r) q.isPrime hdisj
    show x ∈ q'.comap (algebraMap R (Localization.Away c.r)) ↔ _
    exact Iff.of_eq (congrArg (x ∈ ·) e)
  have hW := c.fibre k hker (torsMap (IsScalarTower.toAlgHom R (Localization.Away c.r) k) z)
  obtain ⟨t⟩ : Nonempty (PrimeSpectrum k) := inferInstance
  refine ⟨_, ⟨(spMap (algebraMap (Localization.Away c.r) k)) t, rfl⟩, hW ⟨t, rfl⟩⟩

end GlobalTheory.GroupBplus.Aff.ChartGrp

namespace GlobalTheory.GroupBplus.Aff

theorem chart_isGrp : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 → ∀ (q : PrimeSpectrum R) (c : PreChart G N q), c.IsGrp := by
  intro R K _ _ _ _ _ _ _ _ G _ _ hG N _ q c
  have hsep : IsSeparated G.hom := hG.separated
  have hdomr : IsDomain (Localization.Away c.r) := IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors c.r_ne_zero)
  have hinj : Function.Injective (c.toK K) := by
    have hM := powers_le_nonZeroDivisors_of_noZeroDivisors c.r_ne_zero
    exact (IsLocalization.lift_injective_iff _).2 fun x y =>
      ⟨fun h => congrArg _ (IsLocalization.injective _ hM h), fun h => congrArg _ (IsFractionRing.injective R K h)⟩

  have gen : ∀ z : Tors G N (Localization.Away c.r), Set.range (torsMap (c.toK K) z).1.left ⊆ c.W := fun z =>
    ChartGrp.genmem R G c.W _ K (c.toK K) hinj z.1 (ChartGrp.fibmeets R G N q c z)

  have hK : ∀ φ φ' : c.C →ₐ[R] K, Set.range (torsMap φ c.j * torsMap φ' c.j).1.left ⊆ c.W := by
    intro φ φ'
    obtain ⟨f, rfl⟩ := ChartGrp.liftRr R K G N q c φ
    obtain ⟨f', rfl⟩ := ChartGrp.liftRr R K G N q c φ'
    rw [← torsMap_comp, ← torsMap_comp, ← torsMap_mul]
    exact gen _
  refine ⟨?_, ?_⟩
  · obtain ⟨φ, -, hφ⟩ := (c.bij K).2.2 (show (1 : Tors G N K) ∈ {z | Set.range z.1.left ⊆ c.W} from by
      have := gen 1; rwa [torsMap_one] at this)
    obtain ⟨f, rfl⟩ := ChartGrp.liftRr R K G N q c φ
    refine ⟨f, Subtype.ext (ChartGrp.sepext R G hsep _ K (c.toK K) hinj _ _ ?_)⟩
    have h1 : torsMap (c.toK K) (torsMap f c.j) = torsMap (c.toK K) 1 := by
      rw [torsMap_comp, torsMap_one]; exact hφ
    exact congrArg Subtype.val h1
  · intro B _ _ ψ ψ'
    obtain ⟨hfl, halg⟩ := GlobalTheory.T.flat_algebraic_tensor_chart_ring R G N q c
    let D := c.C ⊗[R] c.C
    let u : Tors G N D := torsMap Algebra.TensorProduct.includeLeft c.j * torsMap Algebra.TensorProduct.includeRight c.j
    have hu : Set.range u.1.left ⊆ c.W := by
      refine ChartGrp.mincover R D G c.W u.1 fun P hP => ?_
      obtain ⟨em, hem⟩ := GlobalTheory.T.exists_injective_embedding_minimal_prime R K D P hP
      have : IsDomain (D ⧸ P) := (Ideal.Quotient.isDomain_iff_prime P).2 hP.1.1
      have hunit : IsUnit (algebraMap R (D ⧸ P) c.r) := by
        have h0 : IsUnit (algebraMap R c.C c.r) := by
          rw [IsScalarTower.algebraMap_apply R (Localization.Away c.r) c.C]
          exact (IsLocalization.Away.algebraMap_isUnit c.r).map _
        have := h0.map ((Ideal.Quotient.mkₐ R P).comp (Algebra.TensorProduct.includeLeft : c.C →ₐ[R] D))
        rwa [AlgHom.commutes] at this
      refine GlobalTheory.T.torsion_chart_range_injective_embedding R K G hsep N q c (D ⧸ P) hunit em hem (torsMap (Ideal.Quotient.mkₐ R P) u) ?_
      rw [torsMap_comp, torsMap_mul, torsMap_comp, torsMap_comp]
      exact hK _ _
    obtain ⟨χ, -, hχ⟩ := (c.bij D).2.2 hu
    refine ⟨(Algebra.TensorProduct.lift ψ ψ' fun _ _ => Commute.all _ _).comp χ, ?_⟩
    have hχ' : torsMap χ c.j = u := hχ
    rw [← torsMap_comp, hχ', torsMap_mul, torsMap_comp, torsMap_comp]
    simp

end GlobalTheory.GroupBplus.Aff
