import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValNorm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAE
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsIntegralIffMemSpanOneTmulIntegralClosure
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemIntegralClosureOfMemSpan
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPtOrdEqAddValuation
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FdegEqFinrankResidueFieldStatement

open ReciprocityTheory.ChartRestriction.G.T0 Formalism.MainNotions.Gaps.EtaleWeightGaps
open scoped TensorProduct

namespace GlobalTheory

namespace CoverPlaces

variable {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A]
  [Algebra O A] {ϖ : O}

theorem ord_pos_iff (h : IsUnif A ϖ) (ζ : Pts O A) [IsDVRAt ζ] (a : As O A) :
    0 < ord ϖ ζ (a : A) ↔ a ∈ ζ.asIdeal := by
  rw [ord_of_mem ζ h a.2, ← not_iff_not, ← vL_eq_zero_iff]
  change ¬ 0 < (vL ζ a).map (Nat.cast : ℕ → ℤ) ↔ _
  generalize vL ζ a = v
  cases v with
  | top => simp
  | coe j =>
    rw [ENat.map_natCast, ← WithTop.coe_zero, WithTop.coe_lt_coe]
    simp

theorem surjective_of_detect [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) {T : Type} [Finite T]
    (Z : T → Pts O A) (hZ : ∀ x, (∀ t, 0 ≤ ord ϖ (Z t) x) → x ∈ As O A) :
    Function.Surjective Z := by
  classical
  cases nonempty_fintype T
  intro ζ
  by_contra hne
  have hex : ∀ t, ∃ a ∈ (Z t).asIdeal, a ∉ ζ.asIdeal := by
    intro t
    by_contra hc
    push Not at hc
    exact hne ⟨t, MaximalSpectrum.ext ((Z t).isMaximal.eq_of_le ζ.isMaximal.ne_top hc)⟩
  choose a ha ha' using hex
  haveI := ζ.isMaximal.isPrime
  have hb : ∏ t, a t ∉ ζ.asIdeal := by
    rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨t, -, ht⟩
    exact ha' t ht
  have hbt : ∀ t, ∏ t, a t ∈ (Z t).asIdeal := fun t =>
    Ideal.prod_mem _ (Finset.mem_univ t) (ha t)
  generalize ∏ t, a t = b at hb hbt
  obtain ⟨v, hv⟩ := h.isUnit.exists_right_inv
  set n : ℕ := ∑ t, ep ϖ (Z t) with hn
  have hx : v * (b : A) ^ n ∈ As O A := by
    apply hZ
    intro t
    have h1 : ord ϖ (Z t) (algebraMap O A ϖ * (v * (b : A) ^ n)) = n • ord ϖ (Z t) b := by
      rw [← mul_assoc, hv, one_mul, ord_pow _ h]
    rw [ord_mul _ h, ord_unif _ h] at h1
    have h2 := (ord_pos_iff h (Z t) b).2 (hbt t)
    have h3 : ep ϖ (Z t) ≤ n :=
      Finset.single_le_sum (f := fun t => ep ϖ (Z t)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
    have h4 := ep_pos (Z t) h
    generalize ord ϖ (Z t) (v * (b : A) ^ n) = p at h1
    generalize ord ϖ (Z t) (b : A) = q at h1 h2
    generalize ep ϖ (Z t) = e at h1 h3 h4
    induction p using WithTop.recTopCoe with
    | top => exact le_top
    | coe p =>
      induction q using WithTop.recTopCoe with
      | top =>
        obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        rw [hm, succ_nsmul, add_top, ← WithTop.coe_add] at h1
        exact absurd h1 WithTop.coe_ne_top
      | coe q =>
        rw [← WithTop.coe_add, ← WithTop.coe_nsmul, WithTop.coe_inj, nsmul_eq_mul] at h1
        have h5 : 0 < q := by exact_mod_cast h2
        have h6 : (e : ℤ) ≤ n := by exact_mod_cast h3
        have h7 : 0 ≤ p := by nlinarith
        exact_mod_cast h7
  have hp : b ^ n = algebraMap O (As O A) ϖ * ⟨_, hx⟩ := by
    apply Subtype.ext
    change (b : A) ^ n = algebraMap O A ϖ * (v * (b : A) ^ n)
    rw [← mul_assoc, hv, one_mul]
  exact hb (ζ.isMaximal.isPrime.mem_of_pow_mem n (hp ▸ Ideal.mul_mem_right _ _ (unif_mem h ζ)))

theorem isIntegral_of_forall {R A ι : Type} [CommRing R] [CommRing A] [Algebra R A] [Finite ι]
    {S : ι → Type} [∀ c, CommRing (S c)] [∀ c, Algebra R (S c)] (Ψ : ∀ c, A →ₐ[R] S c)
    (hΨ : ∀ a, (∀ c, Ψ c a = 0) → a = 0) (x : A) (hx : ∀ c, IsIntegral R (Ψ c x)) :
    IsIntegral R x := by
  classical
  cases nonempty_fintype ι
  choose p hp hp0 using hx
  refine ⟨∏ c, p c, Polynomial.monic_prod_of_monic _ _ fun c _ => hp c, hΨ _ fun c => ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_algHom_apply, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ c) (by rw [Polynomial.aeval_def]; exact hp0 c)

end CoverPlaces

open CoverPlaces in

theorem exists_equiv_pts_places_baseChange : ∀ (R R' F F' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [Module.Flat R R'] [IsLocalHom (algebraMap R R')] [Field F] [Algebra R F] [IsFractionRing R F] [Field F'] [Algebra R' F'] [IsFractionRing R' F'] [Algebra F F'] [Algebra R F'] [IsScalarTower R F F'] [IsScalarTower R R' F'], Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' → Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R R')) → ∀ (ι : Type) [Finite ι] (L : ι → Type) [∀ c, Field (L c)] [∀ c, Algebra F (L c)] [∀ c, FiniteDimensional F (L c)] [∀ c, Algebra.IsSeparable F (L c)] [∀ c, Algebra R (L c)] [∀ c, IsScalarTower R F (L c)] (A : Type) [CommRing A] [Algebra R' A] (ϖ : R'), IsUnif A ϖ → ∀ [∀ ζ : Pts R' A, IsDVRAt ζ] (Ψ : ∀ c, A →ₐ[R'] F' ⊗[F] L c), (∀ c, Function.Surjective (Ψ c)) → (∀ a, (∀ c, Ψ c a = 0) → a = 0) → (∀ c c', c ≠ c' → ∃ a, Ψ c a = 0 ∧ Ψ c' a = 1) → ∃ e : Pts R' A ≃ Σ c, ValPl.PlacesOver R (L c), ∀ ζ, fdeg ζ = (letI := resAlg (F := F) (e ζ).2.1; Module.finrank (IsLocalRing.ResidueField ((vRing (e ζ).2.1).comap (algebraMap F (L (e ζ).1)))) (IsLocalRing.ResidueField (vRing (e ζ).2.1))) ∧ ∃ u : AddValuation (F' ⊗[F] L (e ζ).1) (WithTop ℤ), (∀ g, u ((1 : F') ⊗ₜ[F] g) = (e ζ).2.1 g) ∧ ∀ a, ord ϖ ζ a = u (Ψ (e ζ).1 a) := by
  intro R R' F F' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hmax hres ι _ L _ _ _ _ _ _ A _ _ ϖ hϖ _ Ψ
    hsurj hinj hsep
  choose w' hw1 hw2 hw3 hw4 using fun c =>
    exists_unique_place_baseChange R R' F F' hmax hres (L c)
      (isIntegral_iff_mem_span_one_tmul_integralClosure R R' F F' hmax hres (L c))
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hex : ∀ t : Σ c, ValPl.PlacesOver R (L c), ∃ ζ : Pts R' A,
      ∀ a, ord ϖ ζ a = w' t.1 t.2 (Ψ t.1 a) := by
    rintro ⟨c, w⟩
    refine exists_pt_ord_eq_addValuation R' A ϖ hϖ ((w' c w).comap (Ψ c).toRingHom) ?_ ?_ ?_
    · intro a ha
      exact (hw2 c _).1 (IsIntegral.map (Ψ c) ha) w
    · have hm : ϖ ∈ Ideal.span {algebraMap R R' π} := by
        rw [← PlaceExt.maximalIdeal_eq_span hmax hπ]
        exact hϖ.irreducible.not_isUnit
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hm
      change 0 < w' c w (Ψ c (algebraMap R' A ϖ))
      rw [AlgHom.commutes, ← hr, map_mul, AddValuation.map_mul, PlaceExt.algebraMap_eq_one_tmul,
        hw1]
      exact lt_of_lt_of_le ((w.2.2 π).2.2 hπ.not_isUnit)
        (le_add_of_nonneg_left ((hw2 c _).1 isIntegral_algebraMap w))
    · obtain ⟨g, hg⟩ := w.2.1.2
      obtain ⟨a, ha⟩ := hsurj c ((1 : F') ⊗ₜ[F] g)
      refine ⟨a, ?_⟩
      change w' c w (Ψ c a) = 1
      rw [ha, hw1, hg]
  choose Z hZ using hex
  have hZinj : Function.Injective Z := by
    rintro ⟨c, w⟩ ⟨c', w₂⟩ he
    have h1 : ∀ a, w' c w (Ψ c a) = w' c' w₂ (Ψ c' a) := fun a => by
      rw [← hZ ⟨c, w⟩ a, he, hZ]
    obtain rfl : c = c' := by
      by_contra hc
      obtain ⟨a, h0, h1'⟩ := hsep c c' hc
      have := h1 a
      rw [h0, h1', AddValuation.map_zero, AddValuation.map_one] at this
      exact WithTop.top_ne_zero this
    congr 1
    apply Subtype.ext
    apply AddValuation.ext
    intro g
    obtain ⟨a, ha⟩ := hsurj c ((1 : F') ⊗ₜ[F] g)
    rw [← hw1, ← hw1, ← ha, h1]
  haveI : ∀ c, Finite (ValPl.PlacesOver R (L c)) := fun c => by
    haveI := integralClosure.isDedekindDomain R F (L c)
    haveI := integralClosure.isFractionRing_of_finite_extension (A := R) F (L c)
    exact (ValPl.placesOver_finite (F := F) R (L c)).to_subtype
  have hZsurj : Function.Surjective Z := by
    refine surjective_of_detect hϖ Z fun x hx => ?_
    refine isIntegral_of_forall Ψ hinj x fun c => (hw2 c _).2 fun w => ?_
    have := hx ⟨c, w⟩
    rwa [hZ] at this
  refine ⟨(Equiv.ofBijective Z ⟨hZinj, hZsurj⟩).symm, fun ζ => ?_⟩
  have hζ : Z ((Equiv.ofBijective Z ⟨hZinj, hZsurj⟩).symm ζ) = ζ :=
    (Equiv.ofBijective Z ⟨hZinj, hZsurj⟩).apply_symm_apply ζ
  generalize (Equiv.ofBijective Z ⟨hZinj, hZsurj⟩).symm ζ = t at hζ ⊢
  subst hζ
  obtain ⟨c, w⟩ := t
  refine ⟨?_, w' c w, hw1 c w, hZ ⟨c, w⟩⟩
  refine T.fdeg_eq_finrank_residueField_alt R R' F hres (L c) A ϖ hϖ _ w.1 w.2 (F' ⊗[F] L c) (w' c w) (Ψ c).toRingHom
    (Algebra.TensorProduct.includeRight : L c →ₐ[F] F' ⊗[F] L c).toRingHom (hsurj c) ?_
    (hw1 c w) (hZ ⟨c, w⟩) (hw3 c w)
  intro r
  exact ((Ψ c).commutes _).trans (PlaceExt.algebraMap_eq_one_tmul r)

end GlobalTheory
