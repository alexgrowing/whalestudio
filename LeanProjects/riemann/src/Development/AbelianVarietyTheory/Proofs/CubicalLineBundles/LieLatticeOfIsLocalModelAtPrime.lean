import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeLocalizationModelLieAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.LocModelLie

section Alg

variable {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R K] [IsFractionRing R K]

theorem exists_ringHom : ∃ f : 𝓞 K →+* R, ∀ x, algebraMap R K (f x) = algebraMap (𝓞 K) K x := by
  have h : ∀ x : 𝓞 K, algebraMap (𝓞 K) K x ∈ (algebraMap R K).range := fun x =>
    IsIntegrallyClosed.isIntegral_iff.1 (x.isIntegral_coe.tower_top (A := R))
  let e := RingEquiv.ofBijective (algebraMap R K).rangeRestrict
    ⟨fun a b hab => IsFractionRing.injective R K (congrArg Subtype.val hab), RingHom.rangeRestrict_surjective _⟩
  refine ⟨e.symm.toRingHom.comp ((algebraMap (𝓞 K) K).codRestrict _ h), fun x => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply ⟨_, h x⟩)

theorem isUnit_of_valuation_eq_one (𝔭 : HeightOneSpectrum (𝓞 K))
    (hR : ∀ r : R, 𝔭.valuation K (algebraMap R K r) ≤ 1) {r : R} (hr : 𝔭.valuation K (algebraMap R K r) = 1) :
    IsUnit r := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hu : ∀ u : Rˣ, 𝔭.valuation K (algebraMap R K u) = 1 := fun u => by
    refine eq_one_of_one_le_mul_left (hR (u : R)) (hR (u⁻¹ : Rˣ)) ?_
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have hlt : 𝔭.valuation K (algebraMap R K ϖ) ≠ 1 := fun h1 => by
    have hall : ∀ s : R, s ≠ 0 → 𝔭.valuation K (algebraMap R K s) = 1 := fun s hs => by
      obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs hϖ
      rw [map_mul, map_mul, map_pow, map_pow, hu, h1, one_pow, _root_.mul_one]
    obtain ⟨π, hπ⟩ := 𝔭.valuation_exists_uniformizer K
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) π
    by_cases ha : a = 0
    · rw [ha, map_zero, zero_div, map_zero] at hπ
      exact WithZero.exp_ne_zero hπ.symm
    · rw [map_div₀, hall a ha, hall b (nonZeroDivisors.ne_zero hb), div_one, ← WithZero.exp_zero,
        WithZero.exp_inj] at hπ
      omega
  have h0 : r ≠ 0 := by
    rintro rfl
    rw [map_zero, map_zero] at hr
    exact zero_ne_one hr
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
  rw [map_mul, map_mul, map_pow, map_pow, hu, _root_.one_mul] at hr
  obtain rfl | hn := Nat.eq_zero_or_pos n
  · simp
  · exact absurd ((pow_eq_one_iff_of_nonneg zero_le hn.ne').1 hr) hlt

theorem isLocalization [Algebra (𝓞 K) R] [IsScalarTower (𝓞 K) R K] (𝔭 : HeightOneSpectrum (𝓞 K))
    (hR : ∀ r : R, 𝔭.valuation K (algebraMap R K r) ≤ 1) : IsLocalization 𝔭.asIdeal.primeCompl R := by
  refine (isLocalization_iff _ _).2 ⟨fun s => isUnit_of_valuation_eq_one 𝔭 hR ?_, fun r => ?_, fun {x y} h => ⟨1, ?_⟩⟩
  · rw [← IsScalarTower.algebraMap_apply]
    exact 𝔭.valuation_eq_one_iff_notMem.2 s.2
  · obtain ⟨n, d, h⟩ := 𝔭.exists_primeCompl_mul_eq_of_integer _ (hR r)
    refine ⟨(n, d), IsFractionRing.injective R K ?_⟩
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, h]
  · have := congrArg (algebraMap R K) h
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
    rw [IsFractionRing.injective (𝓞 K) K this]

end Alg

theorem exists_iso_of_models (h : HomExtDvr) (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G']
    (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G') (H : Over (Sp K)) [GrpObj H] {ψ : H.left ⟶ G.left}
    {ψ' : H.left ⟶ G'.left} (hψ : IsGrpPullback H G (spMap (algebraMap T K)) ψ)
    (hψ' : IsGrpPullback H G' (spMap (algebraMap T K)) ψ') :
    ∃ e : G ≅ G', IsMonHom e.hom ∧ ψ ≫ e.hom.left = ψ' := by
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso hψ (isGrpPullback_pullback G _)
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso hψ' (isGrpPullback_pullback G' _)
  let f := a.symm ≪≫ b
  have hf : IsMonHom f.hom := by
    change IsMonHom (a.inv ≫ b.hom)
    infer_instance
  obtain ⟨F, ⟨hF, eF⟩, -⟩ := h T K G G' hG hG' f.hom hf
  obtain ⟨F', ⟨hF', eF'⟩, -⟩ := h T K G' G hG' hG f.inv inferInstance
  refine ⟨⟨F, F', (h T K G G hG hG (𝟙 _) inferInstance).unique ⟨inferInstance, ?_⟩
      ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩,
    (h T K G' G' hG' hG' (𝟙 _) inferInstance).unique ⟨inferInstance, ?_⟩
      ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩⟩, hF, ?_⟩
  · rw [Functor.map_comp, eF, eF']
    exact f.hom_inv_id
  · rw [Functor.map_comp, eF, eF']
    exact f.inv_hom_id
  · have A : ((Over.pullback (spMap (algebraMap T K))).map F).left ≫ pullback.fst G'.hom _ =
        pullback.fst G.hom _ ≫ F.left := pullback.lift_fst _ _ _
    change ψ ≫ F.left = ψ'
    rw [← ha', Category.assoc, ← A, eF, ← hb', ← Category.assoc, ← Over.comp_left]
    congr 2
    exact a.hom_inv_id_assoc _

theorem eq_dualMapR {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (F : DualNumber R →+* DualNumber R')
    (h₁ : ∀ a, F (algebraMap R _ a) = algebraMap R' _ (f a)) (h₂ : F DualNumber.eps = DualNumber.eps) :
    F = Chart.dualMapR f := by
  refine RingHom.ext fun x => ?_
  have e : x = algebraMap R _ x.fst + algebraMap R _ x.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  conv_lhs => rw [e, map_add, map_mul, h₁, h₁, h₂]
  ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.LocModelLie

namespace GlobalTheory.CM

open LocModelLie

theorem lieLat_of_isLocalModel : HomExtDvr → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (hg rig hr th hth) (𝔭 : HeightOneSpectrum (𝓞 K)) (a : K) (M : Matrix (Fin F.P₀.g) (Fin F.P₀.g) K), KeyPow.IsLocalModel (F.key hg rig hr th hth) 𝔭 a M → (∀ i, ∃ s : 𝓞 K, s ∉ 𝔭.asIdeal ∧ s • M i ∈ F.lieLat) ∧ ∀ c ∈ F.lieLat, ∃ s : 𝓞 K, s ∉ 𝔭.asIdeal ∧ s • c ∈ Submodule.span (𝓞 K) (Set.range fun i => M i) := by
  intro hE K _ _ P F hg rig hr th hth 𝔭 a M
    ⟨R, _, _, _, _, _, y, th', hth', v', hv', hR, _, hM, ψ, _, _, hgg, Φ, hψ, _, _, _, hΦ₁, hΦ₂, hv⟩
  obtain ⟨f, hf⟩ := exists_ringHom (K := K) (R := R)
  letI : Algebra (𝓞 K) R := f.toAlgebra
  haveI : IsScalarTower (𝓞 K) R K := IsScalarTower.of_algebraMap_eq fun x => (hf x).symm
  haveI := isLocalization 𝔭 hR
  obtain rfl := eq_dualMapR _ Φ hΦ₁ hΦ₂
  change F.P₀.g = y.P.g at hgg
  change IsGrpPullback F.P₀.A y.P.A (spMap (algebraMap R K)) ψ at hψ
  have hc : spMap (algebraMap (𝓞 K) K) = spMap (algebraMap R K) ≫ spMap (algebraMap (𝓞 K) R) := by
    rw [IsScalarTower.algebraMap_eq (𝓞 K) R K]
    exact Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _)
  have hF := F.fib.2.1.congr hc rfl
  have hp := isGrpPullback_pullback P.A (spMap (algebraMap (𝓞 K) R))
  let ψ' := hp.1.lift F.φ (F.P₀.A.hom ≫ spMap (algebraMap R K)) (by rw [hF.1.w, Category.assoc])
  have hψ' : ψ' ≫ pullback.fst _ _ = F.φ := hp.1.lift_fst _ _ _
  obtain ⟨e, he, hψe⟩ := exists_iso_of_models hE R K y.P.A _ (isSemiAbelian_of_isAbelianScheme _ y.P.isAb)
    (IsSemiAbelian.pullback _ _ (isSemiAbelian_of_isAbelianScheme _ P.isAb)) F.P₀.A hψ
    (IsGrpPullback.cancel hp (hF.congr rfl hψ'.symm) (hp.1.lift_snd _ _ _))
  have hb : IsLieBasis fun i : Fin F.P₀.g => y.v (i.cast hgg) := by
    have : ∀ (n : ℕ) (h : n = y.P.g), IsLieBasis fun i : Fin n => y.v (i.cast h) := by
      rintro _ rfl
      exact y.basis
    exact this _ _
  obtain ⟨h₁, h₂⟩ := GlobalTheory.T.lieLattice_localization_modelLieAlgebra K P F R 𝔭.asIdeal.primeCompl y.P.A (e.hom.left ≫ pullback.fst _ _) ψ _ v' M
    (((isGrpPullback_of_iso e).comp hp).congr (Category.id_comp _) rfl) hψ
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst _ _) hψe).trans hψ')) hb (fun i => ⟨hv i, hM i⟩)
  refine ⟨h₁, fun c hc => ?_⟩
  obtain ⟨b, rfl⟩ := h₂ c hc
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite 𝔭.asIdeal.primeCompl b
  refine ⟨s, s.2, ?_⟩
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨t, ht⟩ := hs i
  have : (s : 𝓞 K) • algebraMap R K (b i) • M i = t • M i := by
    have e : algebraMap (𝓞 K) K t = algebraMap (𝓞 K) K s * algebraMap R K (b i) := by
      rw [IsScalarTower.algebraMap_apply (𝓞 K) R K t, ht, Algebra.smul_def, map_mul,
        ← IsScalarTower.algebraMap_apply]
    rw [← algebraMap_smul K t, e, mul_smul, algebraMap_smul K (s : 𝓞 K)]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory.CM
