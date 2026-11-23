import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.DimEqZero
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsPowMulMemRangeOfLocalDenominators

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AffineComplement

open ReciprocityTheory.AnForm.R

theorem effCartier_of_stalkId_of_isLocallyNoetherian {W : Scheme.{0}} [IsLocallyNoetherian W]
    (G : W.IdealSheafData)
    (hG : ∀ x : W, ∃ t ∈ nonZeroDivisors (W.presheaf.stalk x), FinalTheorems.stalkId G x = Ideal.span {t}) :
    FinalTheorems.EffCartier G := by
  intro x
  obtain ⟨t, htnzd, ht⟩ := hG x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let U' : W.affineOpens := ⟨U, hU⟩
  have hx : x ∈ U'.1 := hxU
  rw [ds_stalkId_eq_map G U' x hx] at ht
  haveI : IsNoetherianRing Γ(W, U) := IsLocallyNoetherian.component_noetherian U'
  letI : Algebra Γ(W, U) (W.presheaf.stalk x) := W.presheaf.algebra_section_stalk ⟨x, hx⟩
  haveI := hU.isLocalization_stalk ⟨x, hx⟩
  have halg : algebraMap Γ(W, U) (W.presheaf.stalk x) = (W.presheaf.germ U x hx).hom := rfl
  rw [Ideal.map] at ht
  obtain ⟨y, ⟨a, haI, rfl⟩, c, hc⟩ := ds_gen_of_span _ t htnzd ht
  have hmap : (G.ideal U').map (algebraMap Γ(W, U) (W.presheaf.stalk x)) =
      Ideal.span {algebraMap Γ(W, U) (W.presheaf.stalk x) a} := by
    rw [halg, Ideal.map, ht, hc, Ideal.span_singleton_mul_left_unit c.isUnit]
  have hnzd : algebraMap Γ(W, U) (W.presheaf.stalk x) a ∈ nonZeroDivisors (W.presheaf.stalk x) := by
    rw [halg, hc]
    exact mul_mem (IsUnit.mem_nonZeroDivisors c.isUnit) htnzd
  obtain ⟨σ, hσP, hT⟩ := ds_spread (hU.primeIdealOf ⟨x, hx⟩).asIdeal (G.ideal U') a haI hmap hnzd
  haveI := hU.isLocalization_basicOpen σ
  obtain ⟨h1, h2⟩ := hT Γ(W, W.basicOpen σ)
  refine ⟨W.affineBasicOpen (U := U') σ, algebraMap Γ(W, U) Γ(W, W.basicOpen σ) a, ?_, h2, ?_⟩
  · show x ∈ W.basicOpen σ
    rw [W.mem_basicOpen σ x hx]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (W.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal σ).2 hσP
  · rw [← G.map_ideal_basicOpen U' σ]
    exact h1

theorem exists_radical_span_singleton_eq {A : Type} [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] {a : A} (ha : a ≠ 0) :
    ∃ t ∈ nonZeroDivisors A, (Ideal.span {a}).radical = Ideal.span {t} := by
  obtain ⟨y, n, hy, hya, hay⟩ := exists_squarefree_dvd_pow_of_ne_zero ha
  refine ⟨y, mem_nonZeroDivisors_of_ne_zero hy.ne_zero, le_antisymm ?_ ?_⟩
  · rw [← (isRadical_iff_span_singleton.1 hy.isRadical).radical]
    exact Ideal.radical_mono (Ideal.span_singleton_le_span_singleton.2 hya)
  · rw [Ideal.span_singleton_le_iff_mem]
    exact ⟨n, Ideal.mem_span_singleton.2 hay⟩

theorem stalkId_vanishingIdeal_compl {X : Scheme.{0}} (U : X.Opens) (x : X)
    (a : X.presheaf.stalk x)
    (h : ∀ q : PrimeSpectrum (X.presheaf.stalk x), X.fromSpecStalk x q ∈ U ↔ a ∉ q.asIdeal) :
    FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal U.compl) x = (Ideal.span {a}).radical := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hx, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  rw [ds_stalkId_eq_map _ ⟨W, hW⟩ x hx, Scheme.IdealSheafData.vanishingIdeal_ideal]
  letI : Algebra Γ(X, W) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  haveI := hW.isLocalization_stalk ⟨x, hx⟩
  have hcl : IsClosed (X := PrimeSpectrum Γ(X, W)) (hW.fromSpec ⁻¹' (U.compl : Set X)) :=
    U.compl.isClosed.preimage hW.fromSpec.continuous
  generalize hJ : PrimeSpectrum.vanishingIdeal (R := Γ(X, W)) (hW.fromSpec ⁻¹' (U.compl : Set X)) = J
  have hz : PrimeSpectrum.zeroLocus (J : Set Γ(X, W)) = hW.fromSpec ⁻¹' (U.compl : Set X) := by
    rw [← hJ, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hcl.closure_eq]
    rfl
  have hr : J.radical = J := hJ ▸ (PrimeSpectrum.isRadical_vanishingIdeal _).radical
  change J.map (algebraMap Γ(X, W) (X.presheaf.stalk x)) = _
  rw [← hr, IsLocalization.map_radical (hW.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl,
    ← PrimeSpectrum.zeroLocus_eq_iff]
  ext q
  have e : X.fromSpecStalk x q =
      hW.fromSpec (PrimeSpectrum.comap (algebraMap Γ(X, W) (X.presheaf.stalk x)) q) := by
    rw [← hW.fromSpecStalk_eq_fromSpecStalk hx]
    rfl
  rw [PrimeSpectrum.mem_zeroLocus, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe,
    SetLike.coe_subset_coe, Ideal.map_le_iff_le_comap, Ideal.span_singleton_le_iff_mem,
    ← not_iff_not, ← h, e]
  have := Set.ext_iff.1 hz (PrimeSpectrum.comap (algebraMap Γ(X, W) (X.presheaf.stalk x)) q)
  exact (not_congr this).trans not_not

theorem exists_nonzeroLocus_eq : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [X.IsSeparated] (U : X.Opens), IsAffineOpen U → (U : Set X).Nonempty → (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) → ∃ (L : LB X) (σ : LB.Sec L), L.IsLB ∧ nonzeroLocus σ = U := by
  intro X _ _ _ U hU hne hufd
  have hι : IsAffineHom U.ι :=
    haveI : IsAffine U := hU
    haveI : IsAffineHom (U.ι ≫ terminal.from X) := inferInstance
    IsAffineHom.of_comp _ (terminal.from X)
  have hE : FinalTheorems.EffCartier (Scheme.IdealSheafData.vanishingIdeal U.compl) := by
    refine effCartier_of_stalkId_of_isLocallyNoetherian _ fun x => ?_
    haveI := hufd x
    have hd : IsDomain (X.presheaf.stalk x) := inferInstance
    have hn : IsNoetherianRing (X.presheaf.stalk x) := inferInstance
    have hA : IsAffineOpen (X.fromSpecStalk x ⁻¹ᵁ U) := by
      have : IsAffineHom (X.fromSpecStalk x ⁻¹ᵁ U).ι :=
        MorphismProperty.of_isPullback (P := @IsAffineHom)
          (isPullback_morphismRestrict (X.fromSpecStalk x) U) hι
      exact isAffine_of_isAffineHom (X.fromSpecStalk x ⁻¹ᵁ U).ι
    have hg : genericPoint X ∈ Set.range (X.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact (genericPoint_spec X).specializes trivial
    obtain ⟨q, hq⟩ := hg
    have hqU : q ∈ X.fromSpecStalk x ⁻¹ᵁ U := by
      change X.fromSpecStalk x q ∈ U
      rw [hq]
      exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hne)
    obtain ⟨a, ha⟩ := @GlobalTheory.exists_eq_basicOpen_of_isAffineOpen_of_uniqueFactorization (X.presheaf.stalk x) (X.presheaf.stalk x).commRing hd hn (hufd x)
      (X.fromSpecStalk x ⁻¹ᵁ U) hA ⟨q, hqU⟩
    have h : ∀ q : PrimeSpectrum (X.presheaf.stalk x),
        X.fromSpecStalk x q ∈ U ↔ a ∉ q.asIdeal := fun q =>
      iff_of_eq (congrArg (fun V => q ∈ V) ha)
    have ha0 : a ≠ 0 := fun h0 => (h q).1 hqU (h0 ▸ zero_mem _)
    rw [stalkId_vanishingIdeal_compl U x a h]
    exact exists_radical_span_singleton_eq ha0
  obtain ⟨D, hD⟩ := EffCartierData.exists_idealSheaf_eq hE
  refine ⟨D.lb, D.canonical, D.isLB_lb, TopologicalSpace.Opens.ext ?_⟩
  refine D.coe_nonzeroLocus_canonical.trans ?_
  rw [hD]
  exact compl_compl _

end GlobalTheory.AffineComplement
