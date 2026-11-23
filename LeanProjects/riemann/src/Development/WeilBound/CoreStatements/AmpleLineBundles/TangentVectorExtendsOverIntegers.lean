import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueSemilinearStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelIsBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModelStatement
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace CoverDenseAlt

theorem dualMap_comp_dualMap' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R')
    (g : R' →+* R'') : (dualMap g).comp (dualMap f) = dualMap (g.comp f) := by
  ext a <;> simp [dualMap]

theorem dualMap_comp_epsMul_ample_line_bundles {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (s : R) :
    (dualMap f).comp (GlobalTheory.CompanionTheory.Ar.epsMul s) = (GlobalTheory.CompanionTheory.Ar.epsMul (f s)).comp (dualMap f) := by
  ext a <;> simp [dualMap, GlobalTheory.CompanionTheory.Ar.epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem spMap_comp_spMap_ample_line_bundles {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R')
    (g : R' →+* R'') : spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem tangent_vector_extends_over_integers : ∀ (O K : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (S : Scheme.{0}) (x : Sp O ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (E : Type) [AddCommGroup E] [Module O E] (M : LieModel G x E) (v : epsAt (spMap (algebraMap O K) ≫ x) ⟶ G), IsTanAt G _ v → (∀ (P : Ideal O) [P.IsMaximal] (c : Localization.AtPrime P →+* K), c.comp (algebraMap O _) = algebraMap O K → ∃ w : epsAt (spMap (algebraMap O (Localization.AtPrime P)) ≫ x) ⟶ G, IsTanAt G _ w ∧ v.left = spMap (dualMap c) ≫ w.left) → ∃ e, M.Lifts (algebraMap O K) (𝟙 G.left) e v := by
  intro O K _ _ _ _ _ S x G _ _ _ E _ _ M v hv hloc
  obtain ⟨EK, _, _, ⟨MK⟩⟩ := lieModel_exists S G K (spMap (algebraMap O K) ≫ x)
  obtain ⟨jK, hjK, -⟩ := LieBaseChange.existsUnique_semilinear_lifts S G O K (algebraMap O K) x E EK M MK
  obtain ⟨eK, rfl⟩ := MK.onto v hv
  let I : Ideal O :=
    { carrier := {a | ∃ e, jK e = algebraMap O K a • eK}
      add_mem' := by
        rintro a b ⟨e, he⟩ ⟨e', he'⟩
        exact ⟨e + e', by rw [map_add, he, he', map_add, add_smul]⟩
      zero_mem' := ⟨0, by rw [map_zero, map_zero, zero_smul]⟩
      smul_mem' := by
        rintro a b ⟨e, he⟩
        refine ⟨a • e, ?_⟩
        rw [jK.map_smulₛₗ, he, smul_eq_mul, map_mul, mul_smul] }
  suffices h1 : (1 : O) ∈ I by
    obtain ⟨e, he⟩ := h1
    rw [map_one, one_smul] at he
    refine ⟨e, ?_⟩
    rw [← he]
    exact hjK e
  by_contra h1
  obtain ⟨P, hP, hIP⟩ := I.exists_le_maximal ((Ideal.ne_top_iff_one I).2 h1)
  have hunit : ∀ y : P.primeCompl, IsUnit (algebraMap O K y) := by
    intro y
    refine IsUnit.mk0 _ ?_
    intro h0
    have h2 : (y : O) = 0 := IsFractionRing.injective O K (by rw [h0, map_zero])
    exact y.2 (h2 ▸ P.zero_mem)
  let c : Localization.AtPrime P →+* K := IsLocalization.lift hunit
  have hc : c.comp (algebraMap O (Localization.AtPrime P)) = algebraMap O K := IsLocalization.lift_comp hunit
  obtain ⟨w, hw, hvw⟩ := hloc P c hc
  obtain ⟨EP, _, _, ⟨MP⟩⟩ := lieModel_exists S G (Localization.AtPrime P)
    (spMap (algebraMap O (Localization.AtPrime P)) ≫ x)
  obtain ⟨jP, hjP, -⟩ := LieBaseChange.existsUnique_semilinear_lifts S G O (Localization.AtPrime P)
    (algebraMap O (Localization.AtPrime P)) x E EP M MP
  obtain ⟨eP, rfl⟩ := MP.onto w hw
  letI : Module O EP := Module.compHom EP (algebraMap O (Localization.AtPrime P))
  haveI : IsScalarTower O (Localization.AtPrime P) EP := ⟨fun a b m => by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  let β : E →ₗ[O] EP :=
    { toFun := jP
      map_add' := map_add jP
      map_smul' := fun a e => by
        rw [jP.map_smulₛₗ]
        rfl }
  have hbc : IsBaseChange (Localization.AtPrime P) β :=
    (LieProj.lie_finite_projective_baseChange S G O x E M).2.2 (Localization.AtPrime P) EP MP β
      (fun e => by
        have h2 := hjP e
        simp only [LieModel.Lifts, Category.comp_id] at h2
        exact h2)
  haveI : IsLocalizedModule P.primeCompl β :=
    (isLocalizedModule_iff_isBaseChange P.primeCompl (Localization.AtPrime P) β).2 hbc
  obtain ⟨⟨e, s⟩, hes⟩ := IsLocalizedModule.surj P.primeCompl β eP
  have hes' : jP e = algebraMap O (Localization.AtPrime P) (s : O) • eP := hes.symm
  have hmem : (s : O) ∈ I := by
    refine ⟨e, ?_⟩
    apply MK.inj
    apply Over.OverMorphism.ext
    have h1 := hjK e
    have h2 := hjP e
    simp only [LieModel.Lifts, Category.comp_id] at h1 h2
    have h3 : (MK.pt (jK e)).left = spMap (dualMap c) ≫ (MP.pt (jP e)).left := by
      rw [h1, h2, ← Category.assoc, spMap_comp_spMap_ample_line_bundles, dualMap_comp_dualMap', hc]
    rw [h3, hes', MP.smul, MK.smul, hvw, ← Category.assoc, ← Category.assoc]
    congr 1
    have h4 := spMap_comp_spMap_ample_line_bundles (GlobalTheory.CompanionTheory.Ar.epsMul (algebraMap O (Localization.AtPrime P) (s : O))) (dualMap c)
    have h5 := spMap_comp_spMap_ample_line_bundles (dualMap c) (GlobalTheory.CompanionTheory.Ar.epsMul (c (algebraMap O (Localization.AtPrime P) (s : O))))
    rw [← RingHom.comp_apply c, hc] at h5
    simp only [spMap] at h4 h5 ⊢
    rw [h4, dualMap_comp_epsMul_ample_line_bundles, h5]
    rw [← RingHom.comp_apply c, hc]
  exact s.2 (hIP hmem)

end CoverDenseAlt
