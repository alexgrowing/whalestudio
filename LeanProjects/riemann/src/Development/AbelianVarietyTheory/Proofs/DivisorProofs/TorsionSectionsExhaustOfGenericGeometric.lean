import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSpecializesSameFibreIsIntegralHom
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfRangeSubset
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniversalTorsionPairPolAV
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.IntTerm

theorem tf_apply_eq_genericPoint {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F]
    [Algebra (FractionRing R) F] (a : Sp F) : (TF (R := R) F).hom a = genericPoint (Sp R) := by
  rw [genericPoint_eq_bot_of_affine]
  have ha : (a : PrimeSpectrum F).asIdeal = ⊥ :=
    @Ideal.eq_bot_of_prime _ _ _ (a : PrimeSpectrum F).isPrime
  have hinj : Function.Injective ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))) :=
    (algebraMap (FractionRing R) F).injective.comp (IsFractionRing.injective R (FractionRing R))
  apply PrimeSpectrum.ext
  show Ideal.comap _ (Ideal.comap _ (a : PrimeSpectrum F).asIdeal) = ⊥
  rw [ha, Ideal.comap_comap]
  exact Ideal.comap_bot_of_injective _ hinj

theorem exists_eq_section_of_finite_flat {R : Type} [CommRing R] [IsDomain R] (T : Over (Sp R))
    [IsFinite T.hom] [Flat T.hom] {C : Type} (σ : C → (𝟙_ (Over (Sp R)) ⟶ T))
    (H : ∀ t : TF (R := R) (AlgebraicClosure (FractionRing R)) ⟶ T, ∃ c, t = toUnit _ ≫ σ c)
    (K : Type) [Field K] (x : Sp K ⟶ Sp R) (p : Over.mk x ⟶ T) : ∃ c, p = toUnit _ ≫ σ c := by
  set Kb := AlgebraicClosure (FractionRing R)
  set q := p.left (IsLocalRing.closedPoint K) with hqdef
  obtain ⟨q', hq'q, hq'⟩ := Flat.generalizingMap T.hom (genericPoint_specializes (T.hom q))
  let j : Sp Kb ⟶ Sp R := (TF (R := R) Kb).hom
  obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := T.hom) (g := j) q'
    (IsLocalRing.closedPoint Kb) (by rw [hq']; exact (tf_apply_eq_genericPoint (R := R) Kb _).symm)
  have : LocallyOfFiniteType (pullback.snd T.hom j) := inferInstance
  have : IsIntegralHom (pullback.snd T.hom j) := inferInstance
  have := LocallyOfFiniteType.jacobsonSpace (pullback.snd T.hom j)
  obtain ⟨c, hcz, hcc⟩ := nonempty_inter_closedPoints (X := (pullback T.hom j : Scheme))
    (Z := closure {z}) ⟨z, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
  have hzc : z = c := GlobalTheory.eq_of_specializes_of_isIntegralHom (pullback.snd T.hom j)
    (specializes_iff_mem_closure.2 hcz) (Subsingleton.elim _ _)
  subst hzc
  let s : Sp Kb ⟶ pullback T.hom j := pointOfClosedPoint (pullback.snd T.hom j) z hcc
  have hs : s ≫ pullback.snd T.hom j = 𝟙 _ := pointOfClosedPoint_comp (pullback.snd T.hom j) z hcc
  have hsz : ∀ a, s a = z := fun a => pointOfClosedPoint_apply (pullback.snd T.hom j) z hcc a
  let t : TF (R := R) Kb ⟶ T := Over.homMk (s ≫ pullback.fst T.hom j) (by
    show (s ≫ pullback.fst T.hom j) ≫ T.hom = j
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp])
  obtain ⟨c0, hc0⟩ := H t
  have hσ : IsClosedImmersion (σ c0).left := by
    have h1 : (σ c0).left ≫ T.hom = 𝟙 _ := Over.w (σ c0)
    have : IsClosedImmersion ((σ c0).left ≫ T.hom) := by rw [h1]; infer_instance
    exact IsClosedImmersion.of_comp (σ c0).left T.hom
  have hq'mem : q' ∈ Set.range (σ c0).left := by
    let pt : Sp Kb := IsLocalRing.closedPoint Kb
    refine ⟨(toUnit (TF (R := R) Kb)).left pt, ?_⟩
    have e1 : t.left pt = q' := by
      show pullback.fst T.hom j (s pt) = q'
      rw [hsz, hz1]
    rw [← e1, hc0]
    rfl
  have hqmem : q ∈ Set.range (σ c0).left :=
    hq'q.mem_closed (σ c0).left.isClosedEmbedding.isClosed_range hq'mem
  have : IsReduced (Sp K) := inferInstance
  obtain ⟨l, hl⟩ := GlobalTheory.AbelianSubgroupFinite.exists_lift_of_range_subset (T := Sp K) p.left (σ c0).left (by
    rintro _ ⟨(a : Sp K), rfl⟩
    rw [Subsingleton.elim a (IsLocalRing.closedPoint K)]
    exact hqmem)
  have hlx : l = x := by
    have h1 : (σ c0).left ≫ T.hom = 𝟙 _ := Over.w (σ c0)
    have h2 : p.left ≫ T.hom = x := Over.w p
    rw [← h2, ← hl, Category.assoc, h1, Category.comp_id]
  refine ⟨c0, Over.OverMorphism.ext ?_⟩
  rw [Over.comp_left, ← hl, hlx]
  congr 1

end GlobalTheory.Poinc.IntTerm

namespace GlobalTheory.Poinc.IntTerm

theorem exhausts_of_generic : ∀ (V : Type) [CommRing V] [IsDomain V] [IsNoetherianRing V]
    (P : PolAV (Sp V)) (N : ℕ), 1 ≤ N → ∀ (C : Type) (b : C → (𝟙_ (Over (Sp V)) ⟶ P.A)),
    (∀ c, b c ^ N = 1) →
    (∀ p : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ P.A, p ^ N = 1 → ∃ c, p = toUnit _ ≫ b c) →
    IntTerm.Exhausts P N b := by
  intro V _ _ _ P N hN C b hb H K _ _ x p hp
  obtain ⟨h1, h2, -⟩ := GlobalTheory.abelianSchemeLaws_all.1.mulN (Sp V) P N hN
  rw [Out.mulA, ← GrpTangent.mulN_eq_pow] at h1 h2
  haveI : IsFinite (torsion P.A N).hom :=
    MorphismProperty.of_isPullback (P := @IsFinite) (GrpTangent.isPullback_torsion P.A N) h1
  haveI : Flat (torsion P.A N).hom :=
    MorphismProperty.of_isPullback (P := @Flat) (GrpTangent.isPullback_torsion P.A N) h2
  haveI : Mono (torsion.ι P.A N) := inferInstanceAs (Mono (pullback.fst _ _))
  obtain ⟨hι, hu⟩ := GlobalTheory.LamF.torsion_universal P.A N
  choose σ hσ using fun c => hu _ (b c) (hb c)
  obtain ⟨t, ht⟩ := hu _ p hp
  obtain ⟨c, hc⟩ := exists_eq_section_of_finite_flat (torsion P.A N) σ (fun t' => by
      obtain ⟨c, hc⟩ := H (t' ≫ torsion.ι P.A N) (by rw [← comp_pow, hι, comp_one])
      exact ⟨c, by rw [← cancel_mono (torsion.ι P.A N), hc, Category.assoc, hσ]⟩) K x t
  exact ⟨c, by rw [← ht, hc, Category.assoc, hσ]⟩

end GlobalTheory.Poinc.IntTerm
