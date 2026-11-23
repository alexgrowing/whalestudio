import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsProjCoordRepresentationHomogeneousIdealFlaStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNonzeroCoordinateAffineChartStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionCoordinatesPullIsoNonzeroLocusStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DehomogenisationIsRadicalAndTorsionFreeStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM

theorem reduced_flat_of_charts {Z S : Scheme.{0}} (s : Z ⟶ S) (U : Z.Opens) {κ : Type} (Y : κ → Scheme.{0})
    (x : ∀ i, Y i ⟶ Z) (hx : ∀ i, IsOpenImmersion (x i)) (hr : ∀ i, IsReduced (Y i)) (hf : ∀ i, Flat (x i ≫ s))
    (hc : ∀ z ∈ U, ∃ i, z ∈ Set.range (x i)) : IsReduced U.toScheme ∧ Flat (U.ι ≫ s) := by
  let 𝒰 : U.toScheme.OpenCover := Scheme.Cover.mkOfCovers κ (fun i => pullback U.ι (x i)) (fun i => pullback.fst U.ι (x i))
    (fun z => by
      obtain ⟨i, y, hy⟩ := hc z.1 z.2
      have : z ∈ Set.range (pullback.fst U.ι (x i)) := by
        rw [Scheme.Pullback.range_fst]
        exact ⟨y, hy⟩
      exact ⟨i, this⟩) (fun i => inferInstance)
  constructor
  · haveI : ∀ i, IsReduced (𝒰.X i) := fun i =>
      by
      change IsReduced (pullback U.ι (x i) :)
      haveI := hr i
      exact isReduced_of_isOpenImmersion (pullback.snd U.ι (x i))
    exact IsReduced.of_openCover _ 𝒰
  · haveI : IsZariskiLocalAtSource @Flat := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat)
    refine IsZariskiLocalAtSource.of_openCover (P := @Flat) 𝒰 (fun i => ?_)
    change Flat (pullback.fst U.ι (x i) ≫ U.ι ≫ s)
    rw [← Category.assoc, pullback.condition, Category.assoc]
    haveI := hf i
    haveI := hx i
    exact MorphismProperty.comp_mem @Flat _ _ inferInstance (hf i)

theorem flat_spMap_of_torsionFree {o σ : Type} [CommRing o] [IsDedekindDomain o] (J : Ideal (MvPolynomial σ o))
    (h : ∀ (c : o) F, c ≠ 0 → MvPolynomial.C c * F ∈ J → F ∈ J) :
    Flat (spMap ((Ideal.Quotient.mk J).comp MvPolynomial.C)) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  have : Module.IsTorsionFree o (MvPolynomial σ o ⧸ J) := by
    refine Module.IsTorsionFree.of_smul_eq_zero ?_
    intro c y hy
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective y
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      rw [Ideal.Quotient.eq_zero_iff_mem]
      apply h c F hc
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← MvPolynomial.smul_eq_C_mul]
      exact hy
  have hfl : Module.Flat o (MvPolynomial σ o ⧸ J) := inferInstance
  exact (RingHom.flat_algebraMap_iff.2 hfl :)

theorem nonempty_MMPre : ∀ (o : Type) [CommRing o] [IsDedekindDomain o] (g n N' : ℕ) (I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)), 0 < N' → I.IsRadical → (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) → (∀ (c : o) F, c ≠ 0 → MvPolynomial.C c * F ∈ I → F ∈ I) → Nonempty (MMPre n N' I) := by
  intro o _ _ g n N' I hN hrad hhom htf
  haveI : NeZero (N' ^ 2) := ⟨by positivity⟩
  obtain ⟨Z, s, M, th, hproj, hrep, hfp, -⟩ := GlobalTheory.T.exists_projCoordRepresentation_homogeneousIdeal_flat o (Ix g (N' ^ 2)) I 0 hhom
  obtain ⟨N, j, hj, hjs⟩ := hproj ⟨0⟩
  haveI := hfp (IsNoetherian.noetherian I)
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian s
  let U : Z.Opens := ⟨⋂ a, ⋃ c, (Out.nonzeroLocus (th (a + (N' / n) • c)) : Set Z),
    isOpen_iInter_of_finite fun a => isOpen_iUnion fun c => (Out.nonzeroLocus _).2⟩
  have hU : ∀ z : Z, z ∈ U ↔ ∀ a, ∃ c, z ∈ Out.nonzeroLocus (th (a + (N' / n) • c)) := fun z => by
    change z ∈ ⋂ a, ⋃ c, (Out.nonzeroLocus (th (a + (N' / n) • c)) : Set Z) ↔ _
    simp only [Set.mem_iInter, Set.mem_iUnion, SetLike.mem_coe]
  choose x hxo hxr hxs _ using fun i => GlobalTheory.T.exists_nonzeroCoordinate_affineChart o _ I Z s M th i hrep
  obtain ⟨hred, hflat⟩ := reduced_flat_of_charts s U _ x hxo
    (fun i => by
      haveI : _root_.IsReduced (MvPolynomial (Ix g (N' ^ 2)) o ⧸ (I ⊔ Ideal.span {MvPolynomial.X i - 1})) :=
        (Ideal.isRadical_iff_quotient_reduced _).1 ((GlobalTheory.T.sup_span_X_sub_one_isRadical_and_torsionFree o _ I i hhom).1 hrad)
      infer_instance)
    (fun i => by
      rw [hxs i]
      exact flat_spMap_of_torsionFree _ ((GlobalTheory.T.sup_span_X_sub_one_isRadical_and_torsionFree o _ I i hhom).2 htf))
    (fun z hz => by
      obtain ⟨c, hc⟩ := (hU z).1 hz 0
      exact ⟨_, by rw [hxr]; exact hc⟩)
  obtain ⟨hpull, -, hnz⟩ := GlobalTheory.T.sectionCoordinates_pull_iso_nonzeroLocus Z M _ th hrep.1
  obtain ⟨th', hth'⟩ := hpull U.toScheme U.ι
  refine ⟨{ MM := U.toScheme, s := U.ι ≫ s, qproj := ⟨N, U.ι ≫ j, inferInstance, inferInstance, by rw [Category.assoc, hjs]⟩
            flat := hflat, reduced := hred, de := M.pull U.ι, isLB := pull_isLB hrep.1 _, th := th', loc := ?_, pts := ?_ }⟩
  · intro R _ β y v hy hv
    rw [hth'] at hv
    refine ⟨(hrep.2.1 R β (y ≫ U.ι) v (by rw [Category.assoc, hy]) hv).2, fun q hq a => ?_⟩
    let p : Sp R := (⟨q, hq⟩ : PrimeSpectrum R)
    obtain ⟨c, hc⟩ := (hU ((y ≫ U.ι) p)).1 (by rw [Scheme.Hom.comp_apply]; exact (y p).2) a
    exact ⟨c, (hnz R _ v _ p hv).1 hc⟩
  · intro R _ β v hv
    have hspan : Ideal.span (Set.range v) = ⊤ := by
      by_contra hne
      obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
      obtain ⟨c, hc⟩ := hv.2 m hm.isPrime 0
      exact hc (hle (Ideal.subset_span ⟨_, rfl⟩))
    obtain ⟨y, ⟨hys, hyv⟩, huniq⟩ := hrep.2.2 R β v hspan hv.1
    have hrange : Set.range y ⊆ Set.range U.ι := by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι]
      refine (hU _).2 fun a => ?_
      obtain ⟨c, hc⟩ := hv.2 p.asIdeal p.isPrime a
      exact ⟨c, (hnz R y v _ p hyv).2 hc⟩
    have hl := IsOpenImmersion.lift_fac U.ι y hrange
    refine ⟨IsOpenImmersion.lift U.ι y hrange, ⟨by rw [← Category.assoc, hl, hys], by rw [hth', hl]; exact hyv⟩, ?_⟩
    rintro y' ⟨h1, h2⟩
    rw [hth'] at h2
    rw [← cancel_mono U.ι, hl]
    exact huniq _ ⟨by rw [Category.assoc, h1], h2⟩

end GlobalTheory.ZM
end
