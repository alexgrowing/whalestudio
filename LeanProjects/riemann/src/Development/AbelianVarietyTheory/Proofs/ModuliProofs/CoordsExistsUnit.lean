import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NotMemBasicOpenOfGeom
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.AwayLiftCompFromZeroRingHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIdealOfLocally
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsRingBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaConstantsUniqueUpToUnit
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasTh
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaPointsVanishingIdealRadicalHomogeneous
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.ZM GlobalTheory.IndefiniteRowSideFullHecke.ThetaCosetLabels

noncomputable section
namespace GlobalTheory.ThetaObjCompare
attribute [local instance] MvPolynomial.gradedAlgebra

section Coords
open MvPolynomial HomogeneousIdeal
variable {σ B R R' : Type} [CommRing B] [CommRing R] [CommRing R'] {y : Sp R ⟶ PJ σ B} {β : B →+* R} {v w : σ → R}

theorem map_irrelevant_iff (β : B →+* R) (v : σ → R) :
    (irrelevant (homogeneousSubmodule σ B)).toIdeal.map (eval₂Hom β v) = ⊤ ↔ Ideal.span (Set.range v) = ⊤ := by
  suffices h : (irrelevant (homogeneousSubmodule σ B)).toIdeal.map (eval₂Hom β v) = Ideal.span (Set.range v) by rw [h]
  refine le_antisymm (Ideal.map_le_iff_le_comap.2 fun F hF => ?_) (Ideal.span_le.2 ?_)
  · have h0 : homogeneousComponent 0 F = 0 := by
      have := (mem_irrelevant_iff _ F).1 hF
      rwa [GradedRing.proj_apply, ← decomposition.decompose'_apply] at *
    have h1 : F ∈ Ideal.span (Set.range (X : σ → MvPolynomial σ B)) := by
      rw [← Set.image_univ, mem_ideal_span_X_image]
      intro m hm
      by_contra hc
      have : m = 0 := by ext i; by_contra hi; exact hc ⟨i, trivial, hi⟩
      subst this
      rw [homogeneousComponent_zero, map_eq_zero_iff _ (C_injective _ _)] at h0
      exact mem_support_iff.1 hm h0
    refine (Ideal.span_le.2 ?_ : _ ≤ Ideal.comap (eval₂Hom β v) (Ideal.span (Set.range v))) h1
    rintro _ ⟨i, rfl⟩
    exact Ideal.mem_comap.2 (by rw [eval₂Hom_X']; exact Ideal.subset_span ⟨i, rfl⟩)
  · rintro _ ⟨i, rfl⟩
    rw [← eval₂Hom_X' β v i]
    exact Ideal.mem_map_of_mem _ (mem_irrelevant_of_mem _ one_pos (isHomogeneous_X B i))

theorem hasCoords_iff : HasCoords y β v ↔ ∃ h, y = ProjPoint.ofHom (homogeneousSubmodule σ B) (eval₂Hom β v) h := by
  refine ⟨fun ⟨h, e⟩ => ⟨?_, e⟩, fun ⟨h, e⟩ => ⟨_, e⟩⟩
  have := ProjPoint.map_irrelevant_comp _ h (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
  rwa [← RingHom.comp_assoc, ← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id, RingHom.id_comp] at this

theorem coords_span (h : HasCoords y β v) : Ideal.span (Set.range v) = ⊤ :=
  (map_irrelevant_iff β v).1 (hasCoords_iff.1 h).1

theorem exists_hasCoords (β : B →+* R) (hv : Ideal.span (Set.range v) = ⊤) : ∃ y : Sp R ⟶ PJ σ B, HasCoords y β v :=
  ⟨_, hasCoords_iff.2 ⟨(map_irrelevant_iff β v).2 hv, rfl⟩⟩

theorem coords_eq {y' : Sp R ⟶ PJ σ B} (h : HasCoords y β v) (h' : HasCoords y' β v) : y = y' :=
  h.2.trans h'.2.symm

theorem coords_over (h : HasCoords y β v) :
    y ≫ Proj.toSpecZero _ ≫ spMap (algebraMap B ↥(homogeneousSubmodule σ B 0)) = spMap β := by
  replace h := hasCoords_iff.1 h
  obtain ⟨h, rfl⟩ := h
  rw [← Category.assoc, ProjPoint.ofHom_toSpecZero]
  refine (spMap_comp _ _).trans (congrArg spMap (RingHom.ext fun r => eval₂Hom_C β v r))

theorem coords_baseChange (h : HasCoords y β v) (φ : R →+* R') :
    HasCoords (spMap φ ≫ y) (φ.comp β) fun a => φ (v a) := by
  replace h := hasCoords_iff.1 h
  obtain ⟨h, rfl⟩ := h
  have e := comp_eval₂Hom β v φ
  refine hasCoords_iff.2 ⟨e ▸ ProjPoint.map_irrelevant_comp _ h φ, (ProjPoint.SpecMap_ofHom _ _ h φ).trans ?_⟩
  congr 1

theorem coords_unit_mul (h : HasCoords y β v) (u : Rˣ) : HasCoords y β fun a => u * v a := by
  have hs : Ideal.span (Set.range fun a => u * v a) = ⊤ := by
    rw [_root_.eq_top_iff, ← coords_span h, Ideal.span_le]
    rintro _ ⟨a, rfl⟩
    simpa using Ideal.mul_mem_left (Ideal.span (Set.range fun a => u * v a)) (u⁻¹ : Rˣ) (Ideal.subset_span ⟨a, rfl⟩)
  replace h := hasCoords_iff.1 h
  obtain ⟨h, rfl⟩ := h
  refine hasCoords_iff.2 ⟨(map_irrelevant_iff _ _).2 hs, (ProjPoint.ofHom_eq_of_scale _ h _ (u : R) fun n F hF => ?_).symm⟩
  have hF' : F.IsHomogeneous n := hF
  simp only [coe_eval₂Hom, eval₂_eq, Finset.mul_sum, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [show ∑ i ∈ d.support, d i = n from by
    rw [← hF' (mem_support_iff.1 hd), Finsupp.weight_apply]; simp [Finsupp.sum]]
  ring

theorem coords_minor (h : HasCoords y β v) (h' : HasCoords y β w) {i : σ} (hi : IsUnit (v i)) (a c : σ) :
    v a * w c = v c * w a := by
  replace h := hasCoords_iff.1 h
  obtain ⟨h, rfl⟩ := h
  obtain ⟨h', e⟩ := hasCoords_iff.1 h'
  have hX : X i ∈ homogeneousSubmodule σ B 1 := isHomogeneous_X B i
  have hi₁ : IsUnit (eval₂Hom β v (X i)) := by simpa using hi
  have hi₂ : IsUnit (eval₂Hom β w (X i)) := by
    have := ProjPoint.ofHom_preimage_basicOpen _ _ h' one_pos hX
    rw [← e, ProjPoint.ofHom_preimage_basicOpen _ _ h one_pos hX] at this
    rw [← Ideal.span_singleton_eq_top, ← PrimeSpectrum.zeroLocus_empty_iff_eq_top, PrimeSpectrum.zeroLocus_span,
      ← Set.compl_univ_iff, ← PrimeSpectrum.basicOpen_eq_zeroLocus_compl, ← this,
      PrimeSpectrum.basicOpen_eq_zeroLocus_compl, Set.compl_univ_iff, ← PrimeSpectrum.zeroLocus_span,
      PrimeSpectrum.zeroLocus_empty_iff_eq_top, Ideal.span_singleton_eq_top]
    exact hi₁
  rw [ProjPoint.ofHom_eq_awayι _ _ h one_pos hX hi₁, ProjPoint.ofHom_eq_awayι _ _ h' one_pos hX hi₂, cancel_mono] at e
  have e' := spMap_injective e
  have k₁ := fun a => ProjPoint.awayLift_mk_mul (homogeneousSubmodule σ B) _ hi₁ hX 1 (X a) (isHomogeneous_X B a)
  have k₂ := fun a => ProjPoint.awayLift_mk_mul (homogeneousSubmodule σ B) _ hi₂ hX 1 (X a) (isHomogeneous_X B a)
  simp only [← e', pow_one, eval₂Hom_X'] at k₁ k₂
  rw [← k₁ a, ← k₁ c, ← k₂ a, ← k₂ c]; ring

theorem coords_exists_unit (h : HasCoords y β v) (h' : HasCoords y β w) : ∃ u : Rˣ, ∀ a, v a = u * w a := by
  refine ThetaClosed.exists_unit_of_minors (coords_span h) (coords_span h') fun a c => ?_
  refine SegreCoord.eq_of_away fun q => ?_
  obtain ⟨i, hi⟩ : ∃ i, v i ∉ q.asIdeal := by
    by_contra! hc
    exact q.2.ne_top (top_le_iff.1 (coords_span h ▸ Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hc i)))
  refine ⟨v i, hi, ?_⟩
  simpa only [map_mul] using coords_minor (coords_baseChange h (algebraMap R (Localization.Away (v i))))
    (coords_baseChange h' _) (i := i) (IsLocalization.Away.algebraMap_isUnit _) a c

end Coords

section Terms
variable {g M : ℕ} {I B : Type} [CommRing B] {ζ : Bˣ} {S S' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B}

theorem isMonHom_mul {G : Over S} [GrpObj G] [IsCommMonObj G] (f h : G ⟶ G) [IsMonHom f] [IsMonHom h] :
    IsMonHom (f * h) where
  one_hom := by rw [MonObj.comp_mul, IsMonHom.one_hom, IsMonHom.one_hom, MonObj.one_eq_one, _root_.mul_one]
  mul_hom := by
    have e : ∀ k : G ⟶ G, [IsMonHom k] → (k ⊗ₘ k) ≫ μ[G] = (fst G G ≫ k) * (snd G G ≫ k) := fun k _ => by
      rw [MonObj.mul_eq_mul, MonObj.comp_mul]
      simp
    rw [MonObj.comp_mul, IsMonHom.mul_hom, IsMonHom.mul_hom, e, e, MonObj.mul_eq_mul, MonObj.comp_mul]
    simp only [← Category.assoc, tensorHom_fst, tensorHom_snd, MonObj.comp_mul]
    exact mul_mul_mul_comm _ _ _ _

theorem isMonHom_ev (X : ThObj g M I ζ s) (t : EndTerm I) : IsMonHom (X.ev t) := by
  letI := X.P.isAb.comm
  induction t with
  | var i => exact X.endo_hom i
  | one => exact inferInstanceAs (IsMonHom (𝟙 _))
  | add t t' h h' => exact isMonHom_mul (X.ev t) (X.ev t')
  | neg t h => exact inferInstanceAs (IsMonHom (X.ev t)⁻¹)
  | mul t t' h h' => exact inferInstanceAs (IsMonHom (X.ev t' ≫ X.ev t))

theorem ev_comm {X' : ThObj g M I ζ s'} {X : ThObj g M I ζ s} {f : S' ⟶ S} {φ : X'.P.A.left ⟶ X.P.A.left}
    (h : IsGrpPullback X'.P.A X.P.A f φ) (he : ∀ i, (X'.endo i).left ≫ φ = φ ≫ (X.endo i).left) (t : EndTerm I) :
    (X'.ev t).left ≫ φ = φ ≫ (X.ev t).left := by
  let Φ : Over.mk (X'.P.A.hom ≫ f) ⟶ X.P.A := Over.homMk φ h.1.w
  suffices H : pushHom h X'.P.A (X'.ev t) = Φ ≫ X.ev t from congrArg (fun z => z.left) H
  induction t with
  | var i => exact Over.OverMorphism.ext (he i)
  | one => exact Over.OverMorphism.ext ((Category.id_comp φ).trans (Category.comp_id φ).symm)
  | add t t' H H' => exact (map_mul _ (X'.ev t) (X'.ev t')).trans (by rw [H, H']; exact (MonObj.comp_mul _ _ _).symm)
  | neg t H => exact (map_inv _ (X'.ev t)).trans (by rw [H]; exact (GrpObj.comp_inv _ _).symm)
  | mul t t' H H' =>
    have e : (X'.ev t).left ≫ φ = φ ≫ (X.ev t).left := congrArg (fun z => z.left) H
    have e' : (X'.ev t').left ≫ φ = φ ≫ (X.ev t').left := congrArg (fun z => z.left) H'
    refine Over.OverMorphism.ext ?_
    show ((X'.ev t').left ≫ (X'.ev t).left) ≫ φ = φ ≫ (X.ev t').left ≫ (X.ev t).left
    rw [Category.assoc, e, ← Category.assoc, e', Category.assoc]

end Terms

end GlobalTheory.ThetaObjCompare
end
