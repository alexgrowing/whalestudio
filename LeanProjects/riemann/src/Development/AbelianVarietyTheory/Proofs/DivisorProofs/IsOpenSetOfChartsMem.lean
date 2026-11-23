import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.ProjLineOpen
open GlobalTheory.ProjSpace

variable (R : Type) [CommRing R]

def vec (i : Fin 2) : Fin 2 → Polynomial R := fun j => if j = i then 1 else Polynomial.X

theorem span_vec (i : Fin 2) : Ideal.span (Set.range (vec R i)) = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, by simp [vec]⟩) isUnit_one

def cmap (i : Fin 2) : Sp (Polynomial R) ⟶ PSpace R 1 := pt Polynomial.C (vec R i) (span_vec R i)

def toPoly (i : Fin 2) : MvPolynomial {j : Fin 2 // j ≠ i} R →+* Polynomial R :=
  MvPolynomial.eval₂Hom Polynomial.C fun _ => Polynomial.X

theorem ne_rev (i : Fin 2) : Fin.rev i ≠ i := by fin_cases i <;> decide

instance (i : Fin 2) : Subsingleton {j : Fin 2 // j ≠ i} :=
  ⟨fun a b => Subtype.ext (Fin.ext (by
    have h1 := Fin.val_ne_of_ne a.2; have h2 := Fin.val_ne_of_ne b.2
    have := a.1.2; have := b.1.2; have := i.2; omega))⟩

def fromPoly (i : Fin 2) : Polynomial R →+* MvPolynomial {j : Fin 2 // j ≠ i} R :=
  Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X ⟨Fin.rev i, ne_rev i⟩)

def polyEquiv (i : Fin 2) : MvPolynomial {j : Fin 2 // j ≠ i} R ≃+* Polynomial R :=
  RingEquiv.ofRingHom (toPoly R i) (fromPoly R i)
    (Polynomial.ringHom_ext (fun r => by simp [fromPoly, toPoly]) (by simp [fromPoly, toPoly]))
    (MvPolynomial.ringHom_ext (fun r => by simp [fromPoly, toPoly]) (fun t => by
      simp [fromPoly, toPoly]; exact congrArg _ (Subsingleton.elim _ _)))

instance (i : Fin 2) : IsIso (spMap (toPoly R i)) :=
  inferInstanceAs (IsIso (Spec.map (polyEquiv R i).toCommRingCatIso.hom))

theorem toPoly_dehom (i : Fin 2) :
    (toPoly R i).comp (RingHomClass.toRingHom (dehom R 1 i)) =
      MvPolynomial.eval₂Hom Polynomial.C (vec R i) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
  · simp [toPoly]
  · by_cases h : j = i
    · subst h; simp [vec]
    · have := dehom_X_of_ne R 1 i ⟨j, h⟩
      simp only [RingHom.comp_apply, RingHom.coe_coe] at this ⊢
      rw [this]; simp [toPoly, vec, h]

theorem chartι_eq (i : Fin 2) : spMap (toPoly R i) ≫ chartι R 1 i = cmap R i := by
  have hu : IsUnit (MvPolynomial.eval₂Hom Polynomial.C (vec R i) (MvPolynomial.X i)) := by
    simp [vec]
  rw [cmap, pt, ProjPoint.ofHom_eq_awayι _ _ _ one_pos (X_mem R 1 i) hu, chartι, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  refine ProjPoint.eq_awayLift _ _ hu (X_mem R 1 i) _ fun n a ha => ?_
  rw [RingHom.comp_apply, awayToPoly_mk R 1 i n a ha]
  have := congrArg (fun φ => φ a) (toPoly_dehom R i)
  simp only [RingHom.comp_apply, RingHom.coe_coe] at this
  rw [this]
  simp [vec]

instance (i : Fin 2) : IsOpenImmersion (cmap R i) := by
  rw [← chartι_eq]; infer_instance

theorem range_cmap (i : Fin 2) : Set.range (cmap R i) = (chart R 1 i : Set (PSpace R 1)) := by
  have e := congrArg (fun U : (PSpace R 1).Opens => (U : Set (PSpace R 1)))
    ((Scheme.Hom.opensRange_comp_of_isIso (spMap (toPoly R i)) (chartι R 1 i)).trans (opensRange_chartι R 1 i))
  simp only [Scheme.Hom.coe_opensRange] at e
  rwa [chartι_eq] at e

theorem cmap_str (i : Fin 2) : cmap R i ≫ PSpace.str R 1 = spMap (algebraMap R (Polynomial R)) := by
  rw [cmap, pt_str, Polynomial.algebraMap_eq]

theorem cmap_preimage (i : Fin 2) : cmap R i ⁻¹ᵁ chart R 1 (Fin.rev i) = spOpen (Polynomial.X : Polynomial R) := by
  rw [cmap, pt_preimage_chart]; simp [vec, ne_rev i]

theorem pt_congr {A : Type} [CommRing A] {c c' : R →+* A} (hc : c = c') {v v' : Fin 2 → A}
    (hv : Ideal.span (Set.range v) = ⊤) (hv' : Ideal.span (Set.range v') = ⊤) (u : Aˣ) (h : v' = u • v) :
    pt c v hv = pt c' v' hv' := by
  subst hc; exact (pt_eq_pt_iff c hv hv').2 ⟨u, h⟩

theorem overlap_eq :
    spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))) ≫ cmap R 0 =
      spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) :
        Localization.Away (Polynomial.X : Polynomial R))).toRingHom ≫ cmap R 1 := by
  set L := Localization.Away (Polynomial.X : Polynomial R)
  set s : L := IsLocalization.Away.invSelf (Polynomial.X : Polynomial R)
  have hs : algebraMap (Polynomial R) L Polynomial.X * s = 1 := IsLocalization.Away.mul_invSelf _
  rw [cmap, cmap, spMap_pt, spMap_pt]
  refine pt_congr R (RingHom.ext fun r => ?_) _ _ (Units.mkOfMulEqOne s _ (by rw [mul_comm]; exact hs)) ?_
  · rw [RingHom.comp_apply, RingHom.comp_apply, ← Polynomial.algebraMap_eq]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
    exact (IsScalarTower.algebraMap_apply R (Polynomial R) L r).symm
  · refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · simp [vec, s, Units.smul_def]
    · have h1 : vec R 1 1 = 1 := by simp [vec]
      have h2 : vec R 0 1 = Polynomial.X := by simp [vec]
      simp only [Units.smul_def, Units.val_mkOfMulEqOne, Pi.smul_apply, Function.comp_apply, smul_eq_mul,
        h1, h2, map_one]
      rw [mul_comm]; exact hs.symm

theorem exists_of_cmap_eq {x x' : Sp (Polynomial R)} (h : cmap R 0 x = cmap R 1 x') :
    ∃ u : Sp (Localization.Away (Polynomial.X : Polynomial R)),
      spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))) u = x ∧
      spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) :
        Localization.Away (Polynomial.X : Polynomial R))).toRingHom u = x' := by
  have h1 : cmap R 0 x ∈ (chart R 1 1 : Set (PSpace R 1)) := by
    rw [← range_cmap R 1, h]; exact ⟨x', rfl⟩
  have h2 : x ∈ cmap R 0 ⁻¹ᵁ chart R 1 (Fin.rev 0) := h1
  rw [cmap_preimage] at h2
  have h3 : (x : PrimeSpectrum (Polynomial R)) ∈
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R) : Set (PrimeSpectrum (Polynomial R))) := h2
  rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away (Polynomial.X : Polynomial R))] at h3
  obtain ⟨u, hu⟩ := h3
  refine ⟨u, hu, (cmap R 1).isOpenEmbedding.injective ?_⟩
  have e := congrArg (fun φ => φ u) (overlap_eq R)
  exact (e.symm.trans (congrArg (cmap R 0) hu)).trans h

theorem isClosedMap_str : IsClosedMap (PSpace.str R 1) := by
  haveI := isProper_str R 1
  exact (PSpace.str R 1).isClosedMap

theorem str_cmap (i : Fin 2) (x : Sp (Polynomial R)) :
    PSpace.str R 1 (cmap R i x) = spMap (algebraMap R (Polynomial R)) x :=
  congrArg (fun φ => φ x) (cmap_str R i)

end GlobalTheory.ProjLineOpen

open GlobalTheory.ProjLineOpen GlobalTheory.ProjSpace in

theorem GlobalTheory.isOpen_setOf_charts_mem (R : Type) [CommRing R] (Y : Scheme.{0}) (g₀ g₁ : Sp (Polynomial R) ⟶ Y)
    (hg : spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))) ≫ g₀ =
      spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) :
        Localization.Away (Polynomial.X : Polynomial R))).toRingHom ≫ g₁)
    (W : Y.Opens) :
    IsOpen {τ : Sp R | ∀ x : Sp (Polynomial R), spMap (algebraMap R (Polynomial R)) x = τ →
      g₀ x ∈ W ∧ g₁ x ∈ W} := by
  set O : Set (PSpace R 1) := cmap R 0 '' (g₀ ⁻¹ᵁ W : Set _) ∪ cmap R 1 '' (g₁ ⁻¹ᵁ W : Set _) with hOdef
  have hO : IsOpen O := ((cmap R 0).isOpenEmbedding.isOpenMap _ (g₀ ⁻¹ᵁ W).isOpen).union
    ((cmap R 1).isOpenEmbedding.isOpenMap _ (g₁ ⁻¹ᵁ W).isOpen)
  have hgu : ∀ u, g₀ (spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))) u) =
      g₁ (spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) :
        Localization.Away (Polynomial.X : Polynomial R))).toRingHom u) := fun u => congrArg (fun φ => φ u) hg
  have key : {τ : Sp R | ∀ x : Sp (Polynomial R), spMap (algebraMap R (Polynomial R)) x = τ →
      g₀ x ∈ W ∧ g₁ x ∈ W} = (PSpace.str R 1 '' Oᶜ)ᶜ := by
    ext τ
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_image, not_exists, not_and]
    constructor
    · intro H q hq hτ
      obtain ⟨i, hi⟩ := exists_mem_chart R 1 q
      rw [← SetLike.mem_coe, ← range_cmap R i] at hi
      obtain ⟨x, rfl⟩ := hi
      have hx := (str_cmap R i x).symm.trans hτ
      refine hq ?_
      fin_cases i
      · exact Or.inl ⟨x, (H x hx).1, rfl⟩
      · exact Or.inr ⟨x, (H x hx).2, rfl⟩
    · intro H x hx
      have c0 : cmap R 0 x ∈ O := by
        by_contra hc; exact H _ hc ((str_cmap R 0 x).trans hx)
      have c1 : cmap R 1 x ∈ O := by
        by_contra hc; exact H _ hc ((str_cmap R 1 x).trans hx)
      constructor
      · rcases c0 with ⟨x', hx', e⟩ | ⟨x', hx', e⟩
        · rw [← (cmap R 0).isOpenEmbedding.injective e]; exact hx'
        · obtain ⟨u, rfl, rfl⟩ := exists_of_cmap_eq R e.symm
          show _ ∈ W
          rw [hgu]; exact hx'
      · rcases c1 with ⟨x', hx', e⟩ | ⟨x', hx', e⟩
        · obtain ⟨u, rfl, rfl⟩ := exists_of_cmap_eq R e
          show _ ∈ W
          rw [← hgu]; exact hx'
        · rw [← (cmap R 1).isOpenEmbedding.injective e]; exact hx'
  rw [key]
  exact (isClosedMap_str R _ hO.isClosed_compl).isOpen_compl
