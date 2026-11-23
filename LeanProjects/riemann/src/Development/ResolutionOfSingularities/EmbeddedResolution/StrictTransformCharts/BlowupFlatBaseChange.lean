import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

namespace FunctorialResolution.EmbeddedResolution

private theorem map_mem_nonZeroDivisors_of_flat {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : φ.Flat) {s : R} (hs : s ∈ nonZeroDivisors R) :
    φ s ∈ nonZeroDivisors S := by
  let _ : Algebra R S := φ.toAlgebra
  have : Module.Flat R S := hφ
  have hmul : ∀ x : S, φ s * x = s • x := by
    intro x
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  have hs1 : ∀ x : R, s * x = 0 → x = 0 := (mem_nonZeroDivisors_iff.mp hs).1
  have hL : Function.Injective (LinearMap.mulLeft R s) := by
    intro a b hab
    have h1 : s * a = s * b := by
      simpa only [LinearMap.mulLeft_apply] using hab
    have h2 : s * (a - b) = 0 := by rw [mul_sub, h1, sub_self]
    exact sub_eq_zero.mp (hs1 _ h2)
  have hinj : Function.Injective ((LinearMap.mulLeft R s).rTensor S) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := S) _ hL
  have key : ∀ t : S, φ s * t = 0 → t = 0 := by
    intro t ht
    have hsmul : s • t = 0 := by rw [← hmul t]; exact ht
    have e1 : TensorProduct.tmul R s t = (0 : TensorProduct R R S) := by
      have h3 : TensorProduct.tmul R s t = TensorProduct.tmul R (1 : R) (s • t) := by
        rw [← TensorProduct.smul_tmul, smul_eq_mul, mul_one]
      rw [h3, hsmul, TensorProduct.tmul_zero]
    have e0 : ((LinearMap.mulLeft R s).rTensor S) (TensorProduct.tmul R (1 : R) t)
        = ((LinearMap.mulLeft R s).rTensor S) 0 := by
      rw [LinearMap.rTensor_tmul, map_zero, LinearMap.mulLeft_apply, mul_one]
      exact e1
    have h1 : TensorProduct.tmul R (1 : R) t = (0 : TensorProduct R R S) := hinj e0
    have h2 : (TensorProduct.lid R S) (TensorProduct.tmul R (1 : R) t)
        = (TensorProduct.lid R S) 0 := by rw [h1]
    rwa [TensorProduct.lid_tmul, one_smul, map_zero] at h2
  exact mem_nonZeroDivisors_iff.mpr
    ⟨key, fun t ht => key t (by rw [mul_comm]; exact ht)⟩

private theorem exists_affineOpen_mem_le {Y : Scheme.{u}} (y : Y) (W : Y.Opens) (hy : y ∈ W) :
    ∃ V : Y.affineOpens, y ∈ (V : Y.Opens) ∧ (V : Y.Opens) ≤ W := by
  obtain ⟨V, hVmem, hyV, hVle⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens hy
  exact ⟨⟨V, hVmem⟩, hyV, hVle⟩

theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.comap_of_flat {X Y : Scheme.{u}} {D : X.IdealSheafData}
    (hD : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor D) (f : Y ⟶ X) [AlgebraicGeometry.Flat f] :
    FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor (D.comap f) := by
  unfold FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor at hD ⊢
  intro y
  obtain ⟨U, s, hxU, hs, hUs⟩ := hD (f.base y)
  obtain ⟨V, hyV, hVle⟩ :=
    EmbeddedResolution.exists_affineOpen_mem_le y (f ⁻¹ᵁ (U : X.Opens))
      (show y ∈ f ⁻¹ᵁ (U : X.Opens) from hxU)
  have hU2 : IsAffineOpen (U : X.Opens) := U.2
  have hV2 : IsAffineOpen (V : Y.Opens) := V.2
  have hflat : (Scheme.Hom.appLE f (U : X.Opens) (V : Y.Opens) hVle).hom.Flat := by
    apply AlgebraicGeometry.Scheme.Hom.flat_appLE <;> assumption
  refine ⟨V, (Scheme.Hom.appLE f (U : X.Opens) (V : Y.Opens) hVle).hom s, hyV, ?_, ?_⟩
  · exact _root_.FunctorialResolution.EmbeddedResolution.map_mem_nonZeroDivisors_of_flat _ hflat hs
  · rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE D f U V hVle, hUs, Ideal.map_span,
      Set.image_singleton]

theorem _root_.FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.pullback_snd_of_flat {X Y B : Scheme.{u}} {π : B ⟶ X}
    {J : X.IdealSheafData} (h : FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf π J) (g : Y ⟶ X) [AlgebraicGeometry.Flat g] :
    FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf (pullback.snd π g) (J.comap g) := by
  have e1 : (J.comap g).comap (pullback.snd π g)
      = (J.comap π).comap (pullback.fst π g) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      pullback.condition]
  refine ⟨?_, ?_⟩
  · rw [e1]
    exact h.1.comap_of_flat (pullback.fst π g)
  · intro W m hm
    have hm' : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor (J.comap (m ≫ g)) := by
      rw [Scheme.IdealSheafData.comap_comp]
      exact hm
    obtain ⟨b, hb, hbuniq⟩ := h.2 W (m ≫ g) hm'
    refine ⟨pullback.lift b m hb, ?_, ?_⟩
    · exact pullback.lift_snd b m hb
    · intro a ha
      refine pullback.hom_ext ?_ ?_
      · rw [pullback.lift_fst]
        refine hbuniq _ ?_
        show (a ≫ pullback.fst π g) ≫ π = m ≫ g
        rw [Category.assoc, pullback.condition, ← Category.assoc, ha]
      · rw [pullback.lift_snd, ha]

theorem _root_.FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.of_isPullback_of_flat {X Y B P : Scheme.{u}} {π : B ⟶ X}
    {J : X.IdealSheafData} (h : FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf π J) (g : Y ⟶ X) [AlgebraicGeometry.Flat g]
    {p : P ⟶ B} {q : P ⟶ Y} (hsq : IsPullback p q π g) :
    FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf q (J.comap g) := by
  have h3 : FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf (pullback.snd π g) (J.comap g) := h.pullback_snd_of_flat g
  have h4 := h3.iso_hom_comp hsq.isoPullback
  rwa [hsq.isoPullback_hom_snd] at h4

theorem _root_.FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.exists_isPullback_of_flat {X Y B B' : Scheme.{u}} {π : B ⟶ X}
    {J : X.IdealSheafData} (h : FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf π J) (g : Y ⟶ X) [AlgebraicGeometry.Flat g]
    {π' : B' ⟶ Y} (h' : FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf π' (J.comap g)) :
    ∃ q : B' ⟶ B, q ≫ π = π' ≫ g ∧ IsPullback q π' π g := by
  obtain ⟨e, he⟩ := h'.exists_iso (h.pullback_snd_of_flat g)
  have hc : (e.hom ≫ pullback.fst π g) ≫ π = π' ≫ g := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, he]
  exact ⟨e.hom ≫ pullback.fst π g, hc, IsPullback.of_iso_pullback ⟨hc⟩ e rfl he⟩

end FunctorialResolution.EmbeddedResolution
