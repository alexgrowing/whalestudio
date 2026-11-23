import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupOpenCover
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProper
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Saturation
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem mem_strictTransform_of_mul_mem {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) [QuasiCompact (strictTransformι π Z D)]
    (V : X₁.affineOpens) (t : Γ(X₁, V.1))
    (ht : (Z.comap π).ideal V = Ideal.span {t}) (f : Γ(X₁, V.1))
    (hf : t * f ∈ (Blowup.strictTransform π Z D).ideal V) :
    f ∈ (Blowup.strictTransform π Z D).ideal V := by
  obtain ⟨n, hn⟩ := (mem_strictTransform_ideal_iff π Z D V t ht (t * f)).mp hf
  refine (mem_strictTransform_ideal_iff π Z D V t ht f).mpr ⟨n + 1, ?_⟩
  rw [pow_succ, mul_assoc]
  exact hn

private theorem exists_ideal_eq_span_singleton_of_le {X : Scheme.{u}} (I : X.IdealSheafData)
    (U V : X.affineOpens) (e : (V : X.Opens) ≤ (U : X.Opens)) (t : Γ(X, (U : X.Opens)))
    (ht : I.ideal U = Ideal.span {t}) :
    ∃ t' : Γ(X, (V : X.Opens)), I.ideal V = Ideal.span {t'} := by
  have e' : (V : X.Opens) ≤ (𝟙 X) ⁻¹ᵁ (U : X.Opens) := e
  have h := Scheme.IdealSheafData.comap_ideal_eq_map_appLE I (𝟙 X) U V e'
  rw [Scheme.IdealSheafData.comap_id] at h
  refine ⟨(Scheme.Hom.appLE (𝟙 X) (U : X.Opens) (V : X.Opens) e').hom t, ?_⟩
  rw [h, ht, Ideal.map_span, Set.image_singleton]

private theorem restrict_basicOpen_mem_nonZeroDivisors {W : Scheme.{u}} (P : W.affineOpens)
    (d : Γ(W, (P : W.Opens))) {u : Γ(W, (P : W.Opens))}
    (hu : u ∈ nonZeroDivisors Γ(W, (P : W.Opens))) :
    (W.presheaf.map (homOfLE (W.basicOpen_le d)).op).hom u
      ∈ nonZeroDivisors Γ(W, W.basicOpen d) := by
  have := P.2.isLocalization_basicOpen d
  have halg : (algebraMap Γ(W, (P : W.Opens)) Γ(W, W.basicOpen d))
      = (W.presheaf.map (homOfLE (W.basicOpen_le d)).op).hom := rfl
  have h : algebraMap Γ(W, (P : W.Opens)) Γ(W, W.basicOpen d) u
      ∈ nonZeroDivisors Γ(W, W.basicOpen d) :=
    IsLocalization.nonZeroDivisors_le_comap (M := Submonoid.powers d)
      (S := Γ(W, W.basicOpen d)) hu
  rwa [halg] at h

private theorem mem_nonZeroDivisors_of_dvd {R : Type u} [CommRing R] {a b : R}
    (hb : b ∈ nonZeroDivisors R) (hab : a ∣ b) : a ∈ nonZeroDivisors R := by
  obtain ⟨c, hc⟩ := hab
  have key : ∀ z : R, a * z = 0 → z = 0 := by
    intro z hz
    refine (mem_nonZeroDivisors_iff.mp hb).1 z ?_
    rw [hc, mul_assoc, mul_comm c z, ← mul_assoc, hz, zero_mul]
  exact mem_nonZeroDivisors_iff.mpr ⟨key, fun z hz => key z (by rw [mul_comm]; exact hz)⟩

private theorem eq_zero_of_locally_eq_zero {W : Scheme.{u}} (U : W.Opens) (x : Γ(W, U))
    (h : ∀ w ∈ U, ∃ (P : W.Opens) (hP : P ≤ U), w ∈ P ∧
      (W.presheaf.map (homOfLE hP).op).hom x = 0) : x = 0 := by
  classical
  choose P hP hmem hzero using h
  refine TopCat.Sheaf.eq_of_locally_eq' W.sheaf
    (fun w : { w : ↥W // w ∈ U } => P w.1 w.2) U
    (fun w => homOfLE (hP w.1 w.2)) ?_ x 0 ?_
  · exact fun w hw => Opens.mem_iSup.mpr ⟨⟨w, hw⟩, hmem w hw⟩
  · intro w
    rw [map_zero]
    exact hzero w.1 w.2

theorem ker_le_ker_strictTransform_subschemeι_comp {X X₁ S : Scheme.{u}}
    (j : S ⟶ X) (π : X₁ ⟶ X) (Z : X.IdealSheafData) :
    j.ker ≤ ((Blowup.strictTransform π Z j.ker).subschemeι ≫ π).ker := by
  rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι,
    Scheme.IdealSheafData.le_map_iff_comap_le]
  exact comap_le_strictTransform π Z j.ker

theorem exists_comp_eq_strictTransform_subschemeι_comp {X X₁ S : Scheme.{u}} (j : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion j] (π : X₁ ⟶ X) (Z : X.IdealSheafData) :
    ∃ q : (Blowup.strictTransform π Z j.ker).subscheme ⟶ S,
      q ≫ j = (Blowup.strictTransform π Z j.ker).subschemeι ≫ π :=
  ⟨AlgebraicGeometry.IsClosedImmersion.lift j ((Blowup.strictTransform π Z j.ker).subschemeι ≫ π)
      (ker_le_ker_strictTransform_subschemeι_comp j π Z),
    AlgebraicGeometry.IsClosedImmersion.lift_fac j _ _⟩

def strictTransformLiftOfClosedImmersion {X X₁ S : Scheme.{u}} (j : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion j] (π : X₁ ⟶ X) (Z : X.IdealSheafData) :
    (Blowup.strictTransform π Z j.ker).subscheme ⟶ S :=
  (exists_comp_eq_strictTransform_subschemeι_comp j π Z).choose

theorem strictTransformLiftOfClosedImmersion_comp {X X₁ S : Scheme.{u}} (j : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion j] (π : X₁ ⟶ X) (Z : X.IdealSheafData) :
    strictTransformLiftOfClosedImmersion j π Z ≫ j = (Blowup.strictTransform π Z j.ker).subschemeι ≫ π :=
  (exists_comp_eq_strictTransform_subschemeι_comp j π Z).choose_spec

theorem isBlowupAlongIdealSheaf_strictTransformLiftOfClosedImmersion {X X₁ S : Scheme.{u}} (j : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion j] [AlgebraicGeometry.IsLocallyNoetherian X₁]
    (π : X₁ ⟶ X) (Z : X.IdealSheafData) (h : Blowup.IsBlowupAlongIdealSheaf π Z) :
    Blowup.IsBlowupAlongIdealSheaf (strictTransformLiftOfClosedImmersion j π Z) (Z.comap j) := by
  have : QuasiCompact (strictTransformι π Z j.ker) :=
    FunctorialResolution.EmbeddedResolution.quasiCompact_strictTransformι_of_isLocallyNoetherian π Z j.ker
  have hcomap : (Z.comap j).comap (strictTransformLiftOfClosedImmersion j π Z)
      = (Z.comap π).comap (Blowup.strictTransform π Z j.ker).subschemeι := by
    rw [← Scheme.IdealSheafData.comap_comp, strictTransformLiftOfClosedImmersion_comp,
      Scheme.IdealSheafData.comap_comp]
  refine ⟨?_, ?_⟩
  · rw [hcomap]
    intro x
    obtain ⟨V, t, hxV, -, hVspan⟩ := h.1 ((Blowup.strictTransform π Z j.ker).subschemeι.base x)
    refine ⟨⟨(Blowup.strictTransform π Z j.ker).subschemeι ⁻¹ᵁ (V : X₁.Opens),
      V.2.preimage (Blowup.strictTransform π Z j.ker).subschemeι⟩,
      ((Blowup.strictTransform π Z j.ker).subschemeι.app (V : X₁.Opens)).hom t, hxV, ?_, ?_⟩
    · have key : ∀ z : Γ((Blowup.strictTransform π Z j.ker).subscheme,
          (Blowup.strictTransform π Z j.ker).subschemeι ⁻¹ᵁ (V : X₁.Opens)),
          z * ((Blowup.strictTransform π Z j.ker).subschemeι.app (V : X₁.Opens)).hom t = 0 → z = 0 := by
        intro z hz
        have hinj : Function.Injective
            ⇑(((Blowup.strictTransform π Z j.ker).subschemeObjIso V).hom.hom) := by
          intro A B hAB
          have h1 : ((((Blowup.strictTransform π Z j.ker).subschemeObjIso V).hom ≫
              ((Blowup.strictTransform π Z j.ker).subschemeObjIso V).inv).hom) A
              = ((((Blowup.strictTransform π Z j.ker).subschemeObjIso V).hom ≫
              ((Blowup.strictTransform π Z j.ker).subschemeObjIso V).inv).hom) B := by
            simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hAB]
          simpa using h1
        have hcompo : ((Blowup.strictTransform π Z j.ker).subschemeι.app (V : X₁.Opens))
            ≫ ((Blowup.strictTransform π Z j.ker).subschemeObjIso V).hom
            = CommRingCat.ofHom (Ideal.Quotient.mk ((Blowup.strictTransform π Z j.ker).ideal V)) := by
          rw [Scheme.IdealSheafData.subschemeι_app, Category.assoc, Iso.inv_hom_id,
            Category.comp_id]
        have hft : (((Blowup.strictTransform π Z j.ker).subschemeObjIso V).hom.hom)
            (((Blowup.strictTransform π Z j.ker).subschemeι.app (V : X₁.Opens)).hom t)
            = Ideal.Quotient.mk ((Blowup.strictTransform π Z j.ker).ideal V) t := by
          have h2 : ((((Blowup.strictTransform π Z j.ker).subschemeι.app (V : X₁.Opens))
              ≫ ((Blowup.strictTransform π Z j.ker).subschemeObjIso V).hom).hom) t
              = (((Blowup.strictTransform π Z j.ker).subschemeObjIso V).hom.hom)
                (((Blowup.strictTransform π Z j.ker).subschemeι.app (V : X₁.Opens)).hom t) := by
            rw [CommRingCat.hom_comp]; rfl
          rw [← h2, hcompo]
          rfl
        obtain ⟨z₀, hz₀⟩ := Ideal.Quotient.mk_surjective
          ((((Blowup.strictTransform π Z j.ker).subschemeObjIso V).hom.hom) z)
        have h1 : (((Blowup.strictTransform π Z j.ker).subschemeObjIso V).hom.hom) z *
            (((Blowup.strictTransform π Z j.ker).subschemeObjIso V).hom.hom)
              (((Blowup.strictTransform π Z j.ker).subschemeι.app (V : X₁.Opens)).hom t) = 0 := by
          rw [← map_mul, hz, map_zero]
        rw [hft, ← hz₀] at h1
        have h2 : Ideal.Quotient.mk ((Blowup.strictTransform π Z j.ker).ideal V) (z₀ * t) = 0 := by
          rw [map_mul]; exact h1
        have h3 : z₀ * t ∈ (Blowup.strictTransform π Z j.ker).ideal V :=
          (Ideal.Quotient.eq_zero_iff_mem).mp h2
        have h4 : z₀ ∈ (Blowup.strictTransform π Z j.ker).ideal V :=
          mem_strictTransform_of_mul_mem π Z j.ker V t hVspan z₀ (by rwa [mul_comm] at h3)
        have h5 : (((Blowup.strictTransform π Z j.ker).subschemeObjIso V).hom.hom) z = 0 := by
          rw [← hz₀]
          exact (Ideal.Quotient.eq_zero_iff_mem).mpr h4
        refine hinj ?_
        rw [h5, map_zero]
      rw [mem_nonZeroDivisors_iff]
      exact ⟨fun z hz => key z (by rw [mul_comm]; exact hz), key⟩
    · rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE (Z.comap π)
          (Blowup.strictTransform π Z j.ker).subschemeι V
          ⟨(Blowup.strictTransform π Z j.ker).subschemeι ⁻¹ᵁ (V : X₁.Opens),
            V.2.preimage (Blowup.strictTransform π Z j.ker).subschemeι⟩ le_rfl,
        hVspan, Ideal.map_span, Scheme.Hom.appLE_eq_app, Set.image_singleton]
  · intro W g hg
    have hECg : Blowup.IsLocallyGeneratedByNonZeroDivisor (Z.comap (g ≫ j)) := by
      rw [Scheme.IdealSheafData.comap_comp]
      exact hg
    obtain ⟨a, hacomp⟩ : ∃ a : W ⟶ X₁, a ≫ π = g ≫ j :=
      ⟨h.lift (g ≫ j) hECg, h.lift_comp (g ≫ j) hECg⟩
    have hWcomap : (Z.comap j).comap g = (Z.comap π).comap a := by
      rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hacomp]
    have hDker : (j.ker).comap π ≤ Scheme.Hom.ker a := by
      rw [← Scheme.IdealSheafData.le_map_iff_comap_le, ← Scheme.Hom.ker_comp, hacomp]
      apply Scheme.Hom.le_ker_comp
    have hD'ker : Blowup.strictTransform π Z j.ker ≤ Scheme.Hom.ker a := by
      have hker : Scheme.Hom.ker a = Scheme.IdealSheafData.ofIdeals
          (fun U : X₁.affineOpens => RingHom.ker ((a.app (U : X₁.Opens)).hom)) := rfl
      rw [hker, Scheme.IdealSheafData.le_ofIdeals_iff]
      intro V s hs
      rw [RingHom.mem_ker]
      refine eq_zero_of_locally_eq_zero (a ⁻¹ᵁ (V : X₁.Opens)) ((a.app (V : X₁.Opens)).hom s) ?_
      intro w hw
      obtain ⟨V₀, t₀, hyV₀, -, hV₀span⟩ := h.1 (a.base w)
      obtain ⟨c, hcle, hcmem⟩ :=
        V.2.exists_basicOpen_le (⟨a.base w, hyV₀⟩ : ↥(V₀ : X₁.Opens)) hw
      obtain ⟨P₀, u, hwP₀, hunzd, hP₀span⟩ := hg w
      have hwc : w ∈ a ⁻¹ᵁ (X₁.basicOpen c) := hcmem
      obtain ⟨d, hdle, hdmem⟩ :=
        P₀.2.exists_basicOpen_le (⟨w, hwc⟩ : ↥(a ⁻¹ᵁ (X₁.basicOpen c))) hwP₀
      have hcle' : ((X₁.affineBasicOpen c : X₁.affineOpens) : X₁.Opens)
          ≤ ((V₀ : X₁.affineOpens) : X₁.Opens) := hcle
      have hdle' : ((W.affineBasicOpen d : W.affineOpens) : W.Opens)
          ≤ a ⁻¹ᵁ ((X₁.affineBasicOpen c : X₁.affineOpens) : X₁.Opens) := hdle
      have hPU' : ((W.affineBasicOpen d : W.affineOpens) : W.Opens) ≤ a ⁻¹ᵁ (V : X₁.Opens) :=
        fun z hz => X₁.basicOpen_le c (hdle hz)
      have hCV : ((X₁.affineBasicOpen c : X₁.affineOpens) : X₁.Opens) ≤ (V : X₁.Opens) :=
        X₁.basicOpen_le c
      obtain ⟨t', ht'⟩ :=
        exists_ideal_eq_span_singleton_of_le (Z.comap π) V₀ (X₁.affineBasicOpen c) hcle' t₀ hV₀span
      have hs₁ : (X₁.presheaf.map (homOfLE hCV).op).hom s
          ∈ (Blowup.strictTransform π Z j.ker).ideal (X₁.affineBasicOpen c) := by
        rw [← Scheme.IdealSheafData.map_ideal_basicOpen]
        exact Ideal.mem_map_of_mem _ hs
      obtain ⟨n, hn⟩ := (mem_strictTransform_ideal_iff π Z j.ker (X₁.affineBasicOpen c) t' ht'
        ((X₁.presheaf.map (homOfLE hCV).op).hom s)).mp hs₁
      have hkerapp : (a.app ((X₁.affineBasicOpen c : X₁.affineOpens) : X₁.Opens)).hom
          (t' ^ n * (X₁.presheaf.map (homOfLE hCV).op).hom s) = 0 := by
        have h1 := (Scheme.IdealSheafData.le_def.mp hDker) (X₁.affineBasicOpen c) hn
        exact RingHom.mem_ker.mp (Scheme.Hom.ideal_ker_le a _ h1)
      have hφ : Scheme.Hom.appLE a ((X₁.affineBasicOpen c : X₁.affineOpens) : X₁.Opens)
            ((W.affineBasicOpen d : W.affineOpens) : W.Opens) hdle'
          = a.app ((X₁.affineBasicOpen c : X₁.affineOpens) : X₁.Opens)
            ≫ W.presheaf.map (homOfLE hdle').op := rfl
      have hzero1 : (Scheme.Hom.appLE a ((X₁.affineBasicOpen c : X₁.affineOpens) : X₁.Opens)
            ((W.affineBasicOpen d : W.affineOpens) : W.Opens) hdle').hom
          (t' ^ n * (X₁.presheaf.map (homOfLE hCV).op).hom s) = 0 := by
        rw [hφ, CommRingCat.hom_comp, RingHom.comp_apply, hkerapp, map_zero]
      have hmulzero : ((Scheme.Hom.appLE a
              ((X₁.affineBasicOpen c : X₁.affineOpens) : X₁.Opens)
              ((W.affineBasicOpen d : W.affineOpens) : W.Opens) hdle').hom t') ^ n *
          (Scheme.Hom.appLE a ((X₁.affineBasicOpen c : X₁.affineOpens) : X₁.Opens)
              ((W.affineBasicOpen d : W.affineOpens) : W.Opens) hdle').hom
            ((X₁.presheaf.map (homOfLE hCV).op).hom s) = 0 := by
        rw [← map_pow, ← map_mul]
        exact hzero1
      have hPspan : ((Z.comap π).comap a).ideal (W.affineBasicOpen d)
          = Ideal.span {(W.presheaf.map (homOfLE (W.basicOpen_le d)).op).hom u} := by
        rw [← Scheme.IdealSheafData.map_ideal_basicOpen, ← hWcomap, hP₀span, Ideal.map_span,
          Set.image_singleton]
      have hPspan' : ((Z.comap π).comap a).ideal (W.affineBasicOpen d)
          = Ideal.span {(Scheme.Hom.appLE a
              ((X₁.affineBasicOpen c : X₁.affineOpens) : X₁.Opens)
              ((W.affineBasicOpen d : W.affineOpens) : W.Opens) hdle').hom t'} := by
        rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE (Z.comap π) a
            (X₁.affineBasicOpen c) (W.affineBasicOpen d) hdle', ht', Ideal.map_span,
          Set.image_singleton]
      have hu'nzd : (W.presheaf.map (homOfLE (W.basicOpen_le d)).op).hom u
          ∈ nonZeroDivisors _ := restrict_basicOpen_mem_nonZeroDivisors P₀ d hunzd
      have hdvd : (Scheme.Hom.appLE a ((X₁.affineBasicOpen c : X₁.affineOpens) : X₁.Opens)
            ((W.affineBasicOpen d : W.affineOpens) : W.Opens) hdle').hom t' ∣
          (W.presheaf.map (homOfLE (W.basicOpen_le d)).op).hom u := by
        have hmem : (W.presheaf.map (homOfLE (W.basicOpen_le d)).op).hom u
            ∈ Ideal.span {(Scheme.Hom.appLE a
                ((X₁.affineBasicOpen c : X₁.affineOpens) : X₁.Opens)
                ((W.affineBasicOpen d : W.affineOpens) : W.Opens) hdle').hom t'} := by
          rw [← hPspan', hPspan]
          exact Ideal.mem_span_singleton_self _
        exact Ideal.mem_span_singleton.mp hmem
      have htnzd := mem_nonZeroDivisors_of_dvd hu'nzd hdvd
      have hpownzd := Submonoid.pow_mem (nonZeroDivisors _) htnzd n
      have happLE : (Scheme.Hom.appLE a ((X₁.affineBasicOpen c : X₁.affineOpens) : X₁.Opens)
            ((W.affineBasicOpen d : W.affineOpens) : W.Opens) hdle').hom
          ((X₁.presheaf.map (homOfLE hCV).op).hom s) = 0 :=
        (mem_nonZeroDivisors_iff.mp hpownzd).1 _ hmulzero
      refine ⟨((W.affineBasicOpen d : W.affineOpens) : W.Opens), hPU', hdmem, ?_⟩
      have hsplit := Scheme.Hom.map_appLE a hdle' (homOfLE hCV).op
      have h0 : ((X₁.presheaf.map (homOfLE hCV).op
            ≫ Scheme.Hom.appLE a ((X₁.affineBasicOpen c : X₁.affineOpens) : X₁.Opens)
                ((W.affineBasicOpen d : W.affineOpens) : W.Opens) hdle').hom) s = 0 := by
        rw [CommRingCat.hom_comp, RingHom.comp_apply]
        exact happLE
      rw [hsplit] at h0
      have hEq : (W.presheaf.map (homOfLE hPU').op).hom ((a.app (V : X₁.Opens)).hom s)
          = (Scheme.Hom.appLE a (V : X₁.Opens)
              ((W.affineBasicOpen d : W.affineOpens) : W.Opens) hPU').hom s := rfl
      rw [hEq]
      exact h0
    have hkerι : Scheme.Hom.ker (Blowup.strictTransform π Z j.ker).subschemeι
        ≤ Scheme.Hom.ker a := by
      rwa [Scheme.IdealSheafData.ker_subschemeι]
    have hbι : AlgebraicGeometry.IsClosedImmersion.lift
        (Blowup.strictTransform π Z j.ker).subschemeι a hkerι
        ≫ (Blowup.strictTransform π Z j.ker).subschemeι = a :=
      AlgebraicGeometry.IsClosedImmersion.lift_fac _ _ _
    refine ⟨AlgebraicGeometry.IsClosedImmersion.lift
      (Blowup.strictTransform π Z j.ker).subschemeι a hkerι, ?_, ?_⟩
    · have hfac : (AlgebraicGeometry.IsClosedImmersion.lift
          (Blowup.strictTransform π Z j.ker).subschemeι a hkerι
          ≫ strictTransformLiftOfClosedImmersion j π Z) ≫ j = g ≫ j := by
        rw [Category.assoc, strictTransformLiftOfClosedImmersion_comp, ← Category.assoc, hbι, hacomp]
      exact (cancel_mono j).mp hfac
    · intro y hy
      have h1 : (y ≫ (Blowup.strictTransform π Z j.ker).subschemeι) ≫ π = g ≫ j := by
        rw [Category.assoc, ← strictTransformLiftOfClosedImmersion_comp, ← Category.assoc, hy]
      have h2 : ((AlgebraicGeometry.IsClosedImmersion.lift
          (Blowup.strictTransform π Z j.ker).subschemeι a hkerι)
          ≫ (Blowup.strictTransform π Z j.ker).subschemeι) ≫ π = g ≫ j := by
        rw [hbι, hacomp]
      have h3 := h.hom_ext_of_comp_eq hECg h1 h2
      exact (cancel_mono (Blowup.strictTransform π Z j.ker).subschemeι).mp h3

theorem isLocallyNoetherian_of_isBlowupAlongIdealSheaf {X X₁ : Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] (π : X₁ ⟶ X) (Z : X.IdealSheafData)
    (h : Blowup.IsBlowupAlongIdealSheaf π Z) : AlgebraicGeometry.IsLocallyNoetherian X₁ := by
  have : AlgebraicGeometry.IsProper π := Blowup.blowupIsProper X X₁ π Z h
  exact AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian π

theorem strictTransformIsBlowupOfClosedSubscheme : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u} := by
  intro X X₁ S hX j hj π Z hπ _
  have := hX
  have := hj
  have := isLocallyNoetherian_of_isBlowupAlongIdealSheaf π Z hπ
  exact ⟨strictTransformLiftOfClosedImmersion j π Z, strictTransformLiftOfClosedImmersion_comp j π Z,
    isBlowupAlongIdealSheaf_strictTransformLiftOfClosedImmersion j π Z hπ⟩

end FunctorialResolution.EmbeddedResolution

end
