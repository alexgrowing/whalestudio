import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransformOffCenter
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem comap_eq_ker_of_mono {U V : Scheme.{u}} (j : U ⟶ V) [Mono j]
    (I : V.IdealSheafData) (lam : I.subscheme ⟶ U) (hlam : lam ≫ j = I.subschemeι) :
    I.comap j = Scheme.Hom.ker lam := by
  have hc : I.comap j = Scheme.Hom.ker (Limits.pullback.fst j I.subschemeι) := rfl
  have hcomm : lam ≫ j = 𝟙 I.subscheme ≫ I.subschemeι := by rw [hlam, Category.id_comp]
  obtain ⟨e, hefst, hesnd⟩ : ∃ e : I.subscheme ⟶ Limits.pullback j I.subschemeι,
      e ≫ Limits.pullback.fst j I.subschemeι = lam ∧
        e ≫ Limits.pullback.snd j I.subschemeι = 𝟙 I.subscheme :=
    ⟨Limits.pullback.lift lam (𝟙 I.subscheme) hcomm, Limits.pullback.lift_fst _ _ _,
      Limits.pullback.lift_snd _ _ _⟩
  have hsndlam : Limits.pullback.snd j I.subschemeι ≫ lam
      = Limits.pullback.fst j I.subschemeι := by
    rw [← cancel_mono j, Category.assoc, hlam, ← Limits.pullback.condition]
  have : IsIso e := by
    refine ⟨Limits.pullback.snd j I.subschemeι, hesnd, ?_⟩
    refine Limits.pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hefst, hsndlam, Category.id_comp]
    · rw [Category.assoc, hesnd, Category.comp_id, Category.id_comp]
  rw [hc]
  exact (ker_eq_ker_of_isIso_comp lam (Limits.pullback.fst j I.subschemeι) e hefst).symm

theorem map_eq_ker_subschemeι_comp {U V : Scheme.{u}} (j : U ⟶ V) (K : U.IdealSheafData) :
    K.map j = Scheme.Hom.ker (K.subschemeι ≫ j) := by
  rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι]

theorem ker_subschemeι_comp_eq_of_ker_le {U V : Scheme.{u}} (j : U ⟶ V) [IsClosedImmersion j]
    (L : V.IdealSheafData) (hL : Scheme.Hom.ker j ≤ L) (K : U.IdealSheafData)
    (hK : K = L.comap j) :
    Scheme.Hom.ker (K.subschemeι ≫ j) = L := by
  have hle : Scheme.Hom.ker j ≤ Scheme.Hom.ker L.subschemeι := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact hL
  have hfac : IsClosedImmersion.lift j L.subschemeι hle ≫ j = L.subschemeι := by
    rw [IsClosedImmersion.lift_fac]
  have hcomap : L.comap j = Scheme.Hom.ker (IsClosedImmersion.lift j L.subschemeι hle) :=
    comap_eq_ker_of_mono j L (IsClosedImmersion.lift j L.subschemeι hle) hfac
  rw [hK, hcomap, Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι,
    ← Scheme.Hom.ker_comp, hfac, Scheme.IdealSheafData.ker_subschemeι]

theorem strictTransform_eq_ker_complComapSupport {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) :
    Blowup.strictTransform π Z D =
      Scheme.Hom.ker
        (((D.comap π).comap (Scheme.Opens.ι (complComapSupport π Z))).subschemeι ≫
          Scheme.Opens.ι (complComapSupport π Z)) := by
  rw [Blowup.strictTransform_eq_ker, Blowup.strictTransformImmersion_eq, Blowup.strictTransformOpens_eq,
    ← complComapSupport_eq]
  exact ker_ι_preimage_comp_subschemeι_eq_ker_comap (D.comap π) (complComapSupport π Z)

theorem preimage_complComapSupport_eq {A A' A₁ A'₁ : Scheme.{u}} (j : A ⟶ A') [IsClosedImmersion j]
    (Z : A.IdealSheafData) (π : A₁ ⟶ A) (π' : A'₁ ⟶ A') (j₁ : A₁ ⟶ A'₁)
    (hsq : j₁ ≫ π' = π ≫ j) :
    (Opens.map j₁.base).obj (complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j))) =
      complComapSupport π Z := by
  have key : ((Scheme.Hom.ker (Z.subschemeι ≫ j)).comap π').comap j₁ = Z.comap π := by
    rw [← Scheme.IdealSheafData.comap_comp, hsq, Scheme.IdealSheafData.comap_comp,
      ← map_eq_ker_subschemeι_comp, Blowup.comap_map_of_isClosedImmersion]
  have h2 : ((Z.comap π).support : Set A₁)
      = ⇑j₁.base ⁻¹'
        ((((Scheme.Hom.ker (Z.subschemeι ≫ j)).comap π').support : Set A'₁)) := by
    rw [← key, Scheme.IdealSheafData.support_comap
      ((Scheme.Hom.ker (Z.subschemeι ≫ j)).comap π') j₁]
    rfl
  apply TopologicalSpace.Opens.ext
  have h1 : (((Opens.map j₁.base).obj
        (complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j)))) : Set A₁)
      = ⇑j₁.base ⁻¹' (((Scheme.Hom.ker (Z.subschemeι ≫ j)).comap π').support : Set A'₁)ᶜ := rfl
  rw [h1, coe_complComapSupport, h2, Set.preimage_compl]

private theorem map_ker_subschemeι_comp_restrict {A A' A₁ A'₁ : Scheme.{u}} (j : A ⟶ A')
    [IsClosedImmersion j]
    (D : A.IdealSheafData) (π : A₁ ⟶ A) (π' : A'₁ ⟶ A') (j₁ : A₁ ⟶ A'₁) [IsClosedImmersion j₁]
    (hsq : j₁ ≫ π' = π ≫ j) (V' : A'₁.Opens) [IsClosedImmersion (j₁ ∣_ V')]
    (hkerr : Scheme.Hom.ker (j₁ ∣_ V') ≤
      ((Scheme.Hom.ker (D.subschemeι ≫ j)).comap π').comap V'.ι) :
    (Scheme.Hom.ker (((D.comap π).comap (j₁ ⁻¹ᵁ V').ι).subschemeι ≫ (j₁ ⁻¹ᵁ V').ι)).map j₁
      = Scheme.Hom.ker
          ((((Scheme.Hom.ker (D.subschemeι ≫ j)).comap π').comap V'.ι).subschemeι ≫ V'.ι) := by
  have hm : (j₁ ∣_ V') ≫ V'.ι ≫ π' = (j₁ ⁻¹ᵁ V').ι ≫ π ≫ j := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hsq]
  have hMcomap :
      ((((Scheme.Hom.ker (D.subschemeι ≫ j)).comap π').comap V'.ι).comap (j₁ ∣_ V'))
        = (D.comap π).comap (j₁ ⁻¹ᵁ V').ι := by
    calc ((((Scheme.Hom.ker (D.subschemeι ≫ j)).comap π').comap V'.ι).comap (j₁ ∣_ V'))
        = (Scheme.Hom.ker (D.subschemeι ≫ j)).comap ((j₁ ∣_ V') ≫ V'.ι ≫ π') := by
          rw [Scheme.IdealSheafData.comap_comp (Scheme.Hom.ker (D.subschemeι ≫ j))
              (j₁ ∣_ V') (V'.ι ≫ π'),
            Scheme.IdealSheafData.comap_comp (Scheme.Hom.ker (D.subschemeι ≫ j)) V'.ι π']
      _ = (Scheme.Hom.ker (D.subschemeι ≫ j)).comap ((j₁ ⁻¹ᵁ V').ι ≫ π ≫ j) := by rw [hm]
      _ = (D.comap π).comap (j₁ ⁻¹ᵁ V').ι := by
          rw [Scheme.IdealSheafData.comap_comp (Scheme.Hom.ker (D.subschemeι ≫ j))
              (j₁ ⁻¹ᵁ V').ι (π ≫ j),
            Scheme.IdealSheafData.comap_comp (Scheme.Hom.ker (D.subschemeι ≫ j)) π j,
            ← map_eq_ker_subschemeι_comp j D, Blowup.comap_map_of_isClosedImmersion j D]
  have hmor : ((((D.comap π).comap (j₁ ⁻¹ᵁ V').ι).subschemeι ≫ (j₁ ⁻¹ᵁ V').ι) ≫ j₁)
      = ((((D.comap π).comap (j₁ ⁻¹ᵁ V').ι).subschemeι ≫ (j₁ ∣_ V')) ≫ V'.ι) := by
    simp only [Category.assoc, morphismRestrict_ι]
  rw [← Scheme.Hom.ker_comp, hmor,
    Scheme.Hom.ker_comp (((D.comap π).comap (j₁ ⁻¹ᵁ V').ι).subschemeι ≫ (j₁ ∣_ V')) V'.ι,
    ker_subschemeι_comp_eq_of_ker_le (j₁ ∣_ V')
      (((Scheme.Hom.ker (D.subschemeι ≫ j)).comap π').comap V'.ι) hkerr
      ((D.comap π).comap (j₁ ⁻¹ᵁ V').ι) hMcomap.symm,
    Scheme.Hom.ker_comp
      ((((Scheme.Hom.ker (D.subschemeι ≫ j)).comap π').comap V'.ι).subschemeι) V'.ι,
    Scheme.IdealSheafData.ker_subschemeι]

theorem image_strictTransform_eq_strictTransform_image {A A' A₁ A'₁ : Scheme.{u}} (j : A ⟶ A')
    [IsClosedImmersion j] (Z D : A.IdealSheafData) (π : A₁ ⟶ A) (π' : A'₁ ⟶ A') (j₁ : A₁ ⟶ A'₁)
    [IsClosedImmersion j₁] [IsNoetherian A₁] [IsNoetherian A'₁]
    (hsq : j₁ ≫ π' = π ≫ j)
    (hker : Scheme.Hom.ker j₁ =
      Blowup.strictTransform π' (Scheme.Hom.ker (Z.subschemeι ≫ j)) (Scheme.Hom.ker j)) :
    Scheme.Hom.ker ((Blowup.strictTransform π Z D).subschemeι ≫ j₁) =
      Blowup.strictTransform π' (Scheme.Hom.ker (Z.subschemeι ≫ j))
        (Scheme.Hom.ker (D.subschemeι ≫ j)) := by
  have : IsClosedImmersion
      (j₁ ∣_ complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j))) := inferInstance
  have hDle : Scheme.Hom.ker j ≤ Scheme.Hom.ker (D.subschemeι ≫ j) := by
    rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι,
      ← Scheme.IdealSheafData.map_bot j]
    exact Scheme.IdealSheafData.map_mono j bot_le
  have hUeq : j₁ ⁻¹ᵁ complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j))
      = complComapSupport π Z := preimage_complComapSupport_eq j Z π π' j₁ hsq
  have hkerr : Scheme.Hom.ker (j₁ ∣_ complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j)))
      ≤ ((Scheme.Hom.ker (D.subschemeι ≫ j)).comap π').comap
          (complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j))).ι := by
    rw [← ker_comap_ι_eq_ker_morphismRestrict j₁
        (complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j))), hker,
      strictTransform_comap_complComapSupport_ι π' (Scheme.Hom.ker (Z.subschemeι ≫ j))
        (Scheme.Hom.ker j)]
    exact Scheme.IdealSheafData.comap_mono
      (complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j))).ι
      (Scheme.IdealSheafData.comap_mono π' hDle)
  have hTmap : Scheme.Hom.ker ((Blowup.strictTransform π Z D).subschemeι ≫ j₁)
      = (Blowup.strictTransform π Z D).map j₁ := by
    rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι]
  rw [hTmap, strictTransform_eq_ker_complComapSupport π Z D, ← hUeq,
    map_ker_subschemeι_comp_restrict j D π π' j₁ hsq
      (complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j))) hkerr]
  exact (strictTransform_eq_ker_complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j))
    (Scheme.Hom.ker (D.subschemeι ≫ j))).symm

theorem map_strictTransform_eq_strictTransform_map {A A' A₁ A'₁ : Scheme.{u}} (j : A ⟶ A')
    [IsClosedImmersion j] (Z D : A.IdealSheafData) (π : A₁ ⟶ A) (π' : A'₁ ⟶ A') (j₁ : A₁ ⟶ A'₁)
    [IsClosedImmersion j₁] [IsNoetherian A₁] [IsNoetherian A'₁]
    (hsq : j₁ ≫ π' = π ≫ j)
    (hker : Scheme.Hom.ker j₁ = Blowup.strictTransform π' (Z.map j) (Scheme.Hom.ker j)) :
    (Blowup.strictTransform π Z D).map j₁ = Blowup.strictTransform π' (Z.map j) (D.map j) := by
  have hZ : Z.map j = Scheme.Hom.ker (Z.subschemeι ≫ j) := map_eq_ker_subschemeι_comp j Z
  have hD : D.map j = Scheme.Hom.ker (D.subschemeι ≫ j) := map_eq_ker_subschemeι_comp j D
  have hT : (Blowup.strictTransform π Z D).map j₁
      = Scheme.Hom.ker ((Blowup.strictTransform π Z D).subschemeι ≫ j₁) :=
    map_eq_ker_subschemeι_comp j₁ (Blowup.strictTransform π Z D)
  rw [hT, hD, hZ]
  exact image_strictTransform_eq_strictTransform_image j Z D π π' j₁ hsq (by rw [hker, hZ])

end FunctorialResolution.EmbeddedResolution
