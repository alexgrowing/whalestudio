import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapIdOfCommonGeneric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTripleGlueTwoOpensStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.TripleGlue

def DensePart {X X₀ : Scheme.{0}} (j : X₀ ⟶ X) : Prop :=
  (Geo.Tor.IsNormalScheme X ∧ ∃ z : X ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z) ∧ IsPreimmersion j ∧ Flat j ∧
    IsDominant j ∧ QuasiCompact j

theorem DensePart.restrict {X X₀ Y : Scheme.{0}} {j : X₀ ⟶ X} (h : DensePart j) (i : Y ⟶ X) [IsOpenImmersion i]
    {k : X₀ ⟶ Y} (hk : k ≫ i = j) : DensePart k := by
  obtain ⟨⟨hn, z, hz₁, hz₂⟩, h₁, h₂, h₃, h₄⟩ := h
  have sq : IsPullback (𝟙 X₀) k j i := IsPullback.of_horiz_isIso_mono ⟨by rw [hk, Category.id_comp]⟩
  refine ⟨⟨fun y => ?_, i ≫ z, inferInstance, inferInstance⟩, MorphismProperty.of_isPullback sq h₁,
    MorphismProperty.of_isPullback sq h₂, ⟨?_⟩, MorphismProperty.of_isPullback sq h₄⟩
  · obtain ⟨_, _⟩ := hn (i y)
    have e := (asIso (i.stalkMap y)).commRingCatIsoToRingEquiv
    exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩
  · have e : Set.range k = i ⁻¹' Set.range j := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, by rw [← hk, Scheme.Hom.comp_apply]⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, i.isOpenEmbedding.injective (by rw [← hx, ← hk, Scheme.Hom.comp_apply])⟩
    rw [DenseRange, e]
    exact j.denseRange.preimage i.isOpenEmbedding.isOpenMap

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_cast {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f g : S' ⟶ S} (m : SABMap t' t f) (h : f = g) :
    ∃ n : SABMap t' t g, n.φ = m.φ := by
  subst h
  exact ⟨m, rfl⟩

theorem exists_fac {X X₀ Y : Scheme.{0}} {j : X₀ ⟶ X} {t₀ : SAB H X₀} {t : SAB H X} (a : SABMap t₀ t j) (i : Y ⟶ X)
    {k : X₀ ⟶ Y} (hk : k ≫ i = j) :
    ∃ (s : SAB H Y) (b : SABMap t₀ s k) (m : SABMap s t i), b.φ ≫ m.φ = a.φ := by
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull i t
  obtain ⟨a', ha'⟩ := exists_cast a hk.symm
  obtain ⟨b, hb⟩ := ObjMaps.exists_sab_cancel m a'
  exact ⟨_, b, m, hb.symm.trans ha'⟩

theorem DensePart.generic {X X₀ : Scheme.{0}} {j : X₀ ⟶ X} (h : DensePart j) {t₀ : SAB H X₀} {t : SAB H X}
    (a : SABMap t₀ t j) (hp : IsProper t₀.G.hom) : IsReduced X ∧ genericPoints X ⊆ abLocus t.G := by
  obtain ⟨hX, h₁, h₂, h₃, h₄⟩ := h
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have := (hX.1 x).1
    infer_instance
  exact ⟨isReduced_of_isReduced_stalk X,
    (densePart_basic X X₀ j h₁ h₂ h₃ h₄).1.trans (range_subset_abLocus_of_isProper t.semi a.cart.1)⟩

section

variable (hdvr : ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f)
include hdvr

theorem DensePart.exists_map {X X₀ Y : Scheme.{0}} {j : X₀ ⟶ X} {k : X₀ ⟶ Y} (h : DensePart k) {i : Y ⟶ X}
    (hk : k ≫ i = j) {t₀ : SAB H X₀} {t : SAB H X} {s : SAB H Y} (a : SABMap t₀ t j) (b : SABMap t₀ s k)
    (hp : IsProper t₀.G.hom) : ∃ n : SABMap s t i, b.φ ≫ n.φ = a.φ := by
  obtain ⟨s', b', m, hm⟩ := exists_fac a i hk
  obtain ⟨c, hc⟩ := exists_sabMap_id_of_common_generic hdvr E H Y X₀ k h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
    t₀ s s' b b' hp
  obtain ⟨n, hn⟩ := ObjMaps.exists_sab_comp m c
  obtain ⟨n', hn'⟩ := exists_cast n (Category.id_comp i)
  exact ⟨n', by rw [hn', hn, ← Category.assoc, hc, hm]⟩

theorem DensePart.glue_top {X X₀ : Scheme.{0}} {j : X₀ ⟶ X} (h : DensePart j) {U V : X.Opens} (hUV : U ⊔ V = ⊤)
    {jU : X₀ ⟶ U.toScheme} {jV : X₀ ⟶ V.toScheme} (hU : jU ≫ U.ι = j) (hV : jV ≫ V.ι = j) {t₀ : SAB H X₀}
    {t₁ : SAB H U.toScheme} {t₂ : SAB H V.toScheme} (a₁ : SABMap t₀ t₁ jU) (a₂ : SABMap t₀ t₂ jV)
    (hp : IsProper t₀.G.hom) : ∃ t : SAB H X, Nonempty (SABMap t₀ t j) := by
  have hr : Set.range j ⊆ Set.range (U ⊓ V).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact ⟨by rw [← hU]; exact (jU x).2, by rw [← hV]; exact (jV x).2⟩
  obtain ⟨k, hk⟩ : ∃ k : X₀ ⟶ (U ⊓ V).toScheme, k ≫ (U ⊓ V).ι = j := ⟨_, IsOpenImmersion.lift_fac _ j hr⟩
  have hkU : k ≫ X.homOfLE inf_le_left = jU := by
    rw [← cancel_mono U.ι, Category.assoc, Scheme.homOfLE_ι, hk, hU]
  have hkV : k ≫ X.homOfLE inf_le_right = jV := by
    rw [← cancel_mono V.ι, Category.assoc, Scheme.homOfLE_ι, hk, hV]
  obtain ⟨s, b, m₁, -⟩ := exists_fac a₁ _ hkU
  obtain ⟨m₂, -⟩ := (h.restrict _ hk).exists_map hdvr hkV a₂ b hp
  obtain ⟨t, n₁, -, -⟩ := GlobalTheory.T.exists_triple_glue_two_opens E H X U V t₁ t₂ s m₁ m₂ hUV ((h.restrict _ hU).generic a₁ hp)
    ((h.restrict _ hV).generic a₂ hp)
  obtain ⟨n, -⟩ := ObjMaps.exists_sab_comp n₁ a₁
  obtain ⟨n', -⟩ := exists_cast n hU
  exact ⟨t, ⟨n'⟩⟩

omit hdvr in

theorem exists_trace {X X₀ Y : Scheme.{0}} {j : X₀ ⟶ X} (i : Y ⟶ X) {k : X₀ ⟶ Y} (hk : k ≫ i = j) {U : X.Opens}
    {jU : X₀ ⟶ U.toScheme} (hU : jU ≫ U.ι = j) {t₀ : SAB H X₀} {t : SAB H U.toScheme} (a : SABMap t₀ t jU) :
    ∃ (k' : X₀ ⟶ (i ⁻¹ᵁ U).toScheme) (s : SAB H (i ⁻¹ᵁ U).toScheme),
      k' ≫ (i ⁻¹ᵁ U).ι = k ∧ Nonempty (SABMap t₀ s k') := by
  have hr : Set.range k ⊆ Set.range (i ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    show i (k x) ∈ U
    rw [← Scheme.Hom.comp_apply, hk, ← hU]
    exact (jU x).2
  obtain ⟨k', hk'⟩ : ∃ k' : X₀ ⟶ (i ⁻¹ᵁ U).toScheme, k' ≫ (i ⁻¹ᵁ U).ι = k := ⟨_, IsOpenImmersion.lift_fac _ k hr⟩
  have e : k' ≫ (i ∣_ U) = jU := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hk', hk, hU]
  obtain ⟨s, b, -, -⟩ := exists_fac a _ e
  exact ⟨k', s, hk', ⟨b⟩⟩

theorem DensePart.glue_sup {X X₀ : Scheme.{0}} {j : X₀ ⟶ X} (h : DensePart j) {t₀ : SAB H X₀} (hp : IsProper t₀.G.hom)
    {U V : X.Opens}
    (hU : ∃ (k : X₀ ⟶ U.toScheme) (s : SAB H U.toScheme), k ≫ U.ι = j ∧ Nonempty (SABMap t₀ s k))
    (hV : ∃ (k : X₀ ⟶ V.toScheme) (s : SAB H V.toScheme), k ≫ V.ι = j ∧ Nonempty (SABMap t₀ s k)) :
    ∃ (k : X₀ ⟶ (U ⊔ V).toScheme) (s : SAB H (U ⊔ V).toScheme), k ≫ (U ⊔ V).ι = j ∧ Nonempty (SABMap t₀ s k) := by
  obtain ⟨jU, t₁, hU, ⟨a₁⟩⟩ := hU
  obtain ⟨jV, t₂, hV, ⟨a₂⟩⟩ := hV
  have hk : (jU ≫ X.homOfLE le_sup_left) ≫ (U ⊔ V).ι = j := by rw [Category.assoc, Scheme.homOfLE_ι, hU]
  obtain ⟨k₁, s₁, hk₁, ⟨b₁⟩⟩ := exists_trace _ hk hU a₁
  obtain ⟨k₂, s₂, hk₂, ⟨b₂⟩⟩ := exists_trace _ hk hV a₂
  have hc : (U ⊔ V).ι ⁻¹ᵁ U ⊔ (U ⊔ V).ι ⁻¹ᵁ V = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, Scheme.Opens.ι_preimage_self]
  obtain ⟨t, ha⟩ := (h.restrict _ hk).glue_top hdvr hc hk₁ hk₂ b₁ b₂ hp
  exact ⟨_, t, hk, ha⟩

end

end GlobalTheory.TripleGlue

theorem GlobalTheory.exists_sab_glue_of_common_generic : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X₀ : Scheme.{0}) (j : X₀ ⟶ X) (t₀ : SAB H X₀) (I : Type) [Finite I] (U : I → X.Opens) (jU : ∀ i, X₀ ⟶ (U i).toScheme) (t : ∀ i, SAB H (U i).toScheme) (a : ∀ i, SABMap t₀ (t i) (jU i)), Nonempty I → (Geo.Tor.IsNormalScheme X ∧ ∃ z : X ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z) → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → IsProper t₀.G.hom → ⨆ i, U i = ⊤ → (∀ i, jU i ≫ (U i).ι = j) → ∃ (t' : SAB H X) (a' : SABMap t₀ t' j) (n : ∀ i, SABMap (t i) t' (U i).ι), ∀ i, (a i).φ ≫ (n i).φ = a'.φ := by
  intro hdvr E _ _ _ H X X₀ j t₀ I _ U jU t a hI hX h₁ h₂ h₃ h₄ hp hcov hj
  have h : TripleGlue.DensePart j := ⟨hX, h₁, h₂, h₃, h₄⟩
  have := Fintype.ofFinite I
  have key : ∃ (k : X₀ ⟶ (Finset.univ.sup' Finset.univ_nonempty U).toScheme) (s : SAB H _),
      k ≫ (Finset.univ.sup' Finset.univ_nonempty U).ι = j ∧ Nonempty (SABMap t₀ s k) :=
    Finset.sup'_induction (p := fun W : X.Opens => ∃ (k : X₀ ⟶ W.toScheme) (s : SAB H W.toScheme),
      k ≫ W.ι = j ∧ Nonempty (SABMap t₀ s k)) _ _ (fun _ hU _ hV => h.glue_sup hdvr hp hU hV)
      (fun i _ => ⟨jU i, t i, hj i, ⟨a i⟩⟩)
  rw [Finset.sup'_univ_eq_ciSup, hcov] at key
  obtain ⟨k, s, hk, ⟨b⟩⟩ := key
  have e : j ≫ X.topIso.inv = k := by
    rw [← hk, Category.assoc]
    exact (congrArg (k ≫ ·) X.topIso.hom_inv_id).trans (Category.comp_id _)
  obtain ⟨t', a', -, -⟩ := TripleGlue.exists_fac b _ e
  choose n hn using fun i => (h.restrict _ (hj i)).exists_map hdvr (hj i) a' (a i) hp
  exact ⟨t', a', n, hn⟩
