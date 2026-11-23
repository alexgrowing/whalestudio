import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.OpenSpecField

variable {S : Type} [CommRing S] [IsDomain S] {Y : Scheme.{0}} [IsIntegral Y]
  (j : Sp S ⟶ Y) [IsOpenImmersion j]

abbrev img : Y.Opens := j ''ᵁ ⊤

theorem isAffineOpen_img : IsAffineOpen (img j) := (isAffineOpen_top _).image_of_isOpenImmersion j

theorem mem_img (q : Sp S) : j.base q ∈ img j := ⟨q, trivial, rfl⟩

instance : Nonempty (img j) := ⟨⟨_, mem_img j (Classical.arbitrary (PrimeSpectrum S))⟩⟩

theorem gen_mem_img : genericPoint Y ∈ img j :=
  gen_mem (mem_img j (Classical.arbitrary (PrimeSpectrum S)))

def secEquiv : Γ(Y, img j) ≃+* S :=
  ((j.appIso ⊤) ≪≫ Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv

instance : IsFractionRing Γ(Y, img j) Y.functionField :=
  functionField_isFractionRing_of_isAffineOpen Y _ (isAffineOpen_img j)

def fieldEquiv : Y.functionField ≃+* FractionRing S := IsFractionRing.ringEquivOfRingEquiv (secEquiv j)

theorem fieldEquiv_fnOf (a : Γ(Y, img j)) :
    fieldEquiv j (fnOf _ (gen_mem_img j) a) = algebraMap S (FractionRing S) (secEquiv j a) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ a

theorem mem_basicOpen_iff (q : Sp S) (b : Γ(Y, img j)) :
    j.base q ∈ Y.basicOpen b ↔ secEquiv j b ∉ q.asIdeal := by
  have h : (Sp S).basicOpen ((j.appIso ⊤).hom b) = (Sp S).basicOpen (j.app (img j) b) := by
    rw [Scheme.Hom.appIso_hom, CommRingCat.comp_apply, Scheme.basicOpen_res]
    exact top_inf_eq _
  change q ∈ j ⁻¹ᵁ Y.basicOpen b ↔ _
  rw [Scheme.preimage_basicOpen, ← h, basicOpen_eq_of_affine']
  exact PrimeSpectrum.mem_basicOpen _ _

theorem secEquiv_algX [Algebra ℂ S] (p : Y ⟶ Sp ℂ) (hjp : j ≫ p = spMap (algebraMap ℂ S)) (a : ℂ) :
    secEquiv j (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (img j) a) = algebraMap ℂ S a := by
  have key : p.appLE ⊤ (img j) (show img j ≤ p ⁻¹ᵁ ⊤ from le_top) ≫ (j.appIso ⊤).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ≫ CommRingCat.ofHom (algebraMap ℂ S) := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE_assoc]
    simp only [hjp]
    have e : (spMap (algebraMap ℂ S)).appLE ⊤ ⊤ (show (⊤ : (Sp S).Opens) ≤ spMap (algebraMap ℂ S) ⁻¹ᵁ ⊤ from le_top) = (spMap (algebraMap ℂ S)).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    rw [e]
    exact Scheme.ΓSpecIso_naturality _
  have := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv a)) key
  refine Eq.trans ?_ (this.trans ?_)
  · rfl
  · simp

theorem fieldEquiv_constFn [Algebra ℂ S] (p : Y ⟶ Sp ℂ) (hjp : j ≫ p = spMap (algebraMap ℂ S))
    (a : ℂ) : fieldEquiv j (GlobalTheory.Cartier.constFn p a) = algebraMap ℂ (FractionRing S) a := by
  rw [← fnOf_comp_algX p (img j) (gen_mem_img j), RingHom.comp_apply, fieldEquiv_fnOf,
    secEquiv_algX j p hjp, IsScalarTower.algebraMap_apply ℂ S (FractionRing S)]

theorem mem_map_locRing (q : Sp S) (g : FractionRing S) :
    g ∈ (locRing (j.base q)).map (fieldEquiv j).toRingHom ↔
      ∃ a b : S, b ∉ q.asIdeal ∧
        g * algebraMap S (FractionRing S) b = algebraMap S (FractionRing S) a := by
  have hU := isAffineOpen_img j
  have hy := mem_img j q
  have hg := gen_mem_img j
  constructor
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨V, hyV, c, rfl⟩ := (mem_locRing.1 hf).exists_fnOf
    obtain ⟨b, hbV, hyb⟩ := hU.exists_basicOpen_le ⟨_, hyV⟩ hy
    have := hU.isLocalization_basicOpen b
    obtain ⟨⟨t, s, hs⟩, hts⟩ := IsLocalization.surj (Submonoid.powers b) (resG Y hbV c)
    obtain ⟨n, rfl⟩ := hs
    have hW : genericPoint Y ∈ Y.basicOpen b := gen_mem hyb
    have e1 := congrArg (fnOf _ hW) hts
    change fnOf _ hW (resG Y hbV c * resG Y (Y.basicOpen_le b) (b ^ n)) =
      fnOf _ hW (resG Y (Y.basicOpen_le b) t) at e1
    rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG] at e1
    refine ⟨secEquiv j t, secEquiv j (b ^ n), ?_, ?_⟩
    · rw [map_pow]
      exact fun h => (mem_basicOpen_iff j q b).1 hyb (q.isPrime.mem_of_pow_mem n h)
    · rw [← fieldEquiv_fnOf, ← fieldEquiv_fnOf]
      change fieldEquiv j _ * _ = _
      rw [← map_mul, e1]
  · rintro ⟨a, b, hb, e⟩
    let a' := (secEquiv j).symm a
    let b' := (secEquiv j).symm b
    have hb' : j.base q ∈ Y.basicOpen b' :=
      (mem_basicOpen_iff j q b').2 (by simpa [b'] using hb)
    refine ⟨fnOf _ hg a' * (fnOf _ hg b')⁻¹, ?_, ?_⟩
    · exact mem_locRing.2 ((regAt_fnOf hy hg a').mul
        ((unitAt_fnOf_iff hy hg b').2 hb').inv.regAt)
    · have hb0 : algebraMap S (FractionRing S) b ≠ 0 := by
        refine IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ?_)
        rintro rfl
        exact hb q.asIdeal.zero_mem
      change fieldEquiv j _ = g
      rw [map_mul, map_inv₀, fieldEquiv_fnOf, fieldEquiv_fnOf]
      simp only [a', b', RingEquiv.apply_symm_apply]
      rw [← e, mul_inv_cancel_right₀ hb0]

theorem exists_fieldEquiv (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] (Y : Scheme.{0})
    [IsIntegral Y] (p : Y ⟶ Sp ℂ) (j : Sp S ⟶ Y) [IsOpenImmersion j]
    (hjp : j ≫ p = spMap (algebraMap ℂ S)) :
    ∃ e : Y.functionField ≃+* FractionRing S,
      (∀ a : ℂ, e (GlobalTheory.Cartier.constFn p a) = algebraMap ℂ (FractionRing S) a) ∧
      ∀ (q : PrimeSpectrum S) (g : FractionRing S), g ∈ (locRing (j.base q)).map e.toRingHom ↔
        ∃ a b : S, b ∉ q.asIdeal ∧
          g * algebraMap S (FractionRing S) b = algebraMap S (FractionRing S) a :=
  ⟨fieldEquiv j, fieldEquiv_constFn j p hjp, mem_map_locRing j⟩

end GlobalTheory.OpenSpecField
