import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.HopfLaurent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapFstSurjective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PinchUniq

section
variable (R : Type) [CommRing R] (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
  [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]

theorem appTop_joint_inj (β : TrivSqZeroExt R M →+* TrivSqZeroExt B M) (hβ : IsSum β (algebraMap R B) id)
    (c : Γ(Sp (TrivSqZeroExt R M), ⊤))
    (h1 : (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).appTop.hom c = 0)
    (h2 : (spMap β).appTop.hom c = 0) : c = 0 := by
  have n1 := congrArg (fun k => k.hom c)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R M).toRingHom))
  have n2 := congrArg (fun k => k.hom c) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom β))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n1 n2
  have h1' : (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R M).toRingHom)).appTop.hom c = 0 := h1
  have h2' : (Spec.map (CommRingCat.ofHom β)).appTop.hom c = 0 := h2
  rw [h1', map_zero] at n1
  rw [h2', map_zero] at n2
  set c' := (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt R M))).hom.hom c with hc'
  have e1 : TrivSqZeroExt.fst c' = 0 := n1.symm
  have e2 : TrivSqZeroExt.snd c' = 0 := by
    have : β c' = TrivSqZeroExt.inl (algebraMap R B (TrivSqZeroExt.fst c')) + TrivSqZeroExt.inr (TrivSqZeroExt.snd c') := by
      conv_lhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq c']
      rw [map_add, hβ.1, hβ.2]; rfl
    have := congrArg TrivSqZeroExt.snd this
    rw [← n2] at this
    simpa using this.symm
  have hc0 : c' = 0 := TrivSqZeroExt.ext e1 e2
  have : c = (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt R M))).inv.hom c' := by
    rw [hc']; simp
  rw [this, hc0, map_zero]

theorem exists_pow_of_appLE_eq_zero {A : Type} [CommRing A] (s a : Γ(Sp A, ⊤)) (n : ℕ)
    {Y : Scheme.{0}} [IsAffine Y] (f : Y ⟶ Sp A)
    (hf : (f.appLE _ _ le_rfl).hom
      (IsLocalization.mk' Γ(Sp A, (Sp A).basicOpen s) a (⟨s ^ n, n, rfl⟩ : Submonoid.powers s)) = 0) :
    ∃ N : ℕ, f.appTop.hom (s ^ N * a) = 0 := by
  have hspec := IsLocalization.mk'_spec Γ(Sp A, (Sp A).basicOpen s) a (⟨s ^ n, n, rfl⟩ : Submonoid.powers s)
  have h3 : (f.appLE _ _ le_rfl).hom (algebraMap Γ(Sp A, ⊤) Γ(Sp A, (Sp A).basicOpen s) a) = 0 := by
    rw [← hspec, map_mul, hf, zero_mul]
  have h4 : (f.appLE ⊤ (f ⁻¹ᵁ (Sp A).basicOpen s) (by simp)).hom a = 0 := by
    rw [← h3]
    show _ = (((Sp A).presheaf.map (homOfLE le_top).op) ≫ f.appLE _ _ le_rfl).hom a
    rw [Scheme.Hom.map_appLE]
  have hle : Y.basicOpen (f.appTop.hom s) ≤ f ⁻¹ᵁ (Sp A).basicOpen s := (Scheme.preimage_basicOpen_top f s).ge
  have h6 : (f.appLE ⊤ (Y.basicOpen (f.appTop.hom s)) (by simp)).hom a = 0 := by
    rw [← Scheme.Hom.appLE_map (i := (homOfLE hle).op), CommRingCat.comp_apply, h4, map_zero]
    simp
  have h5 : f.appTop.hom a |_ (Y.basicOpen (f.appTop.hom s)) = 0 := h6
  obtain ⟨N, hN⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen Y (isAffineOpen_top Y) _ _ h5
  exact ⟨N, by rw [map_mul, map_pow]; exact hN⟩

theorem appLE_basicOpen_joint_inj (β : TrivSqZeroExt R M →+* TrivSqZeroExt B M) (hβ : IsSum β (algebraMap R B) id)
    (s : Γ(Sp (TrivSqZeroExt R M), ⊤)) (t : Γ(Sp (TrivSqZeroExt R M), (Sp (TrivSqZeroExt R M)).basicOpen s))
    (h1 : ((spMap (TrivSqZeroExt.fstHom R R M).toRingHom).appLE _ _ le_rfl).hom t = 0)
    (h2 : ((spMap β).appLE _ _ le_rfl).hom t = 0) : t = 0 := by
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) t
  obtain ⟨N₁, hN₁⟩ := exists_pow_of_appLE_eq_zero s a n _ h1
  obtain ⟨N₂, hN₂⟩ := exists_pow_of_appLE_eq_zero s a n _ h2
  have hc : s ^ (N₁ + N₂) * a = 0 := by
    apply appTop_joint_inj R B M β hβ
    · rw [pow_add, mul_comm (s ^ N₁), _root_.mul_assoc, map_mul, hN₁, mul_zero]
    · rw [pow_add, _root_.mul_assoc, map_mul, hN₂, mul_zero]
  rw [IsLocalization.mk'_eq_zero_iff]
  exact ⟨⟨_, N₁ + N₂, rfl⟩, hc⟩

theorem resLE_appTop_joint_inj (β : TrivSqZeroExt R M →+* TrivSqZeroExt B M) (hβ : IsSum β (algebraMap R B) id)
    (s : Γ(Sp (TrivSqZeroExt R M), ⊤)) (a b : Γ(((Sp (TrivSqZeroExt R M)).basicOpen s).toScheme, ⊤))
    (h1 : ((spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE _ _ le_rfl).appTop.hom a =
      ((spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE _ _ le_rfl).appTop.hom b)
    (h2 : ((spMap β).resLE _ _ le_rfl).appTop.hom a = ((spMap β).resLE _ _ le_rfl).appTop.hom b) : a = b := by
  have conv : ∀ {Y : Scheme.{0}} (f : Y ⟶ Sp (TrivSqZeroExt R M)) (c : Γ(((Sp (TrivSqZeroExt R M)).basicOpen s).toScheme, ⊤)),
      (f.resLE ((Sp (TrivSqZeroExt R M)).basicOpen s) (f ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s) le_rfl).appTop.hom c =
        (f ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s).topIso.inv.hom
          ((f.appLE _ _ le_rfl).hom (((Sp (TrivSqZeroExt R M)).basicOpen s).topIso.hom.hom c)) := by
    intro Y f c
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
    rfl
  rw [conv, conv] at h1 h2
  replace h1 := congrArg (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ
    (Sp (TrivSqZeroExt R M)).basicOpen s).topIso.hom.hom h1
  replace h2 := congrArg (spMap β ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s).topIso.hom.hom h2
  simp only [Iso.inv_hom_id_apply] at h1 h2
  have hz := appLE_basicOpen_joint_inj R B M β hβ s
    (((Sp (TrivSqZeroExt R M)).basicOpen s).topIso.hom.hom a - ((Sp (TrivSqZeroExt R M)).basicOpen s).topIso.hom.hom b)
    (by rw [map_sub, h1, sub_self]) (by rw [map_sub, h2, sub_self])
  exact (((Sp (TrivSqZeroExt R M)).basicOpen s).topIso.commRingCatIsoToRingEquiv).injective (sub_eq_zero.mp hz)

end

theorem uniq : ∀ (R : Type) [CommRing R] (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (β : TrivSqZeroExt R M →+* TrivSqZeroExt B M), IsSum β (algebraMap R B) id → ∀ (X : Scheme.{0}) (x : Sp R ⟶ X) (V : (Sp (TrivSqZeroExt R M)).Opens) (s : Γ((Sp (TrivSqZeroExt R M)), ⊤)), V = (Sp (TrivSqZeroExt R M)).basicOpen s → ∀ (U : X.affineOpens), spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ V ≤ x ⁻¹ᵁ U.1 → ∀ g₁ g₂ : V.toScheme ⟶ X, (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE V _ le_rfl ≫ g₁ = (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ V).ι ≫ x → (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE V _ le_rfl ≫ g₂ = (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ V).ι ≫ x → (spMap β).resLE V _ le_rfl ≫ g₁ = (spMap β).resLE V _ le_rfl ≫ g₂ → g₁ = g₂ := by
  intro R _ B M _ _ _ _ _ _ _ _ _ _ β hβ X x V s hV U hU g₁ g₂ h₁ h₂ h₃
  subst hV
  have hrange : ∀ g : ((Sp (TrivSqZeroExt R M)).basicOpen s).toScheme ⟶ X,
      (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE _ _ le_rfl ≫ g =
        (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s).ι ≫ x →
      Set.range g ⊆ Set.range U.1.ι := by
    rintro g hg _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    obtain ⟨w, hw⟩ := GlobalTheory.Pinch.spMap_fst_surjective R M p.1
    have hwV : w ∈ spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s := by
      rw [Scheme.Hom.mem_preimage, hw]; exact p.2
    have hp : (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE _ _ le_rfl ⟨w, hwV⟩ = p :=
      Subtype.ext (by rw [Scheme.Hom.coe_resLE_apply]; exact hw)
    rw [← hp]
    change ((spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE _ _ le_rfl ≫ g) ⟨w, hwV⟩ ∈ (U.1 : Set X)
    rw [hg]
    exact hU hwV
  haveI : IsAffine U.1.toScheme := U.2
  have f₁ := IsOpenImmersion.lift_fac U.1.ι g₁ (hrange g₁ h₁)
  have f₂ := IsOpenImmersion.lift_fac U.1.ι g₂ (hrange g₂ h₂)
  have ei : (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE _ _ le_rfl ≫ IsOpenImmersion.lift U.1.ι g₁ (hrange g₁ h₁) =
      (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE _ _ le_rfl ≫ IsOpenImmersion.lift U.1.ι g₂ (hrange g₂ h₂) := by
    rw [← cancel_mono U.1.ι, Category.assoc, Category.assoc, f₁, f₂, h₁, h₂]
  have ej : (spMap β).resLE _ _ le_rfl ≫ IsOpenImmersion.lift U.1.ι g₁ (hrange g₁ h₁) =
      (spMap β).resLE _ _ le_rfl ≫ IsOpenImmersion.lift U.1.ι g₂ (hrange g₂ h₂) := by
    rw [← cancel_mono U.1.ι, Category.assoc, Category.assoc, f₁, f₂, h₃]
  have hl : IsOpenImmersion.lift U.1.ι g₁ (hrange g₁ h₁) = IsOpenImmersion.lift U.1.ι g₂ (hrange g₂ h₂) := by
    apply ext_of_isAffine
    ext u
    apply resLE_appTop_joint_inj R B M β hβ s
    · have := congrArg (fun φ => φ.appTop.hom u) ei
      simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using this
    · have := congrArg (fun φ => φ.appTop.hom u) ej
      simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using this
  rw [← f₁, ← f₂, hl]

end GlobalTheory.PinchUniq
