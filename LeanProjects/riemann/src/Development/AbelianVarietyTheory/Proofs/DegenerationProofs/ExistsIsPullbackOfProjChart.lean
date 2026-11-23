import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsHomOpenPart
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}
  {Ω' : Type} [Field Ω'] [Algebra o Ω'] {φ : Ω →ₐ[o] Ω'}

theorem IsHom.apply_genericPoint_mem {N : RatModel o Ω'} {q : N.Z ⟶ M.Z} (h : M.IsHom N φ q) {W : M.Z.Opens}
    (hW : (W : Set M.Z).Nonempty) : q (genericPoint N.Z) ∈ W := by
  rw [← N.pt_apply (IsLocalRing.closedPoint Ω')]
  have e : (N.pt ≫ q) (IsLocalRing.closedPoint Ω') =
      (spMap φ.toRingHom ≫ M.pt) (IsLocalRing.closedPoint Ω') := by
    rw [show N.pt ≫ q = _ from h]
  have e' : q (N.pt (IsLocalRing.closedPoint Ω')) = M.pt (spMap φ.toRingHom (IsLocalRing.closedPoint Ω')) := e
  rw [e']
  exact M.top_le_preimage_pt hW (x := spMap φ.toRingHom (IsLocalRing.closedPoint Ω')) trivial

theorem IsHom.comp_id {N Q : RatModel o Ω'} {q : N.Z ⟶ M.Z} {a : Q.Z ⟶ N.Z} (h : M.IsHom N φ q)
    (ha : N.IsHom Q (AlgHom.id o Ω') a) : M.IsHom Q φ (a ≫ q) := by
  simpa only [AlgHom.id_comp] using h.comp ha

theorem exists_isHom_of_projChart {N₁ N₂ : RatModel o Ω'} {q₁ : N₁.Z ⟶ M.Z} {q₂ : N₂.Z ⟶ M.Z}
    (h₁ : M.IsHom N₁ φ q₁) (h₂ : M.IsHom N₂ φ q₂) {J : Type} [Finite J] {t : J → Ω'}
    (h : ∀ z, ∃ (W : M.Z.Opens) (i : J), q₁ z ∈ W ∧ N₁.Div t i z ∧ M.ProjChart N₂ φ q₂ W t) :
    ∃ a, N₂.IsHom N₁ (AlgHom.id o Ω') a := by
  refine exists_isHom_of_local fun z => ?_
  obtain ⟨W, i, hz, hi, hc⟩ := h z
  obtain ⟨U, hU, hD, hR⟩ := hc.2 i hi.1
  refine ⟨q₁ ⁻¹ᵁ W ⊓ ⟨_, N₁.isOpen_setOf_div t i⟩, U, ⟨hz, hi⟩, hU,
    ⟨genericPoint N₂.Z, hD ▸ ⟨h₂.apply_genericPoint_mem ⟨_, hz⟩, div_genericPoint hi.1⟩⟩,
    fun x hx => mem_ringOn.2 fun w hw => ?_⟩
  rw [hR] at hx
  refine (Algebra.adjoin_le ?_ : _ ≤ N₁.O w) hx
  rintro _ (⟨y, hy, rfl⟩ | ⟨j, rfl⟩)
  · exact h₁.map_mem_O (ringOn_le_O (M := M) (U := W) (z := q₁ w) hw.1 hy)
  · exact hw.2.2 j

theorem exists_isPullback_of_projChart_of_isPullback {N P Q : RatModel o Ω'} {U₀ : M.Z.Opens} {b : N.Z ⟶ U₀.toScheme}
    {f : P.Z ⟶ M.Z} {ι : Q.Z ⟶ P.Z} [IsOpenImmersion ι] {g : Q.Z ⟶ U₀.toScheme} (hι : P.IsHom Q (AlgHom.id o Ω') ι)
    (hpb : IsPullback ι g f U₀.ι) {J : Type} [Finite J] {t : J → Ω'} (hb : M.IsHom N φ (b ≫ U₀.ι))
    (hf : M.IsHom P φ f)
    (h : ∀ W : M.Z.Opens, W ≤ U₀ → IsAffineOpen W → (W : Set M.Z).Nonempty →
      M.ProjChart N φ (b ≫ U₀.ι) W t ∧ M.ProjChart P φ f W t) :
    ∃ a₀ : N.Z ⟶ P.Z, P.IsHom N (AlgHom.id o Ω') a₀ ∧ IsPullback a₀ b f U₀.ι := by
  have hU : ∀ {X : Scheme.{0}} (b : X ⟶ U₀.toScheme) (z : X), (b ≫ U₀.ι) z ∈ U₀ := fun b z => by
    rw [Scheme.Hom.comp_apply]
    exact (b z).2
  obtain ⟨a₀, ha₀⟩ : ∃ a, P.IsHom N (AlgHom.id o Ω') a := by
    refine exists_isHom_of_projChart hb hf (t := t) fun z => ?_
    obtain ⟨W, hW, hz, hle⟩ := exists_isAffineOpen_mem_and_subset (hU b z)
    obtain ⟨h1, h2⟩ := h W hle hW ⟨_, hz⟩
    obtain ⟨i, hi⟩ := h1.1 z hz
    exact ⟨W, i, hz, hi, h2⟩
  have hfι : M.IsHom Q φ (ι ≫ f) := hf.comp_id hι
  obtain ⟨c, hc⟩ : ∃ c, N.IsHom Q (AlgHom.id o Ω') c := by
    refine exists_isHom_of_projChart hfι hb (t := t) fun z => ?_
    have hz0 : (ι ≫ f) z ∈ U₀ := hpb.w ▸ hU g z
    obtain ⟨W, hW, hz, hle⟩ := exists_isAffineOpen_mem_and_subset hz0
    obtain ⟨h1, h2⟩ := h W hle hW ⟨_, hz⟩
    obtain ⟨i, hi⟩ := h2.1 (ι z) (by rwa [Scheme.Hom.comp_apply] at hz)
    refine ⟨W, i, hz, ⟨hi.1, fun j => ?_⟩, h1⟩
    rw [hι.O_eq z]
    exact hi.2 j
  have hw : a₀ ≫ f = b ≫ U₀.ι := IsHom.unique (φ := φ) (hf.comp_id ha₀) hb
  obtain ⟨a₁, e₁, e₂⟩ : ∃ a₁ : N.Z ⟶ Q.Z, a₁ ≫ ι = a₀ ∧ a₁ ≫ g = b :=
    ⟨hpb.lift a₀ b hw, hpb.lift_fst _ _ _, hpb.lift_snd _ _ _⟩
  have ha₁ : Q.IsHom N (AlgHom.id o Ω') a₁ := by
    unfold IsHom at hι ha₀ ⊢
    have e : spMap (AlgHom.id o Ω').toRingHom = 𝟙 _ := Spec.map_id _
    rw [e, Category.id_comp] at hι ha₀ ⊢
    rw [← cancel_mono ι, Category.assoc, e₁, hι, ha₀]
  have h₁ : a₁ ≫ c = 𝟙 N.Z := IsHom.unique (φ := AlgHom.id o Ω') (hc.comp_id ha₁) N.isHom_id
  have h₂ : c ≫ a₁ = 𝟙 Q.Z := IsHom.unique (φ := AlgHom.id o Ω') (ha₁.comp_id hc) Q.isHom_id
  have : IsIso a₁ := ⟨c, h₁, h₂⟩
  refine ⟨a₀, ha₀, ?_⟩
  exact hpb.of_iso (asIso a₁).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [← e₁]) (by simp [← e₂]) (by simp) (by simp)

theorem exists_isPullback_of_projChart :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') [IsNoetherianRing o] (N P : RatModel o Ω') (U₀ : M.Z.Opens) (b : N.Z ⟶ U₀.toScheme) (f : P.Z ⟶ M.Z) (J : Type) [Finite J] (t : J → Ω'), M.IsHom N φ (b ≫ U₀.ι) → M.IsHom P φ f → (∀ W : M.Z.Opens, W ≤ U₀ → IsAffineOpen W → (W : Set M.Z).Nonempty → M.ProjChart N φ (b ≫ U₀.ι) W t ∧ M.ProjChart P φ f W t) → ∃ a₀ : N.Z ⟶ P.Z, P.IsHom N (AlgHom.id o Ω') a₀ ∧ IsPullback a₀ b f U₀.ι := by
  intro o Ω _ _ _ M Ω' _ _ φ _ N P U₀ b f J _ t hb hf h
  have hbU : (b ≫ U₀.ι) (genericPoint N.Z) ∈ U₀ := by
    rw [Scheme.Hom.comp_apply]
    exact (b _).2
  have hV : ((f ⁻¹ᵁ U₀ : P.Z.Opens) : Set P.Z).Nonempty := ⟨_, hf.apply_genericPoint_mem ⟨_, hbU⟩⟩
  exact @exists_isPullback_of_projChart_of_isPullback o Ω _ _ _ M Ω' _ _ φ N P (P.openPart _ hV) U₀ b f
    (f ⁻¹ᵁ U₀).ι (inferInstanceAs (IsOpenImmersion (f ⁻¹ᵁ U₀).ι)) (f ∣_ U₀) (P.isHom_openPart _ hV)
    (isPullback_morphismRestrict f U₀).flip J _ t hb hf h

end GlobalTheory.ZH.RatModel
end
