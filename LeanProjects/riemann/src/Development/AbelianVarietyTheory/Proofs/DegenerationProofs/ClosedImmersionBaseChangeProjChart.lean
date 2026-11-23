import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsHomOpenPart
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

theorem IsHom.valR_mem_image_ringOn {o Ω Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Field Ω'] [Algebra o Ω']
    {M : RatModel o Ω} {N : RatModel o Ω'} {φ : Ω →ₐ[o] Ω'} {Y : Scheme.{0}} {j : Y ⟶ M.Z} [IsOpenImmersion j]
    {b : N.Z ⟶ Y} (h : M.IsHom N φ (b ≫ j)) {V : Y.Opens} (hV : ⊤ ≤ (N.pt ≫ b) ⁻¹ᵁ V) (g : Γ(Y, V)) :
    valR (N.pt ≫ b) V g ∈ φ '' (M.ringOn (j ''ᵁ V : M.Z.Opens) : Set Ω) := by
  have hne : ((j ''ᵁ V : M.Z.Opens) : Set M.Z).Nonempty :=
    ⟨_, _, hV (x := IsLocalRing.closedPoint Ω') trivial, rfl⟩
  have hle : V ≤ j ⁻¹ᵁ (j ''ᵁ V) := (j.preimage_image_eq V).ge
  refine ⟨valF M.pt _ ((j.appIso V).inv.hom g), (mem_ringOn_iff_exists hne).2 ⟨_, rfl⟩, ?_⟩
  refine (valR_spMap_comp φ.toRingHom M.pt _ (M.top_le_preimage_pt hne) _).symm.trans ?_
  rw [← show N.pt ≫ b ≫ j = spMap φ.toRingHom ≫ M.pt from h, ← Category.assoc, ← valR_appLE _ j hle hV,
    ← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_appLE]
  exact valR_res _ le_rfl hV g

theorem projChart_of_isPullback : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') (N : RatModel o Ω') (U₀ : M.Z.Opens) (R : Type) [CommRing R] (X : Scheme.{0}) (p : X ⟶ Sp R) (u₀ : U₀.toScheme ⟶ Sp R) (a : N.Z ⟶ X) (b : N.Z ⟶ U₀.toScheme) (H : LB X) (J : Type) (s : J → H.Sec) (t : J → Ω'), IsPullback a b p u₀ → M.IsHom N φ (b ≫ U₀.ι) → ImmBy p H s Set.univ → Crd H s (N.pt ≫ a) t → (∀ (i : J) (z : N.Z), N.Div t i z ↔ a z ∈ nonzeroLocus (s i)) → ∀ W : M.Z.Opens, W ≤ U₀ → IsAffineOpen W → (W : Set M.Z).Nonempty → M.ProjChart N φ (b ≫ U₀.ι) W t := by
  intro o Ω _ _ _ M Ω' _ _ φ N U₀ R _ X p u₀ a b H J s t sq hom imm crd hdiv W hWU hW hne
  obtain ⟨V, rfl⟩ : ∃ V : U₀.toScheme.Opens, U₀.ι ''ᵁ V = W :=
    ⟨U₀.ι ⁻¹ᵁ W, by rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]; exact inf_eq_right.2 hWU⟩
  have hV : IsAffineOpen V := U₀.ι.isAffineOpen_iff_of_isOpenImmersion.1 hW
  have hmem : ∀ z : N.Z, (b ≫ U₀.ι) z ∈ U₀.ι ''ᵁ V ↔ b z ∈ V := fun z =>
    Iff.of_eq (congrArg (b z ∈ ·) (U₀.ι.preimage_image_eq V))
  refine ⟨fun z _ => ?_, fun i hi => ?_⟩
  · have hz : a z ∈ ⨆ i ∈ (Set.univ : Set J), nonzeroLocus (s i) := by rw [imm.1]; trivial
    simp only [Set.mem_univ, iSup_pos, TopologicalSpace.Opens.mem_iSup] at hz
    obtain ⟨i, hi⟩ := hz
    exact ⟨i, (hdiv i z).2 hi⟩
  obtain ⟨hD, r, hr, hgen⟩ := imm.2 i trivial
  have hU : IsAffineOpen (a ⁻¹ᵁ nonzeroLocus (s i) ⊓ b ⁻¹ᵁ V) := by
    have : IsAffine _ := isAffineOpen_top (Sp R)
    have : IsAffine _ := hV
    have : IsAffine _ := hD
    exact .of_isIso (Scheme.Hom.isPullback_resLE sq (US := ⊤) (UT := V) (UX := nonzeroLocus (s i)) le_top le_top
      rfl).isoPullback.hom
  have hset : ((a ⁻¹ᵁ nonzeroLocus (s i) ⊓ b ⁻¹ᵁ V : N.Z.Opens) : Set N.Z) =
      {z' | (b ≫ U₀.ι) z' ∈ U₀.ι ''ᵁ V ∧ N.Div t i z'} :=
    Set.ext fun z => and_comm.trans (and_congr (hmem z).symm (hdiv i z).symm)
  refine ⟨_, hU, hset, le_antisymm (fun x hx => ?_) (Algebra.adjoin_le ?_)⟩
  · have hgp : (b ≫ U₀.ι) (genericPoint N.Z) ∈ U₀.ι ''ᵁ V := by
      have e := congrArg (fun f => f (IsLocalRing.closedPoint Ω')) (show N.pt ≫ b ≫ U₀.ι = _ from hom)
      rw [← N.pt_apply (IsLocalRing.closedPoint Ω')]
      refine (congrArg (· ∈ U₀.ι ''ᵁ V) e).mpr ?_
      exact M.top_le_preimage_pt hne (x := spMap φ.toRingHom (IsLocalRing.closedPoint Ω')) trivial
    have hUne : ((a ⁻¹ᵁ nonzeroLocus (s i) ⊓ b ⁻¹ᵁ V : N.Z.Opens) : Set N.Z).Nonempty :=
      ⟨_, hset.ge ⟨hgp, div_genericPoint hi⟩⟩
    have hpt := N.top_le_preimage_pt hUne
    have ha : ⊤ ≤ (N.pt ≫ a) ⁻¹ᵁ nonzeroLocus (s i) := le_preimage_comp _ a inf_le_left hpt
    have hb : ⊤ ≤ (N.pt ≫ b) ⁻¹ᵁ V := le_preimage_comp _ b inf_le_right hpt
    set A := Algebra.adjoin o (φ '' (M.ringOn (U₀.ι ''ᵁ V : M.Z.Opens) : Set Ω) ∪ Set.range fun j => t j / t i)
    have hB : ∀ g, valR (N.pt ≫ b) V g ∈ A := fun g =>
      Algebra.subset_adjoin (Or.inl (hom.valR_mem_image_ringOn hb g))
    have hA : ∀ g, valR (N.pt ≫ a) (nonzeroLocus (s i)) g ∈ A := fun g => by
      have : Subring.closure (Set.range (constFn p (nonzeroLocus (s i))) ∪ Set.range r) ≤
          A.toSubring.comap (valMap _ _ ha).hom := by
        rw [Subring.closure_le]
        rintro _ (⟨c, rfl⟩ | ⟨j, rfl⟩)
        · show (valMap _ _ ha).hom _ ∈ A
          rw [← valR_eq, valR_constFn _ _ _ ha, Category.assoc, sq.w, ← Category.assoc, ← valR_constFn _ _ _ hb]
          exact hB _
        · show (valMap _ _ ha).hom _ ∈ A
          rw [← valR_eq, eq_div_of_mul_eq hi (CrdCalc.crd_ratio crd (hr j) ha).symm]
          exact Algebra.subset_adjoin (Or.inr ⟨j, rfl⟩)
      rw [valR_eq _ _ ha]
      exact this (hgen.ge (Subring.mem_top g))
    have po := (isIso_pushoutSection_iff sq (US := ⊤) (UT := V) (UX := nonzeroLocus (s i)) le_top le_top rfl).1
      (isIso_pushoutSection_of_isAffineOpen sq _ _ _ (isAffineOpen_top _) hV hD)
    have hcl := CommRingCat.closure_range_union_range_eq_top_of_isPushout po
    have hle : (⊤ : Subring _) ≤ A.toSubring.comap (valMap _ _ hpt).hom := by
      rw [← hcl, Subring.closure_le]
      rintro _ (⟨g, rfl⟩ | ⟨g, rfl⟩)
      · show (valMap _ _ hpt).hom _ ∈ A
        rw [← valR_eq, valR_appLE _ _ _ hpt]
        exact hA g
      · show (valMap _ _ hpt).hom _ ∈ A
        rw [← valR_eq, valR_appLE _ _ _ hpt]
        exact hB g
    obtain ⟨f, rfl⟩ := (mem_ringOn_iff_exists hUne).1 hx
    rw [valF_eq_valR, valR_eq _ _ hpt]
    exact hle (Subring.mem_top f)
  · rintro _ (⟨x, hx, rfl⟩ | ⟨j, rfl⟩)
    · exact mem_ringOn.2 fun z hz => hom.map_mem_O (mem_ringOn.1 hx _ (hset.le hz).1)
    · exact mem_ringOn.2 fun z hz => (hset.le hz).2.2 j

end GlobalTheory.ZH.RatModel
end
