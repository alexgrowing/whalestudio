import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.BdDim GlobalTheory.Spread
open scoped CategoryTheory.Obj

namespace GlobalTheory.FibreSpread

theorem isGrpPullback_transition {k R S : Type} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (A : Over (Sp k)) [GrpObj A] (ρ : R →ₐ[k] S) :
    IsGrpPullback ((Over.pullback (spMap (algebraMap k S))).obj A) ((Over.pullback (spMap (algebraMap k R))).obj A)
      (spMap ρ.toRingHom) (bcMap A.hom ρ) :=
  (isGrpPullback_pullback A _).cancel
    ((isGrpPullback_pullback A _).congr (spMap_algHom_comp ρ).symm (bcMap_fst A.hom ρ).symm) (bcMap_snd A.hom ρ)

theorem exists_descend {K Ω : Type} [CommRing K] [CommRing Ω] [Algebra K Ω] (A B : Over (Sp K))
    [QuasiCompact A.hom] [QuasiSeparated A.hom] [LocallyOfFinitePresentation B.hom]
    (f : (Over.pullback (spMap (algebraMap K Ω))).obj A ⟶ (Over.pullback (spMap (algebraMap K Ω))).obj B) :
    ∃ R : Subalgebra K Ω, R.FG ∧ ∀ L : Subalgebra K Ω, R ≤ L →
      ∃ g : (Over.pullback (spMap (algebraMap K L))).obj A ⟶ (Over.pullback (spMap (algebraMap K L))).obj B,
        f.left ≫ bcMap B.hom L.val = bcMap A.hom L.val ≫ g.left := by
  have hfw : f.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w f
  obtain ⟨R, ψ, hR, hψ, hψf⟩ := exists_fg_comp_eq A.hom B.hom (f.left ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ _) hfw)
  refine ⟨R, hR, fun L hle => ?_⟩
  let ρ : R →ₐ[K] L := Subalgebra.inclusion hle
  have hw : (bcMap A.hom ρ ≫ ψ) ≫ B.hom = pullback.snd _ _ ≫ spMap (algebraMap K L) := by
    rw [Category.assoc, hψ, bcMap_fst_assoc, pullback.condition]
  let g₀ : pullback A.hom (spMap (algebraMap K L)) ⟶ pullback B.hom (spMap (algebraMap K L)) :=
    pullback.lift (bcMap A.hom ρ ≫ ψ) (pullback.snd _ _) hw
  let f₀ : pullback A.hom (spMap (algebraMap K Ω)) ⟶ pullback B.hom (spMap (algebraMap K Ω)) := f.left
  have hf₀ : f₀ ≫ pullback.snd _ _ = pullback.snd _ _ := hfw
  have hψ₀ : bcMap A.hom R.val ≫ ψ = f₀ ≫ pullback.fst _ _ := hψf
  refine ⟨Over.homMk g₀ (pullback.lift_snd _ _ _), ?_⟩
  symm
  change bcMap A.hom L.val ≫ g₀ = f₀ ≫ bcMap B.hom L.val
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, bcMap_fst, pullback.lift_fst,
      bcMap_comp_of_eq_assoc A.hom ρ L.val R.val fun _ ↦ rfl, hψ₀]
  · rw [Category.assoc, Category.assoc, bcMap_snd, pullback.lift_snd, bcMap_snd, reassoc_of% hf₀]

theorem exists_fg_sameFibre {K Ω : Type} [CommRing K] [CommRing Ω] [Algebra K Ω] (A B : Over (Sp K)) [GrpObj A]
    [GrpObj B] (hA : IsSemiAbelian A) (hB : IsSemiAbelian B)
    (h : SameFibre A (spMap (algebraMap K Ω)) B (spMap (algebraMap K Ω))) :
    ∃ L : Subalgebra K Ω, L.FG ∧ SameFibre A (spMap (algebraMap K L)) B (spMap (algebraMap K L)) := by
  obtain ⟨C, _, φ, ψ, hφ, hψ⟩ := h
  obtain ⟨a, ha, -⟩ := grpPullback_iso (isGrpPullback_pullback A _) hφ
  obtain ⟨b, hb, -⟩ := grpPullback_iso hψ (isGrpPullback_pullback B _)
  have := hA.smooth
  have := hB.smooth
  have := hA.separated
  have := hB.separated
  have := hA.quasiCompact
  have := hB.quasiCompact
  obtain ⟨R₁, hR₁, h₁⟩ := exists_descend A B (a ≪≫ b).hom
  obtain ⟨R₂, hR₂, h₂⟩ := exists_descend B A (a ≪≫ b).inv
  obtain ⟨f, hf⟩ := h₁ (R₁ ⊔ R₂) le_sup_left
  obtain ⟨g, hg⟩ := h₂ (R₁ ⊔ R₂) le_sup_right
  refine ⟨R₁ ⊔ R₂, hR₁.sup hR₂, ?_⟩
  generalize R₁ ⊔ R₂ = L at f g hf hg
  have gA := isGrpPullback_transition A L.val
  have gB := isGrpPullback_transition B L.val
  have : IsSchemeTheoreticallyDominant (spMap L.val.toRingHom) :=
    ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom L.val.toRingHom) Subtype.val_injective
  obtain ⟨_, _⟩ := ExtUnique.flat_and_isSeparated_of_isSemiAbelian _
    (IsSemiAbelian.pullback (f := spMap (algebraMap K L)) _ hA)
  obtain ⟨_, _⟩ := ExtUnique.flat_and_isSeparated_of_isSemiAbelian _
    (IsSemiAbelian.pullback (f := spMap (algebraMap K L)) _ hB)
  have : IsIso f := ExtUnique.isIso_of_isPullback gA.1 gB.1 (a ≪≫ b) f g hf hg
  have : IsMonHom (a ≪≫ b).hom := by rw [Iso.trans_hom]; infer_instance
  have : IsMonHom (asIso f).hom := ExtUnique.isMonHom_of_isGrpPullback gA gB (a ≪≫ b).hom f hf
  exact ⟨_, _, _, _, isGrpPullback_pullback A _,
    ((isGrpPullback_of_iso (asIso f)).comp (isGrpPullback_pullback B _)).congr (Category.id_comp _) rfl⟩

end GlobalTheory.FibreSpread

namespace GlobalTheory

theorem sameFibre_spreads_to_fg_subalgebra : ∀ (k₀ k : Type) [Field k₀] [Field k] (ι : k₀ →+* k) (Y : Scheme.{0}) (s : Y ⟶ Sp k₀) (G G' : Over Y) [GrpObj G] [GrpObj G'] (z : Sp k ⟶ Y), LocallyOfFiniteType s → IsSemiAbelian G → IsSemiAbelian G' → z ≫ s = spMap ι → SameFibre G z G' z → ∃ (A : Type) (_ : CommRing A) (_ : Algebra k₀ A) (j : A →+* k) (a : Sp A ⟶ Y), Algebra.FiniteType k₀ A ∧ Function.Injective j ∧ spMap j ≫ a = z ∧ a ≫ s = spMap (algebraMap k₀ A) ∧ SameFibre G a G' a := by
  intro k₀ k _ _ ι Y s G G' _ _ z hs hG hG' hz h
  letI := ι.toAlgebra
  have : LocallyOfFinitePresentation s := inferInstance
  obtain ⟨R, y, hR, -, hy⟩ := exists_fg_points s (fun _ : Unit => z) (fun _ => hz) ⊥ Subalgebra.fg_bot
  obtain ⟨hy₁, hy₂⟩ := hy ()
  have hy₃ : spMap (algebraMap R k) ≫ y () = z := hy₂
  have p := isGrpPullback_pullback G (y ())
  have p' := isGrpPullback_pullback G' (y ())
  obtain ⟨C, _, φ, ψ, hφ, hψ⟩ := h
  have w : φ ≫ G.hom = (C.hom ≫ spMap (algebraMap R k)) ≫ y () := by rw [Category.assoc, hy₃, hφ.1.w]
  have w' : ψ ≫ G'.hom = (C.hom ≫ spMap (algebraMap R k)) ≫ y () := by rw [Category.assoc, hy₃, hψ.1.w]
  obtain ⟨L, hL, D, _, α, β, hα, hβ⟩ := FibreSpread.exists_fg_sameFibre (Ω := k) _ _
    (IsSemiAbelian.pullback (f := y ()) _ hG) (IsSemiAbelian.pullback (f := y ()) _ hG')
    ⟨C, _, pullback.lift φ _ w, pullback.lift ψ _ w',
      p.cancel (hφ.congr hy₃.symm (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _),
      p'.cancel (hψ.congr hy₃.symm (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)⟩
  have : Algebra.FiniteType k₀ R := (Subalgebra.fg_iff_finiteType R).1 hR
  have : Algebra.FiniteType R L := (Subalgebra.fg_iff_finiteType L).1 hL
  refine ⟨L, inferInstance, inferInstance, L.val.toRingHom, spMap (algebraMap R L) ≫ y (),
    Algebra.FiniteType.trans (S := R) ‹_› ‹_›, Subtype.val_injective, ?_, ?_, D, _, _, _, hα.comp p, hβ.comp p'⟩
  · rw [← Category.assoc, spMap_algHom_comp, hy₃]
  · rw [Category.assoc, hy₁]
    exact spMap_algHom_comp (IsScalarTower.toAlgHom k₀ R L)

end GlobalTheory

end
