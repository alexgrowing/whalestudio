import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.Spread

section

variable {k V : Type} [CommRing k] [CommRing V] [Algebra k V] {P Q T : Scheme.{0}}
  {p : P ⟶ Sp k} {q : Q ⟶ Sp k} {t : T ⟶ Sp V} {τ : T ⟶ P} {τ' : T ⟶ Q}

theorem eq_isoPullback_hom_comp_bcMap (hτ : IsPullback τ t p (spMap (algebraMap k V)))
    (R : Subalgebra k V) (σ : T ⟶ pullback p (spMap (algebraMap k R)))
    (h₁ : σ ≫ pullback.fst _ _ = τ) (h₂ : σ ≫ pullback.snd _ _ = t ≫ spMap R.val.toRingHom) :
    σ = hτ.isoPullback.hom ≫ bcMap p R.val := by
  apply pullback.hom_ext
  · rw [h₁, Category.assoc, bcMap_fst, IsPullback.isoPullback_hom_fst]
  · rw [h₂, Category.assoc, bcMap_snd, ← Category.assoc, IsPullback.isoPullback_hom_snd]

theorem comp_eq_id_of_models [Flat p] [IsSeparated p]
    (hτ : IsPullback τ t p (spMap (algebraMap k V)))
    (hτ' : IsPullback τ' t q (spMap (algebraMap k V))) (R : Subalgebra k V)
    (f : pullback p (spMap (algebraMap k R)) ⟶ pullback q (spMap (algebraMap k R)))
    (g : pullback q (spMap (algebraMap k R)) ⟶ pullback p (spMap (algebraMap k R)))
    (hf : f ≫ pullback.snd _ _ = pullback.snd _ _) (hg : g ≫ pullback.snd _ _ = pullback.snd _ _)
    (hf' : hτ.isoPullback.hom ≫ bcMap p R.val ≫ f ≫ pullback.fst _ _ = τ')
    (hg' : hτ'.isoPullback.hom ≫ bcMap q R.val ≫ g ≫ pullback.fst _ _ = τ) :
    f ≫ g = 𝟙 _ := by

  have hu : hτ.isoPullback.hom ≫ bcMap p R.val ≫ f = hτ'.isoPullback.hom ≫ bcMap q R.val := by
    apply eq_isoPullback_hom_comp_bcMap hτ' R
    · simpa only [Category.assoc] using hf'
    · rw [Category.assoc, Category.assoc, hf, bcMap_snd, ← Category.assoc,
        IsPullback.isoPullback_hom_snd]

  have hfst : bcMap p R.val ≫ f ≫ g ≫ pullback.fst _ _ = pullback.fst _ _ := by
    rw [← cancel_epi hτ.isoPullback.hom, reassoc_of% hu, IsPullback.isoPullback_hom_fst]
    exact hg'

  refine hom_ext_bcMap p R.val Subtype.val_injective (pullback.snd p (spMap (algebraMap k R)))
    ?_ ?_
  · rw [Category.assoc, hg, hf, Category.id_comp]
  · rw [Category.comp_id]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hfst, bcMap_fst]
    · rw [Category.assoc, Category.assoc, hg, hf]

end

end GlobalTheory.Spread

namespace GlobalTheory

open Spread

theorem smooth_models_iso_over_fg_subalgebra :
    ∀ (k V : Type) [CommRing k] [CommRing V] [Algebra k V] (P Q T : Scheme.{0}) (p : P ⟶ Sp k) (q : Q ⟶ Sp k) (t : T ⟶ Sp V) (τ : T ⟶ P) (τ' : T ⟶ Q), Smooth p → IsSeparated p → QuasiCompact p → Smooth q → IsSeparated q → QuasiCompact q → IsPullback τ t p (spMap (algebraMap k V)) → IsPullback τ' t q (spMap (algebraMap k V)) → ∃ (R : Subalgebra k V) (e : pullback p (spMap (algebraMap k R)) ≅ pullback q (spMap (algebraMap k R))), R.FG ∧ e.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧ ∀ σ : T ⟶ pullback p (spMap (algebraMap k R)), σ ≫ pullback.fst _ _ = τ → σ ≫ pullback.snd _ _ = t ≫ spMap R.val.toRingHom → σ ≫ e.hom ≫ pullback.fst _ _ = τ' := by
  intro k V _ _ _ P Q T p q t τ τ' _ _ _ _ _ _ hτ hτ'

  have hΦ : (hτ.isoPullback.inv ≫ τ') ≫ q = pullback.fst _ _ ≫ p := by
    rw [← hτ.isoPullback_inv_fst]
    simp only [Category.assoc, hτ.w, hτ'.w]
  have hΨ : (hτ'.isoPullback.inv ≫ τ) ≫ p = pullback.fst _ _ ≫ q := by
    rw [← hτ'.isoPullback_inv_fst]
    simp only [Category.assoc, hτ.w, hτ'.w]

  obtain ⟨R₁, ψ₁, hR₁, hψ₁, hψ₁'⟩ := exists_fg_comp_eq p q _ hΦ
  obtain ⟨R, ψ₂, hR, hle, hψ₂⟩ :=
    exists_fg_forall_comp_eq q p (fun _ : Unit ↦ hτ'.isoPullback.inv ≫ τ) (fun _ ↦ hΨ) R₁ hR₁

  have ha : (bcMap p (Subalgebra.inclusion hle) ≫ ψ₁) ≫ q =
      pullback.snd _ _ ≫ spMap (algebraMap k R) := by
    rw [Category.assoc, hψ₁, bcMap_fst_assoc, pullback.condition]
  have hb : ψ₂ () ≫ p = pullback.snd _ _ ≫ spMap (algebraMap k R) := by
    rw [(hψ₂ ()).1, pullback.condition]
  obtain ⟨f, hf₁, hf₂⟩ : ∃ f : pullback p (spMap (algebraMap k R)) ⟶
      pullback q (spMap (algebraMap k R)),
      f ≫ pullback.fst _ _ = bcMap p (Subalgebra.inclusion hle) ≫ ψ₁ ∧
        f ≫ pullback.snd _ _ = pullback.snd _ _ :=
    ⟨pullback.lift _ _ ha, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨g, hg₁, hg₂⟩ : ∃ g : pullback q (spMap (algebraMap k R)) ⟶
      pullback p (spMap (algebraMap k R)),
      g ≫ pullback.fst _ _ = ψ₂ () ∧ g ≫ pullback.snd _ _ = pullback.snd _ _ :=
    ⟨pullback.lift _ _ hb, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

  have hf' : hτ.isoPullback.hom ≫ bcMap p R.val ≫ f ≫ pullback.fst _ _ = τ' := by
    rw [hf₁, bcMap_comp_of_eq_assoc p (Subalgebra.inclusion hle) R.val R₁.val (fun _ ↦ rfl), hψ₁',
      Iso.hom_inv_id_assoc]
  have hg' : hτ'.isoPullback.hom ≫ bcMap q R.val ≫ g ≫ pullback.fst _ _ = τ := by
    rw [hg₁, (hψ₂ ()).2, Iso.hom_inv_id_assoc]
  refine ⟨R, ⟨f, g, comp_eq_id_of_models hτ hτ' R f g hf₂ hg₂ hf' hg',
    comp_eq_id_of_models hτ' hτ R g f hg₂ hf₂ hg' hf'⟩, hR, hf₂, ?_⟩
  intro σ h₁ h₂
  rw [eq_isoPullback_hom_comp_bcMap hτ R σ h₁ h₂, Category.assoc]
  exact hf'

end GlobalTheory
