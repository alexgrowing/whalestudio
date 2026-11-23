import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkIdComapOfAffine
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmpStOfSabExtNormalSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SabExtNormalStOfHomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VanishingIdealComapOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsEtaleCompletionCompOpenImmersion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabDescentOfFieldExtension
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TorRef

theorem hasToricChart_of_genIso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (Z : GMod Xo c) (e : gen Y ≅ gen Z),
    Y.jQ ≫ e.hom = Z.jQ → (∀ x ∈ genBd Y, HasToricChart Y x) → ∀ x ∈ genBd Z, HasToricChart Z x := by
  intro E _ _ _ H D l Xo c Y Z e hjQ hY x hx
  have hZY : Z.jQ ≫ e.inv = Y.jQ := by rw [← hjQ, Category.assoc, Iso.hom_inv_id, Category.comp_id]

  have hbd : ∀ w : gen Y, e.hom w ∈ genBd Z ↔ w ∈ genBd Y := by
    intro w
    rw [mem_genBd, mem_genBd, not_iff_not]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      rw [← hZY, Scheme.Hom.comp_apply, hz, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
      rfl
    · rintro ⟨z, rfl⟩
      exact ⟨z, by rw [← hjQ, Scheme.Hom.comp_apply]⟩
  have hxe : e.hom (e.inv x) = x := by
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  obtain ⟨k, hk, m, d, ξ, t, P, γ, hξ, h1, h2, h3, ⟨μ⟩, h5, h6, h7⟩ :=
    hY (e.inv x) (by rw [← hbd, hxe]; exact hx)

  obtain ⟨t₀, n₁, n₂, -⟩ := cmpSt_of_sabExtNormalSt (sabExtNormalSt_of_homExtNormalSt homExtNormal) E H D l Xo c
    c.F (𝓞 c.F) (RingHom.id c.F) (algebraMap (𝓞 c.F) c.F) Y Z e.inv hZY
    (GlobalTheory.ModelRelCompare.normal_genericFibre Z (GlobalTheory.ModelRelCompare.isDedFrac_in_use c).1).1
  obtain ⟨a, -⟩ := GlobalTheory.LevelCover.sab_cancel n₂ μ (ξ ≫ e.hom) (by rw [Category.assoc, e.hom_inv_id_assoc])
  obtain ⟨b, -⟩ := GlobalTheory.LevelCover.sab_comp a n₁ (e := (ξ ≫ e.hom) ≫ genι Z) rfl

  have hcomap : (genBdIdeal Z).comap e.hom = genBdIdeal Y :=
    GlobalTheory.vanishingIdeal_comap_of_isOpenImmersion (gen Y) (gen Z) e.hom (genBd Z) (genBd Y) fun w => (hbd w).symm
  refine ⟨k, hk, m, d, ξ ≫ e.hom, t, P, γ, ?_, ?_, ?_, ?_, ⟨b⟩, h5, h6, h7⟩
  · change e.hom (ξ _) = x
    rw [hξ, hxe]
  · exact GlobalTheory.MemberEt.isEtaleCompletion_comp_openImmersion _ _ e.hom _ ξ h1
  · have h2' := h2
    rw [← hcomap, GlobalTheory.VanStalk.stalkId_comap, Ideal.map_map] at h2'
    rw [Scheme.stalkClosedPointTo_comp]
    exact h2'
  · intro p
    rw [Scheme.Hom.comp_apply, hbd]
    exact h3 p

end GlobalTheory.TorRef
