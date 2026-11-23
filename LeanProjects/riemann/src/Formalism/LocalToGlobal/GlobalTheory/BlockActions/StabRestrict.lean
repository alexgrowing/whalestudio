import Formalism.LocalToGlobal.GlobalTheory.BlockActions.InJSymRestrict
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.StabiliserBijectiveOfInjection

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix
open scoped TensorProduct
open IsDedekindDomain

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

set_option maxHeartbeats 4000000 in
theorem stab_restrict (Tf : FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP)
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl))
    (hγ : γ ∈ ((Tf.cls D.R.m le_rfl (Or.inr rfl)).stabI ((D.fm u).til c)).range)
    (δ : UJ (sigD D : D.host.E →+* D.host.E) (gramP D))
    (hδ : IsExt D Tf.til.z0 (RingHom.id D.host.E) δ.1.1 ((Tf.til.ga c).1.1 * γ.1.1 * ((Tf.til.ga c)⁻¹).1.1)) :
    δ ∈ (Tf.clsP.stabI c).range := by
  set Km := Tf.cls D.R.m le_rfl (Or.inr rfl) with hKm
  rw [Km.stabI_range] at hγ
  obtain ⟨κ, hκ, hκe⟩ := Subgroup.mem_map.mp hγ
  rw [Tf.clsP.stabI_range]
  have hdet : IsUnit ((Tf.clsP.y c).1.1).det := (Matrix.isUnit_iff_isUnit_det _).mp (Tf.clsP.y c).1.isUnit
  obtain ⟨g, hg, hu⟩ := til_ext Tf (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Tf.clsP.y c).1.1
  set Gc : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := ((Matrix.isUnit_iff_isUnit_det g).mpr (hu hdet)).unit with hGcdef
  have hGcv : Gc.1 = g := IsUnit.unit_spec _
  have hGc : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Tf.clsP.y c).1.1 Gc.1 := by rw [hGcv]; exact hg
  have e1 := Tf.tilAd.til_ad c Gc hGc
  have hGc1 : Gc = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Tf.til.ga c).1 * (Km.y ((D.fm u).til c)).1 *
      ((Tf.tilAd.ka c).1)⁻¹ := eq_mul_inv_of_mul_eq e1.symm
  have hbc : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 = (Km.y ((D.fm u).til c)).1 * κ * ((Km.y ((D.fm u).til c)).1)⁻¹ := by
    rw [← hκe]; rfl
  set Γ : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :=
    bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ((Tf.til.ga c).1 * γ.1 * ((Tf.til.ga c)⁻¹).1) with hΓ
  have hGK : Gc⁻¹ * Γ * Gc ∈ Km.lev.U := by
    have e : Gc⁻¹ * Γ * Gc = (Tf.tilAd.ka c).1 * κ * ((Tf.tilAd.ka c).1)⁻¹ := by
      rw [hΓ, map_mul, map_mul, hbc, hGc1]
      have hi : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ((Tf.til.ga c)⁻¹).1 = (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Tf.til.ga c).1)⁻¹ := by
        rw [← map_inv]; rfl
      rw [hi]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Tf.tilAd.ka c).2 hκ) (Subgroup.inv_mem _ (Tf.tilAd.ka c).2)
  have hinv : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ((Tf.clsP.y c).1.1)⁻¹ (Gc⁻¹).1 :=
    isExt_inv hGc (Units.inv_mul Gc) (Matrix.mul_nonsing_inv _ hdet)
  have hΓ1 : (Γ.1 : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) =
      ((Tf.til.ga c).1.1 * γ.1.1 * ((Tf.til.ga c)⁻¹).1.1).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    rw [hΓ]; rfl
  have hΓE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (δ.1.1.map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) Γ.1 := by
    rw [hΓ1]; exact isExt_map hδ
  set K : GL (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :=
    ((Tf.clsP.y c).1)⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ.1 * (Tf.clsP.y c).1 with hK
  have hKE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) K.1 (Gc⁻¹ * Γ * Gc).1 := by
    have e : K.1 = ((Tf.clsP.y c).1.1)⁻¹ * δ.1.1.map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * (Tf.clsP.y c).1.1 := by
      rw [hK, Units.val_mul, Units.val_mul, Matrix.coe_units_inv]; rfl
    rw [e, Units.val_mul, Units.val_mul]
    exact isExt_mul (isExt_mul hinv hΓE) hGc
  have hKU := lev_mem Tf K _ hKE hGK
  refine Subgroup.mem_map.mpr ⟨K, hKU, ?_⟩
  show (Tf.clsP.y c).1 * K * ((Tf.clsP.y c).1)⁻¹ = _
  rw [hK]
  group

end Formalism.L2.GlobalTheoryTheory.Br
