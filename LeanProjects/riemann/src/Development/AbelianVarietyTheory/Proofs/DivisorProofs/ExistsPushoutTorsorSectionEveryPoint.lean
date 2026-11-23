import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FfDescentPairs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleDescends
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushoutFaithfullyFlat
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt.PushSec

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] [IsCommMonObj A]

theorem injective_of_ff {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D']
    (ψ : D →ₐ[R] D') (h : (ψ : D →+* D').FaithfullyFlat) : Function.Injective ψ := by
  letI : Algebra D D' := (ψ : D →+* D').toAlgebra
  haveI : Module.FaithfullyFlat D D' := h
  exact FaithfulSMul.algebraMap_injective D D'

theorem root_map {n : ℕ} {D D' E : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] [CommRing E]
    [Algebra R E] (φ : D →ₐ[R] D') (ρ : D' →ₐ[R] E) (x : Pt A D) (z : Pt A D') (hz : z ^ n = spOver φ ≫ x) :
    (spOver ρ ≫ z) ^ n = spOver (ρ.comp φ) ≫ x := by
  rw [← MonObj.comp_pow, hz, ← Category.assoc, spOver_comp]

theorem pow_mul_inv_eq_one {n : ℕ} {E : Type} [CommRing E] [Algebra R E] {y w u : Pt A E} (hy : y ^ n = u)
    (hw : w ^ n = u) : (y * w⁻¹) ^ n = 1 := by
  rw [mul_pow, inv_pow, hy, hw, mul_inv_cancel]

section Fixed

variable {n : ℕ} {b : Fn0 A} {D D₁ : Type} [CommRing D] [Algebra R D] [CommRing D₁] [Algebra R D₁]

def val (b : Fn0 A) (z₀ : Pt A D₁) (a : D₁) {D' F : Type} [CommRing D'] [Algebra R D'] [CommRing F] [Algebra R F]
    (ρ : D' →ₐ[R] F) (φ' : D₁ →ₐ[R] F) (z : Pt A D') : F :=
  φ' a + b F ((spOver ρ ≫ z) * (spOver φ' ≫ z₀)⁻¹)

variable (hb : IsTorsChar n b) (ψ : D →ₐ[R] D₁) (x : Pt A D) (z₀ : Pt A D₁) (hz₀ : z₀ ^ n = spOver ψ ≫ x)
  (a : D₁)
  (ha : ∀ (E : Type) [CommRing E] [Algebra R E] (α β : D₁ →ₐ[R] E), α.comp ψ = β.comp ψ →
    b E ((spOver β ≫ z₀) * (spOver α ≫ z₀)⁻¹) = β a - α a)

include hz₀ in

theorem val_tors {D' F : Type} [CommRing D'] [Algebra R D'] [CommRing F] [Algebra R F] (φ : D →ₐ[R] D')
    (z : Pt A D') (hz : z ^ n = spOver φ ≫ x) (ρ : D' →ₐ[R] F) (φ' : D₁ →ₐ[R] F) (h : ρ.comp φ = φ'.comp ψ) :
    ((spOver ρ ≫ z) * (spOver φ' ≫ z₀)⁻¹) ^ n = 1 :=
  pow_mul_inv_eq_one (root_map φ ρ x z hz) (by rw [root_map ψ φ' x z₀ hz₀, h])

include hb hz₀ in

theorem map_val {D' F G : Type} [CommRing D'] [Algebra R D'] [CommRing F] [Algebra R F] [CommRing G] [Algebra R G]
    (φ : D →ₐ[R] D') (z : Pt A D') (hz : z ^ n = spOver φ ≫ x) (ρ : D' →ₐ[R] F) (φ' : D₁ →ₐ[R] F)
    (h : ρ.comp φ = φ'.comp ψ) (g₁ : F →ₐ[R] G) :
    g₁ (val b z₀ a ρ φ' z) = val b z₀ a (g₁.comp ρ) (g₁.comp φ') z := by
  unfold val
  rw [map_add, ← hb.1 F G g₁ _ (val_tors ψ x z₀ hz₀ φ z hz ρ φ' h), MonObj.comp_mul, GrpObj.comp_inv,
    ← Category.assoc, ← Category.assoc, spOver_comp, spOver_comp]
  rfl

include hb hz₀ ha in

theorem val_indep {D' F : Type} [CommRing D'] [Algebra R D'] [CommRing F] [Algebra R F] (φ : D →ₐ[R] D')
    (z : Pt A D') (hz : z ^ n = spOver φ ≫ x) (ρ : D' →ₐ[R] F) (α β : D₁ →ₐ[R] F) (hα : ρ.comp φ = α.comp ψ)
    (hβ : ρ.comp φ = β.comp ψ) : val b z₀ a ρ α z = val b z₀ a ρ β z := by
  unfold val
  have t1 := val_tors ψ x z₀ hz₀ φ z hz ρ β hβ
  have t2 : ((spOver β ≫ z₀) * (spOver α ≫ z₀)⁻¹) ^ n = 1 :=
    pow_mul_inv_eq_one (by rw [root_map ψ β x z₀ hz₀, ← hβ]) (by rw [root_map ψ α x z₀ hz₀, ← hα])
  have e : (spOver ρ ≫ z) * (spOver α ≫ z₀)⁻¹ =
      ((spOver ρ ≫ z) * (spOver β ≫ z₀)⁻¹) * ((spOver β ≫ z₀) * (spOver α ≫ z₀)⁻¹) := by
    rw [_root_.mul_assoc, _root_.inv_mul_cancel_left]
  rw [e, hb.2 F _ _ t1 t2, ha F α β (hα.symm.trans hβ)]
  abel

def IsVal {D' : Type} [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (z : Pt A D') (e : D') : Prop :=
  ∀ (F : Type) [CommRing F] [Algebra R F] (ρ : D' →ₐ[R] F) (φ' : D₁ →ₐ[R] F), ρ.comp φ = φ'.comp ψ →
    ρ e = val b z₀ a ρ φ' z

include hb hz₀ ha in

theorem exists_isVal (hψ : (ψ : D →+* D₁).FaithfullyFlat) {D' : Type} [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (z : Pt A D') (hz : z ^ n = spOver φ ≫ x) : ∃ e : D', IsVal (b := b) ψ z₀ a φ z e := by
  obtain ⟨E', _, _, ρ₀, φ₀, hff, hsq⟩ := GlobalTheory.exists_pushout_faithfullyFlat R D D₁ D' ψ φ hψ
  obtain ⟨e, he, -⟩ := GlobalTheory.ff_descent_pairs R D' E' ρ₀ hff (val b z₀ a ρ₀ φ₀ z) (by
    intro G _ _ g₁ g₂ hg₁g₂
    rw [map_val hb ψ x z₀ hz₀ a φ z hz ρ₀ φ₀ hsq g₁, map_val hb ψ x z₀ hz₀ a φ z hz ρ₀ φ₀ hsq g₂, ← hg₁g₂]
    refine val_indep hb ψ x z₀ hz₀ a ha φ z hz _ _ _ ?_ ?_
    · rw [AlgHom.comp_assoc, hsq, AlgHom.comp_assoc]
    · rw [hg₁g₂, AlgHom.comp_assoc, hsq, AlgHom.comp_assoc])
  refine ⟨e, fun F _ _ ρ φ' h ↦ ?_⟩
  obtain ⟨G, _, _, ρ₀', ρ', hff', hsq'⟩ := GlobalTheory.exists_pushout_faithfullyFlat R D' E' F ρ₀ ρ hff
  apply injective_of_ff ρ₀' hff'
  rw [map_val hb ψ x z₀ hz₀ a φ z hz ρ φ' h ρ₀']
  change (ρ₀'.comp ρ) e = _
  rw [hsq', AlgHom.comp_apply, he, map_val hb ψ x z₀ hz₀ a φ z hz ρ₀ φ₀ hsq ρ']
  refine val_indep hb ψ x z₀ hz₀ a ha φ z hz _ _ _ ?_ ?_
  · rw [AlgHom.comp_assoc, hsq, AlgHom.comp_assoc]
  · rw [← hsq', AlgHom.comp_assoc, h, AlgHom.comp_assoc]

theorem isVal_unique (hψ : (ψ : D →+* D₁).FaithfullyFlat) {D' : Type} [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (z : Pt A D') {e e' : D'} (he : IsVal (b := b) ψ z₀ a φ z e) (he' : IsVal (b := b) ψ z₀ a φ z e') : e = e' := by
  obtain ⟨E', _, _, ρ₀, φ₀, hff, hsq⟩ := GlobalTheory.exists_pushout_faithfullyFlat R D D₁ D' ψ φ hψ
  exact injective_of_ff ρ₀ hff ((he E' ρ₀ φ₀ hsq).trans (he' E' ρ₀ φ₀ hsq).symm)

end Fixed

section Sec

variable {n : ℕ} {b : Fn0 A} {D D₁ : Type} [CommRing D] [Algebra R D] [CommRing D₁] [Algebra R D₁]
  (hb : IsTorsChar n b) (ψ : D →ₐ[R] D₁) (x : Pt A D) (z₀ : Pt A D₁) (hz₀ : z₀ ^ n = spOver ψ ≫ x)
  (a : D₁)
  (ha : ∀ (E : Type) [CommRing E] [Algebra R E] (α β : D₁ →ₐ[R] E), α.comp ψ = β.comp ψ →
    b E ((spOver β ≫ z₀) * (spOver α ≫ z₀)⁻¹) = β a - α a)
  (hψ : (ψ : D →+* D₁).FaithfullyFlat)

open Classical in

def sec : RootFn A D := fun D' _ _ φ z ↦
  if h : z ^ n = spOver φ ≫ x then Classical.choose (exists_isVal hb ψ x z₀ hz₀ a ha hψ φ z h) else 0

theorem sec_spec {D' : Type} [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (z : Pt A D')
    (hz : z ^ n = spOver φ ≫ x) : IsVal (b := b) ψ z₀ a φ z (sec hb ψ x z₀ hz₀ a ha hψ D' φ z) := by
  unfold sec
  rw [dif_pos hz]
  exact Classical.choose_spec (exists_isVal hb ψ x z₀ hz₀ a ha hψ φ z hz)

theorem isSec_sec : IsSec n b x (sec hb ψ x z₀ hz₀ a ha hψ) := by
  refine ⟨fun D' _ _ D'' _ _ φ ψ₂ z hz ↦ ?_, fun D' _ _ φ z w hz hw ↦ ?_⟩
  · have hz' : (spOver ψ₂ ≫ z) ^ n = spOver (ψ₂.comp φ) ≫ x := root_map φ ψ₂ x z hz
    refine isVal_unique ψ z₀ a hψ (ψ₂.comp φ) _ (sec_spec hb ψ x z₀ hz₀ a ha hψ _ _ hz') ?_
    intro F _ _ ρ φ' h
    change (ρ.comp ψ₂) _ = _
    rw [sec_spec hb ψ x z₀ hz₀ a ha hψ φ z hz F (ρ.comp ψ₂) φ' (by rw [AlgHom.comp_assoc]; exact h)]
    unfold val
    rw [← Category.assoc, spOver_comp]
  · have hzw : (z * w) ^ n = spOver φ ≫ x := by rw [mul_pow, hz, hw, _root_.mul_one]
    refine isVal_unique ψ z₀ a hψ φ _ (sec_spec hb ψ x z₀ hz₀ a ha hψ _ _ hzw) ?_
    intro F _ _ ρ φ' h
    have tw : (spOver ρ ≫ w) ^ n = 1 := by rw [← MonObj.comp_pow, hw, MonObj.comp_one]
    rw [map_add, sec_spec hb ψ x z₀ hz₀ a ha hψ φ z hz F ρ φ' h, ← hb.1 D' F ρ w hw]
    unfold val
    rw [add_assoc, ← hb.2 F _ _ (val_tors ψ x z₀ hz₀ φ z hz ρ φ' h) tw, MonObj.comp_mul, _root_.mul_right_comm]

end Sec

theorem exists_isSec : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ), HasRoots A n →
    ∀ b : Fn0 A, IsTorsChar n b → ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D),
      ∃ s : RootFn A D, IsSec n b x s := by
  intro R _ A _ _ n hR b hb D _ _ x
  obtain ⟨D₁, _, _, ψ, z₀, hψ, hz₀⟩ := hR D x
  obtain ⟨a, ha⟩ := GlobalTheory.FlatDescent.cocycle_descends R D D₁ ψ hψ
    (fun E _ _ α β ↦ b E ((spOver β ≫ z₀) * (spOver α ≫ z₀)⁻¹)) (by
      intro E _ _ E' _ _ α β g hαβ
      have t : ((spOver β ≫ z₀) * (spOver α ≫ z₀)⁻¹) ^ n = 1 :=
        pow_mul_inv_eq_one (root_map ψ β x z₀ hz₀) (by rw [root_map ψ α x z₀ hz₀, hαβ])
      show b E' _ = g (b E _)
      rw [← hb.1 E E' g _ t, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, spOver_comp,
        spOver_comp]) (by
      intro E _ _ f₁ f₂ f₃ h12 h23
      have t1 : ((spOver f₂ ≫ z₀) * (spOver f₁ ≫ z₀)⁻¹) ^ n = 1 :=
        pow_mul_inv_eq_one (root_map ψ f₂ x z₀ hz₀) (by rw [root_map ψ f₁ x z₀ hz₀, h12])
      have t2 : ((spOver f₃ ≫ z₀) * (spOver f₂ ≫ z₀)⁻¹) ^ n = 1 :=
        pow_mul_inv_eq_one (root_map ψ f₃ x z₀ hz₀) (by rw [root_map ψ f₂ x z₀ hz₀, h23])
      have e : (spOver f₃ ≫ z₀) * (spOver f₁ ≫ z₀)⁻¹ =
          ((spOver f₂ ≫ z₀) * (spOver f₁ ≫ z₀)⁻¹) * ((spOver f₃ ≫ z₀) * (spOver f₂ ≫ z₀)⁻¹) := by
        rw [_root_.mul_comm ((spOver f₂ ≫ z₀) * _), _root_.mul_assoc, _root_.inv_mul_cancel_left]
      show b E _ = b E _ + b E _
      rw [e, hb.2 E _ _ t1 t2])
  exact ⟨_, isSec_sec hb ψ x z₀ hz₀ a (fun E _ _ α β h ↦ ha E α β h) hψ⟩

end GlobalTheory.PtExt.PushSec
