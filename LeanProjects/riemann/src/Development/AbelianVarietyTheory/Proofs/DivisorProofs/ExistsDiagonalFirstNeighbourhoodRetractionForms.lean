import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormQuotientClassEqOfRelDifferences
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormsMapOfDividedPowerDerivationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivPowerCompatRelFiltrationTwoSidedRelEqBotOfBasStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers TrivSqZeroExt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm
open GlobalTheory.CrysConn

namespace GlobalTheory.PDForm.Nbhd

open GlobalTheory.SmoothLift

attribute [local instance] opK isCentral_K isTower_K

set_option maxHeartbeats 4000000 in

theorem exists_retraction : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0})
    (t : X ⟶ Sp R), ∃ (S : Thick κ t ⥤ Thick κ t) (u v : 𝟭 _ ⟶ S)
    (r1 : ∀ T, (KK κ t).M1.obj (S.obj T) →+ (KK κ t).M1.obj T)
    (r2 : ∀ T, (KK κ t).M2.obj (S.obj T) →+ (KK κ t).M2.obj T)
    (r3 : ∀ T, (KK κ t).M3.obj (S.obj T) →+ (KK κ t).M3.obj T),
    ((∀ (T T' : Thick κ t) (φ : T ⟶ T') x, r1 T' ((KK κ t).M1.map (S.map φ) x) = (KK κ t).M1.map φ (r1 T x)) ∧
      (∀ T x, r1 T ((KK κ t).M1.map (u.app T) x) = 0) ∧ (∀ T x, r1 T ((KK κ t).M1.map (v.app T) x) = x)) ∧
    ((∀ (T T' : Thick κ t) (φ : T ⟶ T') x, r2 T' ((KK κ t).M2.map (S.map φ) x) = (KK κ t).M2.map φ (r2 T x)) ∧
      (∀ T x, r2 T ((KK κ t).M2.map (u.app T) x) = 0) ∧ (∀ T x, r2 T ((KK κ t).M2.map (v.app T) x) = x)) ∧
    (∀ (T T' : Thick κ t) (φ : T ⟶ T') x, r3 T' ((KK κ t).M3.map (S.map φ) x) = (KK κ t).M3.map φ (r3 T x)) ∧
      (∀ T x, r3 T ((KK κ t).M3.map (u.app T) x) = 0) ∧ (∀ T x, r3 T ((KK κ t).M3.map (v.app T) x) = x) := by
  intro R _ I κ X t
  have hr : ∀ T : Thick κ t, ∀ x ∈ rel R T.δ, ∀ y, x * y ∈ rel R T.δ := fun T ↦ (GlobalTheory.T.divPowerCompatRel_filtration_twoSided_rel_eq_bot_of_base.1 R T.B T.J T.δ).1
  have H := fun T : Thick κ t ↦ GlobalTheory.T.exists_formsMap_of_dividedPowerDerivation R T.B T.J T.δ (ER T) (nb T).J (nb T).δ (fstA T) (sndA T)
    (sndA_mul T) (sndA_algebraMap T) (fun n a ha ↦ sndA_dpow T n a ha)
  choose ρ ha hm h0 h1 hrel hone hdeg using H
  have natK : ∀ (j : ℕ) (T T' : Thick κ t) (φ : T ⟶ T') (x : K R (nb T).δ j),
      rK (nb T').δ (ha T') (hrel T') (hdeg T') j (km (SemiHom.of_algHom (nbAlg φ)) (nbF.map φ).dp j x) =
        km (SemiHom.of_algHom φ.φ) φ.dp j (rK (nb T).δ (ha T) (hrel T) (hdeg T) j x) := by
    intro j T T' φ x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx : (x : DR R (ER T)) ∈ ⋀[ER T]^j Ω[ER T⁄R] := x.2
    have hd := hdeg T j _ hx
    let y := hd.choose
    have hy : y ∈ ⋀[T.B]^j Ω[T.B⁄R] := hd.choose_spec.1
    have hρy : ρ T x - y ∈ rel R T.δ := hd.choose_spec.2
    rw [rK_spec (nb T).δ (ha T) (hrel T) (hdeg T) (y := ⟨y, hy⟩) hρy, km_mk]
    have e := add_mem (natAgree hr φ (ρ T) (ρ T') (ha T) (hm T) (h0 T) (h1 T) (ha T') (hm T') (h0 T') (h1 T') x)
      (mDR_mem_rel (SemiHom.of_algHom φ.φ) φ.dp hρy)
    rw [map_sub, sub_add_sub_cancel] at e
    exact rK_spec (nb T').δ (ha T') (hrel T') (hdeg T') (x := (SemiHom.of_algHom (nbAlg φ)).mOm j x)
      (y := (SemiHom.of_algHom φ.φ).mOm j ⟨y, hy⟩) e
  have uK : ∀ (j : ℕ), j ≠ 0 → ∀ (T : Thick κ t) (x : K R T.δ j),
      rK (nb T).δ (ha T) (hrel T) (hdeg T) j (km (SemiHom.of_algHom (inlMap T).φ) (inlMap T).dp j x) = 0 := by
    intro j hj T x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have e := uAgree hr T (ρ T) (ha T) (hm T) (h0 T) (h1 T) x
    rw [algebraMapInv_eq_zero hj x.2, map_zero] at e
    have e' : ρ T ((SemiHom.of_algHom (inlMap T).φ).mDR x) - ((0 : Om R T.B j) : DR R T.B) ∈ rel R T.δ := by
      rw [ZeroMemClass.coe_zero]; exact e
    exact (rK_spec (nb T).δ (ha T) (hrel T) (hdeg T) (x := (SemiHom.of_algHom (inlMap T).φ).mOm j x) e').trans
      (Submodule.Quotient.mk_zero _)
  have vK : ∀ (j : ℕ) (T : Thick κ t) (x : K R T.δ j),
      rK (nb T).δ (ha T) (hrel T) (hdeg T) j (km (SemiHom.of_algHom (difMap T).φ) (difMap T).dp j x) = x := by
    intro j T x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact rK_spec (nb T).δ (ha T) (hrel T) (hdeg T) (x := (SemiHom.of_algHom (difMap T).φ).mOm j x) (y := x)
      (vAgree hr T (ρ T) (ha T) (hm T) (h0 T) (h1 T) x)
  refine ⟨nbF, uN, vN, fun T ↦ r1 (nb T).δ (ha T) (hrel T) (hone T), fun T ↦ rK (nb T).δ (ha T) (hrel T) (hdeg T) 2,
    fun T ↦ rK (nb T).δ (ha T) (hrel T) (hdeg T) 3, ⟨?_, ?_, ?_⟩, ⟨fun T T' φ x ↦ natK 2 T T' φ x,
      fun T x ↦ uK 2 (by norm_num) T x, fun T x ↦ vK 2 T x⟩, fun T T' φ x ↦ natK 3 T T' φ x,
      fun T x ↦ uK 3 (by norm_num) T x, fun T x ↦ vK 3 T x⟩
  · intro T T' φ x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hd := hone T x
    let ω := hd.choose
    have hω : ρ T (ι1 x) - ι1 ω ∈ rel R T.δ := hd.choose_spec
    have e := add_mem (natAgree hr φ (ρ T) (ρ T') (ha T) (hm T) (h0 T) (h1 T) (ha T') (hm T') (h0 T') (h1 T') (ι1 x))
      (mDR_mem_rel (SemiHom.of_algHom φ.φ) φ.dp hω)
    rw [map_sub, sub_add_sub_cancel, SemiHom.mDR_ι, SemiHom.mDR_ι] at e
    have l := divPowerCompatOneForm_retraction_spec (nb T).δ (ha T) (hrel T) (hone T) (x := x) hω
    exact (divPowerCompatOneForm_retraction_spec (nb T').δ (ha T') (hrel T') (hone T') (x := (SemiHom.of_algHom (nbAlg φ)).m1 x)
      (ω := (SemiHom.of_algHom φ.φ).m1 ω) e).trans (congrArg (km1 (SemiHom.of_algHom φ.φ) φ.dp) l).symm
  · intro T x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have e := uAgree hr T (ρ T) (ha T) (hm T) (h0 T) (h1 T) (ι1 x)
    have z : ExteriorAlgebra.algebraMapInv (ι1 x) = 0 := by simp [ExteriorAlgebra.algebraMapInv]
    rw [z, map_zero, SemiHom.mDR_ι] at e
    have e' : ρ T (ι1 ((SemiHom.of_algHom (inlMap T).φ).m1 x)) - ι1 (0 : Ω[T.B⁄R]) ∈ rel R T.δ := by
      rw [map_zero]; exact e
    exact (divPowerCompatOneForm_retraction_spec (nb T).δ (ha T) (hrel T) (hone T) (x := (SemiHom.of_algHom (inlMap T).φ).m1 x) e').trans
      (Submodule.Quotient.mk_zero _)
  · intro T x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have e := vAgree hr T (ρ T) (ha T) (hm T) (h0 T) (h1 T) (ι1 x)
    rw [SemiHom.mDR_ι] at e
    exact divPowerCompatOneForm_retraction_spec (nb T).δ (ha T) (hrel T) (hone T) (x := (SemiHom.of_algHom (difMap T).φ).m1 x) (ω := x) e

end GlobalTheory.PDForm.Nbhd
