import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCdvrMkLeContinuum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProperRelAmpleOfSystem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AppLEEqIffStalk
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsProperSemiAbelianTripleOfAbelianLocusEqUniv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrincipallyPolarizedCMExtensionDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPolAVGenericFibre
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.KeyUnitGood

theorem exists_unit_of_map {R K A B : Type} [CommRing R] [IsDomain R] [ValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing A] [Field B] [Algebra A B] [IsFractionRing A B] (e : R →+* A)
    [IsLocalHom e] (la : K →+* B) (hla : ∀ r, la (algebraMap R K r) = algebraMap A B (e r)) (x : K) (u : Aˣ)
    (hx : la x = algebraMap A B u) : ∃ v : Rˣ, x = algebraMap R K v := by
  rcases ValuationRing.isInteger_or_isInteger R x with ⟨r, hr⟩ | ⟨r, hr⟩
  · have h : e r = u := IsFractionRing.injective A B (by rw [← hla, hr, hx])
    obtain ⟨v, rfl⟩ : IsUnit r := isUnit_of_map_unit e r (h ▸ u.isUnit)
    exact ⟨v, hr.symm⟩
  · have h : e r = (u⁻¹ : Aˣ) := IsFractionRing.injective A B (by rw [← hla, hr, map_inv₀, hx, map_units_inv])
    obtain ⟨v, rfl⟩ : IsUnit r := isUnit_of_map_unit e r (h ▸ (u⁻¹).isUnit)
    exact ⟨v⁻¹, by rw [map_units_inv, hr, inv_inv]⟩

theorem isUnit_key_of_good : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), ∀ κ : KeyRule, IsKeyRule κ → ∀ (M : GChart Y) (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (z : Sp R ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U) (y : Sp K ⟶ Xo.XF c), y ≫ Y.j = spMap (algebraMap R K) ≫ z → Set.range z ⊆ abLocus Y.t.G → ∀ x : KeyIn K, KeyAt M (spMap (algebraMap R K) ≫ z) (le_preimage_comp _ hz) x → ∃ u : Rˣ, (κ K x : K) = algebraMap R K u := by
  intro E _ _ _ H D l Xo c O _ β Y κ hκ M R K _ _ _ _ _ _ _ z hz y hy hab x hx
  have : CharZero R := (algebraMap R K).charZero
  obtain ⟨T, i, hi, hil⟩ : ∃ (T : Formalism.L2.Pj.CDVR) (i : R →+* T.V), Function.Injective i ∧ IsLocalHom i :=
    ⟨GlobalTheory.CountableCompletion.completionCDVR R, algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R),
      GlobalTheory.algebraMap_adicCompletion_injective_of_dvr R, inferInstance⟩
  have hiF : Function.Injective ((algebraMap T.V T.Fr).comp i) := (IsFractionRing.injective T.V T.Fr).comp hi
  let iK : K →+* T.Fr := IsFractionRing.lift hiF
  have hiK : ∀ r, iK (algebraMap R K r) = algebraMap T.V T.Fr (i r) := fun r => IsFractionRing.lift_algebraMap hiF r
  have hsq : spMap iK ≫ spMap (algebraMap R K) = spMap (algebraMap T.V T.Fr) ≫ spMap i := by
    rw [← GlobalTheory.KeyAtBC.spMap_comp₀, ← GlobalTheory.KeyAtBC.spMap_comp₀]
    exact congrArg spMap (RingHom.ext hiK)
  have hpt : spMap iK ≫ spMap (algebraMap R K) ≫ z = spMap (algebraMap T.V T.Fr) ≫ spMap i ≫ z := by
    rw [← Category.assoc, hsq, Category.assoc]
  obtain ⟨t, ⟨m⟩⟩ := exists_sab (spMap i ≫ z) Y.t
  obtain ⟨tK, ⟨mK⟩⟩ := exists_sab (spMap (algebraMap T.V T.Fr)) t
  obtain ⟨n, -⟩ := ObjMaps.exists_sab_comp m mK
  have hj : spMap (algebraMap T.V T.Fr) ≫ spMap i ≫ z = (spMap iK ≫ y) ≫ Y.j := by
    rw [← hpt, Category.assoc, hy]
  obtain ⟨n₁, -⟩ := ObjMaps.exists_sab_cancel (show SABMap Y.oF.t Y.t Y.j from Y.m) (hj ▸ n)
  obtain ⟨n₂, -⟩ := ObjMaps.exists_sab_comp Y.m0.toSABMap n₁
  have hp : IsProper t.G.hom := GlobalTheory.GoodProper.isProper_of_abLocus_eq_univ E H D l Xo T _ t tK n₂ mK
    (Set.eq_univ_of_forall fun q => (abLocus_pullback abLocusOne Y.t.semi m.cart.1 q).1
      (hab ⟨spMap i q, (Scheme.Hom.comp_apply _ _ _).symm⟩))
  obtain ⟨-, hA, hK⟩ := GlobalTheory.GenericPol.proper_ample_kTriv (show SABMap Y.oF.t Y.t Y.j from Y.m)
    Y.oF.proper Y.oF.ample Y.oF.ktriv n (by
      rw [hj]
      rintro _ ⟨q, rfl⟩
      exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩)
  have hA' : Out.RelAmple t.G t.PP.L := GlobalTheory.GoodPol.relAmple_of_generic GlobalTheory.firstFiveLaws.1
    ⟨inferInstance, t.semi.smooth, hp, t.semi.geomConnected⟩ t.cub mK.cart tK.PP.isLB
    (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap mK) hA hK
  obtain ⟨x', hx'⟩ := GlobalTheory.KeyPow.exists_keyPB_ring x iK
  have hzT : ⊤ ≤ (spMap i ≫ z) ⁻¹ᵁ M.U := le_preimage_comp _ hz
  have h₁ : KeyAt M (spMap (algebraMap T.V T.Fr) ≫ spMap i ≫ z) (le_preimage_comp _ hzT) x' := by
    have cast : ∀ (p q : Sp T.Fr ⟶ Y.X) (_ : p = q) hp hq, KeyAt M p hp x' → KeyAt M q hq x' := by
      rintro p q rfl _ _ h
      exact h
    exact cast _ _ hpt _ _ (GlobalTheory.KeyAtBC.keyAt_of_keyPB hx hx')
  obtain ⟨xT, -, hT⟩ := GlobalTheory.KeyAtFam.exists_keyAt_of_point M hzT m hp hA' _ h₁
  obtain ⟨u, hu, -⟩ := hκ.2.2.1 T.V T.Fr xT x' (GlobalTheory.KeyAtBC.keyPB_of_keyAt hT h₁)
  exact exists_unit_of_map i iK hiK _ u ((hκ.2.1 K T.Fr iK x x' hx').symm.trans hu)

end GlobalTheory.KeyUnitGood
