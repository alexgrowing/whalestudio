import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem isIntegral_of_pow {R : Type} [CommRing R] (φ : R →+* R) {n : ℕ} (hn : 0 < n)
    (hφ : ∀ y, φ y = y ^ n) : φ.IsIntegral := by
  intro y
  refine ⟨Polynomial.X ^ n - Polynomial.C y, Polynomial.monic_X_pow_sub_C y hn.ne', ?_⟩
  simp [hφ]

private theorem isIntegralHom_absFrob_affine (p f : ℕ) (hp : Nat.Prime p) (Y : Scheme) [IsAffine Y] (h : ((p : ℕ) : Γ(Y, ⊤)) = 0) :
    IsIntegralHom (GlobalTheory.SS.FrobField.absFrob Y p f hp h) := by
  have hk : ((p : ℕ) : Γ(Sp Γ(Y, ⊤), ⊤)) = 0 := GlobalTheory.SS.FrobField.cast_zero_sp Γ(Y, ⊤) h
  have hsp : GlobalTheory.SS.FrobField.absFrob (Sp Γ(Y, ⊤)) p f hp hk =
      spMap (GlobalTheory.SS.FrobField.powHom Γ(Y, ⊤) p f hp h) :=
    GlobalTheory.SS.FrobField.absFrob_spec Γ(Y, ⊤) p f hp hk _ (fun _ => rfl)
  have hnat := GlobalTheory.SS.FrobField.absFrob_nat Y.isoSpec.hom p f hp h hk
  have he : GlobalTheory.SS.FrobField.absFrob Y p f hp h =
      Y.isoSpec.hom ≫ GlobalTheory.SS.FrobField.absFrob (Sp Γ(Y, ⊤)) p f hp hk ≫ Y.isoSpec.inv := by
    rw [← Category.comp_id (GlobalTheory.SS.FrobField.absFrob Y p f hp h), ← Y.isoSpec.hom_inv_id,
      ← Category.assoc, hnat, Category.assoc]
    rfl
  rw [he, hsp]
  have hi : IsIntegralHom (spMap (GlobalTheory.SS.FrobField.powHom Γ(Y, ⊤) p f hp h)) :=
    (IsIntegralHom.SpecMap_iff).mpr (isIntegral_of_pow _ (pow_pos hp.pos f) (fun _ => rfl))
  infer_instance

theorem UpperTheory.Gal.crystallineComparison.Mod.frobFin_of :
    FrobFin := by
  intro p f hp κ _ _ _ X s hs h
  haveI : Fact p.Prime := ⟨hp⟩
  have hk0 : ((p : ℕ) : κ) = 0 := CharP.cast_eq_zero κ p
  have hκ : ((p : ℕ) : Γ(Sp κ, ⊤)) = 0 := GlobalTheory.SS.FrobField.cast_zero_sp κ hk0
  have hsp : GlobalTheory.SS.FrobField.absFrob (Sp κ) p f hp hκ = spMap (GlobalTheory.SS.FrobField.powHom κ p f hp hk0) :=
    GlobalTheory.SS.FrobField.absFrob_spec κ p f hp hκ _ (fun _ => rfl)
  have hb : Function.Bijective (GlobalTheory.SS.FrobField.powHom κ p f hp hk0) := by
    constructor
    · intro x y hxy
      change x ^ p ^ f = y ^ p ^ f at hxy
      have hz : (x - y) ^ p ^ f = 0 := by rw [sub_pow_char_pow, hxy, sub_self]
      exact sub_eq_zero.mp (pow_eq_zero_iff (pow_pos hp.pos f).ne' |>.mp hz)
    · intro y
      obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos hp.pos f)
      exact ⟨x, hx⟩
  let e : κ ≃+* κ := RingEquiv.ofBijective _ hb
  haveI : IsIso (spMap (GlobalTheory.SS.FrobField.powHom κ p f hp hk0)) := by
    change IsIso (Spec.map (RingEquiv.toCommRingCatIso e).hom)
    infer_instance
  refine ⟨?_, ⟨fun x => ⟨x, rfl⟩⟩⟩
  rw [IsFinite.iff_isIntegralHom_and_locallyOfFiniteType]
  constructor
  · rw [@HasAffineProperty.eq_targetAffineLocally @IsIntegralHom _ IsIntegralHom.hasAffineProperty]
    intro U
    haveI : IsAffine U.1.toScheme := U.2
    apply (@HasAffineProperty.iff_of_isAffine @IsIntegralHom _ IsIntegralHom.hasAffineProperty _ _ _ _).mp
    have hU : ((p : ℕ) : Γ(U.1.toScheme, ⊤)) = 0 := GlobalTheory.SS.FrobField.cast_zero_of_hom U.1.ι h
    have heq : GlobalTheory.SS.FrobField.absFrob X p f hp h ⁻¹ᵁ U.1 = U.1 := rfl
    have hres : GlobalTheory.SS.FrobField.absFrob X p f hp h ∣_ U.1 =
        (X.isoOfEq heq).hom ≫ GlobalTheory.SS.FrobField.absFrob U.1.toScheme p f hp hU := by
      rw [← cancel_mono U.1.ι, morphismRestrict_ι, Category.assoc,
        GlobalTheory.SS.FrobField.absFrob_nat U.1.ι p f hp hU h, ← Category.assoc, Scheme.isoOfEq_hom_ι]
    rw [hres]
    haveI := isIntegralHom_absFrob_affine p f hp U.1.toScheme hU
    infer_instance
  · have hc : GlobalTheory.SS.FrobField.absFrob X p f hp h ≫ s = s ≫ spMap (GlobalTheory.SS.FrobField.powHom κ p f hp hk0) := by
      rw [GlobalTheory.SS.FrobField.absFrob_nat s p f hp h hκ, hsp]
    haveI : LocallyOfFiniteType (GlobalTheory.SS.FrobField.absFrob X p f hp h ≫ s) := by
      rw [hc]
      infer_instance
    exact locallyOfFiniteType_of_comp _ s
