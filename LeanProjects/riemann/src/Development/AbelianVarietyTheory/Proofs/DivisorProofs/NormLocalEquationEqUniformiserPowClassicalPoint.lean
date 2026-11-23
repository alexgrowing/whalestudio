import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc.EqNormAt

theorem spectrumMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem norm_val_eqAt : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (D : GlobalTheory.EffCartierData M.Z) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ϖ : V) (a : ℕ) (ξ : Sp V ⟶ M.Z) (p : ℕ) [Fact p.Prime] (ι : FractionRing V →+* PadicAlgCl p) (j : V →+* OO p), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → (∀ v, (j v : PadicAlgCl p) = ι (algebraMap V (FractionRing V) v)) → idlAlong D.idealSheaf ξ = Ideal.span {ϖ ^ a} → ∀ f, EqAt M D (ξ (closedPoint V)) f → ‖M.val (gPt p ≫ spMap j ≫ ξ) f‖ = ‖ι (algebraMap V (FractionRing V) ϖ)‖ ^ a := by
  intro o Ω _ _ _ M D V _ _ _ ϖ a ξ p _ ι j hι hj hid f hf
  obtain ⟨i, hxi, rfl⟩ := hf
  set z := ξ (closedPoint V) with hz
  set e : V := (Scheme.stalkClosedPointTo ξ).hom ((M.Z.presheaf.germ _ z hxi).hom (D.f i)) with he
  have key : Ideal.span {e} = Ideal.span {ϖ ^ a} := by
    rw [← hid, idlAlong, D.stalkId_idealSheaf i z hxi, Ideal.map_span, Set.image_singleton]
  obtain ⟨u, hu⟩ := (Ideal.span_singleton_eq_span_singleton).1 key

  have hval : M.val (gPt p ≫ spMap j ≫ ξ) (valF M.pt (D.U i) (D.f i)) = ((j e : OO p) : PadicAlgCl p) := by
    rw [← Category.assoc, gPt, spectrumMap_comp, RatModel.val_spMap_comp _ ξ (specializes_rfl : z ⤳ z)
      ⟨valF M.pt (D.U i) (D.f i), RatModel.valF_mem_O hxi _⟩]
    have hv : M.valLoc ξ z specializes_rfl ⟨valF M.pt (D.U i) (D.f i), RatModel.valF_mem_O hxi _⟩ = e := by
      simp only [RatModel.valLoc, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        ← RatModel.stalkEquiv_germ hxi, RingEquiv.symm_apply_apply, TopCat.Presheaf.stalkSpecializes_refl,
        Category.id_comp, he]
      rw [Category.id_comp]
    rw [RingHom.comp_apply, hv]
    rfl
  rw [hval, hj]
  have hunit : ∀ w : Vˣ, ‖ι (algebraMap V (FractionRing V) (w : V))‖ = 1 := by
    intro w
    have h1 := (hι _).2 ⟨(w : V), rfl⟩
    have h2 := (hι _).2 ⟨((w⁻¹ : Vˣ) : V), rfl⟩
    have h3 : ‖ι (algebraMap V (FractionRing V) (w : V))‖ * ‖ι (algebraMap V (FractionRing V) ((w⁻¹ : Vˣ) : V))‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
    nlinarith [norm_nonneg (ι (algebraMap V (FractionRing V) (w : V))),
      norm_nonneg (ι (algebraMap V (FractionRing V) ((w⁻¹ : Vˣ) : V)))]
  have he' : e = ϖ ^ a * ((u⁻¹ : Vˣ) : V) := by
    rw [← hu, mul_assoc, Units.mul_inv, mul_one]
  rw [he', map_mul, map_mul, norm_mul, hunit, mul_one, map_pow, map_pow, norm_pow]

end GlobalTheory.Poinc.EqNormAt
