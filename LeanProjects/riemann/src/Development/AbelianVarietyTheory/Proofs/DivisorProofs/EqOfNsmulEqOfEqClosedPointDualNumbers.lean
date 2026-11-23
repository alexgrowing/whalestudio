import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteEtaleCoverConstantTorsion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem eq_of_pow_eq_of_eq_at_closed : ∀ (k : Type) [Field k] (B : Over (Sp (DualNumber k))) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, (n : k) ≠ 0 → ∀ x x' : 𝟙_ (Over (Sp (DualNumber k))) ⟶ B, x ^ n = x' ^ n → spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x.left = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x'.left → x = x' := by
  intro k _ B _ hB n hn x x' hpow h0
  haveI : IsCommMonObj B := hB.comm
  haveI hloc : IsLocalRing (DualNumber k) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one, isUnit_iff_ne_zero]
    by_cases ha : a.fst = 0
    · right; rw [ha, sub_zero]; exact one_ne_zero
    · left; exact ha
  have hnD : IsUnit (n : DualNumber k) := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_natCast]
    exact hn.isUnit
  have hnΓ : IsUnit (n : Γ(Sp (DualNumber k), ⊤)) := by
    simpa using hnD.map (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom
  haveI : PreconnectedSpace (Sp (DualNumber k)) := by
    have : PreconnectedSpace (PrimeSpectrum (DualNumber k)) := by
      refine ⟨isPreconnected_of_forall (IsLocalRing.closedPoint (DualNumber k)) fun y _ =>
        ⟨closure {y}, Set.subset_univ _, ?_, subset_closure rfl, isPreconnected_singleton.closure⟩⟩
      exact (IsLocalRing.specializes_closedPoint y).mem_closure
    exact this
  haveI : PreconnectedSpace (𝟙_ (Over (Sp (DualNumber k)))).left := ‹PreconnectedSpace (Sp (DualNumber k))›
  let T : Over (Sp (DualNumber k)) := Over.mk (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)
  haveI : Nonempty T.left := inferInstanceAs (Nonempty (Sp k))
  have hw : (x * x'⁻¹) ^ n = 1 := by rw [mul_pow, inv_pow, hpow, mul_inv_cancel]
  obtain ⟨C, hC, hz⟩ := GlobalTheory.TorsionCover.exists_clopen_eq_one B hB hnΓ (x * x'⁻¹) hw
  have hT : toUnit T ≫ x = toUnit T ≫ x' := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left, GlobalTheory.ObjPull.toUnit_left']
    exact h0
  have h1 : toUnit T ≫ (x * x'⁻¹) = 1 := by
    show (preHom (toUnit T)) (x * x'⁻¹) = 1
    rw [map_mul, map_inv]
    show (toUnit T ≫ x) * (toUnit T ≫ x')⁻¹ = 1
    rw [hT, mul_inv_cancel]
  have hsub := (hz T (toUnit T)).1 h1
  obtain ⟨p⟩ := ‹Nonempty T.left›
  have hne : C.Nonempty := ⟨_, hsub ⟨p, rfl⟩⟩
  have huniv : C = Set.univ := hC.eq_univ hne
  have h2 : 𝟙 _ ≫ (x * x'⁻¹) = 1 := (hz _ (𝟙 _)).2 (by rw [huniv]; exact Set.subset_univ _)
  rw [Category.id_comp] at h2
  exact mul_inv_eq_one.1 h2

end GlobalTheory.UCanon
