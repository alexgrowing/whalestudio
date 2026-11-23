import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GlobalFunctionsDvrOpen

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrGeneric

open ReciprocityTheory.ChartRestriction.G.Out

theorem powObj_props {S : Scheme.{0}} (G : Over S) [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] :
    ∀ n : ℕ, Smooth (powObj G n).hom ∧ IsSeparated (powObj G n).hom ∧ QuasiCompact (powObj G n).hom
  | 0 => ⟨by show Smooth (𝟙 S); infer_instance, by show IsSeparated (𝟙 S); infer_instance,
      by show QuasiCompact (𝟙 S); infer_instance⟩
  | n + 1 => by
    obtain ⟨h1, h2, h3⟩ := powObj_props G n
    refine ⟨?_, ?_, ?_⟩
    · show Smooth (G ⊗ powObj G n).hom
      rw [Over.tensorObj_hom, pullback.condition]
      infer_instance
    · show IsSeparated (G ⊗ powObj G n).hom
      rw [Over.tensorObj_hom, pullback.condition]
      infer_instance
    · show QuasiCompact (G ⊗ powObj G n).hom
      rw [Over.tensorObj_hom, pullback.condition]
      infer_instance

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem appTop_spMap (v : V) :
    (spMap (algebraMap V (FractionRing V))).appTop ((Scheme.ΓSpecIso (CommRingCat.of V)).inv v) =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv (algebraMap V (FractionRing V) v) := by
  have h := AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap V (FractionRing V)))
  have h2 := congrArg (fun g => g.hom v) h
  first
  | exact h2.symm
  | simp
  | simpa using h2.symm

theorem bij_of_generic (A : Over (Sp V)) [GrpObj A] [Flat A.hom] [QuasiCompact A.hom] [QuasiSeparated A.hom]
    (hK : Function.Bijective ((Over.pullback (spMap (algebraMap V (FractionRing V)))).obj A).hom.appTop.hom) :
    Function.Bijective A.hom.appTop.hom := by
  classical
  have hψ : Function.Injective (pullback.fst A.hom (spMap (algebraMap V (FractionRing V)))).appTop :=
    GlobalFunctionsDvrOpen.appTop_fst_injective A.hom
  have hκ : Function.Bijective (pullback.snd A.hom (spMap (algebraMap V (FractionRing V)))).appTop := hK
  have he : (η[A]).left ≫ A.hom = 𝟙 _ := Over.w (η[A])
  have h1 : A.hom.appTop ≫ (η[A]).left.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, he, Scheme.Hom.id_appTop]
    rfl
  have hret : ∀ y, (η[A]).left.appTop (A.hom.appTop y) = y := fun y => by
    have := congrArg (fun φ => φ y) h1
    simpa only [CategoryTheory.comp_apply, CategoryTheory.id_apply] using this
  have hcomm : ∀ y, (pullback.fst A.hom (spMap (algebraMap V (FractionRing V)))).appTop (A.hom.appTop y) =
      (pullback.snd A.hom (spMap (algebraMap V (FractionRing V)))).appTop
        ((spMap (algebraMap V (FractionRing V))).appTop y) := fun y => by
    have h := congrArg Scheme.Hom.appTop (pullback.condition (f := A.hom) (g := spMap (algebraMap V (FractionRing V))))
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h
    have := congrArg (fun φ => φ y) h
    simpa only [CategoryTheory.comp_apply] using this
  have hinj : Function.Injective A.hom.appTop := fun a b hab => by
    rw [← hret a, ← hret b, hab]
  refine ⟨hinj, fun a => ?_⟩
  obtain ⟨c, hc⟩ := hκ.2 ((pullback.fst A.hom (spMap (algebraMap V (FractionRing V)))).appTop a)
  set c' : FractionRing V := (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).hom c with hc'
  have hcc : c = (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv c' := by rw [hc', Iso.hom_inv_id_apply]
  by_cases h : ∃ v : V, algebraMap V (FractionRing V) v = c'
  · obtain ⟨v, hv⟩ := h
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of V)).inv v, hψ ?_⟩
    rw [hcomm, appTop_spMap, hv, ← hcc, hc]
  · exfalso
    have hc0 : c' ≠ 0 := fun h0 => h ⟨0, by rw [map_zero, h0]⟩
    obtain ⟨v, hv⟩ : ∃ v : V, algebraMap V (FractionRing V) v = c'⁻¹ := by
      rcases ValuationRing.isInteger_or_isInteger V c' with h' | h'
      · exact absurd h' h
      · exact h'
    have hvu : ¬ IsUnit v := by
      rintro ⟨u, rfl⟩
      apply h
      refine ⟨↑u⁻¹, ?_⟩
      rw [← inv_inv c', ← hv]
      refine (eq_inv_of_mul_eq_one_left ?_)
      rw [← map_mul, Units.inv_mul, map_one]
    have hone : a * A.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of V)).inv v) = 1 := by
      apply hψ
      rw [map_mul, map_one, hcomm, appTop_spMap, hv, ← hc, hcc, ← map_mul, ← map_mul, mul_inv_cancel₀ hc0, map_one,
        map_one]
    have hu : IsUnit (A.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of V)).inv v)) := ⟨⟨_, a, (mul_comm _ _).trans hone, hone⟩, rfl⟩
    have hu2 : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of V)).inv v) := by
      have := hu.map ((η[A]).left.appTop.hom)
      rwa [show (η[A]).left.appTop.hom (A.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of V)).inv v)) = (Scheme.ΓSpecIso (CommRingCat.of V)).inv v from hret _] at this
    apply hvu
    have := hu2.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom
    rwa [show (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv v) = v from
      Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of V)) v] at this

end ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrGeneric
