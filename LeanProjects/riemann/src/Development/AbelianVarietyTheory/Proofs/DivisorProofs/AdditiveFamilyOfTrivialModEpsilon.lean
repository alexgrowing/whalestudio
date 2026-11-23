import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveLineBundleFamilyOfGeometricFibresStatement

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen

theorem isLocalRing_dualNumber_field (k : Type) [Field k] : IsLocalRing (DualNumber k) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x ↦ by
    by_cases h : TrivSqZeroExt.fst x = 0
    · right
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
      simp [h]
    · left
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
      exact isUnit_iff_ne_zero.2 h

theorem pic_sp_local_eq_zero (R : Type) [CommRing R] [IsLocalRing R] (c : Pic (Sp R)) : c = 0 := by
  obtain ⟨V, hV, h⟩ := exists_pull_eq_zero c (IsLocalRing.closedPoint R)
  have hV' : V = ⊤ := (IsLocalRing.closedPoint_mem_iff V).1 hV
  have e := pull_eq_zero_of_mem V (𝟙 _) (fun z ↦ by rw [hV']; trivial) h
  rwa [pull_id] at e

theorem ringHom_dualNumber_factor {k K : Type} [CommRing k] [Field K] (φ : DualNumber k →+* K) :
    φ = (φ.comp (dnInl k)).comp (dnFst k) := by
  have hε : φ DualNumber.eps = 0 := by
    have e : φ DualNumber.eps * φ DualNumber.eps = 0 := by rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
    exact mul_self_eq_zero.1 e
  refine RingHom.ext fun x ↦ ?_
  have hx : x = TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inr x.snd := by ext <;> simp
  conv_lhs => rw [hx]
  rw [map_add, DualNumber.inr_eq_smul_eps, Algebra.smul_def, map_mul, hε, mul_zero, add_zero]
  rfl

theorem fam_of_triv_mod_eps : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (k : Type) [Field k]
    (s : Sp (DualNumber k) ⟶ S) (D : LB (A ⊗ Over.mk s).left) (hD : D.IsLB),
    GlobalTheory.CechPic.pull (A ◁ ptMap s (dnFst k)).left (cls D hD) = 0 → Fam A D := by
  intro S A _ hA k _ s D hD h0
  haveI := isLocalRing_dualNumber_field k
  haveI : Module.Finite k (DualNumber k) := inferInstanceAs (Module.Finite k (k × k))
  haveI : IsNoetherianRing (DualNumber k) := IsNoetherianRing.of_finite k (DualNumber k)
  haveI : IsLocallyNoetherian (Over.mk s).left := (inferInstance : IsLocallyNoetherian (Sp (DualNumber k)))
  refine ⟨hD, GlobalTheory.T.isAdditive_lineBundleFamily_of_geometricFibres S A (Over.mk s) hA D hD ?_ ?_⟩
  · rw [triv_ev_iff hD]
    exact pic_sp_local_eq_zero _ _
  · intro K _ _ s' t
    obtain ⟨φ, hφ⟩ := Spec.map_surjective t.left
    set ψ : k →+* K := φ.hom.comp (dnInl k)
    have ht : t.left = spMap ψ ≫ spMap (dnFst k) := by
      rw [← hφ, ← Spec.map_comp]
      congr 1
      ext1
      exact ringHom_dualNumber_factor φ.hom
    have hN : (ev D (fst A (Over.mk s')) (snd A (Over.mk s') ≫ t)).IsLB := pull_isLB hD _
    refine (isAdditive_iff hN).2 fun Y a a' y ↦ ?_
    have key : ∀ b : Y ⟶ A, evc hN b y = 0 := fun b ↦ by
      rw [evc_ev hD, lift_fst, lift_snd_assoc]
      let u : Y ⟶ Over.mk (spMap (dnFst k) ≫ s) := Over.homMk (y.left ≫ spMap ψ) (by
        have e1 : y.left ≫ s' = Y.hom := by simpa using Over.w y
        have e2 : t.left ≫ s = s' := by simpa using Over.w t
        simp only [Over.mk_hom]
        rw [Category.assoc, ← Category.assoc (spMap ψ), ← ht, e2, e1])
      have hu : y ≫ t = u ≫ ptMap s (dnFst k) := by
        refine Over.OverMorphism.ext ?_
        simp only [Over.comp_left, ptMap_left, ht]
        rfl
      rw [hu, evc, ← lift_whiskerLeft, Over.comp_left, pull_comp, h0, map_zero]
    rw [key, key, key, add_zero]

end GlobalTheory.DualOpen
