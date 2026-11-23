import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushRProdPtsResP

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieAway

section Basic

variable {R : Type} [CommRing R]

theorem scaleS_toRingHom (c : R) : (Chart.scaleS (S := R) c).toRingHom = epsScaleR c := by
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_
  · simp [Chart.scaleS_fst, epsScaleR]
  · simp [Chart.scaleS_snd, epsScaleR]

variable {G : Over (Sp R)} [GrpObj G]

theorem tanS_of_isTangent {v : epsR R ⟶ G} (h : IsTangent v) : Chart.TanS (S := R) (A := R) v :=
  (Chart.isTan_iff v).mpr h

theorem isTangent_of_tanS {v : epsR R ⟶ G} (h : Chart.TanS (S := R) (A := R) v) : IsTangent v :=
  (Chart.isTan_iff v).mp h

theorem isTangent_iff_tanS (r : R) (y : epsR (Localization.Away r) ⟶ Chart.Gs G r) :
    IsTangent y ↔ Chart.TanS (Chart.pushR G y) := by
  rw [← Chart.isTan_iff]
  constructor
  · intro h
    have := congrArg (Chart.pushR G) h
    rw [Chart.pushR_spMap, Chart.pushR_one] at this
    exact this
  · intro h
    apply Chart.pushR_inj G
    rw [Chart.pushR_spMap, Chart.pushR_one]
    exact h

theorem scale_left (c : R) (v : epsR R ⟶ G) :
    Geo.Tor.spMap (epsScaleR c) ≫ v.left = (Chart.spMap (Chart.scaleS (S := R) c) ≫ v).left := by
  rw [Over.comp_left, Chart.spMap_left, ← scaleS_toRingHom]

end Basic

end GlobalTheory.LieAway

namespace GlobalTheory.LieAway

section Res

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] (r : R)

def resA (v : epsR R ⟶ G) : epsR (Localization.Away r) ⟶ Chart.Gs G r :=
  Chart.pullR G (Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away r))) ≫ v)

theorem pushR_resA (v : epsR R ⟶ G) :
    Chart.pushR G (resA r v) = Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away r))) ≫ v :=
  Chart.pushR_pullR G _

variable {O O' : Type} [CommRing O] [CommRing O'] [IsCommMonObj G] (a : OAct O G)
  (a' : OAct O' (Chart.Gs G r))

def resL (v : GlobalTheory.Serre.Lie a) : GlobalTheory.Serre.Lie a' :=
  GlobalTheory.Serre.Lie.mk a' (resA r v.hom) (by
    rw [isTangent_iff_tanS, pushR_resA]
    exact Chart.tanS_restrict _ (tanS_of_isTangent v.isTangent))

theorem pushR_resL (v : GlobalTheory.Serre.Lie a) :
    Chart.pushR G (resL r a a' v).hom = Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away r))) ≫ v.hom :=
  pushR_resA r v.hom

theorem pushR_smul (c : Localization.Away r) (y : GlobalTheory.Serre.Lie a') :
    Chart.pushR G (c • y).hom = Chart.spMap (Chart.scaleS (S := R) c) ≫ Chart.pushR G y.hom := by
  have e : (c • y).hom = Chart.spMap (Chart.scaleS (S := Localization.Away r) c) ≫ y.hom :=
    Over.OverMorphism.ext ((GlobalTheory.Serre.Lie.hom_smul_left c y).trans (scale_left c y.hom))
  rw [e, Chart.pushR_spMap]
  rfl

theorem hom_smul_eq (c : R) (v : GlobalTheory.Serre.Lie a) :
    (c • v).hom = Chart.spMap (Chart.scaleS (S := R) c) ≫ v.hom :=
  Over.OverMorphism.ext ((GlobalTheory.Serre.Lie.hom_smul_left c v).trans (scale_left c v.hom))

theorem pushR_add (y z : GlobalTheory.Serre.Lie a') :
    Chart.pushR G (y + z).hom = Chart.pushR G y.hom * Chart.pushR G z.hom :=
  map_mul (Chart.pushforwardHom G) y.hom z.hom

theorem resL_add (v w : GlobalTheory.Serre.Lie a) : resL r a a' (v + w) = resL r a a' v + resL r a a' w := by
  ext1
  apply Chart.pushR_inj G
  rw [pushR_add, pushR_resL, pushR_resL, pushR_resL, GlobalTheory.Serre.Lie.hom_add, MonObj.comp_mul]

theorem resL_smul (c : R) (v : GlobalTheory.Serre.Lie a) :
    resL r a a' (c • v) = algebraMap R (Localization.Away r) c • resL r a a' v := by
  ext1
  apply Chart.pushR_inj G
  rw [pushR_smul, pushR_resL, pushR_resL, hom_smul_eq, Chart.res_scale]
  rfl

end Res

end GlobalTheory.LieAway

namespace GlobalTheory.LieAway

section Cover

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [∀ s : R, Smooth (Chart.Gs G s).hom]

theorem tan_away_uniq (r : R) {w : Chart.sp (R₀ := R) (DualNumber R) ⟶ G} (hw : Chart.TanS w)
    (h1 : Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away r))) ≫ w = 1) :
    ∃ N : ℕ, Chart.spMap (Chart.scaleS (S := R) (r ^ N)) ≫ w = 1 := by
  classical
  obtain ⟨n, s, hs, hC⟩ := Chart.exists_cover G
  have C : ∀ k, Chart.Chart (Chart.Gs G (s k)) := fun k => (hC k).some
  have hwk : ∀ k, Chart.TanS (Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away (s k)))) ≫ w) :=
    fun k => Chart.tanS_restrict _ hw
  have hone : ∀ (A : Type) [CommRing A] [Algebra R A], Chart.TanS (1 : Chart.sp (R₀ := R) (DualNumber A) ⟶ G) :=
    fun A _ _ => Chart.comp_one' _
  have h2 : ∀ k, ∃ N : ℕ, Chart.spMap (Chart.scaleS (S := R) (algebraMap R (Localization.Away (s k)) r ^ N)) ≫
      Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away (s k)))) ≫ w =
      Chart.spMap (Chart.scaleS (S := R) (algebraMap R (Localization.Away (s k)) r ^ N)) ≫ 1 := by
    intro k
    apply Chart.tanS_away_uniq (C k) (A := Localization.Away (s k)) r (hwk k) (hone _)
    have hu : IsUnit (algebraMap R (Localization.Away (algebraMap R (Localization.Away (s k)) r)) r) :=
      Chart.isUnit_qv (s k) r
    rw [Chart.comp_one', Chart.res_res,
      show (IsScalarTower.toAlgHom R (Localization.Away (s k))
          (Localization.Away (algebraMap R (Localization.Away (s k)) r))).comp
          (Algebra.ofId R (Localization.Away (s k))) =
        (Chart.awayHom r _ hu).comp (Algebra.ofId R (Localization.Away r)) from Chart.ofId_ext _ _,
      ← Chart.res_res, h1, Chart.comp_one']
  choose N hN using h2
  refine ⟨Finset.univ.sup N, Chart.tan_ext_cover s hs fun k => ?_⟩
  rw [Chart.comp_one', Chart.res_scale, Algebra.ofId_apply, map_pow,
    Chart.scale_pow_mono _ (Finset.le_sup (f := N) (Finset.mem_univ k)) (hN k), Chart.comp_one']

theorem tan_away_lift (r : R) (hr : Nonempty (Chart.Chart (Chart.Gs G r)))
    {y : Chart.sp (R₀ := R) (DualNumber (Localization.Away r)) ⟶ G} (hy : Chart.TanS y) :
    ∃ N : ℕ, ∃ w : Chart.sp (R₀ := R) (DualNumber R) ⟶ G, Chart.TanS w ∧
      Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away r))) ≫ w =
        Chart.spMap (Chart.scaleS (S := R) (algebraMap R (Localization.Away r) r ^ N)) ≫ y := by
  obtain ⟨n, s, hs, hC⟩ := Chart.exists_cover G
  let s' : Fin (n + 1) → R := Fin.cons r s
  have hs' : Ideal.span (Set.range s') = ⊤ := by
    rw [eq_top_iff, ← hs]
    apply Ideal.span_mono
    rintro _ ⟨k, rfl⟩
    exact ⟨k.succ, Fin.cons_succ _ _ _⟩
  have C : ∀ k, Chart.Chart (Chart.Gs G (s' k)) := Fin.cases hr.some (fun k => (hC k).some)
  exact Chart.tan_extend s' hs' C 0 hy

end Cover

end GlobalTheory.LieAway

namespace GlobalTheory.LieAway

theorem lie_away {R O O' : Type} [CommRing R] [CommRing O] [CommRing O'] (G : Over (Sp R)) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] (a : OAct O G) (r : R) (a' : OAct O' (ReciprocityTheory.ChartRestriction.G.Chart.Gs G r)) :
    Nonempty (ReciprocityTheory.ChartRestriction.G.Chart.Chart (ReciprocityTheory.ChartRestriction.G.Chart.Gs G r)) →
    Nonempty (LocalizedModule (Submonoid.powers r) (GlobalTheory.Serre.Lie a) ≃ₗ[Localization.Away r] GlobalTheory.Serre.Lie a') := by
  intro hr
  have : ∀ s : R, Smooth (Chart.Gs G s).hom := fun s => show Smooth (pullback.snd G.hom _) from inferInstance
  letI : Module R (GlobalTheory.Serre.Lie a') := Module.compHom _ (algebraMap R (Localization.Away r))
  haveI : IsScalarTower R (Localization.Away r) (GlobalTheory.Serre.Lie a') :=
    ⟨fun x y z => by rw [Algebra.smul_def]; exact mul_smul _ y z⟩
  let ρ : GlobalTheory.Serre.Lie a →ₗ[R] GlobalTheory.Serre.Lie a' :=
    { toFun := resL r a a'
      map_add' := resL_add r a a'
      map_smul' := resL_smul r a a' }
  have hρ : ∀ v, Chart.pushR G (ρ v).hom =
      Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away r))) ≫ v.hom := pushR_resL r a a'
  haveI : IsLocalizedModule (Submonoid.powers r) ρ := by
    refine ⟨fun x => ?_, fun y => ?_, fun {x₁ x₂} h => ?_⟩
    · rw [Module.End.isUnit_iff]
      obtain ⟨u, hu⟩ := IsLocalization.map_units (Localization.Away r) x
      have hx : ∀ m : GlobalTheory.Serre.Lie a',
          (algebraMap R (Module.End R (GlobalTheory.Serre.Lie a')) x) m = (u : Localization.Away r) • m := fun m => by
        rw [Module.algebraMap_end_apply, hu]; rfl
      refine ⟨fun m₁ m₂ e => ?_, fun m => ⟨(↑u⁻¹ : Localization.Away r) • m, ?_⟩⟩
      · rw [hx, hx] at e
        have := congrArg (fun z => (↑u⁻¹ : Localization.Away r) • z) e
        simp only [smul_smul, Units.inv_mul, one_smul] at this
        exact this
      · rw [hx, smul_smul, Units.mul_inv, one_smul]
    · have hy : Chart.TanS (Chart.pushR G y.hom) := (isTangent_iff_tanS r y.hom).mp y.isTangent
      obtain ⟨N, w, hw, he⟩ := tan_away_lift r hr hy
      refine ⟨(GlobalTheory.Serre.Lie.mk a w (isTangent_of_tanS hw), ⟨r ^ N, N, rfl⟩), ?_⟩
      ext1
      apply Chart.pushR_inj G
      rw [hρ, GlobalTheory.Serre.Lie.hom_mk, he]
      change Chart.pushR G ((algebraMap R (Localization.Away r) (r ^ N)) • y).hom = _
      rw [pushR_smul, map_pow]
    · have h0 : ρ (x₁ - x₂) = 0 := by rw [map_sub, h, sub_self]
      have h1 : Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away r))) ≫ (x₁ - x₂).hom = 1 := by
        rw [← hρ, h0, GlobalTheory.Serre.Lie.hom_zero, Chart.pushR_one]
      obtain ⟨N, hN⟩ := tan_away_uniq r (tanS_of_isTangent (x₁ - x₂).isTangent) h1
      refine ⟨⟨r ^ N, N, rfl⟩, ?_⟩
      rw [← sub_eq_zero, ← smul_sub]
      ext1
      rw [Submonoid.smul_def, hom_smul_eq, hN, GlobalTheory.Serre.Lie.hom_zero]
  exact ⟨(IsLocalizedModule.iso (Submonoid.powers r) ρ).extendScalarsOfIsLocalization (Submonoid.powers r)
    (Localization.Away r)⟩

end GlobalTheory.LieAway
