import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentialsStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys.Defect

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
  {s₀ : X₀ ⟶ Sp R₀} {S S' : Sys I π s₀} (Φ : S.LocIso S')

abbrev al {U V : AffOp X₀} (a : U ⟶ V) : S.F.obj U →ₐ[R] S'.F.obj V :=
  (mp S'.F a).comp (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U)

abbrev be {U V : AffOp X₀} (a : U ⟶ V) : S.F.obj U →ₐ[R] S'.F.obj V :=
  (Φ.φ V : S.F.obj V →ₐ[R] S'.F.obj V).comp (mp S.F a)

theorem map_mem {B B' : Type} [CommRing B] [CommRing B'] [Algebra R B] [Algebra R B'] (f : B →ₐ[R] B')
    {x : B} (hx : x ∈ I.map (algebraMap R B)) : f x ∈ I.map (algebraMap R B') := by
  have h := Ideal.mem_map_of_mem (f : B →+* B') hx
  rwa [Ideal.map_map, f.comp_algebraMap] at h

theorem mul_eq_zero' (hI : I ^ 2 = 0) {B : Type} [CommRing B] [Algebra R B] {x y : B}
    (hx : x ∈ I.map (algebraMap R B)) (hy : y ∈ I.map (algebraMap R B)) : x * y = 0 := by
  have h := Ideal.mul_mem_mul hx hy
  rw [← sq, map_sq hI B] at h
  simpa using h

theorem diff_mem {U V : AffOp X₀} (a : U ⟶ V) (b : S.F.obj U) :
    al Φ a b - be Φ a b ∈ I.map (algebraMap R (S'.F.obj V)) := by
  rw [← S'.ker V, map_sub, sub_eq_zero]
  change S'.p V (mp S'.F a (Φ.φ U b)) = S'.p V (Φ.φ V (mp S.F a b))
  rw [S'.nat, Φ.red, Φ.red, S.nat]

theorem ex (hI : I ^ 2 = 0) (hπ : Function.Surjective π) {U V : AffOp X₀} (a : U ⟶ V) :
    ∃! θ : Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V, IsTheta I (S.p U) (al Φ a) (be Φ a) θ :=
  (GlobalTheory.T.algHom_lifts_sqZero_classified_by_differentials R R₀ (S.F.obj U) (Sec s₀ U.unop.1) (S'.F.obj V) I hI π hπ (S.p U) (S.semi U)
    (S.surj U) (S.ker U) (al Φ a)).1 (be Φ a) (diff_mem Φ a)

def th (hI : I ^ 2 = 0) (hπ : Function.Surjective π) {U V : AffOp X₀} (a : U ⟶ V) : Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V :=
  (ex Φ hI hπ a).exists.choose

theorem th_spec (hI : I ^ 2 = 0) (hπ : Function.Surjective π) {U V : AffOp X₀} (a : U ⟶ V) : IsTheta I (S.p U) (al Φ a) (be Φ a) (th Φ hI hπ a) :=
  (ex Φ hI hπ a).exists.choose_spec

theorem th_comp (hI : I ^ 2 = 0) (hπ : Function.Surjective π) {U V W : AffOp X₀} (a : U ⟶ V)
    (b : V ⟶ W) (x : Ω[Sec s₀ U.unop.1⁄R₀]) :
    th Φ hI hπ (a ≫ b) x = mp S'.F b (th Φ hI hπ a x) + th Φ hI hπ b (p1 (OAff s₀) a x) := by
  let θ' : Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj W :=
    ((mp S'.F b).toRingHom.toAddMonoidHom.comp (th Φ hI hπ a)) +
      (th Φ hI hπ b).comp (p1 (OAff s₀) a).toAddMonoidHom
  have hA := th_spec Φ hI hπ a
  have hB := th_spec Φ hI hπ b
  have h : IsTheta I (S.p U) (al Φ (a ≫ b)) (be Φ (a ≫ b)) θ' := by
    refine ⟨fun c w ↦ ?_, fun c ↦ ?_, fun w ↦ ?_⟩
    · change mp S'.F b (th Φ hI hπ a (S.p U c • w)) + th Φ hI hπ b (p1 (OAff s₀) a (S.p U c • w)) =
        al Φ (a ≫ b) c * (mp S'.F b (th Φ hI hπ a w) + th Φ hI hπ b (p1 (OAff s₀) a w))
      rw [hA.smul, oneFormsMapOfFunctorMorphism_smul]
      have e : mp (OAff s₀) a (S.p U c) = S.p V (mp S.F a c) := (S.nat a c).symm
      rw [e, hB.smul, map_mul]
      have hz : (mp S'.F b (al Φ a c) - al Φ b (mp S.F a c)) * th Φ hI hπ b (p1 (OAff s₀) a w) = 0 := by
        refine mul_eq_zero' hI ?_ (hB.mem _)
        have : al Φ b (mp S.F a c) = mp S'.F b (be Φ a c) := rfl
        rw [this, ← map_sub]
        exact map_mem _ (diff_mem Φ a c)
      have e2 : al Φ (a ≫ b) c = mp S'.F b (al Φ a c) := mp_comp S'.F a b _
      rw [e2]
      linear_combination -hz
    · change mp S'.F b (th Φ hI hπ a (D R₀ _ (S.p U c))) + th Φ hI hπ b (p1 (OAff s₀) a (D R₀ _ (S.p U c))) =
        al Φ (a ≫ b) c - be Φ (a ≫ b) c
      rw [hA.der, p1_D]
      have e : mp (OAff s₀) a (S.p U c) = S.p V (mp S.F a c) := (S.nat a c).symm
      rw [e, hB.der, map_sub]
      have e2 : al Φ (a ≫ b) c = mp S'.F b (al Φ a c) := mp_comp S'.F a b _
      have e3 : be Φ (a ≫ b) c = be Φ b (mp S.F a c) := by
        change Φ.φ W (mp S.F (a ≫ b) c) = Φ.φ W (mp S.F b (mp S.F a c)); rw [mp_comp]
      have e4 : al Φ b (mp S.F a c) = mp S'.F b (be Φ a c) := rfl
      rw [e2, e3, e4]; ring
    · exact Ideal.add_mem _ (map_mem _ (hA.mem w)) (hB.mem _)
  have := (ex Φ hI hπ (a ≫ b)).unique (th_spec Φ hI hπ (a ≫ b)) h
  exact DFunLike.congr_fun this x

def cocyc (hI : I ^ 2 = 0) (hπ : Function.Surjective π) : GlobForm s₀ →+ Z1 S'.F where
  toFun w := ⟨fun U V a ↦ th Φ hI hπ a (w.1 U), fun U V W a b ↦ by
    change th Φ hI hπ (a ≫ b) (w.1 U) = mp S'.F b (th Φ hI hπ a (w.1 U)) + th Φ hI hπ b (w.1 V)
    rw [th_comp, w.2 a]⟩
  map_zero' := Subtype.ext (by funext U V a; exact map_zero _)
  map_add' w w' := Subtype.ext (by funext U V a; exact map_add _ _ _)

theorem th_smul (hI : I ^ 2 = 0) (hπ : Function.Surjective π) {U V : AffOp X₀} (a : U ⟶ V) (r : R)
    (x : Ω[Sec s₀ U.unop.1⁄R₀]) : th Φ hI hπ a (π r • x) = r • th Φ hI hπ a x := by
  rw [← algebraMap_smul (Sec s₀ U.unop.1) (π r) x, ← (S.semi U).map_algebraMap, (th_spec Φ hI hπ a).smul,
    AlgHom.commutes, ← Algebra.smul_def]

end GlobalTheory.LiftSys.Defect

theorem GlobalTheory.LiftSys.exists_defect_cocycle : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S S' : Sys I π s₀) (Φ : S.LocIso S'), ∃ (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V) (v : GlobForm s₀ →+ Z1 S'.F), Φ.IsDefect θ ∧ (∀ w U V a, (v w).1 U V a = θ U V a (w.1 U)) ∧ (∀ w, S'.IsIdealValuedLiftSystemCocycle (v w)) ∧ ∀ (r : R) w, v (π r • w) = r • v w := by
  intro R R₀ _ _ I hI π hπ _ X₀ s₀ S S' Φ
  refine ⟨fun U V a ↦ Defect.th Φ hI hπ a, Defect.cocyc Φ hI hπ, fun U V a ↦ Defect.th_spec Φ hI hπ a,
    fun w U V a ↦ rfl, fun w U V a ↦ (Defect.th_spec Φ hI hπ a).mem _, fun r w ↦ ?_⟩
  refine Subtype.ext ?_
  funext U V a
  exact Defect.th_smul Φ hI hπ a r (w.1 U)
