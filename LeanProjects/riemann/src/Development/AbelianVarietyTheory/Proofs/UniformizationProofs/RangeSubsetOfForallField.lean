import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.OverHomEqIffForallIsAlgClosedAlgebra
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonsingularIffNodal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NodalCubic

open GlobalTheory.WeierstrassCurve

noncomputable def evalAt {Z : Scheme.{0}} {k : Type} [CommRing k] (x : Spec (.of k) ⟶ Z) :
    Γ(Z, ⊤) →+* k := (x.appTop ≫ (Scheme.ΓSpecIso (.of k)).hom).hom

theorem comp_toSpecΓ {Z : Scheme.{0}} {k : Type} [CommRing k] (x : Spec (.of k) ⟶ Z) :
    x ≫ Z.toSpecΓ = Spec.map (CommRingCat.ofHom (evalAt x)) := by
  rw [Scheme.toSpecΓ_naturality, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
  rfl

theorem evalAt_comp {Z Z' : Scheme.{0}} {k : Type} [CommRing k] (x : Spec (.of k) ⟶ Z)
    (f : Z ⟶ Z') (s : Γ(Z', ⊤)) : evalAt (x ≫ f) s = evalAt x (f.appTop.hom s) := by
  simp [evalAt]
  rfl

theorem evalAt_specMap {A : CommRingCat.{0}} {k : Type} [CommRing k] (φ : A ⟶ .of k) (a : A) :
    evalAt (Spec.map φ) ((Scheme.ΓSpecIso A).inv.hom a) = φ.hom a := by
  rw [evalAt, Scheme.ΓSpecIso_naturality]
  simp

theorem isUnit_of_forall_evalAt {Z : Scheme.{0}} (s : Γ(Z, ⊤))
    (h : ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ Z), evalAt x s ≠ 0) : IsUnit s := by
  apply RingedSpace.isUnit_of_isUnit_germ Z.toRingedSpace ⊤ s
  intro z hz
  have h1 : IsUnit ((Z.fromSpecResidueField z).appTop.hom s) :=
    (isUnit_map_iff (Scheme.ΓSpecIso (Z.residueField z)).commRingCatIsoToRingEquiv _).mp
      (Ne.isUnit (h _ (Z.fromSpecResidueField z)))
  have h3 : (Z.fromSpecResidueField z) ⁻¹ᵁ Z.basicOpen s = ⊤ := by
    rw [Scheme.preimage_basicOpen_top, Scheme.basicOpen_of_isUnit _ h1]
  have h4 : (Z.fromSpecResidueField z) default ∈ Z.basicOpen s :=
    h3.ge (Set.mem_univ _)
  rw [Scheme.fromSpecResidueField_apply] at h4
  exact (Z.mem_basicOpen_top s z).mp h4

section Torus

variable {S : Scheme.{0}} {Z : Over S}

noncomputable def unitOf (t : Z ⟶ splitTorus S ℤ) : Γ(Z.left, ⊤)ˣ :=
  splitTorusPointsEquiv S ℤ Z t (Multiplicative.ofAdd 1)

theorem unitOf_mul (a b : Z ⟶ splitTorus S ℤ) : unitOf (a * b) = unitOf a * unitOf b := by
  simp [unitOf]

theorem unitOf_injective : Function.Injective (unitOf : (Z ⟶ splitTorus S ℤ) → _) :=
  fun _ _ h => (splitTorusPointsEquiv S ℤ Z).injective (MonoidHom.ext_mint h)

theorem unitOf_surjective : Function.Surjective (unitOf : (Z ⟶ splitTorus S ℤ) → _) :=
  fun u => ⟨(splitTorusPointsEquiv S ℤ Z).symm (zpowersHom _ u), by simp [unitOf]⟩

theorem unitOf_comp {Z' : Over S} (x : Z' ⟶ Z) (t : Z ⟶ splitTorus S ℤ) :
    (unitOf (x ≫ t)).val = x.left.appTop.hom (unitOf t).val := by
  simp [unitOf, splitTorusPointsEquiv_val]
  rfl

noncomputable def valOf {k : Type} [CommRing k] {s : Spec (.of k) ⟶ S}
    (t : Over.mk s ⟶ splitTorus S ℤ) : kˣ :=
  Units.map (Scheme.ΓSpecIso (.of k)).hom.hom.toMonoidHom (unitOf t)

variable {k : Type} [CommRing k] {s : Spec (.of k) ⟶ S}

theorem valOf_mul (a b : Over.mk s ⟶ splitTorus S ℤ) : valOf (a * b) = valOf a * valOf b := by
  rw [valOf, unitOf_mul, map_mul]; rfl

theorem valOf_injective : Function.Injective (valOf : (Over.mk s ⟶ splitTorus S ℤ) → kˣ) :=
  fun _ _ h => unitOf_injective (Units.map_injective
    (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.injective h)

theorem valOf_comp (x : Over.mk s ⟶ Z) (t : Z ⟶ splitTorus S ℤ) :
    (valOf (x ≫ t) : k) = evalAt x.left (unitOf t).val := by
  change (Scheme.ΓSpecIso (.of k)).hom.hom (unitOf (x ≫ t)).val = _
  rw [unitOf_comp]
  rfl

end Torus

def param {A : Type} [CommRing A] (u : A) : Fin 3 → A := ![u * (1 - u), u ^ 2, (1 - u) ^ 3]

abbrev node (K : Type) [CommRing K] : WeierstrassCurve K := ⟨1, 0, 0, 0, 0⟩

theorem node_map {K A : Type} [CommRing K] [CommRing A] (ρ : K →+* A) :
    (node K).map ρ = node A := by
  ext <;> simp

theorem comp_param {A B : Type} [CommRing A] [CommRing B] (g : A →+* B) (u : A) :
    g ∘ param u = param (g u) := by
  ext i
  fin_cases i <;> simp [param]

theorem isUnimodularSol_param {K A : Type} [CommRing K] [CommRing A] (ρ : K →+* A) (u : Aˣ) :
    IsUnimodularSol ((node K).map ρ) (param (u : A)) := by
  refine .of_isUnit ?_ 1 (u.isUnit.pow 2)
  rw [node_map, WeierstrassCurve.Projective.equation_iff]
  simp [param]
  ring

variable (K : Type) [Field K]

noncomputable def constHom (Z : Over (Spec (.of K))) : K →+* Γ(Z.left, ⊤) :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ Z.hom.appTop).hom

theorem toSpecΓ_constHom (Z : Over (Spec (.of K))) :
    Z.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (constHom K Z)) = Z.hom := by
  rw [constHom, CommRingCat.ofHom_hom, Spec.map_comp, ← Category.assoc,
    ← Scheme.toSpecΓ_naturality, ← SpecMap_ΓSpecIso_hom, Category.assoc, ← Spec.map_comp]
  simp

noncomputable def paramHom : (splitTorus (Spec (.of K)) ℤ).left ⟶ scheme (node K) :=
  (splitTorus (Spec (.of K)) ℤ).left.toSpecΓ ≫
    ptHom (node K) (constHom K _) (param (unitOf (𝟙 _)).val) (isUnimodularSol_param _ _)

theorem paramHom_toSpec : paramHom K ≫ toSpec (node K) = (splitTorus (Spec (.of K)) ℤ).hom := by
  rw [paramHom, Category.assoc, ptHom_toSpec, toSpecΓ_constHom]

variable {K}

theorem comp_paramHom {k : Type} [CommRing k] {ρ : K →+* k}
    (x : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ splitTorus (Spec (.of K)) ℤ) :
    x.left ≫ paramHom K = ptHom (node K) ρ (param (valOf x : k)) (isUnimodularSol_param _ _) := by
  have e := comp_toSpecΓ (k := k) x.left
  have e2 : (evalAt (k := k) x.left).comp (constHom K _) = ρ := by
    have : Spec.map (CommRingCat.ofHom ((evalAt (k := k) x.left).comp (constHom K _))) =
        Spec.map (CommRingCat.ofHom ρ) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, ← e]
      exact (Category.assoc _ _ _).trans
        ((congrArg (x.left ≫ ·) (toSpecΓ_constHom K _)).trans (Over.w x))
    exact congrArg (·.hom) (Spec.map_injective this)
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e).trans ?_)
  rw [SpecMap_ptHom]
  refine ptHom_congr _ _ _ _ e2 ?_ _
  rw [comp_param, ← valOf_comp, Category.comp_id]

theorem exists_over_point {Z : Over (Spec (.of K))} {k : Type} [CommRing k]
    (x : Spec (.of k) ⟶ Z.left) :
    ∃ (ρ : K →+* k) (y : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ Z), y.left = x :=
  ⟨(Spec.preimage (x ≫ Z.hom)).hom, Over.homMk x (by simp), rfl⟩

theorem range_subset_of_forall_field {Z Y : Scheme.{0}} (f : Z ⟶ Y) (V : Y.Opens)
    (h : ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ Z), ⊤ ≤ (x ≫ f) ⁻¹ᵁ V) :
    Set.range f ⊆ V := by
  rintro _ ⟨z, rfl⟩
  have := h _ (Z.fromSpecResidueField z) (Set.mem_univ default)
  have h2 : f ((Z.fromSpecResidueField z) default) ∈ V := this
  rwa [Scheme.fromSpecResidueField_apply] at h2

theorem over_hom_ext_field {T Y : Over (Spec (.of K))} [IsReduced T.left] [IsSeparated Y.hom]
    {f g : T ⟶ Y} (h : ∀ (k : Type) [Field k] (ρ : K →+* k)
      (x : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ T), x ≫ f = x ≫ g) : f = g :=
  over_hom_eq_iff_forall_field_algebra.mpr fun k _ _ x => h k _ x

section Locus

variable (U : (scheme (node K)).Opens)
  (hU : ∀ (k : Type) [Field k] (ρ : K →+* k) (P : Fin 3 → k)
    (h : IsUnimodularSol ((node K).map ρ) P),
    ⊤ ≤ ptHom (node K) ρ P h ⁻¹ᵁ U ↔ ((node K).map ρ).toProjective.Nonsingular P)

include hU

theorem exists_toLocus : ∃ f : splitTorus (Spec (.of K)) ℤ ⟶ Over.mk (U.ι ≫ toSpec (node K)),
    f.left ≫ U.ι = paramHom K := by
  have h : Set.range (paramHom K) ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    refine range_subset_of_forall_field _ _ fun k _ x => ?_
    obtain ⟨ρ, y, rfl⟩ := exists_over_point x
    rw [comp_paramHom, hU, node_map]
    exact (nonsingular_points k).1 _
  have e := IsOpenImmersion.lift_fac U.ι (paramHom K) h
  refine ⟨Over.homMk (IsOpenImmersion.lift U.ι (paramHom K) h) ?_, e⟩
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e).trans (paramHom_toSpec K))

theorem exists_nonsingular {k : Type} [Field k] {ρ : K →+* k}
    (y : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ Over.mk (U.ι ≫ toSpec (node K))) :
    ∃ (P : Fin 3 → k) (h : IsUnimodularSol ((node K).map ρ) P),
      y.left ≫ U.ι = ptHom (node K) ρ P h ∧ (node k).toProjective.Nonsingular P := by
  obtain ⟨P, h, e⟩ := exists_eq_ptHom (node K) ρ (y.left ≫ U.ι)
    ((Category.assoc _ _ _).trans (Over.w y))
  refine ⟨P, h, e, ?_⟩
  rw [← node_map ρ, ← hU k ρ P h, ← e]
  intro z _
  exact (y.left z).2

theorem exists_fromLocus : ∃ g : Over.mk (U.ι ≫ toSpec (node K)) ⟶ splitTorus (Spec (.of K)) ℤ,
    ∀ (k : Type) [Field k] (ρ : K →+* k)
      (y : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ Over.mk (U.ι ≫ toSpec (node K)))
      (P : Fin 3 → k) (h : IsUnimodularSol ((node K).map ρ) P),
      y.left ≫ U.ι = ptHom (node K) ρ P h → (valOf (y ≫ g) : k) = P 1 / (P 0 + P 1) := by
  have h : Set.range U.ι ⊆ Set.range (awayChart (node K) 1) := by
    rw [← (awayChart (node K) 1).coe_opensRange, opensRange_awayChart]
    refine range_subset_of_forall_field _ _ fun k _ x => ?_
    obtain ⟨ρ, y, rfl⟩ := exists_over_point (Z := Over.mk (U.ι ≫ toSpec (node K))) x
    obtain ⟨P, hP, e, hn⟩ := exists_nonsingular U hU y
    have h1 := ((nonsingular_points k).2.2 P hn).1
    refine le_of_eq (Eq.symm ?_)
    refine (congrArg (· ⁻¹ᵁ _) e).trans ?_
    rw [ptHom_preimage_coordOpen]
    exact top_le_iff.mp fun p _ hp => p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hp h1.isUnit)
  let j := IsOpenImmersion.lift (awayChart (node K) 1) U.ι h
  have hj : j ≫ awayChart (node K) 1 = U.ι := IsOpenImmersion.lift_fac _ _ h
  let s : Γ(U.toScheme, ⊤) := j.appTop.hom ((Scheme.ΓSpecIso (.of (AwayRing (node K) 1))).inv.hom
    (awayCoord (node K) 1 0 + 1))
  have key : ∀ (k : Type) [Field k] (ρ : K →+* k) (x : Spec (.of k) ⟶ U.toScheme)
      (P : Fin 3 → k) (h : IsUnimodularSol ((node K).map ρ) P),
      x ≫ U.ι = ptHom (node K) ρ P h →
        P 1 ≠ 0 ∧ P 0 + P 1 ≠ 0 ∧ evalAt x s * P 1 = P 0 + P 1 := by
    intro k _ ρ x P hP e
    have hn : (node k).toProjective.Nonsingular P := by
      rw [← node_map ρ, ← hU k ρ P hP, ← e]
      intro z _
      exact (x z).2
    obtain ⟨h1, h2, -⟩ := (nonsingular_points k).2.2 P hn
    refine ⟨h1, h2, ?_⟩
    have e2 : x ≫ j = Spec.map (CommRingCat.ofHom
        (awayEval (node K) 1 ρ P hP.equation h1.isUnit)) := by
      rw [← cancel_mono (awayChart (node K) 1), Category.assoc, hj, e,
        ptHom_eq_awayChart _ 1 _ _ _ h1.isUnit]
    rw [← evalAt_comp, e2, evalAt_specMap, CommRingCat.hom_ofHom, map_add, map_one, add_mul,
      awayEval_awayCoord_mul, _root_.one_mul]
  have hs : IsUnit s := by
    refine isUnit_of_forall_evalAt s fun k _ x h0 => ?_
    obtain ⟨ρ, y, rfl⟩ := exists_over_point (Z := Over.mk (U.ι ≫ toSpec (node K))) x
    obtain ⟨P, hP, e, -⟩ := exists_nonsingular U hU y
    obtain ⟨-, h2, h3⟩ := key k ρ y.left P hP e
    exact h2 (by rw [← h3]; exact mul_eq_zero_of_left h0 _)
  obtain ⟨g, hg⟩ := unitOf_surjective (Z := Over.mk (U.ι ≫ toSpec (node K))) hs.unit⁻¹
  refine ⟨g, fun k _ ρ y P hP e => ?_⟩
  obtain ⟨h1, h2, h3⟩ := key k ρ y.left P hP e
  have h4 : evalAt (k := k) y.left (unitOf g).val * evalAt (k := k) y.left s = 1 := by
    rw [hg]
    exact (map_mul _ _ _).symm.trans ((congrArg _ hs.val_inv_mul).trans (map_one _))
  rw [valOf_comp, eq_div_iff h2, ← h3, ← _root_.mul_assoc]
  exact (congrArg (· * P 1) h4).trans (_root_.one_mul _)

end Locus

theorem isMonHom_of_mul_hom {C : Type*} [Category C] [CartesianMonoidalCategory C] {G H : C}
    [GrpObj G] [GrpObj H] (f : G ⟶ H) (h : μ[G] ≫ f = (f ⊗ₘ f) ≫ μ[H]) : IsMonHom f where
  mul_hom := h
  one_hom := by
    have e : (η[G] ≫ f) * (η[G] ≫ f) = η[G] ≫ f := by
      have h1 : lift η[G] η[G] ≫ μ[G] = η[G] := by
        simpa using MonObj.lift_comp_one_left (𝟙 (𝟙_ C)) η[G]
      rw [Hom.mul_def, ← lift_map, Category.assoc, ← h, ← Category.assoc, h1]
    rw [mul_eq_left.mp e, Hom.one_def]
    simp

theorem exists_splitTorus_iso : ∀ (K : Type) [Field K] (W : WeierstrassCurve K), W = ⟨1, 0, 0, 0, 0⟩ → ∀ (U : (GlobalTheory.WeierstrassCurve.scheme W).Opens), (∀ (k : Type) [Field k] (ρ : K →+* k) (P : Fin 3 → k) (h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P), ⊤ ≤ GlobalTheory.WeierstrassCurve.ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P) → Smooth (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → GeometricallyIntegral (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → ∀ [GrpObj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))], (∀ (k : Type) [Field k] (ρ : K →+* k) (x y : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))) (P Q : Fin 3 → k) (hP : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P) (hQ : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) Q), x.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ P hP → y.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ Q hQ → ∃ h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.add P Q), (lift x y ≫ μ[(Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))]).left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ _ h) → ∃ i : splitTorus (Spec (CommRingCat.of K)) ℤ ≅ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)), IsMonHom i.hom := by
  intro K _ W hW
  subst hW
  intro U hU hsm _ _ hadd
  obtain ⟨f, hf⟩ := exists_toLocus U hU
  obtain ⟨g, hg⟩ := exists_fromLocus U hU
  have hpt : ∀ (k : Type) [Field k] (ρ : K →+* k)
      (x : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ splitTorus (Spec (.of K)) ℤ),
      (x ≫ f).left ≫ U.ι =
        ptHom (node K) ρ (param (valOf x : k)) (isUnimodularSol_param _ _) := fun k _ ρ x =>
    (Category.assoc _ _ _).trans ((congrArg (x.left ≫ ·) hf).trans (comp_paramHom x))
  have r1 : IsReduced (splitTorus (Spec (.of K)) ℤ).left :=
    isReduced_of_smooth_of_isReduced (splitTorus (Spec (.of K)) ℤ).hom
  have r2 : IsReduced (Over.mk (U.ι ≫ toSpec (node K))).left :=
    @isReduced_of_smooth_of_isReduced _ _ (U.ι ≫ toSpec (node K)) hsm _
  have s3 : Smooth (splitTorus (Spec (.of K)) ℤ ⊗ splitTorus (Spec (.of K)) ℤ).hom :=
    inferInstanceAs (Smooth (pullback.fst (splitTorus (Spec (.of K)) ℤ).hom
      (splitTorus (Spec (.of K)) ℤ).hom ≫ (splitTorus (Spec (.of K)) ℤ).hom))
  have r3 : IsReduced (splitTorus (Spec (.of K)) ℤ ⊗ splitTorus (Spec (.of K)) ℤ).left :=
    isReduced_of_smooth_of_isReduced
      (splitTorus (Spec (.of K)) ℤ ⊗ splitTorus (Spec (.of K)) ℤ).hom
  have sep : IsSeparated (Over.mk (U.ι ≫ toSpec (node K))).hom :=
    inferInstanceAs (IsSeparated (U.ι ≫ toSpec (node K)))
  have ext : ∀ {Z : Over (Spec (.of K))} {a b : Z ⟶ Over.mk (U.ι ≫ toSpec (node K))},
      a.left ≫ U.ι = b.left ≫ U.ι → a = b := fun h =>
    Over.OverMorphism.ext ((cancel_mono U.ι).mp h)
  refine ⟨⟨f, g, ?_, ?_⟩, isMonHom_of_mul_hom f ?_⟩
  · refine over_hom_ext_field fun k _ ρ x => valOf_injective (Units.ext ?_)
    rw [← Category.assoc, hg k ρ _ _ _ (hpt k ρ x), Category.comp_id]
    have := (valOf x).ne_zero
    have e : param (valOf x : k) 0 + param (valOf x : k) 1 = valOf x := by
      simp [param]; ring
    rw [e, div_eq_iff this]
    simp [param, sq]
  · refine over_hom_ext_field fun k _ ρ y => ext ?_
    obtain ⟨P, hP, e, hn⟩ := exists_nonsingular U hU y
    obtain ⟨-, -, c, hc⟩ := (nonsingular_points k).2.2 P hn
    rw [← Category.assoc, hpt, Category.comp_id, e, ptHom_eq_ptHom_iff]
    exact ⟨c, by rw [hg k ρ y P hP e]; exact hc⟩
  · refine over_hom_ext_field fun k _ ρ x => ext ?_
    obtain ⟨h, e⟩ := hadd k ρ _ _ _ _ _ _ (hpt k ρ (x ≫ fst _ _)) (hpt k ρ (x ≫ snd _ _))
    have e1 : x ≫ μ = (x ≫ fst _ _) * (x ≫ snd _ _) := by
      rw [Hom.mul_def, lift_comp_fst_snd]
    have e2 : x ≫ (f ⊗ₘ f) = lift ((x ≫ fst _ _) ≫ f) ((x ≫ snd _ _) ≫ f) := by
      rw [← lift_map, lift_comp_fst_snd]
    obtain ⟨c, hc⟩ := (nonsingular_points k).2.1 (valOf (x ≫ fst _ _)) (valOf (x ≫ snd _ _))
    rw [← Category.assoc, ← Category.assoc, e1, e2, hpt, e, ptHom_eq_ptHom_iff]
    exact ⟨c, by rw [valOf_mul, node_map]; exact hc⟩

end GlobalTheory.NodalCubic
