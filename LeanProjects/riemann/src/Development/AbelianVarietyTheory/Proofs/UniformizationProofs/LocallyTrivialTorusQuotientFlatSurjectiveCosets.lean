import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusStableAffineOpenFunctionsWeightGradedStatement

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.LocTriv

section Algebra
variable {R A X : Type} [CommRing R] [CommRing A] [AddCommGroup X]

theorem of_basis (f : R →+* A) (u : Multiplicative X →* Aˣ)
    (hs : ∀ a : A, ∃ c : X →₀ R, a = c.sum fun χ r => f r * (u (Multiplicative.ofAdd χ)).val)
    (hi : ∀ c : X →₀ R, (c.sum fun χ r => f r * (u (Multiplicative.ofAdd χ)).val) = 0 → c = 0) :
    f.Flat ∧ ∃ σ : A →+* R, σ.comp f = RingHom.id R :=  by
  classical
  letI : Algebra R A := f.toAlgebra
  have hφ : ∀ c : AddMonoidAlgebra R X,
      AddMonoidAlgebra.lift R A X ((Units.coeHom A).comp u) c =
        c.coeff.sum fun χ r => f r * (u (Multiplicative.ofAdd χ)).val :=
    fun c => AddMonoidAlgebra.lift_apply' _ _
  have hbij : Function.Bijective (AddMonoidAlgebra.lift R A X ((Units.coeHom A).comp u)) := by
    refine ⟨?_, fun a => ?_⟩
    · rw [injective_iff_map_eq_zero]
      intro c hc
      obtain ⟨c⟩ := c
      have h0 : c = 0 := hi c ((hφ _).symm.trans hc)
      subst h0
      rfl
    · obtain ⟨c, hc⟩ := hs a
      exact ⟨AddMonoidAlgebra.ofCoeff c, (hφ _).trans hc.symm⟩
  let e := AlgEquiv.ofBijective (AddMonoidAlgebra.lift R A X ((Units.coeHom A).comp u)) hbij
  refine ⟨?_, ((AddMonoidAlgebra.lift R R X 1).comp e.symm.toAlgHom).toRingHom, ?_⟩
  · have hfl : Module.Flat R (AddMonoidAlgebra R X) := inferInstance
    have : Module.Flat R A := Module.Flat.of_linearEquiv e.symm.toLinearEquiv
    exact this
  · ext r
    exact ((AddMonoidAlgebra.lift R R X 1).comp e.symm.toAlgHom).commutes r

end Algebra

theorem hom_ext_appLE {Z Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U) {a b : Z ⟶ Y}
    (ha : ⊤ ≤ a ⁻¹ᵁ U) (hb : ⊤ ≤ b ⁻¹ᵁ U) (h : a.appLE U ⊤ ha = b.appLE U ⊤ hb) : a = b :=  by
  haveI : IsAffine U.toScheme := hU
  have h1 : a.resLE U ⊤ ha = b.resLE U ⊤ hb := by
    apply ext_of_isAffine
    show (a.resLE U ⊤ ha).app ⊤ = (b.resLE U ⊤ hb).app ⊤
    rw [Scheme.Hom.resLE_app_top, Scheme.Hom.resLE_app_top, h]
  have h2 := congrArg (· ≫ U.ι) h1
  simp only [Scheme.Hom.resLE_comp_ι] at h2
  calc a = Z.topIso.inv ≫ (⊤ : Z.Opens).ι ≫ a := by
        rw [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]
    _ = Z.topIso.inv ≫ (⊤ : Z.Opens).ι ≫ b := by rw [h2]
    _ = b := by rw [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]

variable {S : Scheme.{0}}

def incl (Z : Over S) (W : Z.left.Opens) : Over.mk (W.ι ≫ Z.hom) ⟶ Z := Over.homMk W.ι rfl

theorem over_ext {Z Y : Over S} {a b : Z ⟶ Y} (h : ∀ z : Z.left, ∃ W, z ∈ W ∧ incl Z W ≫ a = incl Z W ≫ b) :
    a = b :=  by
  choose W hW he using h
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext (Z.left.openCoverOfIsOpenCover W ?_) _ _ fun z => ?_
  · rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro z _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨z, hW z⟩
  · have := congrArg (fun f => f.left) (he z)
    simp only [incl, Over.comp_left, Over.homMk_left] at this
    exact this

theorem incl_le {Z Y : Over S} (a : Z ⟶ Y) (U : Y.left.Opens) :
    ⊤ ≤ (incl Z (a.left ⁻¹ᵁ U) ≫ a).left ⁻¹ᵁ U :=  by
  rintro ⟨z, hz⟩ -
  exact hz

variable {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] {i : splitTorus S X ⟶ G} {q : G ⟶ B}

theorem stable {U : G.left.Opens}
    (hU : (snd (splitTorus _ X) G).left ⁻¹ᵁ U ≤ ((fst (splitTorus _ X) G ≫ i) * snd _ G).left ⁻¹ᵁ U)
    {Z : Over S} (t : Z ⟶ splitTorus S X) {g : Z ⟶ G} (hg : ⊤ ≤ g.left ⁻¹ᵁ U) :
    ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ U :=  by
  intro z _
  have h1 : (lift t g).left z ∈ (snd (splitTorus S X) G).left ⁻¹ᵁ U := by
    have : z ∈ g.left ⁻¹ᵁ U := hg trivial
    rwa [← lift_snd t g, Over.comp_left] at this
  have h2 := hU h1
  have e : (t ≫ i) * g = lift t g ≫ ((fst (splitTorus S X) G ≫ i) * snd _ G) := by
    rw [comp_mul, lift_fst_assoc, lift_snd]
  rw [e, Over.comp_left]
  exact h2

theorem eq_of_units {U : G.left.Opens}
    (hU : (snd (splitTorus _ X) G).left ⁻¹ᵁ U ≤ ((fst (splitTorus _ X) G ≫ i) * snd _ G).left ⁻¹ᵁ U)
    (u : X → Γ(G.left, U)ˣ) (hu : ∀ χ, IsWt i U (u χ).val χ)
    {Z : Over S} {t t' : Z ⟶ splitTorus S X} {g : Z ⟶ G} (hg : ⊤ ≤ g.left ⁻¹ᵁ U) (h : t ≫ i = t' ≫ i) : t = t' :=  by
  have h₁ := stable hU t hg
  have h₁' := stable hU t' hg
  have e3 : ∀ (s s' : Z ⟶ G) (hs : ⊤ ≤ s.left ⁻¹ᵁ U) (hs' : ⊤ ≤ s'.left ⁻¹ᵁ U), s = s' →
      s.left.appLE U ⊤ hs = s'.left.appLE U ⊤ hs' := by
    rintro s _ hs hs' rfl; rfl
  have key : ∀ χ, chV t χ = chV t' χ := by
    intro χ
    have e1 := hu χ Z t g h₁ hg
    have e2 := hu χ Z t' g h₁' hg
    rw [e3 _ _ h₁ h₁' (by rw [h])] at e1
    rw [e1] at e2
    have hunit : IsUnit ((g.left.appLE U ⊤ hg).hom (u χ).val) := (u χ).isUnit.map _
    apply Units.ext
    rw [chV_val, chV_val]
    exact hunit.mul_right_cancel e2
  apply (splitTorusPointsEquiv S X Z).injective
  refine MonoidHom.ext fun m => ?_
  exact key (Multiplicative.toAdd m)

section Chart
variable [IsMonHom i] [IsAffineHom q.left] {V : B.left.Opens} (hV : IsAffineOpen V)
  (h₀ : ∀ a : Γ(G.left, q.left ⁻¹ᵁ V), IsWt i _ a 0 ↔ ∃ c, (q.left.app V).hom c = a)
  (hU : (snd (splitTorus _ X) G).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) ≤
    ((fst (splitTorus _ X) G ≫ i) * snd _ G).left ⁻¹ᵁ (q.left ⁻¹ᵁ V))
  (u : Multiplicative X →* Γ(G.left, q.left ⁻¹ᵁ V)ˣ) (hu : ∀ χ, IsWt i _ (u (Multiplicative.ofAdd χ)).val χ)
include hV h₀ hU

include hu in

theorem exists_sum (a : Γ(G.left, q.left ⁻¹ᵁ V)) : ∃ c : X →₀ Γ(B.left, V),
    a = c.sum fun χ r => (q.left.app V).hom r * (u (Multiplicative.ofAdd χ)).val :=  by
  classical
  have hA : IsAffineOpen (q.left ⁻¹ᵁ V) := hV.preimage q.left
  obtain ⟨w, hw, rfl⟩ := (GlobalTheory.T.torusStable_affineOpen_functions_weightGraded S G X i inferInstance _ hA hU).1 a
  have hc : ∀ χ, ∃ c, (q.left.app V).hom c = w χ * ((u (Multiplicative.ofAdd χ))⁻¹).val := by
    intro χ
    refine (h₀ _).1 ?_
    have := (hw χ).mul (IsWt.inv (hu χ))
    rwa [add_neg_cancel] at this
  choose c hc using hc
  refine ⟨Finsupp.onFinset w.support (fun χ => if w χ = 0 then 0 else c χ) ?_, ?_⟩
  · intro χ hχ
    rw [Finsupp.mem_support_iff]
    intro h0
    exact hχ (if_pos h0)
  · rw [Finsupp.onFinset_sum]
    · rw [Finsupp.sum]
      refine Finset.sum_congr rfl fun χ hχ => ?_
      rw [if_neg (Finsupp.mem_support_iff.1 hχ), hc, Units.inv_mul_cancel_right]
    · intro χ
      simp

include hu in

theorem eq_zero_of_sum (hinj : Function.Injective (q.left.app V).hom) (c : X →₀ Γ(B.left, V))
    (hc : (c.sum fun χ r => (q.left.app V).hom r * (u (Multiplicative.ofAdd χ)).val) = 0) : c = 0 :=  by
  classical
  have hA : IsAffineOpen (q.left ⁻¹ᵁ V) := hV.preimage q.left
  have hsupp : ∀ χ, (q.left.app V).hom (c χ) * (u (Multiplicative.ofAdd χ)).val ≠ 0 → χ ∈ c.support := by
    intro χ hχ
    rw [Finsupp.mem_support_iff]
    intro h0
    apply hχ
    rw [h0, map_zero, zero_mul]
  let w : X →₀ Γ(G.left, q.left ⁻¹ᵁ V) := Finsupp.onFinset c.support
    (fun χ => (q.left.app V).hom (c χ) * (u (Multiplicative.ofAdd χ)).val) hsupp
  have hwt : ∀ χ, IsWt i _ (w χ) χ := by
    intro χ
    have := ((h₀ _).2 ⟨c χ, rfl⟩).mul (hu χ)
    rw [zero_add] at this
    exact this
  have hsum : (w.sum fun _ x => x) = 0 := by
    rw [Finsupp.onFinset_sum hsupp (fun _ => rfl), ← hc, Finsupp.sum]
  have hw : w = 0 := (GlobalTheory.T.torusStable_affineOpen_functions_weightGraded S G X i inferInstance _ hA hU).2 w hwt hsum
  ext χ
  have h1 : w χ = 0 := by rw [hw]; rfl
  have h2 : (q.left.app V).hom (c χ) = 0 := (Units.mul_left_eq_zero _).1 h1
  exact hinj (h2.trans (map_zero _).symm)

omit hV h₀ hU [GrpObj G] [IsMonHom i] [IsAffineHom q.left] in

theorem appLE_app {Z : Over S} (g : Z ⟶ G) (hg : ⊤ ≤ g.left ⁻¹ᵁ (q.left ⁻¹ᵁ V)) :
    q.left.app V ≫ g.left.appLE _ ⊤ hg = (g ≫ q).left.appLE V ⊤ hg :=  by
  exact (Scheme.Hom.comp_appLE g.left q.left V ⊤ hg).symm

omit [IsMonHom i] [IsAffineHom q.left] in

theorem comp_eq {Z : Over S} (t : Z ⟶ splitTorus S X) {g : Z ⟶ G} (hg : ⊤ ≤ g.left ⁻¹ᵁ (q.left ⁻¹ᵁ V)) :
    g ≫ q = ((t ≫ i) * g) ≫ q :=  by
  have h₁ := stable hU t hg
  apply Over.OverMorphism.ext
  refine hom_ext_appLE hV hg h₁ ?_
  have e1 := appLE_app (q := q) g hg
  have e2 := appLE_app (q := q) ((t ≫ i) * g) h₁
  rw [← e1, ← e2]
  apply CommRingCat.hom_ext
  ext c
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  rw [(h₀ _).2 ⟨c, rfl⟩ Z t g h₁ hg, ← chV_val, chV_zero, Units.val_one, _root_.one_mul]

include hu in

theorem exists_point {Z : Over S} {g g' : Z ⟶ G} (hg : ⊤ ≤ g.left ⁻¹ᵁ (q.left ⁻¹ᵁ V)) (h : g ≫ q = g' ≫ q) :
    ∃ t : Z ⟶ splitTorus S X, g' = (t ≫ i) * g :=  by
  have hg' : ⊤ ≤ g'.left ⁻¹ᵁ (q.left ⁻¹ᵁ V) := by
    have : ⊤ ≤ (g ≫ q).left ⁻¹ᵁ V := hg
    rw [h] at this
    exact this
  let φ : Multiplicative X →* Γ(Z.left, ⊤)ˣ :=
    (Units.map (g'.left.appLE _ ⊤ hg').hom.toMonoidHom).comp u /
      (Units.map (g.left.appLE _ ⊤ hg).hom.toMonoidHom).comp u
  refine ⟨(splitTorusPointsEquiv S X Z).symm φ, ?_⟩
  set t := (splitTorusPointsEquiv S X Z).symm φ with ht
  have hχ : ∀ χ, (chV t χ).val * (g.left.appLE _ ⊤ hg).hom (u (Multiplicative.ofAdd χ)).val =
      (g'.left.appLE _ ⊤ hg').hom (u (Multiplicative.ofAdd χ)).val := by
    intro χ
    have h3 : chV t χ = φ (Multiplicative.ofAdd χ) := by
      show (splitTorusPointsEquiv S X Z) t (Multiplicative.ofAdd χ) = _
      rw [ht]
      simp
    have h4 : φ (Multiplicative.ofAdd χ) *
        Units.map (g.left.appLE _ ⊤ hg).hom.toMonoidHom (u (Multiplicative.ofAdd χ)) =
        Units.map (g'.left.appLE _ ⊤ hg').hom.toMonoidHom (u (Multiplicative.ofAdd χ)) := by
      simp only [φ, MonoidHom.div_apply, MonoidHom.comp_apply, div_mul_cancel]
    rw [h3]
    exact congrArg Units.val h4
  have e3 : ∀ (s s' : Z ⟶ B) (hs : ⊤ ≤ s.left ⁻¹ᵁ V) (hs' : ⊤ ≤ s'.left ⁻¹ᵁ V), s = s' →
      s.left.appLE V ⊤ hs = s'.left.appLE V ⊤ hs' := by
    rintro s _ hs hs' rfl; rfl
  have hq : ∀ r, (g.left.appLE _ ⊤ hg).hom ((q.left.app V).hom r) =
      (g'.left.appLE _ ⊤ hg').hom ((q.left.app V).hom r) := by
    intro r
    have e1 := appLE_app (q := q) g hg
    have e2 := appLE_app (q := q) g' hg'
    have := congrArg (fun f => f.hom r) (e1.trans ((e3 _ _ hg hg' h).trans e2.symm))
    simpa using this
  have hA : IsAffineOpen (q.left ⁻¹ᵁ V) := hV.preimage q.left
  have h₁ := stable hU t hg
  apply Over.OverMorphism.ext
  refine hom_ext_appLE hA hg' h₁ ?_
  apply CommRingCat.hom_ext
  ext a
  obtain ⟨c, rfl⟩ := exists_sum hV h₀ hU u hu a
  simp only [Finsupp.sum, map_sum, map_mul]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [(h₀ _).2 ⟨c χ, rfl⟩ Z t g h₁ hg, hu χ Z t g h₁ hg, ← chV_val t (0 : X), chV_zero, Units.val_one,
    _root_.one_mul, ← chV_val t χ, hq, ← hχ]

end Chart

theorem main : (∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (G B : Over S) [GrpObj G] (i : splitTorus S X ⟶ G) (q : G ⟶ B), IsMonHom i → IsAffineHom q.left → (∀ b : B.left, ∃ V : B.left.Opens, b ∈ V ∧ IsAffineOpen V ∧ (∀ a : Γ(G.left, q.left ⁻¹ᵁ V), IsWt i _ a 0 ↔ ∃ c, (q.left.app V).hom c = a) ∧ Function.Injective (q.left.app V).hom ∧ (snd (splitTorus _ X) G).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) ≤ ((fst (splitTorus _ X) G ≫ i) * snd _ G).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) ∧ ∃ u : Multiplicative X →* Γ(G.left, q.left ⁻¹ᵁ V)ˣ, ∀ χ, IsWt i _ (u (Multiplicative.ofAdd χ)).val χ) → Mono i ∧ Flat q.left ∧ Surjective q.left ∧ (Smooth G.hom → Smooth B.hom) ∧ ∀ (Z : Over S) (g g' : Z ⟶ G), g ≫ q = g' ≫ q ↔ ∃ t : Z ⟶ splitTorus S X, g' = (t ≫ i) * g) :=  by
  intro S X _ G B _ i q hi hq hloc
  choose V hbV hV h₀ hinj hU u hu using hloc
  have hA : ∀ b, IsAffineOpen (q.left ⁻¹ᵁ V b) := fun b => (hV b).preimage q.left
  have hB : ∀ b, (q.left.app (V b)).hom.Flat ∧
      ∃ σ : Γ(G.left, q.left ⁻¹ᵁ V b) →+* Γ(B.left, V b), σ.comp (q.left.app (V b)).hom = RingHom.id _ :=
    fun b => of_basis _ (u b) (exists_sum (hV b) (h₀ b) (hU b) (u b) (hu b))
      (fun c hc => eq_zero_of_sum (hV b) (h₀ b) (hU b) (u b) (hu b) (hinj b) c hc)
  have hsec : ∀ b, ∃ s : (V b).toScheme ⟶ (q.left ⁻¹ᵁ V b).toScheme, s ≫ (q.left ∣_ V b) = 𝟙 _ := by
    intro b
    obtain ⟨σ, hσ⟩ := (hB b).2
    refine ⟨(hV b).isoSpec.hom ≫ Spec.map (CommRingCat.ofHom σ) ≫ (hA b).isoSpec.inv, ?_⟩
    have e1 : q.left.app (V b) ≫ CommRingCat.ofHom σ = 𝟙 _ := by
      ext r
      exact RingHom.congr_fun hσ r
    rw [← cancel_mono (V b).ι]
    simp only [Category.assoc, morphismRestrict_ι, Category.id_comp]
    rw [← Category.assoc (hA b).isoSpec.inv, IsAffineOpen.isoSpec_inv_ι,
      ← IsAffineOpen.SpecMap_appLE_fromSpec q.left (hV b) (hA b) le_rfl, ← Spec.map_comp_assoc,
      ← Scheme.Hom.app_eq_appLE, e1, Spec.map_id, Category.id_comp, IsAffineOpen.isoSpec_hom_fromSpec]
  have hcov : TopologicalSpace.IsOpenCover V := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨x, hbV x⟩
  refine ⟨⟨fun {Z} t t' h => ?_⟩, ?_, ⟨fun b => ?_⟩, fun hGs => ?_, fun Z g g' => ⟨fun h => ?_, ?_⟩⟩
  · apply over_ext
    intro z
    refine ⟨(t ≫ i).left ⁻¹ᵁ (q.left ⁻¹ᵁ V (q.left ((t ≫ i).left z))), hbV _, ?_⟩
    refine eq_of_units (hU (q.left ((t ≫ i).left z)))
      (fun χ => u (q.left ((t ≫ i).left z)) (Multiplicative.ofAdd χ)) (hu (q.left ((t ≫ i).left z)))
      (incl_le (t ≫ i) (q.left ⁻¹ᵁ V (q.left ((t ≫ i).left z)))) ?_
    rw [Category.assoc, Category.assoc, h]
  · rw [HasRingHomProperty.iff_exists_appLE (P := @Flat)
      ((RingHom.Flat.stableUnderComposition.stableUnderCompositionWithLocalizationAway
        RingHom.Flat.holdsForLocalizationAway).left)]
    intro x
    refine ⟨⟨V (q.left x), hV _⟩, ⟨q.left ⁻¹ᵁ V (q.left x), hA _⟩, hbV _, le_rfl, ?_⟩
    rw [← Scheme.Hom.app_eq_appLE]
    exact (hB _).1
  · obtain ⟨s, hs⟩ := hsec b
    obtain ⟨x, hx⟩ := (GlobalTheory.Retract.surjective_retraction hs).surj ⟨b, hbV b⟩
    refine ⟨(q.left ⁻¹ᵁ V b).ι x, ?_⟩
    have e2 : (V b).ι ((q.left ∣_ V b) x) = q.left ((q.left ⁻¹ᵁ V b).ι x) :=
      congrArg (fun f => f.base x) (morphismRestrict_ι q.left (V b))
    rw [← e2, hx]
    rfl
  · have h1 : HasRingHomProperty @AlgebraicGeometry.Smooth RingHom.Smooth := inferInstance
    have h2 : IsZariskiLocalAtSource @AlgebraicGeometry.Smooth :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @AlgebraicGeometry.Smooth)
    refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @AlgebraicGeometry.Smooth) (f := B.hom) V hcov fun b => ?_
    obtain ⟨s, hs⟩ := hsec b
    have hr : (q.left ∣_ V b) ≫ ((V b).ι ≫ B.hom) = (q.left ⁻¹ᵁ V b).ι ≫ G.hom := by
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w q]
    exact GlobalTheory.Retract.smooth hs hr
  · obtain ⟨W, hWg⟩ : ∃ W : Z.left → Z.left.Opens,
        ∀ z, W z = g.left ⁻¹ᵁ (q.left ⁻¹ᵁ V (q.left (g.left z))) := ⟨_, fun _ => rfl⟩
    have hW : ∀ z, z ∈ W z := fun z => by rw [hWg z]; exact hbV _
    have hWI : ∀ z, ⊤ ≤ (incl Z (W z) ≫ g).left ⁻¹ᵁ (q.left ⁻¹ᵁ V (q.left (g.left z))) := fun z => by
      rw [hWg z]
      exact incl_le g _
    have hWc : TopologicalSpace.IsOpenCover W := by
      rw [TopologicalSpace.IsOpenCover, eq_top_iff]
      intro z _
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨z, hW z⟩
    have hloc : ∀ z, ∃ t : Over.mk ((W z).ι ≫ Z.hom) ⟶ splitTorus S X,
        incl Z (W z) ≫ g' = (t ≫ i) * (incl Z (W z) ≫ g) := by
      intro z
      refine exists_point (hV (q.left (g.left z))) (h₀ (q.left (g.left z))) (hU (q.left (g.left z)))
        (u (q.left (g.left z))) (hu (q.left (g.left z))) (hWI z) ?_
      rw [Category.assoc, Category.assoc, h]
    choose t ht using hloc
    let 𝒰 := Z.left.openCoverOfIsOpenCover W hWc
    have hcompat : ∀ x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ (t x).left =
        pullback.snd (𝒰.f x) (𝒰.f y) ≫ (t y).left := by
      intro x y
      let PO : Over S := Over.mk (pullback.fst (𝒰.f x) (𝒰.f y) ≫ (W x).ι ≫ Z.hom)
      let a : PO ⟶ Over.mk ((W x).ι ≫ Z.hom) := Over.homMk (pullback.fst (𝒰.f x) (𝒰.f y)) rfl
      let a' : PO ⟶ Over.mk ((W y).ι ≫ Z.hom) := Over.homMk (pullback.snd (𝒰.f x) (𝒰.f y))
        (pullback.condition_assoc (f := 𝒰.f x) (g := 𝒰.f y) Z.hom).symm
      have hc : a ≫ incl Z (W x) = a' ≫ incl Z (W y) := by
        apply Over.OverMorphism.ext
        exact pullback.condition (f := 𝒰.f x) (g := 𝒰.f y)
      have hgl : ⊤ ≤ (a ≫ incl Z (W x) ≫ g).left ⁻¹ᵁ (q.left ⁻¹ᵁ V (q.left (g.left x))) := by
        rw [Over.comp_left, Scheme.Hom.comp_preimage, top_le_iff.1 (hWI x)]
        exact fun p _ => trivial
      have hti : (a ≫ t x) ≫ i = (a' ≫ t y) ≫ i := by
        have e1 := congrArg (a ≫ ·) (ht x)
        have e2 := congrArg (a' ≫ ·) (ht y)
        simp only [comp_mul, ← Category.assoc] at e1 e2
        rw [← hc] at e2
        exact _root_.mul_right_cancel (e1.symm.trans e2)
      have key : a ≫ t x = a' ≫ t y :=
        eq_of_units (hU (q.left (g.left x))) (fun χ => u (q.left (g.left x)) (Multiplicative.ofAdd χ))
          (hu (q.left (g.left x))) hgl hti
      exact congrArg (fun f => f.left) key
    let T := 𝒰.glueMorphisms (fun x => (t x).left) hcompat
    have hT : ∀ x, 𝒰.f x ≫ T = (t x).left := fun x => 𝒰.ι_glueMorphisms _ hcompat x
    let tt : Z ⟶ splitTorus S X := Over.homMk T (by
      refine Scheme.Cover.hom_ext 𝒰 _ _ fun x => ?_
      rw [← Category.assoc, hT]
      exact Over.w (t x))
    refine ⟨tt, over_ext fun z => ⟨W z, hW z, ?_⟩⟩
    have e3 : incl Z (W z) ≫ tt = t z := by
      apply Over.OverMorphism.ext
      exact hT z
    rw [ht z, comp_mul, ← Category.assoc, e3]
  · rintro ⟨t, rfl⟩
    apply over_ext
    intro z
    refine ⟨g.left ⁻¹ᵁ (q.left ⁻¹ᵁ V (q.left (g.left z))), hbV _, ?_⟩
    have := comp_eq (hV (q.left (g.left z))) (h₀ (q.left (g.left z))) (hU (q.left (g.left z)))
      (incl Z (g.left ⁻¹ᵁ (q.left ⁻¹ᵁ V (q.left (g.left z)))) ≫ t)
      (incl_le g (q.left ⁻¹ᵁ V (q.left (g.left z))))
    simpa only [← Category.assoc, comp_mul] using this

end GlobalTheory.LocTriv
end
