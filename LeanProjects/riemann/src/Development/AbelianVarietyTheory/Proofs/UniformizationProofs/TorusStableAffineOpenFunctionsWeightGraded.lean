import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory
namespace TorusGrading

theorem toSpecΓ_appLE_fromSpec {Y Z : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) (g : Z ⟶ Y)
    (h : ⊤ ≤ g ⁻¹ᵁ V) : Z.toSpecΓ ≫ Spec.map (g.appLE V ⊤ h) ≫ hV.fromSpec = g := by
  have : IsIso (⊤ : Z.Opens).ι := inferInstanceAs (IsIso Z.topIso.hom)
  rw [← cancel_epi (⊤ : Z.Opens).ι, ← Category.assoc, ← Scheme.Opens.toSpecΓ_top,
    Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, IsAffineOpen.toSpecΓ_fromSpec, Scheme.Hom.resLE_comp_ι]

theorem appLE_comp_top {Y Z W : Scheme.{0}} {V : Y.Opens} (s : W ⟶ Z) (g : Z ⟶ Y) (h : ⊤ ≤ g ⁻¹ᵁ V)
    {g' : W ⟶ Y} (e : s ≫ g = g') (h' : ⊤ ≤ g' ⁻¹ᵁ V) (u : Γ(Y, V)) :
    (g'.appLE V ⊤ h').hom u = s.appTop.hom ((g.appLE V ⊤ h).hom u) := by
  subst e
  have e : s.appTop = s.appLE ⊤ ⊤ le_top := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [e]
  exact (congrArg (fun q => q.hom u) (Scheme.Hom.appLE_comp_appLE s g V ⊤ ⊤ h le_top)).symm

theorem top_le_comp {Y Z W : Scheme.{0}} {V : Y.Opens} (s : W ⟶ Z) {g : Z ⟶ Y} (h : ⊤ ≤ g ⁻¹ᵁ V) :
    ⊤ ≤ (s ≫ g) ⁻¹ᵁ V := fun _ _ => h trivial

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem chV_comp {W Z : Over S} (s : W ⟶ Z) (t : Z ⟶ splitTorus S X) (χ : X) :
    (chV (s ≫ t) χ).val = s.left.appTop.hom (chV t χ).val := by
  rw [chV_val, chV_val, Rosenlicht.over_appTop_comp]

theorem chV_one {Z : Over S} (χ : X) : chV (1 : Z ⟶ splitTorus S X) χ = 1 := by
  rw [chV, map_one]; rfl

theorem eq_zero_of_sum_chV (Z : Over S) (s : Finset X) (h : X → Γ(Z.left, ⊤))
    (hs : ∑ χ ∈ s, (chV (fst (splitTorus S X) Z) χ).val * (snd (splitTorus S X) Z).left.appTop.hom (h χ) = 0) :
    ∀ χ ∈ s, h χ = 0 := by
  refine TorusInj.eq_zero_of_sum X Z s h (Eq.trans (Finset.sum_congr rfl fun χ _ => ?_) hs)
  refine congrArg₂ (· * ·) ?_ rfl
  rw [chV_val]
  exact congrArg (fun q => q.hom (TorusInj.chiP X Z χ))
    ((splitTorus S X ⊗ Z).left.presheaf.map_id (Opposite.op ⊤))

variable {G : Over S} [GrpObj G] {i : splitTorus S X ⟶ G} {V : G.left.Opens}

theorem top_le_act
    (hst : (snd (splitTorus S X) G).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ V)
    {Z : Over S} (t : Z ⟶ splitTorus S X) {g : Z ⟶ G} (h : ⊤ ≤ g.left ⁻¹ᵁ V) : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ V := by
  have e : (t ≫ i) * g = lift t g ≫ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G) := by
    rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
  rw [e, Over.comp_left, Scheme.Hom.comp_preimage]
  refine le_trans ?_ ((lift t g).left.preimage_mono hst)
  rw [← Scheme.Hom.comp_preimage, ← Over.comp_left, lift_snd]
  exact h

theorem exists_expansion (hV : IsAffineOpen V)
    (hst : (snd (splitTorus S X) G).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ V)
    (u : Γ(G.left, V)) : ∃ a : X →₀ Γ(G.left, V), ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G)
      (h₁ : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ V) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V),
      (((t ≫ i) * g).left.appLE V ⊤ h₁).hom u =
        ∑ χ ∈ a.support, (chV t χ).val * (g.left.appLE V ⊤ h₂).hom (a χ) := by
  let B : CommRingCat.{0} := TorusInj.GA (X := X) (V := V)
  let P : Over S := Over.mk (TorusInj.ptY (X := X) hV ≫ G.hom)
  let g₀ : P ⟶ G := Over.homMk (TorusInj.ptY (X := X) hV) rfl
  let ε : Γ(P.left, ⊤) ≅ B := Scheme.ΓSpecIso B
  let t₀ : P ⟶ splitTorus S X := (splitTorusPointsEquiv S X P).symm
    (ε.inv.hom.toMonoidHom.comp (AddMonoidAlgebra.of Γ(G.left, V) X)).toHomUnits
  have ht₀ : ∀ χ, (chV t₀ χ).val = ε.inv.hom (AddMonoidAlgebra.single χ 1) := fun χ => by
    rw [chV, MulEquiv.apply_symm_apply]; rfl
  have hg₀ : ⊤ ≤ g₀.left ⁻¹ᵁ V := (TorusInj.ptY_preimage hV).ge
  let f : AddMonoidAlgebra Γ(G.left, V) X :=
    ε.hom.hom ((((t₀ ≫ i) * g₀).left.appLE V ⊤ (top_le_act hst t₀ hg₀)).hom u)
  refine ⟨f.coeff, fun Z t g h₁ h₂ => ?_⟩
  letI : Algebra Γ(G.left, V) Γ(Z.left, ⊤) := (g.left.appLE V ⊤ h₂).hom.toAlgebra
  let φ₀ : AddMonoidAlgebra Γ(G.left, V) X →ₐ[Γ(G.left, V)] Γ(Z.left, ⊤) :=
    AddMonoidAlgebra.lift Γ(G.left, V) Γ(Z.left, ⊤) X ((Units.coeHom _).comp (splitTorusPointsEquiv S X Z t))
  let φ : B ⟶ Γ(Z.left, ⊤) := CommRingCat.ofHom φ₀.toRingHom
  have hφ : ∀ χ c, φ.hom (AddMonoidAlgebra.single χ c) = (chV t χ).val * (g.left.appLE V ⊤ h₂).hom c := fun χ c => by
    change φ₀ (AddMonoidAlgebra.single χ c) = _
    rw [AddMonoidAlgebra.lift_single, Algebra.smul_def, mul_comm]; rfl
  have hσ : (Z.left.toSpecΓ ≫ Spec.map φ) ≫ TorusInj.ptY (X := X) hV = g.left := by
    rw [TorusInj.ptY, Category.assoc, ← Spec.map_comp_assoc]
    refine Eq.trans ?_ (toSpecΓ_appLE_fromSpec hV g.left h₂)
    congr 3
    exact CommRingCat.hom_ext (RingHom.ext fun c => φ₀.commutes c)
  let σ : Z ⟶ P := Over.homMk (Z.left.toSpecΓ ≫ Spec.map φ)
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ G.hom) hσ).trans (Over.w g)))
  have hσa : ∀ x : Γ(P.left, ⊤), σ.left.appTop.hom x = φ.hom (ε.hom.hom x) := fun x => by
    have : (Z.left.toSpecΓ ≫ Spec.map φ).appTop = ε.hom ≫ φ := by
      rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality]
    exact congrArg (fun q => q.hom x) this
  have hε : ∀ x : B, ε.hom.hom (ε.inv.hom x) = x := fun x => congrArg (fun q => q.hom x) ε.inv_hom_id
  have eg : σ ≫ g₀ = g := Over.OverMorphism.ext hσ
  have et : σ ≫ t₀ = t := (splitTorusPointsEquiv S X Z).injective (MonoidHom.ext fun χ => Units.ext (by
    change (chV (σ ≫ t₀) χ.toAdd).val = (chV t χ.toAdd).val
    rw [chV_comp, ht₀, hσa, hε, hφ, map_one, _root_.mul_one]))
  have ea : σ ≫ ((t₀ ≫ i) * g₀) = (t ≫ i) * g := by
    rw [MonObj.comp_mul, ← Category.assoc, et, eg]
  rw [appLE_comp_top σ.left _ (top_le_act hst t₀ hg₀) (congrArg (fun q => q.left) ea) h₁ u, hσa]
  change φ.hom f = _
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single f]
  rw [Finsupp.sum, map_sum]
  exact Finset.sum_congr rfl fun χ _ => hφ χ _

theorem exists_point (hV : IsAffineOpen V) : ∃ (Z : Over S) (g : Z ⟶ G) (h : ⊤ ≤ g.left ⁻¹ᵁ V),
    Function.Injective (g.left.appLE V ⊤ h).hom := by
  refine ⟨Over.mk (hV.fromSpec ≫ G.hom), Over.homMk hV.fromSpec rfl, hV.fromSpec_preimage_self.ge, ?_⟩
  have h1 : hV.fromSpec.appLE V ⊤ hV.fromSpec_preimage_self.ge = (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg _ (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
  change Function.Injective (hV.fromSpec.appLE V ⊤ hV.fromSpec_preimage_self.ge).hom
  rw [h1]
  exact (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv.injective

omit [GrpObj G] in
theorem val_comp {W Z : Over S} (s : W ⟶ Z) {g : Z ⟶ G} (h : ⊤ ≤ g.left ⁻¹ᵁ V) (h' : ⊤ ≤ (s ≫ g).left ⁻¹ᵁ V)
    (u : Γ(G.left, V)) : ((s ≫ g).left.appLE V ⊤ h').hom u = s.left.appTop.hom ((g.left.appLE V ⊤ h).hom u) :=
  appLE_comp_top s.left g.left h (Over.comp_left _ _ _ s g).symm h' u

omit [GrpObj G] in
theorem val_congr {Z : Over S} {g g' : Z ⟶ G} (e : g = g') (h : ⊤ ≤ g.left ⁻¹ᵁ V) (h' : ⊤ ≤ g'.left ⁻¹ᵁ V)
    (u : Γ(G.left, V)) : (g.left.appLE V ⊤ h).hom u = (g'.left.appLE V ⊤ h').hom u := by
  subst e; rfl

omit [GrpObj G] in
theorem top_le_comp_left {W Z : Over S} (s : W ⟶ Z) {g : Z ⟶ G} (h : ⊤ ≤ g.left ⁻¹ᵁ V) :
    ⊤ ≤ (s ≫ g).left ⁻¹ᵁ V := by
  rw [Over.comp_left]; exact top_le_comp s.left h

theorem isWt_of_expansion [IsMonHom i]
    (hst : (snd (splitTorus S X) G).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ V)
    {u : Γ(G.left, V)} {s : Finset X} {a : X → Γ(G.left, V)}
    (ha : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G)
      (h₁ : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ V) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V),
      (((t ≫ i) * g).left.appLE V ⊤ h₁).hom u =
        ∑ χ ∈ s, (chV t χ).val * (g.left.appLE V ⊤ h₂).hom (a χ)) {χ : X} (hχ : χ ∈ s) : IsWt i V (a χ) χ := by
  intro Z t g h₁ h₂
  rw [← chV_val, ← sub_eq_zero]
  refine eq_zero_of_sum_chV Z s (fun χ => (((t ≫ i) * g).left.appLE V ⊤ h₁).hom (a χ) -
    (chV t χ).val * (g.left.appLE V ⊤ h₂).hom (a χ)) ?_ χ hχ
  generalize fst (splitTorus S X) Z = p
  generalize snd (splitTorus S X) Z = q
  have k₁ := top_le_comp_left q h₁
  have k₂ := top_le_comp_left q h₂
  have e : (p ≫ i) * (q ≫ ((t ≫ i) * g)) = ((p * (q ≫ t)) ≫ i) * (q ≫ g) := by
    rw [MonObj.mul_comp, MonObj.comp_mul, _root_.mul_assoc, Category.assoc]
  have a₁ := ha _ p _ (top_le_act hst p k₁) k₁
  have a₂ := ha _ (p * (q ≫ t)) _ (top_le_act hst _ k₂) k₂
  have a₃ := (a₁.symm.trans (val_congr e _ _ u)).trans a₂
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at a₃
  refine Eq.trans (Finset.sum_congr rfl fun ψ _ => ?_) a₃
  rw [val_comp q h₁ k₁, val_comp q h₂ k₂, chV_mul, Units.val_mul, chV_comp, map_sub, map_mul, mul_sub,
    _root_.mul_assoc]

theorem eq_zero_of_sum_isWt (hV : IsAffineOpen V)
    (hst : (snd (splitTorus S X) G).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ V)
    {s : Finset X} {a : X → Γ(G.left, V)} (ha : ∀ χ, IsWt i V (a χ) χ) (hs : ∑ χ ∈ s, a χ = 0) {χ : X}
    (hχ : χ ∈ s) : a χ = 0 := by
  obtain ⟨Z₀, g₀, h₀, inj⟩ := exists_point hV
  refine inj (Eq.trans ?_ (map_zero _).symm)
  refine eq_zero_of_sum_chV Z₀ s (fun χ => (g₀.left.appLE V ⊤ h₀).hom (a χ)) ?_ χ hχ
  generalize fst (splitTorus S X) Z₀ = p
  generalize snd (splitTorus S X) Z₀ = q
  have k := top_le_comp_left q h₀
  have := congrArg (((p ≫ i) * (q ≫ g₀)).left.appLE V ⊤ (top_le_act hst p k)).hom hs
  rw [map_sum, map_zero] at this
  refine Eq.trans (Finset.sum_congr rfl fun χ _ => ?_) this
  rw [ha χ _ p (q ≫ g₀) _ k, ← chV_val, val_comp q h₀ k]

theorem eq_sum_of_expansion [IsMonHom i] (hV : IsAffineOpen V)
    {u : Γ(G.left, V)} {s : Finset X} {a : X → Γ(G.left, V)}
    (ha : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G)
      (h₁ : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ V) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V),
      (((t ≫ i) * g).left.appLE V ⊤ h₁).hom u =
        ∑ χ ∈ s, (chV t χ).val * (g.left.appLE V ⊤ h₂).hom (a χ)) : u = ∑ χ ∈ s, a χ := by
  obtain ⟨Z₀, g₀, h₀, inj⟩ := exists_point hV
  refine inj ?_
  have e : ((1 : Z₀ ⟶ splitTorus S X) ≫ i) * g₀ = g₀ := by rw [MonObj.one_comp, _root_.one_mul]
  have h₁ : ⊤ ≤ (((1 : Z₀ ⟶ splitTorus S X) ≫ i) * g₀).left ⁻¹ᵁ V := by rw [e]; exact h₀
  rw [map_sum, ← val_congr e h₁ h₀ u, ha Z₀ 1 g₀ h₁ h₀]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [chV_one, Units.val_one, _root_.one_mul]

end TorusGrading

open TorusGrading in

theorem functions_graded_by_weights :
    (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] (i : splitTorus S X ⟶ G), IsMonHom i → ∀ V : G.left.Opens, IsAffineOpen V → (snd (splitTorus S X) G).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ V → (∀ u : Γ(G.left, V), ∃ a : X →₀ Γ(G.left, V), (∀ χ, IsWt i V (a χ) χ) ∧ u = a.sum fun _ x => x) ∧ ∀ a : X →₀ Γ(G.left, V), (∀ χ, IsWt i V (a χ) χ) → (a.sum fun _ x => x) = 0 → a = 0) := by
  intro S G _ X _ i hi V hV hst
  refine ⟨fun u => ?_, fun a ha hs => ?_⟩
  · obtain ⟨a, ha⟩ := exists_expansion hV hst u
    refine ⟨a, fun χ => ?_, eq_sum_of_expansion hV ha⟩
    by_cases hχ : χ ∈ a.support
    · exact isWt_of_expansion hst ha hχ
    · rw [Finsupp.notMem_support_iff.1 hχ]
      exact isWt_zero χ
  · refine Finsupp.ext fun χ => ?_
    by_contra h
    exact h (eq_zero_of_sum_isWt hV hst ha hs (Finsupp.mem_support_iff.2 h))

end GlobalTheory
end
