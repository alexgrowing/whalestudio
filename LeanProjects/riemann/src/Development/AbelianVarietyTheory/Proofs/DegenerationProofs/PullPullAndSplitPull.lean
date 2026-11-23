import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section
namespace GlobalTheory.ZJ.SplitPull

theorem free_of_isField {R M : Type} [CommRing R] (hR : IsField R) [AddCommGroup M] [Module R M] :
    Module.Free R M := by
  letI := hR.toField
  exact Module.Free.of_divisionRing R M

theorem exists_basis_pushout {R R' : CommRingCat.{0}} (hR : IsField R) (b : R ⟶ R') :
    ∃ (J : Type) (e : J → R'), ∀ (A A' : CommRingCat.{0}) (a : R ⟶ A) (p : A ⟶ A') (q : R' ⟶ A'),
      IsPushout a b p q →
      (∀ u : A', ∃ (s : Finset J) (x : J → A), u = ∑ l ∈ s, p.hom (x l) * q.hom (e l)) ∧
      ∀ (s : Finset J) (x : J → A), ∑ l ∈ s, p.hom (x l) * q.hom (e l) = 0 → ∀ l ∈ s, x l = 0 := by
  letI := b.hom.toAlgebra
  haveI : Module.Free R R' := free_of_isField hR
  let e := Module.Free.chooseBasis R R'
  refine ⟨_, e, fun A A' a p q h => ?_⟩
  letI := a.hom.toAlgebra
  letI := p.hom.toAlgebra
  letI := q.hom.toAlgebra
  letI := (p.hom.comp a.hom).toAlgebra
  haveI : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower R R' A' := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom h.w)
  have hp : Algebra.IsPushout R A R' A' := CommRingCat.isPushout_iff_isPushout.mp h
  let B := hp.out.basis e
  have hB : ∀ l, B l = q.hom (e l) := fun l => hp.out.basis_apply e l
  refine ⟨fun u => ⟨(B.repr u).support, B.repr u, ?_⟩, fun s x hx => ?_⟩
  · conv_lhs => rw [← B.linearCombination_repr u]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    exact Finset.sum_congr rfl fun l _ => by rw [hB, Algebra.smul_def]; rfl
  · refine linearIndependent_iff'.1 B.linearIndependent s x ?_
    rw [← hx]
    exact Finset.sum_congr rfl fun l _ => by rw [hB, Algebra.smul_def]; rfl

theorem exists_basis_sections {K K' : Type} [Field K] [Field K'] (f : Sp K' ⟶ Sp K) :
    ∃ (J : Type) (e : J → Γ(Sp K', ⊤)), ∀ (X Y : Scheme.{0}) (g : Y ⟶ X) (iX : X ⟶ Sp K) (iY : Y ⟶ Sp K'),
      IsPullback g iY iX f →
      (∀ U : X.Opens, IsAffineOpen U → ∀ u : Γ(Y, g ⁻¹ᵁ U), ∃ (s : Finset J) (x : J → Γ(X, U)),
        u = ∑ l ∈ s, (g.app U).hom (x l) * (iY.appLE ⊤ (g ⁻¹ᵁ U) le_top).hom (e l)) ∧
      ∀ (s : Finset J) (x : J → Γ(X, ⊤)), ∑ l ∈ s, g.appTop.hom (x l) * iY.appTop.hom (e l) = 0 →
        ∀ l ∈ s, x l = 0 := by
  have hR : IsField Γ(Sp K, ⊤) :=
    MulEquiv.isField (Field.toIsField K) (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv
  obtain ⟨J, e, he⟩ := exists_basis_pushout hR (f.appLE ⊤ ⊤ le_top)
  refine ⟨J, e, fun X Y g iX iY h => ?_⟩
  have po : ∀ U : X.Opens, IsAffineOpen U → _ := fun U hU => he _ _ _ _ _
    ((isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := U) (UY := g ⁻¹ᵁ U) le_top
      le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _)
        (isAffineOpen_top _) hU))
  refine ⟨fun U hU u => ?_, fun s x hx l hl => ?_⟩
  · have := (po U hU).1 u
    rwa [Scheme.Hom.appLE_eq_app] at this
  · refine X.IsSheaf.section_ext fun y _ => ?_
    obtain ⟨_, ⟨U, hU, rfl⟩, hy, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    refine ⟨U, le_top, hy, ?_⟩
    rw [map_zero]
    refine (po U hU).2 s (fun l => resG X le_top (x l)) ?_ l hl
    have := congrArg (resG Y (le_top : g ⁻¹ᵁ U ≤ ⊤)) hx
    rw [map_zero, map_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul]
    congr 1
    exact congrArg (fun q : Γ(X, ⊤) ⟶ Γ(Y, g ⁻¹ᵁ U) => q.hom (x l)) (g.map_appLE le_rfl (homOfLE le_top).op)

open GlobalTheory.UU

theorem appLE_app {A B C : Scheme.{0}} (r : A ⟶ B) (φ : B ⟶ C) (s : A ⟶ C) (hs : s = r ≫ φ) (V : C.Opens)
    (k : ⊤ ≤ r ⁻¹ᵁ φ ⁻¹ᵁ V) (k' : ⊤ ≤ s ⁻¹ᵁ V) (u : Γ(C, V)) :
    (r.appLE (φ ⁻¹ᵁ V) ⊤ k).hom ((φ.app V).hom u) = (s.appLE V ⊤ k').hom u := by
  subst hs
  rw [Scheme.Hom.comp_appLE]
  rfl

theorem appTop_appLE {A B C : Scheme.{0}} (r : A ⟶ B) (φ : B ⟶ C) (s : A ⟶ C) (hs : s = r ≫ φ) (V : C.Opens)
    (k : ⊤ ≤ φ ⁻¹ᵁ V) (k' : ⊤ ≤ s ⁻¹ᵁ V) (u : Γ(C, V)) :
    r.appTop.hom ((φ.appLE V ⊤ k).hom u) = (s.appLE V ⊤ k').hom u := by
  subst hs
  have := Scheme.Hom.appLE_comp_appLE r φ V ⊤ ⊤ k le_top
  rw [← this]
  erw [r.appLE_eq_app]
  rfl

theorem appLE_appLE_top {A B C : Scheme.{0}} (r : A ⟶ B) (φ : B ⟶ C) (s : A ⟶ C) (hs : r ≫ φ = s) (V : B.Opens)
    (k : ⊤ ≤ r ⁻¹ᵁ V) (u : Γ(C, ⊤)) :
    (r.appLE V ⊤ k).hom ((φ.appLE ⊤ V le_top).hom u) = s.appTop.hom u := by
  subst hs
  have := Scheme.Hom.appLE_comp_appLE r φ ⊤ V ⊤ le_top k
  erw [(r ≫ φ).appLE_eq_app] at this
  exact congrArg (fun q => q.hom u) this

section
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {X : Type} [AddCommGroup X] {G : Over S} {G' : Over S'} [GrpObj G]
  [GrpObj G'] {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) {i : splitTorus S X ⟶ G}
  {i' : splitTorus S' X ⟶ G'} (hi : TorusCompat f F i' i)
include hF hi

theorem stable_pull {V : G.left.Opens} (hV : Stable i V) : Stable i' (F ⁻¹ᵁ V) := by
  obtain ⟨τ, hτ, hχ, hc⟩ := hi
  intro Z t g h
  have ht : (pushPt hτ t ≫ i).left = (t ≫ i').left ≫ F := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, ← hc, ← Category.assoc]; rfl
  have := hV _ (pushPt hτ t) (pushPt hF.1.w g) h
  rwa [hF.2 Z (t ≫ i') g _ (pushPt hF.1.w g) ht rfl] at this

theorem hasWt_pull {V : G.left.Opens} {u : Γ(G.left, V)} {χ : X} (hu : HasWt i V u χ) :
    HasWt i' (F ⁻¹ᵁ V) ((F.app V).hom u) χ := by
  obtain ⟨τ, hτ, hχ, hc⟩ := hi
  intro Z t g h h'
  have ht : (pushPt hτ t ≫ i).left = (t ≫ i').left ≫ F := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, ← hc, ← Category.assoc]; rfl
  have e := hF.2 Z (t ≫ i') g _ (pushPt hF.1.w g) ht rfl
  rw [appLE_app _ F _ e V h' (by rw [e]; exact h'), appLE_app _ F (pushPt hF.1.w g).left rfl V h h, ← hχ]
  refine (hu _ (pushPt hτ t) (pushPt hF.1.w g) _ _).trans (congrArg (· * _) ?_)
  show (t.left ≫ τ).appTop.hom _ = _
  rw [Scheme.Hom.comp_appTop]
  rfl

theorem hasWt_coeff {J : Type} (e : J → Γ(S', ⊤))
    (he : ∀ (Y : Over S) (s : Finset J) (x : J → Γ(Y.left, ⊤)),
      ∑ l ∈ s, (pullback.fst Y.hom f).appTop.hom (x l) * (pullback.snd Y.hom f).appTop.hom (e l) = 0 →
        ∀ l ∈ s, x l = 0)
    {V : G.left.Opens} (s : Finset J) (x : J → Γ(G.left, V))
    (hu : HasWt i' (F ⁻¹ᵁ V) (∑ l ∈ s, (F.app V).hom (x l) * (G'.hom.appLE ⊤ (F ⁻¹ᵁ V) le_top).hom (e l)) 0) :
    ∀ l ∈ s, HasWt i V (x l) 0 := by
  intro l hl Y t g h h'
  rw [torusCompat_iff] at hi
  let Y' : Over S' := Over.mk (pullback.snd Y.hom f)
  let p : Y'.left ⟶ Y.left := pullback.fst Y.hom f
  have hp : p ≫ Y.hom = Y'.hom ≫ f := pullback.condition
  let p' : Over.mk (Y'.hom ≫ f) ⟶ Y := Over.homMk p hp
  have hT := SplitTorus.isPullback_bcMap f X
  have wt : (p ≫ t.left) ≫ (splitTorus S X).hom = Y'.hom ≫ f := by rw [Category.assoc, Over.w, hp]
  have wg : (p ≫ g.left) ≫ G.hom = Y'.hom ≫ f := by rw [Category.assoc, Over.w, hp]
  let t' : Y' ⟶ splitTorus S' X := Over.homMk (hT.lift _ _ wt) (hT.lift_snd _ _ wt)
  let g' : Y' ⟶ G' := Over.homMk (hF.1.lift _ _ wg) (hF.1.lift_snd _ _ wg)
  have ht' : t'.left ≫ SplitTorus.bcMap f X = p ≫ t.left := hT.lift_fst _ _ wt
  have hg' : p ≫ g.left = g'.left ≫ F := (hF.1.lift_fst _ _ wg).symm
  have hm : p ≫ ((t ≫ i) * g).left = ((t' ≫ i') * g').left ≫ F := by
    rw [← hF.2 Y' (t' ≫ i') g' (p' ≫ t ≫ i) (p' ≫ g) ?_ hg', ← MonObj.comp_mul]
    · rfl
    · change p ≫ t.left ≫ i.left = (t'.left ≫ i'.left) ≫ F
      rw [Category.assoc, ← hi, ← Category.assoc t'.left, ht', Category.assoc]
  have key : ∀ (r : Y ⟶ G) (r' : Y' ⟶ G') (_ : p ≫ r.left = r'.left ≫ F) (k : ⊤ ≤ r.left ⁻¹ᵁ V),
      ∃ k' : ⊤ ≤ r'.left ⁻¹ᵁ F ⁻¹ᵁ V, (r'.left.appLE _ ⊤ k').hom
        (∑ l ∈ s, (F.app V).hom (x l) * (G'.hom.appLE ⊤ (F ⁻¹ᵁ V) le_top).hom (e l)) =
        ∑ l ∈ s, p.appTop.hom ((r.left.appLE V ⊤ k).hom (x l)) * Y'.hom.appTop.hom (e l) := by
    intro r r' hr k
    have k₁ : ⊤ ≤ (p ≫ r.left) ⁻¹ᵁ V := p.preimage_mono k
    have k₂ : ⊤ ≤ (r'.left ≫ F) ⁻¹ᵁ V := hr ▸ k₁
    refine ⟨k₂, ?_⟩
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, appLE_app _ F _ hr V k₂ k₁, appTop_appLE p r.left _ rfl V k k₁]
    exact congrArg (_ * ·) (appLE_appLE_top _ _ _ (Over.w r') _ _ _)
  obtain ⟨k₁, e₁⟩ := key _ _ hm h'
  obtain ⟨k₂, e₂⟩ := key _ _ hg' h
  have h0 := hu Y' t' g' k₂ k₁
  rw [e₁, e₂, charUnit_zero_val, map_one, _root_.one_mul, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h0
  rw [charUnit_zero_val, map_one, _root_.one_mul, ← sub_eq_zero]
  refine he Y s (fun l => (((t ≫ i) * g).left.appLE V ⊤ h').hom (x l) - (g.left.appLE V ⊤ h).hom (x l)) ?_ l hl
  rw [← h0]
  exact Finset.sum_congr rfl fun l _ => by rw [map_sub, sub_mul]; rfl

end

theorem pull_pull_and_split_pull : (∀ (X Y Y' : Scheme.{0}) (C : Charts X) (φ : Y ⟶ X) (ψ : Y' ⟶ Y) [IsAffineHom φ] [IsAffineHom ψ], (C.pull φ).pull ψ = C.pull (ψ ≫ φ)) ∧ ∀ (K K' : Type) [Field K] [Field K'] (H : Over (Sp K)) [GrpObj H] (H' : Over (Sp K')) [GrpObj H'] (f : Sp K' ⟶ Sp K) (φ : H'.left ⟶ H.left) [IsAffineHom φ], IsGrpPullback H' H f φ → ∀ (C : Charts H.left) (d : ℕ) (c : Fin d → C.Cl), C.Split c → Charts.Split (C.pull φ) c := by
  refine ⟨fun X Y Y' C φ ψ _ _ => rfl, ?_⟩
  rintro K K' _ _ H _ H' _ f φ _ hφ C d c ⟨hc, i, hT⟩
  obtain ⟨i', hi, -⟩ := existsUnique_torusCompat hφ.1 i
  have := hT.hom
  refine ⟨MorphismProperty.of_isPullback (P := @GeometricallyConnected) hφ.1 hc, i', hi.isMonHom hφ,
    fun a => stable_pull hφ hi (hT.stable a), fun a j hj => hasWt_pull hφ hi (hT.inv a j hj),
    fun a j k hj => hasWt_pull hφ hi (hT.wt a j k hj), fun k x => ?_, fun a u hu => ?_⟩
  · obtain ⟨a, j, hj, hx⟩ := hT.bpf k (φ x)
    refine ⟨a, j, hj, ?_⟩
    change x ∈ H'.left.basicOpen ((φ.app (C.W a)).hom (C.r a j))
    rw [← Scheme.preimage_basicOpen]
    exact hx
  · obtain ⟨J, e, he⟩ := exists_basis_sections f
    obtain ⟨s, x, rfl⟩ := (he _ _ φ _ _ hφ.1).1 (C.W a) (C.aff a) u
    have hx := hasWt_coeff hφ hi e (fun Y => (he _ _ _ _ _ (IsPullback.of_hasPullback Y.hom f)).2) s x hu
    refine Subring.sum_mem _ fun l hl => Subring.mul_mem _ ?_ (Subring.subset_closure (Or.inl ⟨e l, rfl⟩))
    have h1 := hT.gen a (x l) (hx l hl)
    refine Subring.mem_comap.1 (Subring.closure_le.2 ?_ h1)
    rintro v (⟨w, rfl⟩ | ⟨j, hj, rfl⟩)
    · refine Subring.subset_closure (Or.inl ⟨f.appTop.hom w, ?_⟩)
      have e₁ := Scheme.Hom.appLE_comp_appLE φ H.hom ⊤ (C.W a) (φ ⁻¹ᵁ C.W a) le_top le_rfl
      have e₂ := Scheme.Hom.appLE_comp_appLE H'.hom f ⊤ ⊤ (φ ⁻¹ᵁ C.W a) le_top le_top
      simp only [hφ.1.w] at e₁
      rw [φ.appLE_eq_app] at e₁
      erw [f.appLE_eq_app] at e₂
      exact congrArg (fun q => q.hom w) (e₂.trans e₁.symm)
    · exact Subring.subset_closure (Or.inr ⟨j, hj, rfl⟩)

end GlobalTheory.ZJ.SplitPull
end
