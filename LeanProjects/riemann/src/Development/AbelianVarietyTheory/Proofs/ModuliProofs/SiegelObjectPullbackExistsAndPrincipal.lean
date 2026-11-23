import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SiegPairPBNonempty
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolPull

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SiegelPull

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
  {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}

theorem push_injective (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Injective (pushHom h T) :=
  fun x y e => Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w]))

theorem push_surjective (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Surjective (pushHom h T) :=
  fun x₀ => ⟨Over.homMk (h.1.lift x₀.left T.hom (Over.w x₀)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

omit [GrpObj A] [GrpObj A'] in

theorem lift_sq (sq : IsSquare φ φ₂) {T : Over S} {T' : Over S'} (χ : T.left ⟶ T'.left) (x' y' : T' ⟶ A')
    {Z : Over S} (ψ : T.left ⟶ Z.left) (x y : Z ⟶ A) (hx : χ ≫ x'.left ≫ φ = ψ ≫ x.left)
    (hy : χ ≫ y'.left ≫ φ = ψ ≫ y.left) : χ ≫ (lift x' y').left ≫ φ₂ = ψ ≫ (lift x y).left := by
  refine pullback.hom_ext (f := A.hom) (g := A.hom) ?_ ?_
  · show (χ ≫ (lift x' y').left ≫ φ₂) ≫ (fst A A).left = (ψ ≫ (lift x y).left) ≫ (fst A A).left
    rw [Category.assoc, Category.assoc, sq.1, ← Category.assoc (lift x' y').left, ← Over.comp_left, lift_fst, hx,
      Category.assoc, ← Over.comp_left, lift_fst]
  · show (χ ≫ (lift x' y').left ≫ φ₂) ≫ (snd A A).left = (ψ ≫ (lift x y).left) ≫ (snd A A).left
    rw [Category.assoc, Category.assoc, sq.2, ← Category.assoc (lift x' y').left, ← Over.comp_left, lift_snd, hy,
      Category.assoc, ← Over.comp_left, lift_snd]

omit [GrpObj A] [GrpObj A'] in

theorem diag_iso (sq : IsSquare φ φ₂) {P : LB (A ⊗ A).left} {P' : LB (A' ⊗ A').left}
    (H : LBIso P' (P.pull φ₂)) :
    LBIso (P'.pull (lift (𝟙 A') (𝟙 A')).left) ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull φ) := by
  obtain ⟨u, hu⟩ := H
  have e : (lift (𝟙 A') (𝟙 A')).left ≫ φ₂ = φ ≫ (lift (𝟙 A) (𝟙 A)).left :=
    (Category.id_comp _).symm.trans (lift_sq sq (T := Over.mk (φ ≫ A.hom)) (T' := A') (𝟙 A'.left) (𝟙 A') (𝟙 A')
      (Z := A) φ (𝟙 A) (𝟙 A) (by simp) (by simp))
  exact LBIso.chartPull (chartPullId _) (chartPullOut P _ _ φ _ fun _ => e)
    (iso_linComb ((isGen_iff u).1 hu) (fun _ : PUnit => (lift (𝟙 A') (𝟙 A')).left) (fun _ => 1))

theorem nondeg_pull (h : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂) {P : LB (A ⊗ A).left}
    {P' : LB (A' ⊗ A').left} (hP : P.IsLB) (hP' : P'.IsLB) (H : LBIso P' (P.pull φ₂))
    (hn : ∀ (T : Over S) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1)
    (T : Over S') (x : T ⟶ A') (hx : ∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) :
    x = 1 := by
  obtain ⟨u, hu⟩ := H
  obtain ⟨t, ht⟩ := hx
  refine push_injective h T ((hn _ (pushHom h T x) ?_).trans (map_one _).symm)
  let T₀ : Over S := Over.mk (T.hom ≫ f)
  have w₁ : (fst A T₀).left ≫ A.hom = ((snd A T₀).left ≫ T.hom) ≫ f :=
    pullback.condition.trans (Category.assoc _ _ _).symm
  let a : (A ⊗ T₀).left ⟶ A'.left := h.1.lift _ _ w₁
  have a₁ : a ≫ φ = (fst A T₀).left := h.1.lift_fst _ _ _
  have a₂ : a ≫ A'.hom = (snd A T₀).left ≫ T.hom := h.1.lift_snd _ _ _
  let χ : (A ⊗ T₀).left ⟶ (A' ⊗ T).left := pullback.lift a (snd A T₀).left a₂
  have c₁ : χ ≫ (fst A' T).left = a := pullback.lift_fst _ _ _
  have c₂ : χ ≫ (snd A' T).left = (snd A T₀).left := pullback.lift_snd _ _ _
  obtain ⟨t₂, ht₂, -⟩ := exists_up ((isGen_iff u).1 hu) hP hP' t ht
  refine gen_chartPull (chartPullSame P _ _ _ χ fun _ => ?_) t₂ ht₂
  refine ((Category.id_comp _).symm.trans (lift_sq sq (T := A ⊗ T₀) χ _ _ (𝟙 _) _ _ ?_ ?_).symm)
  · rw [Over.comp_left, Category.assoc, ← Category.assoc χ, c₂, Category.id_comp]
    rfl
  · rw [← Category.assoc, c₁, a₁, Category.id_comp]

def secPull (h : IsGrpPullback A' A f φ) (x : 𝟙_ (Over S) ⟶ A) : 𝟙_ (Over S') ⟶ A' :=
  Over.homMk (h.1.lift (f ≫ x.left) (𝟙 S') (by
    rw [Category.assoc, Over.w x]; exact (Category.comp_id _).trans (Category.id_comp _).symm)) (h.1.lift_snd _ _ _)

theorem secPull_left (h : IsGrpPullback A' A f φ) (x : 𝟙_ (Over S) ⟶ A) : (secPull h x).left ≫ φ = f ≫ x.left :=
  h.1.lift_fst _ _ _

theorem push_secPull (h : IsGrpPullback A' A f φ) (x : 𝟙_ (Over S) ⟶ A) (T : Over S') :
    pushHom h T (toUnit T ≫ secPull h x) = toUnit (Over.mk (T.hom ≫ f)) ≫ x := by
  apply Over.OverMorphism.ext
  show ((toUnit T).left ≫ (secPull h x).left) ≫ φ = (toUnit (Over.mk (T.hom ≫ f))).left ≫ x.left
  rw [Category.assoc, secPull_left, Over.toUnit_left, Over.toUnit_left, ← Category.assoc]
  rfl

theorem push_secPull' (h : IsGrpPullback A' A f φ) (x : 𝟙_ (Over S) ⟶ A) :
    pushHom h _ (secPull h x) = toUnit _ ≫ x := by
  have e := push_secPull h x (𝟙_ (Over S'))
  rwa [toUnit_unit, Category.id_comp] at e

end GlobalTheory.SiegelPull

namespace GlobalTheory

open SiegelPull

theorem siegPre_pullback : ∀ (h M : ℕ) (o : Type) [CommRing o] (ζ : o) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (c : SiegPre h M ζ s), f ≫ s = s' → (∃ c' : SiegPre h M ζ s', SiegPB c' c f) ∧ ∀ c' : SiegPre h M ζ s', SiegPB c' c f → c.Principal → c'.Principal := by
  intro h M o _ ζ S S' s s' f c hs
  refine ⟨?_, ?_⟩
  · obtain ⟨p⟩ := siegPairPB_nonempty c f
    refine ⟨{
      A := p.A
      ab := p.ab
      P := p.P
      isLB := p.isLB
      rig₁ := p.rig₁
      rig₂ := p.rig₂
      symm := p.symm
      lev := fun a => secPull p.pb (c.lev a)
      lev_add := fun a b => push_injective p.pb _ (by
        rw [map_mul, push_secPull', push_secPull', push_secPull', c.lev_add, MonObj.comp_mul])
      lev_tors := fun a => push_injective p.pb _ (by
        rw [map_pow, map_one, push_secPull', ← MonObj.comp_pow, c.lev_tors, MonObj.comp_one])
      geom := fun k _ _ x β z hx hz => ?_ }, p.φ, p.φ₂, p.pb, p.sq, p.iso, fun a => secPull_left p.pb _⟩
    obtain ⟨g₁, g₂, g₃⟩ := c.geom k (x ≫ f) β z (by rw [Category.assoc, hs, hx]) hz
    refine ⟨fun a => Iff.trans ?_ (g₁ a), fun g hg => ?_, fun a b => ?_⟩
    · rw [← (push_injective p.pb (Over.mk x)).eq_iff, push_secPull, map_one]
      rfl
    · obtain ⟨a, ha⟩ := g₂ (pushHom p.pb (Over.mk x) g) (by
        have := congrArg (pushHom p.pb (Over.mk x)) hg
        rw [map_pow, map_one] at this
        exact this)
      exact ⟨a, push_injective p.pb _ ((push_secPull p.pb _ _).trans ha)⟩
    · exact (weilIs_grpPullback_of_comm S S' c.A p.A f p.φ _ _ (pull_isLB c.isLB _) (pull_isLB p.isLB _) p.pb
        (diag_iso p.sq p.iso) (Over.mk x) M _ _ _ _ _
        (congrArg (fun q => q.left) (push_secPull p.pb (c.lev a) (Over.mk x)).symm)
        (congrArg (fun q => q.left) (push_secPull p.pb (c.lev b) (Over.mk x)).symm)).2 (g₃ a b)
  · rintro c' ⟨φ, φ₂, pb, sq, iso, -⟩ ⟨h₁, h₂⟩
    exact ⟨(pol_pull S S' c.A c'.A f φ _ _ (pull_isLB c.isLB _) (pull_isLB c'.isLB _) c.ab pb
      (diag_iso sq iso)).2.1 h₁, nondeg_pull pb sq c.isLB c'.isLB iso h₂⟩

end GlobalTheory
