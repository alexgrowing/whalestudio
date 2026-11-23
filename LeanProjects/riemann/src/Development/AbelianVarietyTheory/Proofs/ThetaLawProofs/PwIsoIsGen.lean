import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyVia

variable {X Y : Scheme.{0}} {L : LB X} {L' : LB Y} {φ : Y ⟶ X}

def Via (w : LB.Iso L' (L.pull φ)) (l : ℕ) (a' : ∀ i, Γ(Y, L'.U i)) (a : ∀ j, Γ(X, L.U j)) : Prop :=
  ∀ (j : (L.pull φ).ι) (i : L'.ι) (h : (L.pull φ).U j ⊓ L'.U i ≤ φ ⁻¹ᵁ L.U (j PUnit.unit)),
    (φ.appLE _ _ h).hom (a (j PUnit.unit)) =
      (show Γ(Y, (L.pull φ).U j ⊓ L'.U i) from (w.s (j, i)).val) ^ l * resG _ inf_le_right (a' i)

theorem chart_le (j : (L.pull φ).ι) : (L.pull φ).U j ≤ φ ⁻¹ᵁ L.U (j PUnit.unit) :=
  LB.wchart_le L (fun _ => φ) j PUnit.unit

theorem Via.unique (hL : L.IsLB) {w : LB.Iso L' (L.pull φ)} {l : ℕ} {a' b' : ∀ i, Γ(Y, L'.U i)}
    {a : ∀ j, Γ(X, L.U j)} (ha : Via w l a' a) (hb : Via w l b' a) : a' = b' := by
  funext i
  refine fn_ext fun y hy => ?_
  obtain ⟨j, hj⟩ := exists_chart (DVR.linComb_isLB L hL (fun _ : PUnit => φ) (fun _ => 1)) y
  have h : (L.pull φ).U j ⊓ L'.U i ≤ φ ⁻¹ᵁ L.U (j PUnit.unit) := inf_le_left.trans (chart_le j)
  have e := (ha j i h).symm.trans (hb j i h)
  have hu : IsUnit ((show Γ(Y, (L.pull φ).U j ⊓ L'.U i) from (w.s (j, i)).val) ^ l) :=
    (Units.isUnit (w.s (j, i))).pow l
  have e' := hu.mul_left_cancel e
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ (L.pull φ).U j ⊓ L'.U i := ⟨hj, hy⟩
  exact (gs_res (𝟙 Y) y inf_le_right hm _).symm.trans ((congrArg (gs (𝟙 Y) y _) e').trans
    (gs_res (𝟙 Y) y inf_le_right hm _))

def pwIso {A B : LB Y} (w : LB.Iso A B) (t : ℤ) : LB.Iso (pw A t) (pw B t) := ⟨fun p => w.s p ^ t⟩

theorem pwIso_isGen {A B : LB Y} {w : LB.Iso A B} (hw : w.IsGen) (t : ℤ) : (pwIso w t).IsGen := by
  intro p q
  have e := congrArg (· ^ t) (hw p q)
  simp only [mul_zpow, ← map_zpow] at e
  refine e.trans (congrArg₂ (· * ·) ?_ rfl)
  exact (mul_zpow _ _ t).trans (congrArg₂ (· * ·) (map_zpow _ _ t).symm
    ((inv_zpow _ t).trans (congrArg (·⁻¹) (map_zpow _ _ t).symm)))

theorem res_appLE {U : X.Opens} {V W : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U) (h' : W ≤ V) (a : Γ(X, U)) :
    resG Y h' ((φ.appLE U V h).hom a) = (φ.appLE U W (h'.trans h)).hom a := by
  have e := congrArg (fun q => q.hom a) (φ.appLE_map h (homOfLE h').op)
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using e

theorem appLE_res {U U' : X.Opens} {V : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U') (h' : U' ≤ U) (a : Γ(X, U)) :
    (φ.appLE U' V h).hom (resG X h' a) = (φ.appLE U V (h.trans fun _ hy => h' hy)).hom a := by
  have e := congrArg (fun q => q.hom a) (φ.map_appLE h (homOfLE h').op)
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using e

theorem pull_g (j j' : (L.pull φ).ι) (h : (L.pull φ).U j ⊓ (L.pull φ).U j' ≤ φ ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit))) :
    (L.pull φ).g j j' = Units.map (φ.appLE _ _ h).hom.toMonoidHom (L.g (j PUnit.unit) (j' PUnit.unit)) := by
  dsimp only [LB.pull, LB.LinComb]
  rw [Fintype.prod_unique]
  exact (zpow_one (Units.map (φ.appLE _ _ h).hom.toMonoidHom (L.g (j PUnit.unit) (j' PUnit.unit))))

def pullSec (φ : Y ⟶ X) {t : ℤ} (s : LB.Sec (pw L t)) : LB.Sec (pw (L.pull φ) t) where
  f j := (φ.appLE _ _ (chart_le j)).hom (s.f (j PUnit.unit))
  compat j j' := by
    have h : (L.pull φ).U j ⊓ (L.pull φ).U j' ≤ φ ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)) :=
      fun _ hy => ⟨chart_le j hy.1, chart_le j' hy.2⟩
    have e := (congrArg (φ.appLE _ _ h).hom (s.compat (j PUnit.unit) (j' PUnit.unit))).trans (map_mul _ _ _)
    refine (res_appLE _ _ _).trans ((appLE_res h _ _).symm.trans (e.trans (congrArg₂ (· * ·) ?_
      ((appLE_res h _ _).trans (res_appLE _ _ _).symm))))
    exact (congrArg Units.val ((congrArg (· ^ t) (pull_g j j' h)).trans (map_zpow _ _ t).symm)).symm

theorem exists_via (hL : L.IsLB) (hL' : L'.IsLB) {w : LB.Iso L' (L.pull φ)} (hw : w.IsGen) (l : ℕ)
    (s : LB.Sec (pw L (l : ℤ))) : ∃ s' : LB.Sec (pw L' (l : ℤ)), Via w l s'.f s.f := by
  have hu := pwIso_isGen hw (l : ℤ)
  have hA := isLB_pw hL' (l : ℤ)
  have hB := isLB_pw (DVR.linComb_isLB L hL (fun _ : PUnit => φ) (fun _ => 1)) (l : ℤ)
  refine ⟨DVR.secOfIso (pullSec φ s) hu hA hB, fun j i h => ?_⟩
  have hV : (L.pull φ).U j ⊓ L'.U i ≤ (pw L' (l : ℤ)).U i ⊓ (pw (L.pull φ) (l : ℤ)).U j := fun _ hy => ⟨hy.2, hy.1⟩
  have h₁ := congrArg (DVR.rs hV) (DVR.secOfIso_spec (pullSec φ s) hu hA hB i j)
  have h₂ := ((DVR.rs_rs _ _ _).symm.trans h₁).trans (DVR.isoCand_rs (pwIso w l) (pullSec φ s) i j hV)
  let u : Γ(Y, (L.pull φ).U j ⊓ L'.U i)ˣ := w.s (j, i)
  have h₃ : res (hV.trans (DVR.divLe i j)) ((pwIso w (l : ℤ)).s (j, i)) = u ^ l :=
    (Units.ext (rs_self le_rfl (u ^ (l : ℤ)).val)).trans (zpow_natCast u l)
  have h₄ : resG Y (inf_le_right : (L.pull φ).U j ⊓ L'.U i ≤ L'.U i) ((DVR.secOfIso (pullSec φ s) hu hA hB).f i) =
      ((u ^ l)⁻¹).val * (φ.appLE _ _ h).hom (s.f (j PUnit.unit)) :=
    h₂.trans (congrArg₂ (· * ·) (congrArg (fun v => (v⁻¹).val) h₃) (res_appLE _ _ _))
  exact ((congrArg₂ (· * ·) (Units.val_pow_eq_pow_val u l).symm h₄).trans (Units.mul_inv_cancel_left _ _)).symm

theorem appLE_cst {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (p : X ⟶ Sp R) (p' : Y ⟶ Sp R')
    (hφ : φ ≫ p = p' ≫ spMap f) {U : X.Opens} {V : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U) (r : R) :
    (φ.appLE U V h).hom (cst p U r) = cst p' V (f r) := by
  refine (appLE_res h le_top _).trans ?_
  have e₁ : p.appTop ≫ φ.appTop = (spMap f).appTop ≫ p'.appTop := by
    rw [← Scheme.Hom.comp_appTop, hφ, Scheme.Hom.comp_appTop]
  have e₂ := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)
  have e₃ : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop ≫ φ.appTop =
      CommRingCat.ofHom f ≫ (Scheme.ΓSpecIso (CommRingCat.of R')).inv ≫ p'.appTop := by
    rw [e₁, ← Category.assoc, ← e₂, Category.assoc]
  exact congrArg (fun q => rs Y (le_top : V ≤ ⊤) (q.hom r)) e₃

theorem Via.comb {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (p : X ⟶ Sp R) (p' : Y ⟶ Sp R')
    (hφ : φ ≫ p = p' ≫ spMap f) {w : LB.Iso L' (L.pull φ)} {l N : ℕ} {b' : Fin N → ∀ i, Γ(Y, L'.U i)}
    {b : Fin N → ∀ j, Γ(X, L.U j)} (hb : ∀ k, Via w l (b' k) (b k)) (c : Fin N → R) :
    Via w l (fun i => ∑ k, cst p' _ (f (c k)) * b' k i) (fun j => ∑ k, cst p _ (c k) * b k j) := by
  intro j i h
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_mul, hb k j i h, appLE_cst f p p' hφ, rs_cst, mul_left_comm]

theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] (x : KeyIn R) (x' : KeyIn R') (f : R →+* R'), (KeyPB x' x f ↔ ∃ φ w, KeyVia x' x f φ w) ∧ ∀ φ w, KeyVia x' x f φ w → (∀ (l : ℕ) (s : RR x l), ∃! s' : RR x' l, SecVia x' x φ w s' s) ∧ (∀ z : Pt x, ∃! z' : Pt x', z'.left ≫ φ = spMap f ≫ z.left) ∧ ∀ (l N : ℕ) (b : Fin N → RR x l) (b' : Fin N → RR x' l) (s : RR x l) (s' : RR x' l) (c : Fin N → R), (∀ k, SecVia x' x φ w (b' k) (b k)) → SecVia x' x φ w s' s → Coords x b c s.f → Coords x' b' (fun k => f (c k)) s'.f := by
  intro R R' _ _ x x' f
  refine ⟨⟨fun ⟨φ, he, w, hg, F, H⟩ => ⟨φ, w, he, hg, F, H⟩, fun ⟨φ, w, he, hg, F, H⟩ => ⟨φ, he, w, hg, F, H⟩⟩, ?_⟩
  rintro φ w ⟨he, hg, F, ⟨hP, -⟩, hw, -⟩
  refine ⟨fun l s => ?_, fun z => ?_, fun l N b b' s s' c hb hs hc => ?_⟩
  · obtain ⟨s', hs'⟩ := exists_via x.P.isLB x'.P.isLB hw l s
    refine ⟨s', hs', fun t ht => ?_⟩
    have e : t.f = s'.f := Via.unique (w := w) (l := l) x.P.isLB ht hs'
    obtain ⟨tf, _⟩ := t
    obtain ⟨sf, _⟩ := s'
    obtain rfl : tf = sf := e
    rfl
  · have hz : z.left ≫ x.P.A.hom = 𝟙 (Sp R) := Over.w z
    have hc : (spMap f ≫ z.left) ≫ x.P.A.hom = 𝟙 (Sp R') ≫ spMap f := by
      rw [Category.assoc, hz, Category.comp_id, Category.id_comp]
    refine ⟨Over.homMk (hP.lift _ _ hc) (hP.lift_snd _ _ hc), hP.lift_fst _ _ hc, fun t ht => ?_⟩
    ext1
    exact hP.hom_ext (ht.trans (hP.lift_fst _ _ hc).symm) ((Over.w t).trans (hP.lift_snd _ _ hc).symm)
  · have H := Via.comb (w := w) (l := l) (b' := fun k => (b' k).f) (b := fun k => (b k).f) f x.P.A.hom x'.P.A.hom hP.w hb c
    have e : s.f = fun j => ∑ k, cst x.P.A.hom (x.P.L.U j) (c k) * (show Γ(x.P.A.left, x.P.L.U j) from (b k).f j) :=
      funext hc
    have hs' : Via w l s'.f s.f := hs
    have hs'' := (congrArg (Via w l s'.f) e).mp hs'
    have e' := Via.unique x.P.isLB hs'' H
    exact fun i => congrFun e' i

end GlobalTheory.KeyVia
end
