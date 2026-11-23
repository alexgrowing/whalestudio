import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.DerMorK

section Deform
variable {Z X : Scheme.{0}} (g : Z ⟶ X) (ψ : ∀ W : X.Opens, Γ(X, W) →+* Γ(Z, g ⁻¹ᵁ W))
  (hnat : ∀ (W W' : X.Opens) (h : W' ≤ W) (f : Γ(X, W)),
    ψ W' (resG X h f) = resG Z (g.preimage_mono h) (ψ W f))

def deformPsh : Z.toPresheafedSpace ⟶ X.toPresheafedSpace where
  base := g.base
  c :=
    { app := fun W => CommRingCat.ofHom (ψ W.unop)
      naturality := fun W W' i => by
        ext f
        exact hnat W.unop W'.unop i.unop.le f }

def deformHom (hnil : ∀ (W : X.Opens) (f : Γ(X, W)), IsNilpotent (ψ W f - (g.app W).hom f)) : Z ⟶ X :=
  ⟨⟨deformPsh g ψ hnat, fun x => ⟨fun a ha => by
    obtain ⟨W, hW, f, rfl⟩ := X.presheaf.germ_exist a
    have h1 := PresheafedSpace.stalkMap_germ_apply (deformPsh g ψ hnat) W x hW f
    have h2 := Scheme.Hom.germ_stalkMap_apply g W x hW f
    have h3 : IsNilpotent ((Z.presheaf.germ (g ⁻¹ᵁ W) x hW).hom (ψ W f - (g.app W).hom f)) :=
      (hnil W f).map _
    have h4 : IsUnit ((Z.presheaf.germ (g ⁻¹ᵁ W) x hW).hom (ψ W f)) := by
      erw [h1] at ha
      exact ha
    have h5 : IsUnit ((Z.presheaf.germ (g ⁻¹ᵁ W) x hW).hom ((g.app W).hom f)) := by
      have := h3.neg.isUnit_add_right_of_commute h4 (Commute.all _ _)
      rw [map_sub] at this
      convert this using 1
      ring
    rw [← h2] at h5
    exact isUnit_of_map_unit (g.stalkMap x).hom _ h5⟩⟩⟩

theorem deformHom_base (hnil) : (deformHom g ψ hnat hnil).base = g.base := rfl

end Deform

theorem hom_ext_appLE {Z X : Scheme.{0}} {f g : Z ⟶ X} (hb : f.base = g.base)
    (h : ∀ U e, f.appLE U (g ⁻¹ᵁ U) e = g.app U) : f = g := by
  refine Scheme.Hom.ext hb fun U => ?_
  rw [← h U (le_of_eq congr((TopologicalSpace.Opens.map $hb.symm).obj U))]
  rfl

theorem appLE_constFn {R : Type} [CommRing R] {Z X : Scheme.{0}} (f : Z ⟶ X) (p : X ⟶ Sp R)
    {U : X.Opens} {V : Z.Opens} (e : V ≤ f ⁻¹ᵁ U) (a : R) :
    (f.appLE U V e).hom (constFn p U a) = constFn (f ≫ p) V a := by
  unfold constFn
  rw [← Scheme.Hom.appLE_comp_appLE f p ⊤ U V (fun _ _ => trivial) e]
  rfl

theorem app_constFn {R : Type} [CommRing R] {Z X : Scheme.{0}} (f : Z ⟶ X) (p : X ⟶ Sp R)
    (U : X.Opens) (a : R) :
    (f.app U).hom (constFn p U a) = constFn (f ≫ p) (f ⁻¹ᵁ U) a := by
  rw [Scheme.Hom.app_eq_appLE, appLE_constFn]

theorem constFn_spMap {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}} (p : X ⟶ Sp R')
    (φ : R →+* R') (U : X.Opens) (a : R) :
    constFn (p ≫ spMap φ) U a = constFn p U (φ a) := by
  unfold constFn
  rw [← Scheme.Hom.appLE_comp_appLE p (spMap φ) ⊤ ⊤ U (fun _ _ => trivial) (fun _ _ => trivial)]
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
  have h2 := congr(($h).hom a)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2 ⊢
  rw [h2]
  congr 1

def constHom {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem constFn_eq {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) (a : R) :
    constFn p U a = constHom p U a := rfl

theorem res_constFn {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U)
    (a : R) : resG X h (constFn p U a) = constFn p V a := by
  have := Scheme.Hom.appLE_map p (U := ⊤) (V := U) (V' := V) (fun _ _ => trivial) (homOfLE h).op
  exact congr(($this).hom _)

theorem res_app {Z X : Scheme.{0}} (f : Z ⟶ X) {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) :
    (f.app V).hom (resG X h a) = resG Z (f.preimage_mono h) ((f.app U).hom a) := by
  have := f.naturality (homOfLE h).op
  exact congr(($this).hom _)

theorem pbT_eq_app {Z X : Scheme.{0}} (f : Z ⟶ X) {U : X.Opens} (a : Γ(X, U)) :
    pbT f a (f ⁻¹ᵁ U) = (f.app U).hom a := by
  unfold pbT
  rw [dif_pos le_rfl, Scheme.Hom.appLE_eq_app]

section Main
variable {K : Type} [Field K] {Y Y' : Scheme.{0}} {q : Y ⟶ Sp K} (π : Y' ⟶ Sp (DualNumber K)) (ρ : Y' ⟶ Y)
  {R : Type} [CommRing R] {D : R → K} {X : Scheme.{0}} {p : X ⟶ Sp R} {m : Y ⟶ X}
  {d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)}

theorem eps_sq (U : Y'.Opens) :
    constFn π U DualNumber.eps * constFn π U DualNumber.eps = 0 := by
  rw [constFn_eq, ← map_mul, DualNumber.eps_mul_eps, map_zero]

def psi (hd : LocDerK q p m D ⊤ d) (W : X.Opens) : Γ(X, W) →+* Γ(Y', (ρ ≫ m) ⁻¹ᵁ W) where
  toFun f := (ρ.app (m ⁻¹ᵁ W)).hom ((m.app W).hom f) +
    constFn π (ρ ⁻¹ᵁ m ⁻¹ᵁ W) DualNumber.eps * (ρ.app (m ⁻¹ᵁ W)).hom (d W f)
  map_one' := by
    have h := hd.mul W le_top 1 1
    simp only [_root_.mul_one, map_one, _root_.one_mul] at h
    have h0 : d W 1 = 0 := by linear_combination -h
    simp only [h0, map_one, map_zero, mul_zero, add_zero]
    rfl
  map_mul' f f' := by
    have h := eps_sq π (ρ ⁻¹ᵁ m ⁻¹ᵁ W)
    rw [hd.mul W le_top]
    simp only [map_mul, map_add]
    change (_ : Γ(Y', ρ ⁻¹ᵁ m ⁻¹ᵁ W)) = (_ : Γ(Y', ρ ⁻¹ᵁ m ⁻¹ᵁ W)) * (_ : Γ(Y', ρ ⁻¹ᵁ m ⁻¹ᵁ W))
    linear_combination -((ρ.app (m ⁻¹ᵁ W)).hom (d W f) * (ρ.app (m ⁻¹ᵁ W)).hom (d W f')) * h
  map_zero' := by
    have h := hd.add W le_top 0 0
    simp only [add_zero] at h
    have h0 : d W 0 = 0 := by linear_combination -h
    simp only [h0, map_zero, mul_zero, add_zero]
    rfl
  map_add' f f' := by
    rw [hd.add W le_top]
    simp only [map_add]
    change (_ : Γ(Y', ρ ⁻¹ᵁ m ⁻¹ᵁ W)) = (_ : Γ(Y', ρ ⁻¹ᵁ m ⁻¹ᵁ W)) + (_ : Γ(Y', ρ ⁻¹ᵁ m ⁻¹ᵁ W))
    ring

theorem psi_apply (hd : LocDerK q p m D ⊤ d) (W : X.Opens) (f : Γ(X, W)) :
    (psi π ρ hd W f : Γ(Y', ρ ⁻¹ᵁ m ⁻¹ᵁ W)) = (ρ.app (m ⁻¹ᵁ W)).hom ((m.app W).hom f) +
    constFn π (ρ ⁻¹ᵁ m ⁻¹ᵁ W) DualNumber.eps * (ρ.app (m ⁻¹ᵁ W)).hom (d W f) := rfl

theorem psi_nat (hd : LocDerK q p m D ⊤ d) (W W' : X.Opens) (h : W' ≤ W) (f : Γ(X, W)) :
    psi π ρ hd W' (resG X h f) = resG Y' ((ρ ≫ m).preimage_mono h) (psi π ρ hd W f) := by
  have h1 : m ⁻¹ᵁ W' ≤ m ⁻¹ᵁ W := m.preimage_mono h
  have h2 : (ρ.app (m ⁻¹ᵁ W')).hom ((m.app W').hom (resG X h f)) +
      constFn π (ρ ⁻¹ᵁ m ⁻¹ᵁ W') DualNumber.eps * (ρ.app (m ⁻¹ᵁ W')).hom (d W' (resG X h f)) =
      resG Y' (ρ.preimage_mono h1) ((ρ.app (m ⁻¹ᵁ W)).hom ((m.app W).hom f) +
      constFn π (ρ ⁻¹ᵁ m ⁻¹ᵁ W) DualNumber.eps * (ρ.app (m ⁻¹ᵁ W)).hom (d W f)) := by
    rw [hd.res W W' h le_top, rsT, dif_pos h1, res_app, res_app, res_app, map_add, map_mul, res_constFn]
  exact h2

theorem psi_nil (hd : LocDerK q p m D ⊤ d) (W : X.Opens) (f : Γ(X, W)) :
    IsNilpotent (psi π ρ hd W f - ((ρ ≫ m).app W).hom f) := by
  have h : IsNilpotent ((ρ.app (m ⁻¹ᵁ W)).hom ((m.app W).hom f) +
      constFn π (ρ ⁻¹ᵁ m ⁻¹ᵁ W) DualNumber.eps * (ρ.app (m ⁻¹ᵁ W)).hom (d W f) -
      (ρ.app (m ⁻¹ᵁ W)).hom ((m.app W).hom f)) := by
    refine ⟨2, ?_⟩
    have h := eps_sq π (ρ ⁻¹ᵁ m ⁻¹ᵁ W)
    linear_combination ((ρ.app (m ⁻¹ᵁ W)).hom (d W f)) ^ 2 * h
  exact h

end Main

theorem exists_hom_of_derivation : ∀ (K : Type) [Field K] (Y Y' : Scheme.{0}) (q : Y ⟶ Sp K) (π : Y' ⟶ Sp (DualNumber K)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap K (DualNumber K))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) → ∀ (R : Type) [CommRing R] (xD : R →+* DualNumber K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : Y ⟶ X) (d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)), m ≫ p = q ≫ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) ≫ spMap xD → LocDerK q p m (fun r => (xD r).snd) ⊤ d → ∃ Φ : Y' ⟶ X, j ≫ Φ = m ∧ Φ ≫ p = π ≫ spMap xD ∧ ∀ (W : X.Opens) (f : Γ(X, W)), pbT Φ f (ρ ⁻¹ᵁ (m ⁻¹ᵁ W)) = pbT (ρ ≫ m) f _ + constFn π _ DualNumber.eps * pbT ρ (d W f) _ := by
  intro K _ Y Y' q π ρ j hpb hjρ hjπ R _ xD X p m d hm hd
  let Φ := deformHom (ρ ≫ m) (psi π ρ hd) (psi_nat π ρ hd) (psi_nil π ρ hd)
  have hjm : j ≫ ρ ≫ m = m := by rw [← Category.assoc, hjρ, Category.id_comp]
  refine ⟨Φ, ?_, ?_, ?_⟩
  · refine hom_ext_appLE (congr(($hjm).base)) fun U e => ?_
    ext f
    have e' : m ⁻¹ᵁ U ≤ j ⁻¹ᵁ (ρ ⁻¹ᵁ m ⁻¹ᵁ U) := e
    have h1 : ((j ≫ Φ).appLE U (m ⁻¹ᵁ U) e).hom f = (j.appLE (ρ ⁻¹ᵁ m ⁻¹ᵁ U) (m ⁻¹ᵁ U) e').hom
        ((ρ.app (m ⁻¹ᵁ U)).hom ((m.app U).hom f) +
          constFn π (ρ ⁻¹ᵁ m ⁻¹ᵁ U) DualNumber.eps * (ρ.app (m ⁻¹ᵁ U)).hom (d U f)) := rfl
    have h2 : (j.appLE (ρ ⁻¹ᵁ m ⁻¹ᵁ U) (m ⁻¹ᵁ U) e').hom ((ρ.app (m ⁻¹ᵁ U)).hom ((m.app U).hom f)) =
        ((j ≫ ρ ≫ m).appLE U (m ⁻¹ᵁ U) e').hom f := rfl
    have h3 : ∀ (k : Y ⟶ X) (_ : k = m) (e''), k.appLE U (m ⁻¹ᵁ U) e'' = m.app U := by
      rintro k rfl e''
      exact Scheme.Hom.appLE_eq_app _
    rw [h1, map_add, map_mul, h2, h3 (j ≫ ρ ≫ m) hjm e', appLE_constFn, hjπ, constFn_spMap, constFn_eq]
    simp
  · apply ext_of_isAffine
    rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of R)).inv]
    ext r
    have h0 : ∀ {Z : Scheme.{0}} (k : Z ⟶ Sp R),
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ k.appTop).hom r = constFn k ⊤ r := by
      intro Z k
      have := Scheme.Hom.appLE_eq_app k (U := ⊤)
      exact congr(($this.symm).hom _)
    rw [h0, h0, constFn_spMap]
    have h1 : constFn (Φ ≫ p) ⊤ r = (ρ.app (m ⁻¹ᵁ ⊤)).hom ((m.app ⊤).hom (constFn p ⊤ r)) +
        constFn π (ρ ⁻¹ᵁ m ⁻¹ᵁ ⊤) DualNumber.eps * (ρ.app (m ⁻¹ᵁ ⊤)).hom (d ⊤ (constFn p ⊤ r)) :=
      (app_constFn Φ p ⊤ r).symm
    rw [h1, hd.base ⊤ le_rfl, app_constFn, hm, ← Category.assoc, constFn_spMap, constFn_spMap,
      app_constFn, app_constFn, hpb.w, constFn_spMap, constFn_spMap, constFn_eq, constFn_eq, constFn_eq,
      ← map_mul, ← map_add]
    change constHom π ⊤ _ = constHom π ⊤ _
    congr 1
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  · intro W f
    have h1 := pbT_eq_app Φ f
    have h2 := pbT_eq_app (ρ ≫ m) f
    have h3 := pbT_eq_app ρ (d W f)
    refine h1.trans ?_
    rw [h3]
    erw [h2]
    rfl

end GlobalTheory.KS.DerMorK
end
