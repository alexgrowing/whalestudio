import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
open TopologicalSpace Opposite

namespace GlobalTheory.BoundaryDivisor

variable {X : Scheme.{0}}

section Pull

variable {Y : Scheme.{0}} [IsIntegral Y] (j : Y ⟶ X) [IsOpenImmersion j]

def pull (y : Y) : X.presheaf.stalk (j y) →+* Y.functionField :=
  (algebraMap (Y.presheaf.stalk y) Y.functionField).comp (j.stalkMap y).hom

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory in
open TopologicalSpace Opposite in
variable {X : Scheme.{0}} in
variable {Y : Scheme.{0}} [IsIntegral Y] (j : Y ⟶ X) [IsOpenImmersion j] in
omit [IsIntegral Y] in

theorem _root_.GlobalTheory.BoundaryDivisor.stalkMap_bijective (y : Y) : Function.Bijective (j.stalkMap y).hom :=
  ConcreteCategory.bijective_of_isIso _

end Pull

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory in
open TopologicalSpace Opposite in
variable {X : Scheme.{0}} in
variable {Y : Scheme.{0}} [IsIntegral Y] (j : Y ⟶ X) [IsOpenImmersion j] in
private lemma pull_germ_eq_pull_germ (V : X.Opens) (s : Γ(X, V)) (y z : Y)
    (hy : j y ∈ V) (hz : j z ∈ V) :
    _root_.GlobalTheory.BoundaryDivisor.pull j y (X.presheaf.germ V (j y) hy s) =
      _root_.GlobalTheory.BoundaryDivisor.pull j z (X.presheaf.germ V (j z) hz s) := by
  have hη : genericPoint Y ∈ j ⁻¹ᵁ V :=
    ((genericPoint_spec Y).mem_open_set_iff (j ⁻¹ᵁ V).isOpen).2 ⟨y, Set.mem_univ _, hy⟩
  have e : ∀ (w : Y) (hw : j w ∈ V), _root_.GlobalTheory.BoundaryDivisor.pull j w (X.presheaf.germ V (j w) hw s) =
      Y.presheaf.germ (j ⁻¹ᵁ V) (genericPoint Y) hη (j.app V s) := by
    intro w hw
    change algebraMap (Y.presheaf.stalk w) Y.functionField
      (j.stalkMap w (X.presheaf.germ V (j w) hw s)) = _
    rw [Scheme.Hom.germ_stalkMap_apply]
    simp only [RingHom.algebraMap_toAlgebra]
    exact Y.presheaf.germ_stalkSpecializes_apply hw _ _
  rw [e y hy, e z hz]

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory in
open TopologicalSpace Opposite in
variable {X : Scheme.{0}} in
private lemma mem_closed_iff_not_isUnit_germ (T : Closeds X) (U : X.affineOpens) (h : Γ(X, U))
    (hI : (Scheme.IdealSheafData.vanishingIdeal T).ideal U = Ideal.span {h}) (z : X)
    (hz : z ∈ (U : X.Opens)) :
    z ∈ T ↔ ¬ IsUnit (X.presheaf.germ U z hz h) := by
  have key : z ∈ (Scheme.IdealSheafData.vanishingIdeal T).support ↔ z ∈ T := by
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal, SetLike.mem_coe]
  rw [← key, Scheme.IdealSheafData.mem_support_iff_of_mem hz, hI, Scheme.mem_zeroLocus_iff,
    ← X.mem_basicOpen h z hz]
  constructor
  · intro H
    exact H h (Ideal.mem_span_singleton_self h)
  · intro H f hf hzf
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hf
    rw [X.basicOpen_mul] at hzf
    exact H hzf.2

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory in
open TopologicalSpace Opposite in
variable {X : Scheme.{0}} in
private lemma mem_vanishingIdeal_of_not_isUnit_germ (T : Closeds X) (W : X.affineOpens)
    (s : Γ(X, W))
    (hs : ∀ (z : X) (hz : z ∈ (W : X.Opens)), z ∈ T → ¬ IsUnit (X.presheaf.germ W z hz s)) :
    s ∈ (Scheme.IdealSheafData.vanishingIdeal T).ideal W := by
  simp [Scheme.IdealSheafData.vanishingIdeal]
  rw [PrimeSpectrum.mem_vanishingIdeal]
  intro p hp
  have hz : W.2.fromSpec p ∈ (W : X.Opens) := by
    rw [← SetLike.mem_coe, ← W.2.range_fromSpec]
    exact ⟨p, rfl⟩
  by_contra hsp
  have h1 : p ∈ PrimeSpectrum.basicOpen s := hsp
  rw [← W.2.fromSpec_preimage_basicOpen] at h1
  exact hs _ hz hp ((X.mem_basicOpen s _ hz).1 h1)

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory in
open TopologicalSpace Opposite in
variable {X : Scheme.{0}} in
private lemma exists_germ_eq_mul_of_not_isUnit_on_closed (T : Closeds X) (U : X.affineOpens) (h : Γ(X, U))
    (hI : (Scheme.IdealSheafData.vanishingIdeal T).ideal U = Ideal.span {h}) (x : X)
    (hx : x ∈ (U : X.Opens)) (V : X.Opens) (hxV : x ∈ V) (s : Γ(X, V))
    (hs : ∀ (z : X) (hz : z ∈ V), z ∈ T → ¬ IsUnit (X.presheaf.germ V z hz s)) :
    ∃ c, X.presheaf.germ V x hxV s = c * X.presheaf.germ U x hx h := by
  obtain ⟨f, hfV, hxf⟩ := U.2.exists_basicOpen_le (V := V) ⟨x, hxV⟩ hx
  have hWV : ((X.affineBasicOpen f : X.affineOpens) : X.Opens) ≤ V := hfV
  have hxW : x ∈ ((X.affineBasicOpen f : X.affineOpens) : X.Opens) := hxf
  have hmem : X.presheaf.map (homOfLE hWV).op s ∈
      (Scheme.IdealSheafData.vanishingIdeal T).ideal (X.affineBasicOpen f) := by
    apply mem_vanishingIdeal_of_not_isUnit_germ
    intro z hz hzT hu
    apply hs z (hWV hz) hzT
    rw [← X.presheaf.germ_res_apply (homOfLE hWV) z hz s]
    exact hu
  rw [← Scheme.IdealSheafData.map_ideal_basicOpen, hI, Ideal.map_span, Set.image_singleton] at hmem
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨X.presheaf.germ _ x hxW c, ?_⟩
  rw [← X.presheaf.germ_res_apply (homOfLE hWV) x hxW s, ← hc]
  refine (map_mul (ConcreteCategory.hom (X.presheaf.germ _ x hxW)) c _).trans ?_
  congr 1
  exact X.presheaf.germ_res_apply _ x hxW h

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory in
open TopologicalSpace Opposite in
variable {X : Scheme.{0}} in
private lemma exists_eq_mul_of_pow_eq_mul_germ (T : Closeds X) (U : X.affineOpens) (h : Γ(X, U))
    (hI : (Scheme.IdealSheafData.vanishingIdeal T).ideal U = Ideal.span {h}) (x : X)
    (hx : x ∈ (U : X.Opens)) (a b : X.presheaf.stalk x) (n : ℕ)
    (hab : a ^ n = b * X.presheaf.germ U x hx h) :
    ∃ c, a = c * X.presheaf.germ U x hx h := by
  obtain ⟨V₁, hx₁, s, rfl⟩ := X.presheaf.germ_exist a
  obtain ⟨V₂, hx₂, t, rfl⟩ := X.presheaf.germ_exist b
  have hx₂U : x ∈ V₂ ⊓ (U : X.Opens) := ⟨hx₂, hx⟩
  have key : X.presheaf.germ V₁ x hx₁ (s ^ n) = X.presheaf.germ (V₂ ⊓ (U : X.Opens)) x hx₂U
      (X.presheaf.map (homOfLE (inf_le_left : V₂ ⊓ (U : X.Opens) ≤ V₂)).op t *
        X.presheaf.map (homOfLE (inf_le_right : V₂ ⊓ (U : X.Opens) ≤ U)).op h) := by
    rw [map_pow, map_mul, X.presheaf.germ_res_apply, X.presheaf.germ_res_apply, hab]
  obtain ⟨W, hxW, i₁, i₂, hW⟩ := X.presheaf.germ_eq x hx₁ hx₂U _ _ key
  have hvan : ∀ (z : X) (hz : z ∈ W), z ∈ T →
      ¬ IsUnit (X.presheaf.germ W z hz (X.presheaf.map i₁.op s)) := by
    intro z hz hzT hu
    have hzU : z ∈ (U : X.Opens) := (i₂.le hz).2
    apply (mem_closed_iff_not_isUnit_germ T U h hI z hzU).1 hzT
    have h1 : IsUnit (X.presheaf.germ W z hz (X.presheaf.map i₁.op (s ^ n))) := by
      rw [map_pow, map_pow]
      exact hu.pow n
    rw [hW, map_mul, map_mul, X.presheaf.germ_res_apply, X.presheaf.germ_res_apply,
      X.presheaf.germ_res_apply, X.presheaf.germ_res_apply] at h1
    exact isUnit_of_mul_isUnit_right h1
  obtain ⟨c, hc⟩ := exists_germ_eq_mul_of_not_isUnit_on_closed T U h hI x hx W hxW
    (X.presheaf.map i₁.op s) hvan
  exact ⟨c, by rw [← hc, X.presheaf.germ_res_apply]⟩

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory in
open TopologicalSpace Opposite in
variable {X : Scheme.{0}} in

theorem _root_.GlobalTheory.BoundaryDivisor.exists_reduced_cartierDiv :
    ∀ (X Y : Scheme.{0}) [IsIntegral Y] (j : Y ⟶ X) [IsOpenImmersion j]
      (T : TopologicalSpace.Closeds X), _root_.ReciprocityTheory.AnForm.R.FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal T) →
      j (genericPoint Y) ∉ T → ∃ D : _root_.GlobalTheory.Cartier.CartierDiv Y, D.Eff ∧
        (∀ y, y ∈ D.supp ↔ j y ∈ T) ∧
        ∀ (y : Y) (g : Y.functionFieldˣ), D.IsEqn y g →
          ∀ (f : Y.functionField) (n : ℕ), _root_.GlobalTheory.Cartier.RegAt y f →
            _root_.GlobalTheory.Cartier.RegAt y (f ^ n / g) →
              _root_.GlobalTheory.Cartier.RegAt y (f / g) := by
  intro X Y _ j _ T hS hη
  have hS' := hS
  unfold _root_.ReciprocityTheory.AnForm.R.FinalTheorems.Snc at hS'
  have hchart : ∀ y : Y, ∃ (U : X.affineOpens) (_ : j y ∈ (U : X.Opens)) (h : Γ(X, U)),
      (Scheme.IdealSheafData.vanishingIdeal T).ideal U = Ideal.span {h} := by
    intro y
    obtain ⟨_, U, hU, n, f, J, _, hJ⟩ := hS' (j y)
    exact ⟨U, hU, _, hJ⟩
  choose U hU h hI using hchart
  have hinj : ∀ y, Function.Injective (_root_.GlobalTheory.BoundaryDivisor.pull j y) := fun y =>
    (IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField).comp
      (_root_.GlobalTheory.BoundaryDivisor.stalkMap_bijective j y).1
  have hne : ∀ y, _root_.GlobalTheory.BoundaryDivisor.pull j y (X.presheaf.germ (U y) (j y) (hU y) (h y)) ≠ 0 := by
    intro y h0
    have hηU : j (genericPoint Y) ∈ (U y : X.Opens) :=
      ((genericPoint_spec Y).mem_open_set_iff (j ⁻¹ᵁ (U y : X.Opens)).isOpen).2
        ⟨y, Set.mem_univ _, hU y⟩
    rw [pull_germ_eq_pull_germ j _ _ y (genericPoint Y) (hU y) hηU] at h0
    have h1 : X.presheaf.germ (U y) _ hηU (h y) = 0 := hinj _ (by rw [h0, map_zero])
    have h2 := (mem_closed_iff_not_isUnit_germ T (U y) (h y) (hI y) _ hηU).not.1 hη
    rw [not_not, h1] at h2
    exact not_isUnit_zero h2
  obtain ⟨g, hg⟩ : ∃ g : Y → Y.functionFieldˣ, ∀ y, (g y : Y.functionField) =
      _root_.GlobalTheory.BoundaryDivisor.pull j y (X.presheaf.germ (U y) (j y) (hU y) (h y)) :=
    ⟨fun y => Units.mk0 _ (hne y), fun y => rfl⟩
  have hunit : ∀ (y z : Y) (hz : j z ∈ (U y : X.Opens)),
      _root_.GlobalTheory.Cartier.UnitAt z ((g y : Y.functionField) / g z) := by
    intro y z hz
    obtain ⟨c, hc⟩ := exists_germ_eq_mul_of_not_isUnit_on_closed T (U z) (h z) (hI z) (j z) (hU z) (U y) hz
      (h y) (fun w hw hwT => (mem_closed_iff_not_isUnit_germ T (U y) (h y) (hI y) w hw).1 hwT)
    obtain ⟨d, hd⟩ := exists_germ_eq_mul_of_not_isUnit_on_closed T (U y) (h y) (hI y) (j z) hz (U z) (hU z)
      (h z) (fun w hw hwT => (mem_closed_iff_not_isUnit_germ T (U z) (h z) (hI z) w hw).1 hwT)
    have gy : (g y : Y.functionField) =
        _root_.GlobalTheory.BoundaryDivisor.pull j z (X.presheaf.germ (U y) (j z) hz (h y)) := by
      rw [hg y]
      exact pull_germ_eq_pull_germ j _ _ y z (hU y) hz
    have hcz : (g y : Y.functionField) = _root_.GlobalTheory.BoundaryDivisor.pull j z c * g z := by
      rw [gy, hg z, hc, map_mul]
    have hdz : (g z : Y.functionField) = _root_.GlobalTheory.BoundaryDivisor.pull j z d * g y := by
      rw [gy, hg z, hd, map_mul]
    have hcd : _root_.GlobalTheory.BoundaryDivisor.pull j z c * _root_.GlobalTheory.BoundaryDivisor.pull j z d = 1 := by
      have e : (_root_.GlobalTheory.BoundaryDivisor.pull j z c * _root_.GlobalTheory.BoundaryDivisor.pull j z d) *
          (g y : Y.functionField) = 1 * g y := by
        rw [one_mul, mul_assoc, ← hdz, ← hcz]
      exact mul_right_cancel₀ (g y).ne_zero e
    rw [hcz, mul_div_cancel_right₀ _ (g z).ne_zero]
    unfold _root_.GlobalTheory.Cartier.UnitAt
    refine ⟨(j.stalkMap z).hom c, isUnit_iff_exists_inv.2 ⟨(j.stalkMap z).hom d, ?_⟩, rfl⟩
    apply IsFractionRing.injective (Y.presheaf.stalk z) Y.functionField
    rw [map_mul, map_one]
    exact hcd
  let F : (y : Y) → _root_.GlobalTheory.Cartier.Germ y := fun y => _root_.GlobalTheory.Cartier.germOf y (g y)
  have hF : F ∈ _root_.GlobalTheory.Cartier.cartierGroup Y := by
    unfold _root_.GlobalTheory.Cartier.cartierGroup
    intro y
    refine ⟨j ⁻¹ᵁ (U y : X.Opens), hU y, g y, fun z hz => ?_⟩
    exact _root_.GlobalTheory.Cartier.germOf_eq_iff.2 (hunit y z hz)
  let D : _root_.GlobalTheory.Cartier.CartierDiv Y := ⟨F, hF⟩
  have hDeq : ∀ y, D.IsEqn y (g y) := fun y => rfl
  have hreg : ∀ y, _root_.GlobalTheory.Cartier.RegAt y (g y) := by
    intro y
    unfold _root_.GlobalTheory.Cartier.RegAt
    exact ⟨_, (hg y).symm⟩
  have hsupp : ∀ y, _root_.GlobalTheory.Cartier.UnitAt y (1 / (g y : Y.functionField)) ↔
      IsUnit (X.presheaf.germ (U y) (j y) (hU y) (h y)) := by
    intro y
    have bij := _root_.GlobalTheory.BoundaryDivisor.stalkMap_bijective j y
    unfold _root_.GlobalTheory.Cartier.UnitAt
    constructor
    · rintro ⟨a, -, ha⟩
      obtain ⟨b, rfl⟩ := bij.2 a
      have hb : _root_.GlobalTheory.BoundaryDivisor.pull j y b = 1 / g y := ha
      refine isUnit_iff_exists_inv.2 ⟨b, hinj y ?_⟩
      rw [map_mul, map_one, hb, ← hg y, mul_one_div_cancel (g y).ne_zero]
    · rintro ⟨u, hu⟩
      refine ⟨(j.stalkMap y).hom ↑u⁻¹, u⁻¹.isUnit.map _, ?_⟩
      show _root_.GlobalTheory.BoundaryDivisor.pull j y ↑u⁻¹ = 1 / g y
      rw [hg y, ← hu, eq_div_iff (by rw [hu]; exact hne y), ← map_mul, Units.inv_mul, map_one]
  refine ⟨D, ?_, ?_, ?_⟩
  · rw [_root_.GlobalTheory.Cartier.CartierDiv.eff_iff]
    intro y g' hg'
    have hu := ((hDeq y).iff_unitAt).1 hg'
    have e : (g' : Y.functionField) = ((g' : Y.functionField) / g y) * g y := by
      rw [div_mul_cancel₀ _ (g y).ne_zero]
    rw [e]
    exact hu.regAt.mul (hreg y)
  · intro y
    show ¬ D.IsEqn y 1 ↔ j y ∈ T
    rw [(hDeq y).iff_unitAt, Units.val_one, hsupp y,
      mem_closed_iff_not_isUnit_germ T (U y) (h y) (hI y) _ (hU y)]
  · intro y g' hg' f n hf hfn
    have hu := ((hDeq y).iff_unitAt).1 hg'
    have hr1 : _root_.GlobalTheory.Cartier.RegAt y (f ^ n / g y) := by
      have e : f ^ n / (g y : Y.functionField) =
          (f ^ n / g') * ((g' : Y.functionField) / g y) := by
        rw [div_mul_div_cancel₀ g'.ne_zero]
      rw [e]
      exact hfn.mul hu.regAt
    have hr2 : _root_.GlobalTheory.Cartier.RegAt y (f / g y) := by
      have bij := _root_.GlobalTheory.BoundaryDivisor.stalkMap_bijective j y
      unfold _root_.GlobalTheory.Cartier.RegAt at hf hr1 ⊢
      obtain ⟨a, ha⟩ := hf
      obtain ⟨b, hb⟩ := hr1
      obtain ⟨a', rfl⟩ := bij.2 a
      obtain ⟨b', rfl⟩ := bij.2 b
      have ha' : _root_.GlobalTheory.BoundaryDivisor.pull j y a' = f := ha
      have hb' : _root_.GlobalTheory.BoundaryDivisor.pull j y b' = f ^ n / g y := hb
      have key : a' ^ n = b' * X.presheaf.germ (U y) (j y) (hU y) (h y) := by
        apply hinj y
        rw [map_pow, map_mul, ha', hb', ← hg y, div_mul_cancel₀ _ (g y).ne_zero]
      obtain ⟨c, hc⟩ := exists_eq_mul_of_pow_eq_mul_germ T (U y) (h y) (hI y) (j y) (hU y) a' b' n key
      refine ⟨(j.stalkMap y).hom c, ?_⟩
      show _root_.GlobalTheory.BoundaryDivisor.pull j y c = f / g y
      rw [← ha', hc, map_mul, ← hg y, mul_div_cancel_right₀ _ (g y).ne_zero]
    have hinv : _root_.GlobalTheory.Cartier.RegAt y ((g y : Y.functionField) / g') := by
      have := ((_root_.GlobalTheory.Cartier.unitAt_iff
        (div_ne_zero g'.ne_zero (g y).ne_zero)).1 hu).2
      rwa [inv_div] at this
    have e : f / (g' : Y.functionField) = f / g y * ((g y : Y.functionField) / g') := by
      rw [div_mul_div_cancel₀ (g y).ne_zero]
    rw [e]
    exact hr2.mul hinv

end GlobalTheory.BoundaryDivisor
