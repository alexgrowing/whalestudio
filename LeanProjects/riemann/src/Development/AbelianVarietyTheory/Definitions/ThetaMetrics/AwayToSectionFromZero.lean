import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (resG)

namespace GlobalTheory.ProjFrac

variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

instance isPrime_point (x : Proj 𝒜) : x.asHomogeneousIdeal.toIdeal.IsPrime :=
  ProjectiveSpectrum.isPrime x

def ev (U : (Proj 𝒜).Opens) (x : Proj 𝒜) (hx : x ∈ U) :
    Γ(Proj 𝒜, U) →+* Localization.AtPrime x.asHomogeneousIdeal.toIdeal :=
  (algebraMap (HomogeneousLocalization.AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal) _).comp
    (openToLocalization 𝒜 U x hx).hom

variable {𝒜}

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite in
variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] in
variable {𝒜} in

theorem _root_.GlobalTheory.ProjFrac.ext {U : (Proj 𝒜).Opens} {s t : Γ(Proj 𝒜, U)}
    (h : ∀ x hx, _root_.GlobalTheory.ProjFrac.ev 𝒜 U x hx s =
      _root_.GlobalTheory.ProjFrac.ev 𝒜 U x hx t) : s = t := by
  refine Subtype.ext (funext fun y => HomogeneousLocalization.val_injective _ ?_)
  exact h y.1 y.2

theorem ev_resG {U V : (Proj 𝒜).Opens} (h : V ≤ U) (x : Proj 𝒜) (hx : x ∈ V) (s : Γ(Proj 𝒜, U)) :
    ev 𝒜 V x hx (resG (Proj 𝒜) h s) = ev 𝒜 U x (h hx) s := rfl

theorem mem_basicOpen_iff {U : (Proj 𝒜).Opens} (s : Γ(Proj 𝒜, U)) (x : Proj 𝒜) (hx : x ∈ U) :
    x ∈ (Proj 𝒜).basicOpen s ↔ IsUnit (ev 𝒜 U x hx s) := by
  rw [Scheme.mem_basicOpen _ _ _ hx]
  refine Iff.trans ?_ (HomogeneousLocalization.isUnit_iff_isUnit_val 𝒜 x.asHomogeneousIdeal.toIdeal
    (s.1 ⟨x, hx⟩)).symm
  rw [← Proj.stalkIso'_germ 𝒜 U x hx s]
  exact (isUnit_map_iff (Proj.stalkIso' 𝒜 x) _).symm

variable (𝒜) in

def frac (U : (Proj 𝒜).Opens) {d : ℕ} (a b : A) (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 d)
    (hU : U ≤ Proj.basicOpen 𝒜 b) : Γ(Proj 𝒜, U) :=
  ⟨fun y => HomogeneousLocalization.mk ⟨d, ⟨a, ha⟩, ⟨b, hb⟩, hU y.2⟩, fun y =>
    ⟨U, y.2, 𝟙 _, d, ⟨a, ha⟩, ⟨b, hb⟩, _, fun _ => rfl⟩⟩

section

variable {U V : (Proj 𝒜).Opens} {d d' : ℕ} {a b a' b' : A} {ha : a ∈ 𝒜 d} {hb : b ∈ 𝒜 d}
  {ha' : a' ∈ 𝒜 d'} {hb' : b' ∈ 𝒜 d'} {hU : U ≤ Proj.basicOpen 𝒜 b} {hU' : U ≤ Proj.basicOpen 𝒜 b'}

theorem ev_frac (x : Proj 𝒜) (hx : x ∈ U) :
    ev 𝒜 U x hx (frac 𝒜 U a b ha hb hU) = Localization.mk a ⟨b, hU hx⟩ := rfl

theorem ev_frac_mul_den (x : Proj 𝒜) (hx : x ∈ U) :
    ev 𝒜 U x hx (frac 𝒜 U a b ha hb hU) * algebraMap A _ b = algebraMap A _ a := by
  rw [ev_frac, Localization.mk_eq_mk']
  exact IsLocalization.mk'_spec _ a (⟨b, hU hx⟩ : x.asHomogeneousIdeal.toIdeal.primeCompl)

theorem resG_frac (h : V ≤ U) :
    resG (Proj 𝒜) h (frac 𝒜 U a b ha hb hU) = frac 𝒜 V a b ha hb (h.trans hU) := rfl

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite in
variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] in
variable {𝒜} in
variable {U V : (Proj 𝒜).Opens} {d d' : ℕ} {a b a' b' : A} {ha : a ∈ 𝒜 d} {hb : b ∈ 𝒜 d}
  {ha' : a' ∈ 𝒜 d'} {hb' : b' ∈ 𝒜 d'} {hU : U ≤ Proj.basicOpen 𝒜 b}
  {hU' : U ≤ Proj.basicOpen 𝒜 b'} in

theorem _root_.GlobalTheory.ProjFrac.frac_eq (h : a * b' = a' * b) :
    _root_.GlobalTheory.ProjFrac.frac 𝒜 U a b ha hb hU =
      _root_.GlobalTheory.ProjFrac.frac 𝒜 U a' b' ha' hb' hU' := by
  refine _root_.GlobalTheory.ProjFrac.ext fun x hx => ?_
  rw [_root_.GlobalTheory.ProjFrac.ev_frac, _root_.GlobalTheory.ProjFrac.ev_frac,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp only [OneMemClass.coe_one, one_mul]; linear_combination h⟩

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite in
variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] in
variable {𝒜} in
variable {U V : (Proj 𝒜).Opens} {d d' : ℕ} {a b a' b' : A} {ha : a ∈ 𝒜 d} {hb : b ∈ 𝒜 d}
  {ha' : a' ∈ 𝒜 d'} {hb' : b' ∈ 𝒜 d'} {hU : U ≤ Proj.basicOpen 𝒜 b}
  {hU' : U ≤ Proj.basicOpen 𝒜 b'} in

theorem _root_.GlobalTheory.ProjFrac.frac_mul :
    _root_.GlobalTheory.ProjFrac.frac 𝒜 U a b ha hb hU *
        _root_.GlobalTheory.ProjFrac.frac 𝒜 U a' b' ha' hb' hU' =
      _root_.GlobalTheory.ProjFrac.frac 𝒜 U (a * a') (b * b') (SetLike.mul_mem_graded ha ha')
        (SetLike.mul_mem_graded hb hb') (by rw [Proj.basicOpen_mul]; exact le_inf hU hU') := by
  refine _root_.GlobalTheory.ProjFrac.ext fun x hx => ?_
  rw [map_mul, _root_.GlobalTheory.ProjFrac.ev_frac, _root_.GlobalTheory.ProjFrac.ev_frac,
    _root_.GlobalTheory.ProjFrac.ev_frac, Localization.mk_mul]
  rfl

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite in
variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] in
variable {𝒜} in
variable {U V : (Proj 𝒜).Opens} {d d' : ℕ} {a b a' b' : A} {ha : a ∈ 𝒜 d} {hb : b ∈ 𝒜 d}
  {ha' : a' ∈ 𝒜 d'} {hb' : b' ∈ 𝒜 d'} {hU : U ≤ Proj.basicOpen 𝒜 b}
  {hU' : U ≤ Proj.basicOpen 𝒜 b'} in

theorem _root_.GlobalTheory.ProjFrac.frac_mul_eq {d'' : ℕ} {a'' b'' : A} {ha'' : a'' ∈ 𝒜 d''}
    {hb'' : b'' ∈ 𝒜 d''} {hU'' : U ≤ Proj.basicOpen 𝒜 b''} (h : a * a' * b'' = a'' * (b * b')) :
    _root_.GlobalTheory.ProjFrac.frac 𝒜 U a b ha hb hU *
        _root_.GlobalTheory.ProjFrac.frac 𝒜 U a' b' ha' hb' hU' =
      _root_.GlobalTheory.ProjFrac.frac 𝒜 U a'' b'' ha'' hb'' hU'' :=
  _root_.GlobalTheory.ProjFrac.frac_mul.trans (_root_.GlobalTheory.ProjFrac.frac_eq h)

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite in
variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] in
variable {𝒜} in
variable {U V : (Proj 𝒜).Opens} {d d' : ℕ} {a b a' b' : A} {ha : a ∈ 𝒜 d} {hb : b ∈ 𝒜 d}
  {ha' : a' ∈ 𝒜 d'} {hb' : b' ∈ 𝒜 d'} {hU : U ≤ Proj.basicOpen 𝒜 b}
  {hU' : U ≤ Proj.basicOpen 𝒜 b'} in

theorem _root_.GlobalTheory.ProjFrac.frac_add {a₂ : A} {ha₂ : a₂ ∈ 𝒜 d} :
    _root_.GlobalTheory.ProjFrac.frac 𝒜 U (a + a₂) b (add_mem ha ha₂) hb hU =
      _root_.GlobalTheory.ProjFrac.frac 𝒜 U a b ha hb hU +
        _root_.GlobalTheory.ProjFrac.frac 𝒜 U a₂ b ha₂ hb hU := by
  refine _root_.GlobalTheory.ProjFrac.ext fun x hx => ?_
  rw [map_add, _root_.GlobalTheory.ProjFrac.ev_frac, _root_.GlobalTheory.ProjFrac.ev_frac,
    _root_.GlobalTheory.ProjFrac.ev_frac, Localization.add_mk_self]

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite in
variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] in
variable {𝒜} in
variable {U V : (Proj 𝒜).Opens} {d d' : ℕ} {a b a' b' : A} {ha : a ∈ 𝒜 d} {hb : b ∈ 𝒜 d}
  {ha' : a' ∈ 𝒜 d'} {hb' : b' ∈ 𝒜 d'} {hU : U ≤ Proj.basicOpen 𝒜 b}
  {hU' : U ≤ Proj.basicOpen 𝒜 b'} in

theorem _root_.GlobalTheory.ProjFrac.frac_self :
    _root_.GlobalTheory.ProjFrac.frac 𝒜 U b b hb hb hU = 1 := by
  refine _root_.GlobalTheory.ProjFrac.ext fun x hx => ?_
  rw [map_one, _root_.GlobalTheory.ProjFrac.ev_frac]
  exact Localization.mk_self (⟨b, hU hx⟩ : x.asHomogeneousIdeal.toIdeal.primeCompl)

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite in
variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] in
variable {𝒜} in
variable {U V : (Proj 𝒜).Opens} {d d' : ℕ} {a b a' b' : A} {ha : a ∈ 𝒜 d} {hb : b ∈ 𝒜 d}
  {ha' : a' ∈ 𝒜 d'} {hb' : b' ∈ 𝒜 d'} {hU : U ≤ Proj.basicOpen 𝒜 b}
  {hU' : U ≤ Proj.basicOpen 𝒜 b'} in

theorem _root_.GlobalTheory.ProjFrac.frac_zero :
    _root_.GlobalTheory.ProjFrac.frac 𝒜 U 0 b (zero_mem _) hb hU = 0 := by
  refine _root_.GlobalTheory.ProjFrac.ext fun x hx => ?_
  rw [map_zero, _root_.GlobalTheory.ProjFrac.ev_frac, Localization.mk_zero]

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite in
variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] in
variable {𝒜} in
variable {U V : (Proj 𝒜).Opens} {d d' : ℕ} {a b a' b' : A} {ha : a ∈ 𝒜 d} {hb : b ∈ 𝒜 d}
  {ha' : a' ∈ 𝒜 d'} {hb' : b' ∈ 𝒜 d'} {hU : U ≤ Proj.basicOpen 𝒜 b}
  {hU' : U ≤ Proj.basicOpen 𝒜 b'} in

theorem _root_.GlobalTheory.ProjFrac.frac_pow (n : ℕ) :
    _root_.GlobalTheory.ProjFrac.frac 𝒜 U a b ha hb hU ^ n =
      _root_.GlobalTheory.ProjFrac.frac 𝒜 U (a ^ n) (b ^ n) (SetLike.pow_mem_graded n ha)
        (SetLike.pow_mem_graded n hb) (fun x hx h => hU hx (x.isPrime.mem_of_pow_mem n h)) := by
  refine _root_.GlobalTheory.ProjFrac.ext fun x hx => ?_
  rw [map_pow, _root_.GlobalTheory.ProjFrac.ev_frac, Localization.mk_pow]
  exact (_root_.GlobalTheory.ProjFrac.ev_frac (a := a ^ n) (b := b ^ n)
    (ha := SetLike.pow_mem_graded n ha) (hb := SetLike.pow_mem_graded n hb)
    (hU := fun x hx h => hU hx (x.isPrime.mem_of_pow_mem n h)) x hx).symm

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite in
variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] in
variable {𝒜} in
variable {U V : (Proj 𝒜).Opens} {d d' : ℕ} {a b a' b' : A} {ha : a ∈ 𝒜 d} {hb : b ∈ 𝒜 d}
  {ha' : a' ∈ 𝒜 d'} {hb' : b' ∈ 𝒜 d'} {hU : U ≤ Proj.basicOpen 𝒜 b}
  {hU' : U ≤ Proj.basicOpen 𝒜 b'} in

theorem _root_.GlobalTheory.ProjFrac.basicOpen_frac :
    (Proj 𝒜).basicOpen (_root_.GlobalTheory.ProjFrac.frac 𝒜 U a b ha hb hU) =
      U ⊓ Proj.basicOpen 𝒜 a := by
  ext x
  constructor
  · intro hx
    have hVU : (Proj 𝒜).basicOpen (_root_.GlobalTheory.ProjFrac.frac 𝒜 U a b ha hb hU) ≤ U :=
      (Proj 𝒜).basicOpen_le _
    have hxU : x ∈ U := hVU hx
    have hres : IsUnit (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG (Proj 𝒜) hVU (_root_.GlobalTheory.ProjFrac.frac 𝒜 U a b ha hb hU)) :=
      (Proj 𝒜).toRingedSpace.isUnit_res_basicOpen _
    have hunit := hres.map (_root_.GlobalTheory.ProjFrac.ev 𝒜 _ x hx)
    have heq : _root_.GlobalTheory.ProjFrac.ev 𝒜 _ x hx
        (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG (Proj 𝒜) hVU (_root_.GlobalTheory.ProjFrac.frac 𝒜 U a b ha hb hU)) =
        Localization.mk a ⟨b, hU hxU⟩ :=
      (_root_.GlobalTheory.ProjFrac.ev_resG hVU x hx _).trans
        (_root_.GlobalTheory.ProjFrac.ev_frac x hxU)
    rw [heq] at hunit
    have hnum : IsUnit (algebraMap A (Localization.AtPrime x.asHomogeneousIdeal.toIdeal) a) := by
      rw [← IsLocalization.mk'_spec (Localization.AtPrime x.asHomogeneousIdeal.toIdeal) a
        (⟨b, hU hxU⟩ : x.asHomogeneousIdeal.toIdeal.primeCompl), ← Localization.mk_eq_mk']
      exact hunit.mul (IsLocalization.map_units _ _)
    exact ⟨hxU, (IsLocalization.AtPrime.isUnit_to_map_iff _ _ a).1 hnum⟩
  · rintro ⟨hxU, hxa⟩
    have hWU : U ⊓ Proj.basicOpen 𝒜 a ≤ U := inf_le_left
    have hunit : IsUnit (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG (Proj 𝒜) hWU
        (_root_.GlobalTheory.ProjFrac.frac 𝒜 U a b ha hb hU)) := by
      rw [_root_.GlobalTheory.ProjFrac.resG_frac]
      exact IsUnit.of_mul_eq_one (_root_.GlobalTheory.ProjFrac.frac 𝒜 _ b a hb ha inf_le_right)
        ((_root_.GlobalTheory.ProjFrac.frac_mul_eq (a'' := a) (b'' := a) (ha'' := ha) (hb'' := ha)
          (hU'' := inf_le_right) (by ring)).trans _root_.GlobalTheory.ProjFrac.frac_self)
    have hb := (Proj 𝒜).basicOpen_of_isUnit hunit
    have hx : x ∈ U ⊓ Proj.basicOpen 𝒜 a := ⟨hxU, hxa⟩
    rw [← hb] at hx
    exact ((Proj 𝒜).basicOpen_res _ (homOfLE hWU).op ▸ hx).2

end

variable (𝒜) in

def fracUnit (U : (Proj 𝒜).Opens) {d : ℕ} (a b : A) (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 d)
    (hUa : U ≤ Proj.basicOpen 𝒜 a) (hUb : U ≤ Proj.basicOpen 𝒜 b) : Γ(Proj 𝒜, U)ˣ where
  val := frac 𝒜 U a b ha hb hUb
  inv := frac 𝒜 U b a hb ha hUa
  val_inv := (frac_mul_eq (by ring)).trans (frac_self (hb := ha) (hU := hUa))
  inv_val := (frac_mul_eq (by ring)).trans (frac_self (hb := ha) (hU := hUa))

theorem awayToSection_mk {f a : A} {d : ℕ} (hf : f ∈ 𝒜 d) (n : ℕ) (ha : a ∈ 𝒜 (n • d)) :
    (Proj.awayToSection 𝒜 f).hom (HomogeneousLocalization.Away.mk 𝒜 hf n a ha) =
      frac 𝒜 (Proj.basicOpen 𝒜 f) a (f ^ n) ha (SetLike.pow_mem_graded n hf)
        (fun x hx h => hx (x.isPrime.mem_of_pow_mem n h)) := rfl

theorem awayToSection_fromZero (f : A) (a : 𝒜 0) :
    (Proj.awayToSection 𝒜 f).hom (HomogeneousLocalization.fromZeroRingHom 𝒜 _ a) =
      frac 𝒜 (Proj.basicOpen 𝒜 f) a 1 a.2 (SetLike.one_mem_graded 𝒜) (by simp) := rfl

section Map

variable {B τ : Type} [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] {ℬ : ℕ → τ} [GradedRing ℬ]
  (φ : 𝒜 →+*ᵍ ℬ) (hφ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ)

theorem map_app_frac (U : (Proj 𝒜).Opens) {d : ℕ} (a b : A) (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 d)
    (hU : U ≤ Proj.basicOpen 𝒜 b) :
    ((Proj.map φ hφ).app U).hom (frac 𝒜 U a b ha hb hU) =
      frac ℬ (Proj.map φ hφ ⁻¹ᵁ U) (φ a) (φ b) (φ.2 ha) (φ.2 hb) (fun _ hx => hU hx) := by
  refine Subtype.ext <| funext fun p ↦ ?_
  change HomogeneousLocalization.mk _ = .mk _
  ext
  simp

end Map

end GlobalTheory.ProjFrac
