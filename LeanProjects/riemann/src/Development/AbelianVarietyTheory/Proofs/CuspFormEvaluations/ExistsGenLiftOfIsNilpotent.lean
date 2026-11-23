import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen

noncomputable section

namespace GlobalTheory.NilGen

section General

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LBGerm

variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Z ⟶ X)} {ε' : K' → ℤ}

theorem exists_ratio (hL : L.IsLB) (p : Z ⟶ Y) (g : LB.Gen (LB.LinComb L φ' ε')) (hg : g.IsGen)
    (hF : FormEq (fun k => p ≫ φ k) ε φ' ε') (u : LB.Sec (LB.LinComb L φ ε)) :
    ∃ h : Γ(Z, ⊤), ∀ y J, Good L y J → sval u p y J = gs (𝟙 Z) y ⊤ h * (val g (𝟙 Z) y J).val := by
  obtain ⟨t, ht⟩ := exists_sec hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [hF U h, mul_inv_cancel])
    (pullMulSec u p (LB.invGen L _ _ g) (DVR.invGen_isGen _ _ _ _ hg))
  have le : (⊤ : Z.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Z ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨(Z.presheaf.map (homOfLE le).op).hom (t.f PEmpty.elim), fun y J hJ => ?_⟩
  have e := ht Z (𝟙 Z) y J hJ
  rw [sval_pullMulSec _ _ _ _ _ _ hJ, val_inv, Category.id_comp,
    sval_of t (𝟙 Z) y J PEmpty.elim (fun k => k.elim)] at e
  refine Eq.trans ?_ (congrArg₂ (· * ·) ((gs_res (𝟙 Z) y le trivial _).trans e).symm rfl)
  exact (Units.inv_mul_cancel_right _ _).symm

def ratioIdeal (p : Z ⟶ Y) (hp : Function.Surjective p.appTop.hom) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (g : LB.Gen (LB.LinComb L φ' ε')) : Ideal Γ(Z, ⊤) where
  carrier := {h | ∃ u : LB.Sec (LB.LinComb L φ ε),
    ∀ y J, Good L y J → sval u p y J = gs (𝟙 Z) y ⊤ h * (val g (𝟙 Z) y J).val}
  zero_mem' := ⟨DVR.SecOps.secZero, fun y J hJ => by
    rw [gs_zero (𝟙 Z) y ⊤ trivial, zero_mul]
    exact gs_zero p y _ (hJ.mem φ p)⟩
  add_mem' := by
    rintro a b ⟨u, hu⟩ ⟨v, hv⟩
    refine ⟨DVR.SecOps.secAdd u v, fun y J hJ => ?_⟩
    rw [gs_add (𝟙 Z) y ⊤ trivial, add_mul, ← hu y J hJ, ← hv y J hJ]
    exact gs_add p y _ (hJ.mem φ p) _ _
  smul_mem' := by
    rintro c a ⟨u, hu⟩
    obtain ⟨c, rfl⟩ := hp c
    refine ⟨DVR.SecOps.secScale c u, fun y J hJ => ?_⟩
    rw [smul_eq_mul, gs_mul (𝟙 Z) y ⊤ trivial, mul_assoc, ← hu y J hJ]
    refine (gs_mul p y _ (hJ.mem φ p) _ _).trans (congrArg₂ (· * ·) ?_ rfl)
    refine (gs_res p y le_top (hJ.mem φ p) c).trans ?_
    exact ((gs_pull (𝟙 Z) p y ⊤ trivial c).trans (by rw [Category.id_comp])).symm

theorem ratioIdeal_eq_top [IsAffine Y] [IsAffine Z] (hL : L.IsLB) (p : Z ⟶ Y)
    (hp : Function.Surjective p.appTop.hom) (g : LB.Gen (LB.LinComb L φ' ε')) (hg : g.IsGen)
    (hF : FormEq (fun k => p ≫ φ k) ε φ' ε') : ratioIdeal p hp φ ε g = ⊤ := by
  have hM : (LB.LinComb L φ ε).IsLB := DVR.linComb_isLB _ hL _ _
  rw [← Ideal.span_eq (ratioIdeal p hp φ ε g), ← (isAffineOpen_top Z).iSup_basicOpen_eq_self_iff]
  refine top_unique fun y _ => ?_
  obtain ⟨k, hk⟩ := exists_chart hM (p y)
  obtain ⟨r, hr, hy⟩ := (isAffineOpen_top Y).exists_basicOpen_le (V := (LB.LinComb L φ ε).U k) ⟨p y, hk⟩ trivial
  obtain ⟨u, hu⟩ := exists_sec_nonzeroLocus_eq_basicOpen hM r k hr
  obtain ⟨h, hh⟩ := exists_ratio hL p g hg hF u
  refine Opens.mem_iSup.2 ⟨⟨h, u, hh⟩, ?_⟩
  choose J hJ using fun χ : Z ⟶ X => exists_chart hL (χ y)
  have h₁ : IsUnit (sval u p y J) :=
    (mem_nonzeroLocus_iff_pull u p y (k := fun k => J (p ≫ φ k)) (Good.mem hJ φ p)).1 (hu.ge hy)
  rw [hh y J hJ] at h₁
  exact (isUnit_gs_iff (𝟙 Z) y ⊤ trivial h).1 (isUnit_of_mul_isUnit_left h₁)

theorem exists_gen_lift [IsAffine Y] [IsAffine Z] (hL : L.IsLB) (p : Z ⟶ Y)
    (hp : Function.Surjective p.appTop.hom) (hp' : Function.Surjective p) (g : LB.Gen (LB.LinComb L φ' ε'))
    (hg : g.IsGen) (hF : FormEq (fun k => p ≫ φ k) ε φ' ε') :
    ∃ g' : LB.Gen (LB.LinComb L φ ε), g'.IsGen ∧ LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε g' p) g := by
  obtain ⟨u, hu⟩ : (1 : Γ(Z, ⊤)) ∈ ratioIdeal p hp φ ε g := by
    rw [ratioIdeal_eq_top hL p hp g hg hF]; trivial
  have hu' : ∀ y J, Good L y J → sval u p y J = (val g (𝟙 Z) y J).val := fun y J hJ => by
    rw [hu y J hJ, gs_eq (𝟙 Z) y ⊤ trivial, map_one, map_one, one_mul]
  have hn : ∀ x, x ∈ nonzeroLocus u := fun x => by
    obtain ⟨y, rfl⟩ := hp' x
    choose J hJ using fun χ : Z ⟶ X => exists_chart hL (χ y)
    refine (mem_nonzeroLocus_iff_pull u p y (k := fun k => J (p ≫ φ k)) (Good.mem hJ φ p)).2 ?_
    exact (congrArg IsUnit (hu' y J hJ)).mpr (Units.isUnit _)
  have hun : ∀ j, IsUnit (u.f j) := fun j => Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => by
    have := (mem_nonzeroLocus_iff_isUnit u hx).1 (hn x)
    rw [gs_eq (𝟙 Y) x _ hx] at this
    exact this
  refine ⟨⟨fun j => (hun j).unit⟩, fun i j => Units.ext (u.compat i j), corr_of_val hL fun y J hJ => ?_⟩
  rw [val_pull hJ, Category.id_comp]
  exact Units.ext ((gs_unit p y _ (hJ.mem φ p) _).symm.trans (hu' y J hJ))

theorem surjective_appTop_spMap {A B : Type} [CommRing A] [CommRing B] (π : A →+* B) (hπ : Function.Surjective π) :
    Function.Surjective (spMap π).appTop.hom := by
  have e : (spMap π).appTop = (Scheme.ΓSpecIso _).hom ≫ CommRingCat.ofHom π ≫ (Scheme.ΓSpecIso _).inv := by
    rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [e, CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.coe_comp, RingHom.coe_comp]
  exact ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).inv).2.comp hπ).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom).2

theorem surjective_spMap {A B : Type} [CommRing A] [CommRing B] (π : A →+* B) (hπ : Function.Surjective π)
    (hn : IsNilpotent (RingHom.ker π)) : Function.Surjective (spMap π) := fun x => by
  have hx : x ∈ PrimeSpectrum.zeroLocus (RingHom.ker π : Set A) := fun a ha => by
    obtain ⟨n, hn⟩ := hn
    have h : a ^ n ∈ RingHom.ker π ^ n := Ideal.pow_mem_pow ha n
    rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at h
    exact x.isPrime.mem_of_pow_mem n (h ▸ x.asIdeal.zero_mem)
  rw [← range_comap_of_surjective B π hπ] at hx
  exact hx

end General

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

theorem exists_gen_lift_of_isNilpotent : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (A B : Type) [CommRing A] [CommRing B] (π : A →+* B), Function.Surjective π → IsNilpotent (RingHom.ker π) → ∀ (K : Type) [Fintype K] (φ : K → (Sp A ⟶ X)) (ε : K → ℤ) (K' : Type) [Fintype K'] (φ' : K' → (Sp B ⟶ X)) (ε' : K' → ℤ) (g : LB.Gen (LB.LinComb L φ' ε')), g.IsGen → (∀ (U : Type) [CommGroup U] (h : (Sp B ⟶ X) → U), ∏ k, h (spMap π ≫ φ k) ^ ε k = ∏ k, h (φ' k) ^ ε' k) → ∃ g' : LB.Gen (LB.LinComb L φ ε), g'.IsGen ∧ LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε g' (spMap π)) g :=
  fun _ _ hL _ _ _ _ π hπ hn _ _ _ _ _ _ _ _ g hg hF =>
    exists_gen_lift hL (spMap π) (surjective_appTop_spMap π hπ) (surjective_spMap π hπ hn) g hg hF

end GlobalTheory.NilGen
