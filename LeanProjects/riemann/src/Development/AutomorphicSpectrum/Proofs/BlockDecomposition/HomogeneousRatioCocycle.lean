import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ConeSite
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.SeamDefs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.ConeYq

theorem awayMap_ratio_trans {K : Type} [Field K] {N e : ℕ} {a b c : MvPolynomial (Fin (N + 1)) K}
    (hb : b ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K e)
    (hc : c ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K e)
    (ha1 : a ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (1 • e))
    (hb1 : b ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (1 • e)) :
    HomogeneousLocalization.awayMap (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) hc (x := b * c) rfl
        (HomogeneousLocalization.Away.mk _ hb 1 a ha1) *
      HomogeneousLocalization.awayMap (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) hb (x := b * c)
        (mul_comm b c) (HomogeneousLocalization.Away.mk _ hc 1 b hb1) =
    HomogeneousLocalization.awayMap (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) hb (x := b * c)
        (mul_comm b c) (HomogeneousLocalization.Away.mk _ hc 1 a ha1) := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.Away.val_mk]
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, OneMemClass.coe_one, one_mul, pow_one]
  ring

theorem away_self {K : Type} [Field K] {N e : ℕ} {a : MvPolynomial (Fin (N + 1)) K}
    (ha : a ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K e)
    (ha1 : a ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (1 • e)) :
    HomogeneousLocalization.Away.mk _ ha 1 a ha1 = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_one]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp

theorem appLE_awayMap {K : Type} [Field K] {X : Scheme.{0}} {N e : ℕ} (i : X ⟶ PSpace K N)
    {f g x : MvPolynomial (Fin (N + 1)) K}
    (hg : g ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K e) (hx : x = f * g) (W : X.Opens)
    (hW : W ≤ i ⁻¹ᵁ Proj.basicOpen _ x) (hW' : W ≤ i ⁻¹ᵁ Proj.basicOpen _ f)
    (u : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f) :
    (i.appLE _ W hW').hom ((Proj.awayToSection _ f).hom u) =
      (i.appLE _ W hW).hom ((Proj.awayToSection _ x).hom
        (HomogeneousLocalization.awayMap (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) hg hx u)) := by
  have h := congrArg (fun φ => φ.hom u)
    (Proj.awayMap_awayToSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) hg hx)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h
  rw [h]
  exact (congrArg (fun φ => φ.hom ((Proj.awayToSection _ f).hom u)) (Scheme.Hom.map_appLE i hW _)).symm

theorem yQ_mul_yQ {K : Type} [Field K] {X : Scheme.{0}} {N m e : ℕ} (i : X ⟶ PSpace K N)
    (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (a b c : Fin m) (W : X.Opens)
    (ha : W ≤ uy i y a) (hb : W ≤ uy i y b) (hc : W ≤ uy i y c) :
    (i.appLE _ W hb).hom (yQ y hy a b) * (i.appLE _ W hc).hom (yQ y hy b c) = (i.appLE _ W hc).hom (yQ y hy a c) ∧
    (i.appLE _ W ha).hom (yQ y hy a a) = 1 := by
  have mem : ∀ k, y k ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K e :=
    fun k => (MvPolynomial.mem_homogeneousSubmodule e (y k)).2 (hy k)
  have mem1 : ∀ k, y k ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (1 • e) :=
    fun k => by simpa using mem k
  constructor
  · have hW : W ≤ i ⁻¹ᵁ Proj.basicOpen _ (y b * y c) := by
      rw [Proj.basicOpen_mul]
      exact le_inf hb hc
    have e1 : (i.appLE _ W hb).hom (yQ y hy a b) = _ :=
      appLE_awayMap i (mem c) (x := y b * y c) rfl W hW hb
        (HomogeneousLocalization.Away.mk _ (mem b) 1 (y a) (mem1 a))
    have e2 : (i.appLE _ W hc).hom (yQ y hy b c) = _ :=
      appLE_awayMap i (mem b) (x := y b * y c) (mul_comm _ _) W hW hc
        (HomogeneousLocalization.Away.mk _ (mem c) 1 (y b) (mem1 b))
    have e3 : (i.appLE _ W hc).hom (yQ y hy a c) = _ :=
      appLE_awayMap i (mem b) (x := y b * y c) (mul_comm _ _) W hW hc
        (HomogeneousLocalization.Away.mk _ (mem c) 1 (y a) (mem1 a))
    rw [e1, e2, e3, ← map_mul, ← map_mul, awayMap_ratio_trans (mem b) (mem c) (mem1 a) (mem1 b)]
  · have : yQ y hy a a = 1 := by
      unfold yQ
      rw [away_self (mem a) (mem1 a), map_one]
    rw [this, map_one]

end GlobalTheory.CompanionTheory.ConeYq
