import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNatCastRes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedSpecialFibreGlobalField

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel
open GlobalTheory.UnitGlue

namespace GlobalTheory.UnitGlue

open GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits

theorem natCast_eq_zero_reducedSpecialFibre {F : Type} [Field F] (V : ValuationSubring F)
    [IsDiscreteValuationRing V] (p : ℕ) (hp : (p : F) ∈ V.nonunits) {X : Scheme.{0}} (s : X ⟶ Sp V)
    (U : (reducedSpecialFibre s).Opens) : (p : Γ(reducedSpecialFibre s, U)) = 0 := by
  obtain ⟨ha, hm⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.1 hp
  have hpV : ((p : V) : V) ∈ IsLocalRing.maximalIdeal V := by
    convert hm using 1
    ext
    simp
  have hk : (p : IsLocalRing.ResidueField V) = 0 := by
    rw [← map_natCast (IsLocalRing.residue V) p]
    exact (IsLocalRing.residue_eq_zero_iff _).2 hpV
  let q : reducedSpecialFibre s ⟶ Spec (.of (IsLocalRing.ResidueField V)) :=
    (specialFibre s).nilradical.subschemeι ≫ pullback.snd _ _
  have e : (p : Γ(reducedSpecialFibre s, U)) =
      ((reducedSpecialFibre s).presheaf.map (homOfLE le_top).op).hom
        (q.appTop.hom ((Scheme.ΓSpecIso (.of (IsLocalRing.ResidueField V))).inv.hom
          (p : IsLocalRing.ResidueField V))) := by
    simp only [map_natCast]
  rw [e, hk]
  simp only [map_zero]

theorem pullU_reducedSpecialι_eq_one {F : Type} [Field F] (V : ValuationSubring F)
    [IsDiscreteValuationRing V] (p : ℕ) (hp : (p : F) ∈ V.nonunits) {X : Scheme.{0}} (s : X ⟶ Sp V)
    (W : X.Opens) (u : Γ(X, W)ˣ) (hu : ((u : Γ(X, W)) - 1) ∈ (Ideal.span {(p : Γ(X, W))}).radical) :
    pullU (reducedSpecialι s) W u = 1 := by
  haveI : IsReduced (reducedSpecialFibre s) := GlobalTheory.RedFibreField.isReduced_nilradical_subscheme _
  obtain ⟨n, hn⟩ := hu
  rw [Ideal.mem_span_singleton] at hn
  have h0 : (((reducedSpecialι s).app W).hom (u : Γ(X, W)) - 1) ^ n = 0 := by
    have hd := map_dvd ((reducedSpecialι s).app W).hom hn
    rw [map_natCast, natCast_eq_zero_reducedSpecialFibre V p hp s, map_pow, map_sub, map_one] at hd
    exact zero_dvd_iff.1 hd
  have h1 : ((reducedSpecialι s).app W).hom (u : Γ(X, W)) - 1 = 0 :=
    IsReduced.eq_zero _ ⟨n, h0⟩
  ext
  exact sub_eq_zero.1 h1

theorem gU_ratioProp {p : ℕ} [Fact p.Prime] {X : Scheme.{0}} {Xw : X.Opens}
    {K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]} (h : ∀ x : X, UnitChartAt p Xw K x) (x y : X)
    (hR : ∃ u, RatioProp h x y u) : RatioProp h x y (gU h x y) := by
  unfold gU
  rw [dif_pos hR]
  exact hR.choose_spec

theorem glueLB_reducedSpecial_gen : ∀ (F : Type) [Field F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (h : ∀ x : X, UnitChartAt p Xw K x), (∀ x y : X, ∃ u, RatioProp h x y u) → ∃ t : ((glueLB h).pull (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.reducedSpecialι s)).Gen, t.IsGen := by
  intro F _ V _ p _ hp X s Xw K h hR
  refine ⟨⟨fun _ => 1⟩, ?_⟩
  intro i j
  rw [map_one, map_one, _root_.mul_one]
  symm
  have key : ∀ (W : (reducedSpecialFibre s).Opens) (k : PUnit)
      (hh : W ≤ reducedSpecialι s ⁻¹ᵁ ((glueLB h).U (i k) ⊓ (glueLB h).U (j k))),
      res hh (pullU (reducedSpecialι s) _ ((glueLB h).g (i k) (j k))) ^ (1 : ℤ) = 1 := by
    intro W k hh
    rw [pullU_reducedSpecialι_eq_one V p hp s (W := (glueLB h).U (i k) ⊓ (glueLB h).U (j k))
      (u := (glueLB h).g (i k) (j k)) (gU_ratioProp h _ _ (hR _ _)).2, map_one, one_zpow]
  exact @Finset.prod_eq_one PUnit (Γ(reducedSpecialFibre s,
    LB.wchart (glueLB h) (fun _ : PUnit => reducedSpecialι s) i ⊓
      LB.wchart (glueLB h) (fun _ : PUnit => reducedSpecialι s) j)ˣ) Finset.univ _ _ (fun k _ => key _ k _)

end GlobalTheory.UnitGlue
