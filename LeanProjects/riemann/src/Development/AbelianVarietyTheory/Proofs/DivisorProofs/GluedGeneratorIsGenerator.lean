import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNatCastRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer

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

theorem mem_genericι_preimage_Xp (F : Type) [Field F] [NumberField F] (V : ValuationSubring F)
    [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (s : X ⟶ Sp V)
    (y : genericFibre s) : y ∈ genericι s ⁻¹ᵁ Xp X p := by
  have hK : IsUnit ((p : ℕ) : FractionRing V) := by
    refine IsUnit.mk0 _ ?_
    rw [← map_natCast (algebraMap V (FractionRing V))]
    refine (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 ?_
    intro h0
    have := congrArg (fun v : V => (v : F)) h0
    simp at this
    exact (Fact.out : p.Prime).ne_zero this
  have hU : IsUnit ((p : ℕ) : Γ(genericFibre s, genericι s ⁻¹ᵁ ⊤)) := by
    have := hK.map (((genericFibre s).presheaf.map
      (homOfLE (le_top : genericι s ⁻¹ᵁ ⊤ ≤ genericStr s ⁻¹ᵁ ⊤)).op).hom.comp
      (((genericStr s).app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom))
    simpa only [map_natCast] using this
  show y ∈ genericι s ⁻¹ᵁ X.basicOpen ((p : ℕ) : Γ(X, ⊤))
  rw [Scheme.preimage_basicOpen, map_natCast, Scheme.basicOpen_of_isUnit _ hU]
  trivial

theorem germ_res_res_pull {X Y : Scheme.{0}} (f : Y ⟶ X) {A : X.Opens} {W W' : Y.Opens} (h1 : W ≤ W')
    (h2 : W' ≤ f ⁻¹ᵁ A) (c : Γ(X, A)ˣ) (y : Y) (hy : y ∈ W) :
    ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU y hy (res h1 (res h2 (pullU f A c))) =
      Units.map (f.stalkMap y).hom (ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU (f.base y) (h2 (h1 hy)) c) := by
  rw [ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU_res, ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU_res,
    ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU_pullU]

theorem germ_res_pull {X Y : Scheme.{0}} (f : Y ⟶ X) {A : X.Opens} {W : Y.Opens}
    (h2 : W ≤ f ⁻¹ᵁ A) (c : Γ(X, A)ˣ) (y : Y) (hy : y ∈ W) :
    ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU y hy (res h2 (pullU f A c)) =
      Units.map (f.stalkMap y).hom (ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU (f.base y) (h2 hy) c) := by
  rw [ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU_res, ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU_pullU]

theorem sigGen_isGen_of_ratio : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (h : ∀ x : X, UnitChartAt p Xw K x), (∀ x y : X, ∃ u, RatioProp h x y u) → (sigGen h s).IsGen := by
  intro F _ _ V _ p _ X s Xw K h hR
  have hc : ∀ j : PUnit → X, LB.wchart (glueLB h) (fun _ : PUnit => genericι s) j ≤
      genericι s ⁻¹ᵁ (Uc h (j PUnit.unit) ⊓ Xp X p) := fun j y hy =>
    ⟨Set.mem_iInter.1 hy PUnit.unit, mem_genericι_preimage_Xp F V p X s y⟩
  intro (i : PUnit → X) (j : PUnit → X)
  have hsi : (sigGen h s).s i = res (hc i) (pullU (genericι s) _ (Cx h (i PUnit.unit))) := dif_pos (hc i)
  have hsj : (sigGen h s).s j = res (hc j) (pullU (genericι s) _ (Cx h (j PUnit.unit))) := dif_pos (hc j)
  have hg : GlobalTheory.UnitGlue.gU h (i PUnit.unit) (j PUnit.unit) = (hR (i PUnit.unit) (j PUnit.unit)).choose :=
    dif_pos (hR _ _)
  have hr := ((hR (i PUnit.unit) (j PUnit.unit)).choose_spec).1
  rw [← hg] at hr
  rw [hsi, hsj]
  apply ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.unit_ext
  intro y hy
  have hxi : (genericι s).base y ∈ Uc h (i PUnit.unit) := Set.mem_iInter.1 hy.1 PUnit.unit
  have hxj : (genericι s).base y ∈ Uc h (j PUnit.unit) := Set.mem_iInter.1 hy.2 PUnit.unit
  have hx : (genericι s).base y ∈ Uc h (i PUnit.unit) ⊓ Uc h (j PUnit.unit) ⊓ Xp X p := ⟨⟨hxi, hxj⟩, mem_genericι_preimage_Xp F V p X s y⟩
  have hr' := congrArg (ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU _ hx) hr
  simp only [map_mul, ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU_res] at hr'
  have hle : ((glueLB h).pull (genericι s)).U i ⊓ ((glueLB h).pull (genericι s)).U j ≤
      genericι s ⁻¹ᵁ (Uc h (i PUnit.unit) ⊓ Uc h (j PUnit.unit)) := fun z hz =>
    ⟨Set.mem_iInter.1 hz.1 PUnit.unit, Set.mem_iInter.1 hz.2 PUnit.unit⟩
  have hgl : ((glueLB h).pull (genericι s)).g i j =
      res hle (pullU (genericι s) _ (GlobalTheory.UnitGlue.gU h (i PUnit.unit) (j PUnit.unit))) :=
    by
      have e := Fintype.prod_unique (fun k : PUnit => (res (fun z hz => ⟨Set.mem_iInter.1 hz.1 k, Set.mem_iInter.1 hz.2 k⟩ :
        LB.wchart (glueLB h) (fun _ : PUnit => genericι s) i ⊓ LB.wchart (glueLB h) (fun _ : PUnit => genericι s) j ≤
          genericι s ⁻¹ᵁ (Uc h (i k) ⊓ Uc h (j k)))
        (pullU (genericι s) (Uc h (i k) ⊓ Uc h (j k)) (GlobalTheory.UnitGlue.gU h (i k) (j k)))) ^ (1:ℤ))
      exact e.trans (zpow_one _)
  rw [hgl, map_mul]
  refine (germ_res_res_pull (genericι s) _ _ _ y hy).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) (germ_res_pull (genericι s) hle _ y hy).symm
    (germ_res_res_pull (genericι s) _ _ _ y hy).symm)
  rw [← map_mul, ← hr']

end GlobalTheory.UnitGlue
