import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.Reindex

open GlobalTheory.CatCoh

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] (F : Fam I g Λ) {Λ' : Type} [AddCommGroup Λ'] (A : Λ' →+ Λ)

abbrev fam : Fam I g Λ' := ⟨F.V, F.τ.comp A, fun l ↦ F.hol (A l)⟩

variable {F A} (K' : Charts (fam F A))

@[reducible] def charts : Charts F where
  K := K'.K
  W := K'.W
  base := K'.base
  le m k' k := ∃ l, A l = m ∧ K'.le l k' k
  le_refl k := ⟨0, map_zero A, K'.le_refl k⟩
  le_trans := by
    rintro _ _ k k' k'' ⟨l, rfl, h⟩ ⟨m, rfl, h'⟩
    exact ⟨l + m, map_add A l m, K'.le_trans h h'⟩
  maps := by
    rintro _ k k' ⟨l, rfl, h⟩
    exact K'.maps h

@[reducible] def obj (T : K'.Obj) : (charts K').Obj where
  k := T.k
  C := T.C
  alg := T.alg
  J := T.J
  nil := T.nil
  ρ := T.ρ
  ρ_cst := T.ρ_cst

def hom {T T' : K'.Obj} (f : T ⟶ T') : obj K' T ⟶ obj K' T' where
  φ := f.φ
  deg := A f.deg
  le := ⟨f.deg, rfl, Charts.Hom.le f⟩
  mem := f.mem
  close := f.close

theorem isPeriod_comp : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (u : Unif F s σ) {Λ' : Type} [AddCommGroup Λ'] (A : Λ' →+ Λ) (u' : Unif (⟨F.V, F.τ.comp A, fun l ↦ F.hol (A l)⟩ : Fam I g Λ') s σ), u'.E = u.E → ∀ (c : FirstDeRham s) (per : Λ →+ Hol F.V), IsPeriod u c per → IsPeriod u' c (per.comp A) := by
  intro I _ g Λ _ F B _ X s σ u Λ' _ A u' hE c per h K' r' hr
  let r : Real (charts K') s σ :=
    { x := r'.x
      w := r'.w
      compat := by
        rintro _ k k' ⟨l, rfl, e⟩
        exact r'.compat e }
  have h1 := h (charts K') r (fun k p hp ↦ (hr k p hp).trans (congrFun hE p))
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  obtain ⟨G, hG⟩ := H1.mk_eq_mk.1 h1
  refine H1.mk_eq_mk.2 ⟨fun T ↦ G (obj K' T), ?_⟩
  funext T T' φ
  exact congrFun (congrFun (congrFun hG (obj K' T)) (obj K' T')) (hom K' φ)

end GlobalTheory.AnPer.Reindex
