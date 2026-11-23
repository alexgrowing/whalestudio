import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionIntegralSectionIntegralNoetherianLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartExpOn
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioEqRefl
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.SecExp

open ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_restrict' {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (h : Z ⟶ Y) (φ' : K → (Z ⟶ X)) (hφ : ∀ k, φ' k = h ≫ φ k) (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃ t : LB.Sec (LB.LinComb L φ' ε), GeneratorPullback.SecScal L φ' ε t φ ε s h 1 := by
  obtain rfl : φ' = fun k => h ≫ φ k := funext hφ
  refine ⟨DVR.pullSec L φ ε s h, fun j₁ j₂ hco => ?_⟩
  obtain rfl : j₁ = j₂ := funext fun k => hco (Sum.inl k) (Sum.inr k) rfl
  rw [resTop, map_one, _root_.one_mul]
  exact (DVR.rs_rs _ _ _).symm

theorem exists_intFam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ k : ℕ, 3 ≤ k → ∀ s : H0 U.LG.L k, ∃ f : IntFam (maximalIdeal R) D.toPre k, ∀ e : ℕ, U.ExpandsAt e k s f.f := by
  intro R _ _ _ hB D A G _ _ hG U k hk s
  have hR : AdmBase R (maximalIdeal R) := hB.1
  have : IsNoetherianRing R := hR.1
  obtain ⟨sK, hsK⟩ := exists_restrict' U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ))
    (pullback.fst G.hom (jK R)) (fun _ => pullback.fst G.hom (jK R)) (fun _ => (Category.comp_id _).symm) s
  obtain ⟨E, hE, -⟩ := (U.expand k (by omega)).1 sK
  obtain ⟨g, hg, hext⟩ := GlobalTheory.IntegralExpansionLocal.main R (maximalIdeal R) le_rfl D A G U.toUnifPre k s sK hsK E hE
  have h1 : scal (DegPre.BF D.toPre (FractionRing R)).hom (1 : R) = 1 := by
    unfold scal; rw [map_one, map_one]
  refine ⟨⟨E, g, fun α => h1 ▸ hext α, fun e => ?_⟩, hg⟩
  obtain ⟨S, hS, -⟩ := hg e
  refine S.finite_toSet.subset fun α hα => by_contra fun h => hα fun j => ?_
  have := (U.gt e).q_flat
  have := (U.gt e).q_surj
  apply ReciprocityTheory.ChartRestriction.G.DVR.TG.app_injective_of_flat_surj (U.gt e).q.left
  rw [map_zero]
  have h' := hS α h j
  have e' : (U.gt e).pG.left = (U.gt e).q.left ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e) := rfl
  rw [e', Scheme.Hom.comp_app] at h'
  exact h'

end GlobalTheory.Mum.SecExp
