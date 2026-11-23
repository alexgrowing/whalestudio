import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelPAdicComparisonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BLieLieComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentEvLieOfLieTie

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatModel

theorem eq_one_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S'}
    (z : Over.mk (T.hom ≫ f) ⟶ G) (hz : z.left = (1 : T ⟶ G').left ≫ φ) : z = 1 := by
  have e := h.2 T 1 1 z z hz hz
  rw [_root_.mul_one, ← hz] at e
  exact _root_.mul_eq_left.1 (Over.OverMorphism.ext e)

theorem lieTie_lieComb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (S0 : Scheme.{0})
    (t : SAB H S0) (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p) (x0 : Sp ℂ_[p] ⟶ S0)
    (ψ' : P.A.A.left ⟶ t.G.left), IsGrpPullback P.A.A t.G x0 ψ' →
    ∀ (m : ℕ) (xs : Fin m → LieG P.Gt) (us : Fin m → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)) (a : Fin m → 𝓞_ℂ_[p])
      (u : Sp (DualNumber ℂ_[p]) ⟶ t.G.left), (∀ i, LieTie P ψ' (xs i) (us i)) →
      IsCombAtG t x0 us (fun i => algebraMap 𝓞_ℂ_[p] ℂ_[p] (a i)) u → LieTie P ψ' (lieComb P.Gt a xs) u := by
  intro E _ _ _ H S0 t p _ _ P x0 ψ' hψ m
  induction m with
  | zero =>
    intro xs us a u _ hc
    obtain ⟨w, -, hw⟩ := hc
    rw [List.ofFn_zero, List.prod_nil] at hw
    subst hw
    refine ⟨lieZero P.G, 1, Corr.one, ?_, ?_⟩
    · have e := eq_one_of_isGrpPullback hψ (pushPt hψ.1.w (1 : specO ℂ_[p] (DualNumber ℂ_[p]) ⟶ P.A.A)) rfl
      exact congrArg (fun z => z.left) e
    · let d : Over.mk ((specO ℂ_[p] (DualNumber ℂ_[p])).hom ≫ spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ⟶
          specO 𝓞_ℂ_[p] (DualNumber 𝓞_ℂ_[p]) :=
        Over.homMk (spMap (dualMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]))) (by
          refine (spMap_spMap _ _).trans (Eq.trans (congrArg _ ?_) (spMap_spMap _ _).symm)
          ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
      have e2 := eq_one_of_isGrpPullback P.gen_pull
        (pushPt P.gen_pull.1.w (1 : specO ℂ_[p] (DualNumber ℂ_[p]) ⟶ P.A.A)) rfl
      have e3 : d ≫ (1 : specO 𝓞_ℂ_[p] (DualNumber 𝓞_ℂ_[p]) ⟶ P.G) =
          pushPt P.gen_pull.1.w (1 : specO ℂ_[p] (DualNumber ℂ_[p]) ⟶ P.A.A) := by
        rw [e2, MonObj.comp_one]
      exact (congrArg (fun z => z.left) e3).symm
  | succ m ih =>
    intro xs us a u hx hc
    obtain ⟨w, hw1, hw2⟩ := hc
    rw [List.ofFn_succ, List.prod_cons] at hw2
    subst hw2
    rw [lieComb_succ]
    have h0 : LieTie P ψ' (AvDefs.lieScale P.Gt (a 0) (xs 0)) (w 0).left := by
      rw [hw1 0]; exact (hx 0).scale (a 0)
    have ht := ih (Fin.tail xs) (Fin.tail us) (Fin.tail a) _ (fun i => hx i.succ)
      ⟨fun i => w i.succ, fun i => hw1 i.succ, rfl⟩
    exact TieIndep.lieTie_add hψ h0 ht

end GlobalTheory.FlatModel

end
