import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Mum.ZeroFam

theorem gs_zero' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs; split_ifs <;> simp

theorem sval_eq_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (hs : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    sval s r z J = 0 := by
  unfold sval; exact (congrArg (gs r z _) (hs _)).trans (gs_zero' _ _ _)

theorem secB_zero_of_pullB {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') {k : ℕ} (x : D'.X) (b : D.SecB k (hD.xe x))
    (b' : D'.SecB k x) (hb : ∀ j, b.f j = 0) (h : PullB hD x b b') : ∀ q, b'.f q = 0 := by
  intro q
  refine fn_ext fun y hy => ?_
  choose p hp using fun κ => exists_chart D.P.isLB
    ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ((D'.famφB x) κ y))
  have e := h _ (𝟙 _) y p q (fun κ => hp κ) (fun κ => Set.mem_iInter.1 hy κ)
  rw [show b.f p = 0 from hb _] at e
  have e2 := e.symm.trans (gs_zero' _ _ _)
  exact ((Units.mul_right_eq_zero _).1 e2).trans (gs_zero' _ _ _).symm

end GlobalTheory.Mum.ZeroFam

namespace GlobalTheory.Mum.ZeroFam

open GlobalTheory.ExpInt

theorem section_eq_zero_of_expansion_zero_family {W : Type} [CommRing W] [IsDomain W] {I : Ideal W} {D : DegData W I}
    {A : PolAV (Sp (FractionRing W))} {G : Over (Sp W)} [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) {k : ℕ}
    (hk : 1 ≤ k) (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (hf : ∀ α j, (f α).f j = 0)
    (hE : ∀ e, U.ExpandsAt e k σ f) : ∀ j, σ.f j = 0 := by
  have := U.smooth
  have : Flat G.hom := inferInstance
  have ex : ∀ (φ' : Fin 1 → (pullback G.hom (jK W) ⟶ G.left))
      (_ : φ' = fun _ => pullback.fst G.hom (jK W) ≫ 𝟙 G.left),
      ∃ s' : LB.Sec (LB.LinComb U.LG.L φ' (fun _ => (k : ℤ))), ∀ z J, Good U.LG.L z J →
        sval s' (𝟙 _) z J = sval σ (pullback.fst G.hom (jK W)) z J := by
    rintro _ rfl
    exact ⟨pullSec _ _ _ σ _, fun z J hJ => (SectionScalarValuation.sval_pullSec _ _ σ _ (𝟙 _) z hJ).trans (by rw [Category.id_comp])⟩
  obtain ⟨s₀, hs₀⟩ := ex (fun _ => pullback.fst G.hom (jK W)) (funext fun _ => (Category.comp_id _).symm)
  have h1 : scal (pullback.snd G.hom (jK W) ≫ jK W) (1 : W) = 1 := by unfold scal; rw [map_one, map_one]
  have h1' : scal (DegPre.BF D.toPre (FractionRing W)).hom (1 : W) = 1 := by unfold scal; rw [map_one, map_one]
  have hF : ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing W) α) (DegPre.famε k)
      ((0 : Fam D.toPre (FractionRing W) k).s α) (D.toPre.famφB α) (DegPre.famε k) (f α)
      (DegPre.prB D.toPre (FractionRing W)).left (scal (DegPre.BF D.toPre (FractionRing W)).hom 1) := fun α => by
    rw [h1']
    exact SectionScalarValuation.secScal_of_sval D.toPre.P.isLB fun y J _ =>
      (sval_eq_zero _ (hf α) _ y J).trans (sval_eq_zero _ (fun _ => rfl) _ y J).symm
  have hE₀ : ∀ e, U.ExpandsAt e k (SecOps.secZero : H0 U.LG.L k) f := fun e => by
    refine ⟨∅, fun α _ j => by rw [show (f α).f j = 0 from hf α j, map_zero], fun p j₁ jf jt _ _ => ?_⟩
    simp only [Finset.attach_empty, Finset.sum_empty]
    erw [show (SecOps.secZero : H0 U.LG.L k).f j₁ = 0 from rfl, map_zero, map_zero, mul_zero]
  have hEs₀ : U.Expands k s₀ 0 := ⟨1, one_ne_zero, σ, f, by
    rw [h1]
    exact SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J hJ => by rw [Category.id_comp]; exact (hs₀ y J hJ).symm, hF, hE⟩
  have hEz : U.Expands k SecOps.secZero 0 := ⟨1, one_ne_zero, SecOps.secZero, f, by
    rw [h1]
    exact SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J _ =>
      (sval_eq_zero _ (fun _ => rfl) _ y J).trans (sval_eq_zero _ (fun _ => rfl) _ y J).symm, hF, hE₀⟩
  have e₀ : s₀ = SecOps.secZero := ((U.expand k hk).2 0).unique hEs₀ hEz
  have hm := secIsMul_of_generic G U.LG.isLB k SecOps.secZero σ SecOps.secZero 1
    (SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J _ =>
      (sval_eq_zero _ (fun _ => rfl) _ y J).trans (sval_eq_zero _ (fun _ => rfl) _ y J).symm)
    (by
      rw [h1]
      exact SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J hJ => by rw [Category.id_comp, ← hs₀ y J hJ, e₀])
  intro j
  rw [hm j]
  exact mul_zero _

end GlobalTheory.Mum.ZeroFam

namespace GlobalTheory.Mum.ZeroFam

theorem exp_of_members_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ), 1 ≤ k → ∀ (s : SecK C.P.L.L C.α k) (F : IntFam (maximalIdeal R) D.toPre k), (∀ α j, (F.f α).f j = 0) → ∀ a b : W, T.Exp a b s F → ∀ b' : W, T.Exp a b' s F := by
  intro R _ _ _ _ D C W _ _ _ T k hk s F hF a b hExp b'
  obtain ⟨σ, ⟨σ', f', hC, hP, hE⟩, hs⟩ := hExp
  have hf' : ∀ x q, (f' x).f q = 0 := fun x => secB_zero_of_pullB T.hD x _ (f' x) (hF _) (hP x)
  have hσ' := section_eq_zero_of_expansion_zero_family T.U hk σ' f' hf' hE
  refine ⟨σ, ⟨σ', f', fun Z r z J J' hJ hJ' => ?_, hP, hE⟩, hs⟩
  rw [hC Z r z J J' hJ hJ', sval_eq_zero _ hσ', mul_zero, mul_zero]

end GlobalTheory.Mum.ZeroFam
