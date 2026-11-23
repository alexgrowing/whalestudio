import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionComponentsProportionalShiftMultipleStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU.SchurConst

theorem gs_zero {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs
  split_ifs with h
  · simp only [map_zero]
  · rfl

theorem sec_zero_of_val {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ y J, Good L y J → sval s (𝟙 Y) y J = 0)
    (j : K → L.ι) : s.f j = 0 := by
  refine fn_ext fun y hy => ?_
  obtain ⟨J, hJ, e⟩ := sval_trans hL s y j hy
  rw [h y J hJ, mul_zero] at e
  exact e.trans (gs_zero _ _ _).symm

theorem sec_zero_of_pull {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K₃ : Type} [Fintype K] [Fintype K₃]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (τ : Y' ⟶ Y) (σ : Y ⟶ Y') (hστ : σ ≫ τ = 𝟙 Y)
    {φ₃ : K₃ → (Y' ⟶ X)} {ε₃ : K₃ → ℤ} (u : LB.Gen (LB.LinComb L φ₃ ε₃)) (hu : u.IsGen)
    (h : ∀ y J, Good L y J → sval s τ y J = 0) (j : K → L.ι) : s.f j = 0 := by
  have h1 := sec_zero_of_val hL (pullMulSec s τ u hu) (fun y J hJ => by
    rw [sval_pullMulSec s τ u hu _ y hJ, Category.id_comp, h y J hJ, zero_mul])
  refine sec_zero_of_val hL s (fun y J hJ => ?_) j
  have h2 : sval (pullMulSec s τ u hu) σ y J = 0 := by
    unfold sval
    rw [h1]
    exact gs_zero _ _ _
  rw [sval_pullMulSec s τ u hu _ y hJ, hστ] at h2
  exact (Units.mul_left_eq_zero _).1 h2

theorem main : Laws → Laws2 → AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => ∀ N : ℕ, 1 ≤ N → (∀ α, ∃ t s, U.ExpF (Kbar V) N t s ∧ DegPre.FamFE D (Kbar V) N s ∧ ∃ j, (s α).f j ≠ 0) → U.FE (Kbar V) N := by
  intro hL1 hL2 V _ _ _ hV D A G _ _ U N hN hw t s hts mu α u hu hcorr
  obtain ⟨t₀, s₀, he₀, hfe₀, j, hj⟩ := hw α
  obtain ⟨a, ha⟩ := GlobalTheory.T.expansionComponents_proportional_shift_multiple hL1 hL2 V hV D A G U N hN α mu u hu ⟨t₀, s₀, he₀, j, hj⟩
  have hc : ∀ (z : (DegPre.BF D (Kbar V)).left) (b c : Kbar V),
      gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) (b * c) ⊤) =
        gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) b ⊤) * gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) c ⊤) := by
    intro z b c
    rw [← gs_mul _ _ ⊤ trivial]
    simp only [DegPre.constBF, map_mul]
  have hc1 : ∀ (z : (DegPre.BF D (Kbar V)).left),
      gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) 1 ⊤) = 1 := by
    intro z
    rw [gs_eq _ _ ⊤ trivial]
    simp only [DegPre.constBF, map_one]
  have hca : ∀ (z : (DegPre.BF D (Kbar V)).left) (b : Kbar V),
      gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) (b - 1) ⊤) =
        gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) b ⊤) - 1 := by
    intro z b
    rw [gs_eq _ _ ⊤ trivial, gs_eq _ _ ⊤ trivial]
    simp only [DegPre.constBF, map_sub, map_one]
  have ha1 : a = 1 := by
    by_contra hne
    apply hj
    have hinv : (DegPre.trF D (Kbar V) (-mu)).left ≫ (DegPre.trF D (Kbar V) mu).left = 𝟙 _ := by
      rw [← Over.comp_left, DVR.UUA.trF_add, neg_add_cancel, DVR.UUA.trF_zero, Over.id_left]
    refine sec_zero_of_pull D.P.isLB (s₀ α) _ _ hinv u hu (fun z J hJ => ?_) j
    have e1 := ha t₀ s₀ he₀ z J hJ
    have e2 := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ _).1 (hfe₀ mu α u hu hcorr) _ (𝟙 _) z J hJ
    rw [Category.id_comp] at e2
    have e3 : gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) (a - 1) ⊤) *
        (sval (s₀ α) (DegPre.trF D (Kbar V) mu).left z J * (val u (𝟙 _) z J).val) = 0 := by
      rw [hca, _root_.sub_mul, _root_.one_mul, ← e1, ← e2, sub_self]
    have e4 := congrArg (gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) (a - 1)⁻¹ ⊤) * ·) e3
    simp only [mul_zero] at e4
    rw [← _root_.mul_assoc, ← hc, inv_mul_cancel₀ (sub_ne_zero.2 hne), hc1, _root_.one_mul] at e4
    exact (Units.mul_left_eq_zero _).1 e4
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ _).2 fun z J hJ => ?_
  rw [Category.id_comp, ha t s hts z J hJ, ha1, hc1, _root_.one_mul]

end GlobalTheory.UU.SchurConst
