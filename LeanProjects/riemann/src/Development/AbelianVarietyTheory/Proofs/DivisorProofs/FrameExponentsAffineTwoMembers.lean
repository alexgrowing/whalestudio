import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameExponentSecondDifferenceConstantMembersStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFCompEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkZeta
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrExp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

namespace GlobalTheory.GSep.TransTerms

theorem affine_on_subgroup_of_second_diff {G : Type*} [AddCommGroup G] (H : AddSubgroup G) {R : Type*} [AddCommGroup R]
    (D : G → R) (hD : ∀ a ∈ H, ∀ b ∈ H, D (a + b) - D a - D b + D 0 = 0) :
    ∃ (κ : R) (h : H →+ R), ∀ (a : G) (ha : a ∈ H), D a = κ + h ⟨a, ha⟩ := by
  refine ⟨D 0, AddMonoidHom.mk' (fun x : H => D x - D 0) ?_, ?_⟩
  · intro x y
    have := hD x x.2 y y.2
    simp only [AddSubgroup.coe_add]
    rw [← sub_eq_zero]
    rw [← this]; abel
  · intro a ha
    simp

theorem frExp_affine_two_members : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1), ∀ (V2 : Type) [CommRing V2] [IsDomain V2] [IsLocalRing V2] (ev2 : X₁.M.Z.presheaf.stalk z₁ →+* V2) (Y2 : Type) [AddCommGroup Y2] (t2 : Y2 → V2) (δ2 : I → Y2 → Y2) (𝔪2 : GlobalTheory.GSep.GMem X₁ z₁ act V2 ev2 Y2 t2 δ2), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ E1 E2 : X₁.S.Gam → ℕ, (∀ a ∈ X₁.S.HH X₁.M z₁, GlobalTheory.GSep.TransTerms.FrExp 𝔪1 a τ (E1 a)) → (∀ a ∈ X₁.S.HH X₁.M z₁, GlobalTheory.GSep.TransTerms.FrExp 𝔪2 a τ (E2 a)) → ∃ (κ : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) (h : X₁.S.HH X₁.M z₁ →+ ZMod ((X₁.S.r * X₁.S.N) ^ 2)), ∀ (a : X₁.S.Gam) (ha : a ∈ X₁.S.HH X₁.M z₁), ((E1 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((E2 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = κ + h ⟨a, ha⟩ := by
  intro I X₁ z₁ act x₀ hdiv V1 _ _ _ ev1 Y1 _ t1 δ1 𝔪1 V2 _ _ _ ev2 Y2 _ t2 δ2 𝔪2 τ hτ E1 E2 h1 h2
  obtain ⟨c, hc⟩ := GlobalTheory.T.frameExponent_second_difference_constant_members I X₁ z₁ act x₀ hdiv τ hτ
  have k1 := hc V1 ev1 Y1 t1 δ1 𝔪1 E1 h1
  have k2 := hc V2 ev2 Y2 t2 δ2 𝔪2 E2 h2
  refine affine_on_subgroup_of_second_diff (X₁.S.HH X₁.M z₁)
    (fun a => ((E1 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((E2 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2))) ?_
  intro a ha b hb
  have e1 := k1 a ha b hb
  have e2 := k2 a ha b hb
  rw [← sub_eq_zero.mpr (e1.trans e2.symm)]
  abel

end GlobalTheory.GSep.TransTerms
