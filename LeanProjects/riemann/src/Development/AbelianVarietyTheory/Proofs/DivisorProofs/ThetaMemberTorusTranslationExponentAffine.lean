import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFCompEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkZeta
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberExistsFrameExponentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationExponentOfFrameExponentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameExponentsAffineTwoMembersStatement
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

theorem trans_exp_affine : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (V2 : Type) [CommRing V2] [IsDomain V2] [IsLocalRing V2] (ev2 : X₁.M.Z.presheaf.stalk z₁ →+* V2) (Y2 : Type) [AddCommGroup Y2] (t2 : Y2 → V2) (δ2 : I → Y2 → Y2) (𝔪2 : GlobalTheory.GSep.GMem X₁ z₁ act V2 ev2 Y2 t2 δ2), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ F1 F2 : X₁.S.Gam → ℕ, (∀ a ∈ X₁.S.HH X₁.M z₁, GlobalTheory.GSep.TransTerms.TransExp 𝔪1 x₀ a τ (F1 a)) ∧ (∀ a ∈ X₁.S.HH X₁.M z₁, GlobalTheory.GSep.TransTerms.TransExp 𝔪2 x₀ a τ (F2 a)) ∧ ∃ (κ : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) (h : X₁.S.HH X₁.M z₁ →+ ZMod ((X₁.S.r * X₁.S.N) ^ 2)), ∀ (a : X₁.S.Gam) (ha : a ∈ X₁.S.HH X₁.M z₁), ((F1 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((F2 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = κ + h ⟨a, ha⟩ := by
  classical
  intro I X₁ z₁ act x₀ hd V1 _ _ _ ev1 Y1 _ t1 δ1 𝔪1 V2 _ _ _ ev2 Y2 _ t2 δ2 𝔪2 τ hτ
  let E1 : X₁.S.Gam → ℕ := fun a => if ha : a ∈ X₁.S.HH X₁.M z₁ then
    Classical.choose (GlobalTheory.T.thetaMember_exists_frame_exponent I X₁ z₁ act x₀ hd V1 ev1 Y1 t1 δ1 𝔪1 a ha τ hτ) else 0
  let E2 : X₁.S.Gam → ℕ := fun a => if ha : a ∈ X₁.S.HH X₁.M z₁ then
    Classical.choose (GlobalTheory.T.thetaMember_exists_frame_exponent I X₁ z₁ act x₀ hd V2 ev2 Y2 t2 δ2 𝔪2 a ha τ hτ) else 0
  have h1 : ∀ a ∈ X₁.S.HH X₁.M z₁, FrExp 𝔪1 a τ (E1 a) := fun a ha => by
    simp only [E1, dif_pos ha]
    exact Classical.choose_spec (GlobalTheory.T.thetaMember_exists_frame_exponent I X₁ z₁ act x₀ hd V1 ev1 Y1 t1 δ1 𝔪1 a ha τ hτ)
  have h2 : ∀ a ∈ X₁.S.HH X₁.M z₁, FrExp 𝔪2 a τ (E2 a) := fun a ha => by
    simp only [E2, dif_pos ha]
    exact Classical.choose_spec (GlobalTheory.T.thetaMember_exists_frame_exponent I X₁ z₁ act x₀ hd V2 ev2 Y2 t2 δ2 𝔪2 a ha τ hτ)
  exact ⟨E1, E2, fun a ha => GlobalTheory.T.translationExponent_of_frameExponent I X₁ z₁ act x₀ hd V1 ev1 Y1 t1 δ1 𝔪1 a ha τ hτ _ (h1 a ha),
    fun a ha => GlobalTheory.T.translationExponent_of_frameExponent I X₁ z₁ act x₀ hd V2 ev2 Y2 t2 δ2 𝔪2 a ha τ hτ _ (h2 a ha),
    GlobalTheory.T.frameExponents_affine_two_members I X₁ z₁ act x₀ hd V1 ev1 Y1 t1 δ1 𝔪1 V2 ev2 Y2 t2 δ2 𝔪2 τ hτ E1 E2 h1 h2⟩

end GlobalTheory.GSep.TransTerms
