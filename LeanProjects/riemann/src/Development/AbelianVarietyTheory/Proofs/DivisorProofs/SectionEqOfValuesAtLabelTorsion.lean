import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullIso
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFCompEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkZeta
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.YKThNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantNeZeroUniformisedMember
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

noncomputable section
namespace GlobalTheory.GSep.GMem

theorem sec_eq_of_valAt : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (th th₂ : SecA 𝔪.A (FractionRing V) 1),
  (∀ a, (fr a).IsGen) → (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) →
  (∀ a, ValAt th₂ (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) → th₂ = th := by
  intro I X₁ z₁ act V _ _ _ ev Y _ t δ 𝔪 x fr th th₂ _ h₁ h₂
  obtain ⟨b, hb⟩ := GlobalTheory.GSep.GMem.exists_th_ne_zero I X₁ z₁ act V ev Y t δ 𝔪
  set y := 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ with hy
  have ht : (show GlobalTheory.TorsionExt.AbSec 𝔪.A (FractionRing V) 1 from th) ≠ 0 := by
    intro h0
    have hz : ValAt (show GlobalTheory.TorsionExt.AbSec 𝔪.A (FractionRing V) 1 from th) (x b) (fr b) 0 := by
      rw [h0]; exact GlobalTheory.TermsMove.valAt_zero (x b) (fr b)
    exact hb (GlobalTheory.TermsMove.valAt_unique (h₁ b) hz)
  obtain ⟨c, hc⟩ := GlobalTheory.TermsMove.exists_eq_smul ht (show GlobalTheory.TorsionExt.AbSec 𝔪.A (FractionRing V) 1 from th₂)
  have hz0 : ValAt (0 : GlobalTheory.TorsionExt.AbSec 𝔪.A (FractionRing V) 1) (x b) (fr b) 0 :=
    GlobalTheory.TermsMove.valAt_zero (x b) (fr b)
  have hl := GlobalTheory.TermsMove.valAt_lin (h₁ b) hz0 c
  rw [add_zero, add_zero, ← hc] at hl
  have e := GlobalTheory.TermsMove.valAt_unique (h₂ b) hl
  have c1 : c = 1 := by
    have : (c - 1) * y = 0 := by rw [sub_mul, ← e]; ring
    rcases mul_eq_zero.1 this with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hb
  rw [c1, one_smul] at hc
  exact hc

end GlobalTheory.GSep.GMem
end
