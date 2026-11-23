import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFCompEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkZeta
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigTorsFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFramesSectionValuesRatioRootOfUnity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFConstMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

namespace GlobalTheory.GSep

theorem over_rescale : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (w₀ : W0 𝔪.U.toUnifPre) (g : GtPtF 𝔪.D.toPre (FractionRing V)) (w w' : Frm 𝔪.D.toPre (FractionRing V) 1 g.b) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) (e e' : FrAt x) (l : FractionRing V), l ≠ 0 → (∀ z J, Good 𝔪.A.L z J → (Geo.Tor.val e' (𝟙 _) z J).val = GlobalTheory.Poinc.TorsRatio.cstK z l * (Geo.Tor.val e (𝟙 _) z J).val) → (∀ z J, Good 𝔪.D.toPre.P.L z J → (val w (𝟙 _) z J).val = cstH (R := V) z l * (val w' (𝟙 _) z J).val) → 𝔪.Over' w₀ g w x e → 𝔪.Over' w₀ g w' x e' := by
  intro I X₁ z₁ act V _ _ _ ev Y _ t δ 𝔪 w₀ g w w' x e e' l hl he hw H k hk wk' hwk' hgen s s' v hs hv
  have hlk : l ^ k ≠ 0 := pow_ne_zero k hl
  obtain ⟨wk, hwkg, hwk⟩ := GlobalTheory.UT.TorsionValue.exists_frm_scale wk' hgen hlk
  have h₁ : ValAt s x e (l ^ k * v) := fun z J hJ => by
    rw [hv z J hJ]
    have r₁ : Geo.Tor.val (powFrame 𝔪.A.A 𝔪.A.L x e (k : ℤ)) (𝟙 _) z J = Geo.Tor.val e (𝟙 _) z J ^ (k : ℤ) :=
      map_zpow _ _ _
    have r₂ : Geo.Tor.val (powFrame 𝔪.A.A 𝔪.A.L x e' (k : ℤ)) (𝟙 _) z J = Geo.Tor.val e' (𝟙 _) z J ^ (k : ℤ) :=
      map_zpow _ _ _
    rw [r₁, r₂, zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, he z J hJ]
    simp only [id, GlobalTheory.Poinc.TorsRatio.cst_eq_cstK, map_mul, map_pow]
    ring
  have h₂ := H k hk wk (fun z J hJ => Units.ext (by
    rw [hwk z J hJ, hwk' z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hw z J hJ, mul_pow,
      GlobalTheory.UT.CoefBasic.cst_eq, map_pow])) hwkg s s' _ hs h₁
  have h₃ := GlobalTheory.Poinc.Sep.sumF_const_mul (l ^ k)⁻¹ h₂
  simpa only [GlobalTheory.UT.TorsionValue.coef_scale hgen hwk, inv_mul_cancel_left₀ hlk] using h₃

end GlobalTheory.GSep
