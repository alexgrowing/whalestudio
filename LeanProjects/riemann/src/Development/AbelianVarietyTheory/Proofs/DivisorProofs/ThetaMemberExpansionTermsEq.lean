import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFCompEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkZeta
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.YKThNeZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIndepCoords
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.EigenEquationTranslationKernelGenericFibre
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

namespace GlobalTheory.GSep.ExpUnique

theorem expandsF_unique {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (hR : AdmBase R I) {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)
    (w : W0 U) (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))) (s s₂ : Fam D.toPre F k)
    (h : U.ExpandsF F k w t s) (h₂ : U.ExpandsF F k w t s₂) : s = s₂ := by
  obtain ⟨σ, hσ, hG⟩ := h
  obtain ⟨σ₂, hσ₂, hG₂⟩ := h₂
  have hf : ∀ j, σ.f j = σ₂.f j := by
    refine ReciprocityTheory.ChartRestriction.G.Geo.Tor.sec_ext_val U.LG.isLB (fun y J hJ => ?_)
    choose J₁ hJ₁ using fun χ : _ ⟶ A.A.left => exists_chart A.isLB (χ y)
    have e₁ := GlobalTheory.Jets.sval_of_isoRelM hσ (𝟙 _) y hJ hJ₁
    have e₂ := GlobalTheory.Jets.sval_of_isoRelM hσ₂ (𝟙 _) y hJ hJ₁
    exact e₁.trans e₂.symm
  obtain rfl : σ = σ₂ := by
    rcases σ with ⟨a, _⟩
    rcases σ₂ with ⟨b, _⟩
    obtain rfl : a = b := funext hf
    rfl
  exact GlobalTheory.expandsG_unique R I hR D A G U k F σ s s₂ hG hG₂

end GlobalTheory.GSep.ExpUnique

theorem GlobalTheory.GSep.ExpUnique.coef_eq_of_expandsF : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (w₀ : W0 𝔪.U.toUnifPre) (k : ℕ) (th : SecA 𝔪.A (FractionRing V) k) (s s₂ : Fam 𝔪.D.toPre (FractionRing V) k),
  w₀.IsGen → 1 ≤ k → 𝔪.U.ExpandsF (FractionRing V) k w₀ th s → 𝔪.U.ExpandsF (FractionRing V) k w₀ th s₂ →
  ∀ (g : GtPtF 𝔪.D.toPre (FractionRing V)) (w : Frm 𝔪.D.toPre (FractionRing V) k g.b), w.IsGen → ∀ χ, coef s₂ g w χ = coef s g w χ := by
  intro I X₁ z₁ act V _ _ _ ev Y _ t δ 𝔪 w₀ k th s s₂ _ _ hs hs₂ g w _ χ
  rw [GlobalTheory.GSep.ExpUnique.expandsF_unique (GlobalTheory.TorRef.admissibleBase_of_completeNormalLocalCharZero 𝔪.cn) 𝔪.U.toUnifPre (FractionRing V) k w₀ th
    s s₂ hs hs₂]
