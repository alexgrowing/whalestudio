import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFCompEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkZeta
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.YKThNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTermsCoefficientsUniqueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic
open GlobalTheory.GSep GlobalTheory.GSep.TransTerms

namespace GlobalTheory.GSep.TransTerms

theorem transExp_of_frExp : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ), ∀ a ∈ X₁.S.HH X₁.M z₁, ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ e : ℕ, GlobalTheory.GSep.TransTerms.FrExp 𝔪 a τ e → GlobalTheory.GSep.TransTerms.TransExp 𝔪 x₀ a τ e := by
  have huniq := GlobalTheory.T.thetaMember_terms_coefficients_unique
  intro I X₁ z₁ act x₀ hdiv V _ _ _ ev Y _ t δ 𝔪 a _ τ _ e hF
  obtain ⟨-, x, fr, th, w₀, s, g', w, hx, hfr, hth, hw₀, hs, htor, hw, hov, htr⟩ := hF
  intro χ hχ C lab T hT c hc C' lab' T' hT' c' hc' mu
  letI := GlobalTheory.TorusExt.gtGroup 𝔪.D.toPre (FractionRing V)
  set g₀ := GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ) with hg₀def
  have hg₀ : IsTor χ g₀ := (GlobalTheory.UT.isTor_iff _ _).2 (GlobalTheory.TorusExt.isTorusPtF_torusPt χ)
  have hadd : g'.IsAdd g₀ (g' + g₀) := (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 rfl
  have hb : (g' + g₀).b = g'.b := (GlobalTheory.UT.ThetaAverage.val_translate hg₀ hadd).1
  set c₀ : FractionRing V := 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) with hc₀def
  have hc₀ : c₀ ≠ 0 :=
    ((((X₁.S.prim.isUnit (by have := X₁.S.r_pos; have := X₁.S.N_ge; positivity)).pow e).map
      (algebraMap X₁.o₁ X₁.S.R)).map 𝔪.yK).ne_zero
  obtain ⟨w₁, hw₁, hv₁⟩ := GlobalTheory.UT.TorsionValue.exists_frm_scale w hw (inv_ne_zero hc₀)
  obtain ⟨w'', hw'', hv''⟩ : ∃ w'' : Frm 𝔪.D.toPre (FractionRing V) 1 (g' + g₀).b, w''.IsGen ∧
      ∀ z J, val w'' (𝟙 _) z J = val w₁ (𝟙 _) z J := by
    rw [hb]; exact ⟨w₁, hw₁, fun _ _ => rfl⟩
  have hvs : ∀ z J, Good 𝔪.D.toPre.P.L z J → (val w'' (𝟙 _) z J).val = cstH z c₀⁻¹ * (val w (𝟙 _) z J).val :=
    fun z J hJ => by rw [hv'' z J, hv₁ z J hJ, GlobalTheory.UT.CoefBasic.cst_eq]
  have hvw : ∀ z J, Good 𝔪.D.toPre.P.L z J → (val w (𝟙 _) z J).val = cstH (R := V) z c₀ * (val w'' (𝟙 _) z J).val :=
    fun z J hJ => by rw [hvs z J hJ, ← _root_.mul_assoc, ← map_mul, mul_inv_cancel₀ hc₀, map_one, _root_.one_mul]
  have hov'' := htr χ hχ g₀ hg₀ (g' + g₀) hadd w'' hw'' hvw
  have htor'' : ∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) (g' + g₀) o ∧ o.IsZero := by
    obtain ⟨o, ho, hoz⟩ := htor
    refine ⟨0, (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 ?_, (GlobalTheory.TorusExt.isZero_iff_eq _).2 rfl⟩
    rw [smul_add, ← (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 ho, (GlobalTheory.TorusExt.isZero_iff_eq _).1 hoz, zero_add, hg₀def,
      ← map_nsmul, ← ofMul_pow, hχ.1, ofMul_one, map_zero]
  obtain ⟨x₁, fr₁, th₁, w₀₁, s₁, G₁, W₁, hx₁, hfr₁, hth₁, hw₀₁, hs₁, hc₁, hT₁⟩ := hT
  obtain ⟨x₂, fr₂, th₂, w₀₂, s₂, G₂, W₂, hx₂, hfr₂, hth₂, hw₀₂, hs₂, hc₂, hT₂⟩ := hT'
  obtain ⟨ht₁, hW₁, ho₁⟩ := hc₁ c
  obtain ⟨ht₂, hW₂, ho₂⟩ := hc₂ c'
  rw [hc] at ho₁
  rw [hc'] at ho₂
  have u₁ := huniq I X₁ z₁ act V ev Y t δ 𝔪 a x x₁ fr fr₁ th th₁ w₀ w₀₁ s s₁ g' (G₁ c) w (W₁ c)
    hx hfr hth hw₀ hs htor hw hov hx₁ hfr₁ hth₁ hw₀₁ hs₁ ht₁ hW₁ ho₁ (𝔪.e₈ mu)
  have u₂ := huniq I X₁ z₁ act V ev Y t δ 𝔪 (a + τ) x x₂ fr fr₂ th th₂ w₀ w₀₂ s s₂ (g' + g₀) (G₂ c') w'' (W₂ c')
    hx hfr hth hw₀ hs htor'' hw'' hov'' hx₂ hfr₂ hth₂ hw₀₂ hs₂ ht₂ hW₂ ho₂ (𝔪.e₈ mu)
  have co := GlobalTheory.UT.ThetaAverage.coef_translate hg₀ hadd hw hvs s (𝔪.e₈ mu)
  have hθ := GlobalTheory.GSep.GMem.yK_th_ne_zero I X₁ z₁ act V ev Y t δ 𝔪 x₀ hdiv
  apply mul_right_cancel₀ hθ
  rw [_root_.mul_assoc, _root_.mul_assoc, hT₁ mu c, hT₂ mu c', ← u₁, ← u₂, co]
  field_simp

end GlobalTheory.GSep.TransTerms
