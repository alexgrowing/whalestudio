import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFCompEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkZeta
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.YKThNeZero
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
namespace GlobalTheory.GSep.FrameUniq

section Gen
variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F] {D : DegPre R}

theorem exists_ratio {b b' : TF (R := R) F ⟶ D.P.A} (h : b' = b) {w : Frm D F 1 b} {w' : Frm D F 1 b'}
    (hw : w.IsGen) (hw' : w'.IsGen) : ∃ c : F, c ≠ 0 ∧ ∀ z J, Good D.P.L z J →
      (val w' (𝟙 _) z J).val = cst F z c * (val w (𝟙 _) z J).val := by
  subst h
  exact exists_frame_ratio hw hw'

theorem coef_congr' {k : ℕ} {g g₂ : GtPtF D F} {w : Frm D F k g.b} {w₂ : Frm D F k g₂.b} (hw : w.IsGen)
    (hb : g₂.b = g.b) (hs : ∀ χ z J, Good D.P.L z J → val (g₂.s χ) (𝟙 _) z J = val (g.s χ) (𝟙 _) z J)
    (hv : ∀ z J, Good D.P.L z J → val w₂ (𝟙 _) z J = val w (𝟙 _) z J) (s : Fam D F k) (χ : D.X) :
    coef s g₂ w₂ χ = coef s g w χ := by
  refine coef_eq fun z J hJ => ?_
  have a := isCoef_coef g hw χ s z J hJ
  have e : lift (𝟙 (TF (R := R) F)) g₂.b = lift (𝟙 (TF (R := R) F)) g.b := by rw [hb]
  rw [hs χ z J hJ, hv z J hJ, e]
  exact a
end Gen

theorem frame_val_eq : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (w₀ : W0 𝔪.U.toUnifPre) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) (fr : FrAt x)
  (g g₂ : GtPtF 𝔪.D.toPre (FractionRing V)) (w : Frm 𝔪.D.toPre (FractionRing V) 1 g.b) (w₂ : Frm 𝔪.D.toPre (FractionRing V) 1 g₂.b),
  w₀.IsGen → fr.IsGen →
  (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g o ∧ o.IsZero) → w.IsGen → 𝔪.Over' w₀ g w x fr →
  (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g₂ o ∧ o.IsZero) → w₂.IsGen → 𝔪.Over' w₀ g₂ w₂ x fr →
  g₂.b = g.b → (∀ χ z J, Good 𝔪.D.toPre.P.L z J → val (g₂.s χ) (𝟙 _) z J = val (g.s χ) (𝟙 _) z J) →
  ∀ z J, Good 𝔪.D.toPre.P.L z J → val w₂ (𝟙 _) z J = val w (𝟙 _) z J := by
  intro I X₁ z₁ act V _ _ _ ev Y _ t δ 𝔪 w₀ x fr g g₂ w w₂ hw₀ hfr _ hw hO _ hw₂ hO₂ hb hs
  have hadm : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  obtain ⟨c, hc, hcv⟩ := exists_ratio hb hw hw₂
  have pow_one_of : ∀ k : ℕ, 4 ≤ k → c ^ k = 1 := by
    intro k hk
    have hk1 : 1 ≤ k := by omega
    obtain ⟨wk, hwkg, hwk⟩ := TorsionValue.exists_frm_pow w hw k
    obtain ⟨wk₂, hwk₂g, hwk₂⟩ := TorsionValue.exists_frm_pow w₂ hw₂ k
    obtain ⟨w', hw'g, hw'⟩ := TorsionValue.exists_frm_scale wk hwkg (pow_ne_zero k hc)
    obtain ⟨th, a, ha0, ha⟩ := GlobalTheory.UT.NonVan.exists_sec_ne_zero GlobalTheory.firstFiveLaws V 𝔪.A (FractionRing V) k hk x fr hfr
    obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF GlobalTheory.globalFns_holds 𝔪.U (FractionRing V) (k := k) hk1 w₀ hw₀
    have hexp : 𝔪.U.ExpandsF (FractionRing V) k w₀ th (e th) := (he th _).2 rfl
    have H1 := hO k hk1 wk hwk hwkg th (e th) a hexp ha
    have H2 := hO₂ k hk1 wk₂ hwk₂ hwk₂g th (e th) a hexp ha
    have hv : ∀ z J, Good 𝔪.D.toPre.P.L z J → val wk₂ (𝟙 _) z J = val w' (𝟙 _) z J := by
      intro z J hJ
      apply Units.ext
      rw [hwk₂ z J hJ, hw' z J hJ, hwk z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hcv z J hJ, mul_pow,
        cst_eq, cst_eq, map_pow]
    have e2 : coef (e th) g₂ wk₂ = fun χ => c ^ k * coef (e th) g wk χ := funext fun χ => by
      rw [coef_congr' hw'g hb hs hv, TorsionValue.coef_scale hwkg hw' (e th) χ]
    rw [e2] at H2
    have hl := ((GlobalTheory.AdicSum.sumF_calculus V (maximalIdeal V) hadm (FractionRing V) _ (coef (e th) g wk)
      (coef (e th) g wk) a a).2.1 H1 H1 (c ^ k - 1))
    have ee : (fun χ => (c ^ k - 1) * coef (e th) g wk χ + coef (e th) g wk χ) = fun χ => c ^ k * coef (e th) g wk χ :=
      funext fun χ => by ring
    rw [ee] at hl
    have := (GlobalTheory.AdicSum.sumF_calculus V (maximalIdeal V) hadm (FractionRing V) _ _ (coef (e th) g wk) a
      ((c ^ k - 1) * a + a)).1 H2 hl
    have h0 : (c ^ k - 1) * a = 0 := by linear_combination -this
    exact sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_right ha0)
  have h4 := pow_one_of 4 le_rfl
  have h5 := pow_one_of 5 (by norm_num)
  have hc1 : c = 1 := by linear_combination (-c) * h4 + h5
  intro z J hJ
  apply Units.ext
  rw [hcv z J hJ, hc1, cst_eq, map_one, _root_.one_mul]

end GlobalTheory.GSep.FrameUniq
