import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTowerStageRankFactorization
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.QuadraticTowerStepStageInduction
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TowerStageSuccessorCoefficients
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaTowerStageNormFactorization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTowerStageRankFactorizationStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.SqStepK
section Values
open GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end Values
theorem seesaw_first_reduction : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW) (lam : T → ℂ) (e : ℕ),
      GlobalTheory.SqTower.IsStageC W i j p (q + 1) X → Factor X W.ψ W.θ lam → A.rank = A'.rank + 2 * e →
      ∃ (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c : T → ℂ), GlobalTheory.SqTower.IsStageC W i j p q Y ∧ Y.IsConst W.ψ W.θ c ∧
        (∀ t, c t ≠ 0) ∧ ∀ t, ∃ (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (e₁ e₂ s : ℤˣ)
          (𝔟 𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), GlobalTheory.SqStep.BaseFits G W i j t Bs ∧
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) ≠ 0 ∧
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) ≠ 0 ∧
          GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) ≠ 0 ∧
          GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j μ₀).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) ≠ 0 ∧
          lam t * GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) *
              GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) * c μ₀ =
            lam μ₀ * GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j μ₀).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) *
              GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) * c t := by
  intro hP hK hM
  obtain ⟨e₁, e₂, s, hSB⟩ := hK.2.1
  refine gbig_three_is (_root_.GlobalTheory.T.quadratic_tower_step_stage_induction hP hK hM) (_root_.GlobalTheory.T.tower_stage_successor_coefficients_alt hP hK hM) (_root_.GlobalTheory.T.exists_factor_of_isStageC hP hK hM) ?_
  intro D T Lc sc G μ₀ C x b hL hy hd hf W S hψ hN i j p q A A' WW X lam e hX hF he
  obtain ⟨B', WW₁, Y, hY, hst⟩ := hy W S hψ hN i j p q A A' WW X hX
  obtain ⟨c, hc⟩ := hf W S hψ hN i j p q A B' WW₁ Y hY
  haveI : Nonempty T := ⟨μ₀⟩
  refine ⟨A, B', WW₁, Y, c, hY, hc.isConst, hc.1, fun t => ?_⟩
  obtain ⟨Bs, bb, Γ, Γ₁, H, H', R, R₁, d, d₁, k, k₁, hfit, hb, hV, hp, hq, hH, hH', hd0, hd10, hk⟩ :=
    hd W S hψ hN i j p q A A' WW B' WW₁ X Y lam c e hX hY hst hF hc he t
  obtain ⟨C₀, hC₀, hstep⟩ := hSB D.host.F D.host.E D.sp.cm.sig Bs A.rank bb Γ Γ₁ H H' R R₁ hV hp hq hH hH'
  have hE : (A.rank - (bb + 2)) / 2 = e := by omega
  have key : ∀ t' ∈ ({t, μ₀} : Set T),
      d * (((GlobalTheory.SqStep.chs G i j t').ν k / (GlobalTheory.SqStep.chs G i j μ₀).ν k : Circle) : ℂ) * lam t' *
      GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j t').ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) *
      (C₀ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t') e₁ e₂ s H.𝔟 H'.𝔟 (-(e : ℤ))) =
      d₁ * (((GlobalTheory.SqStep.chs G i j t').ν k₁ / (GlobalTheory.SqStep.chs G i j μ₀).ν k₁ : Circle) : ℂ) * c t' := by
    intro t' ht'
    obtain ⟨⟨om, om', Rf, hm, hκ⟩, ⟨om₁, om₁', Rf₁, hm₁, hκ₁⟩⟩ := hk t' ht'
    obtain ⟨u, hu1, hu2⟩ := hstep _ om om' Rf om₁ om₁' Rf₁ hm hm₁ _ _ hκ hκ₁
    rw [hE] at hu1 hu2
    have e1 : (((e : ℕ) : ℂ) + 1) = ((e + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [e1] at hu2
    change _ * GlobalTheory.LFun.charL _ (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) _ = _ at hu2
    rw [hu2, mul_right_comm, hu1, one_mul]
  have good : ∀ t' ∈ ({t, μ₀} : Set T), GlobalTheory.LFun.IsHecke D.host.F D.host.E (GlobalTheory.SqStep.chs G i j t').ν ∧
      ∀ᶠ w in Filter.cofinite, GlobalTheory.LFun.UnrAt (GlobalTheory.SqStep.chs G i j t').ν w := by
    intro t' ht'
    obtain ⟨⟨om, om', Rf, hm, -⟩, -⟩ := hk t' ht'
    exact nu_good hm.triple.chars
  obtain ⟨gt, ut⟩ := good t (by simp)
  obtain ⟨gμ, uμ⟩ := good μ₀ (by simp)
  obtain ⟨n, hn, hv⟩ := val_quot_pow G hL W S hN i j t
  obtain ⟨𝔟, r, hr, st, sμ⟩ := exists_stepFac_twist Bs (X := GlobalTheory.SqStep.chs G i j t) (Y := GlobalTheory.SqStep.chs G i j μ₀)
    ⟨gt.1.div' gμ.1, fun y => by simp only [MonoidHom.div_apply, gt.2 y, gμ.2 y, div_one]⟩
    ((ut.and uμ).mono fun w hw => by rw [div_eq_mul_inv]; exact hw.1.mul hw.2.inv) hn hv e₁ e₂ s H.𝔟 H'.𝔟 (-(e : ℤ)) (k / k₁)
  have kt := key t (by simp)
  have kμ := key μ₀ (by simp)
  rw [div_self', div_self', Circle.coe_one, mul_one, mul_one] at kμ
  have ek : (((GlobalTheory.SqStep.chs G i j t).ν k / (GlobalTheory.SqStep.chs G i j μ₀).ν k : Circle) : ℂ) =
      (((GlobalTheory.SqStep.chs G i j t).ν (k / k₁) / (GlobalTheory.SqStep.chs G i j μ₀).ν (k / k₁) : Circle) : ℂ) *
        (((GlobalTheory.SqStep.chs G i j t).ν k₁ / (GlobalTheory.SqStep.chs G i j μ₀).ν k₁ : Circle) : ℂ) := by
    rw [← Circle.coe_mul, div_mul_div_comm, ← map_mul, ← map_mul, div_mul_cancel]
  rw [ek] at kt
  have z₀ := Circle.coe_ne_zero ((GlobalTheory.SqStep.chs G i j t).ν (k / k₁) / (GlobalTheory.SqStep.chs G i j μ₀).ν (k / k₁))
  have z₁ := Circle.coe_ne_zero ((GlobalTheory.SqStep.chs G i j t).ν k₁ / (GlobalTheory.SqStep.chs G i j μ₀).ν k₁)
  have nt := mul_ne_zero (mul_ne_zero hd10 z₁) (hc.1 t)
  have nμ : d₁ * c μ₀ ≠ 0 := mul_ne_zero hd10 (hc.1 μ₀)
  rw [← kt] at nt
  rw [← kμ] at nμ
  refine ⟨Bs, e₁, e₂, s, 𝔟, H'.𝔟, hfit, ?_, ?_, right_ne_zero_of_mul (left_ne_zero_of_mul nt),
    right_ne_zero_of_mul (left_ne_zero_of_mul nμ), ?_⟩
  · rw [st]
    exact mul_ne_zero (mul_ne_zero z₀ hr) (right_ne_zero_of_mul (right_ne_zero_of_mul nt))
  · rw [sμ]
    exact mul_ne_zero hr (right_ne_zero_of_mul (right_ne_zero_of_mul nμ))
  · rw [st, sμ]
    refine mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hd0 hC₀) z₁) ?_
    linear_combination (r * c μ₀) * kt -
      (r * c t * (((GlobalTheory.SqStep.chs G i j t).ν k₁ / (GlobalTheory.SqStep.chs G i j μ₀).ν k₁ : Circle) : ℂ)) * kμ
end GlobalTheory.SqStepK
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.seesaw_first_reduction_level : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW) (lam : T → ℂ) (e : ℕ),
      GlobalTheory.SqTower.IsStageC W i j p (q + 1) X → Factor X W.ψ W.θ lam → A.rank = A'.rank + 2 * e →
      ∃ (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c : T → ℂ), GlobalTheory.SqTower.IsStageC W i j p q Y ∧ Y.IsConst W.ψ W.θ c ∧
        (∀ t, c t ≠ 0) ∧ ∀ t, ∃ (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (e₁ e₂ s : ℤˣ)
          (𝔟 𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), GlobalTheory.SqStep.BaseFits G W i j t Bs ∧
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) ≠ 0 ∧
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) ≠ 0 ∧
          GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) ≠ 0 ∧
          GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j μ₀).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) ≠ 0 ∧
          lam t * GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) *
              GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) * c μ₀ =
            lam μ₀ * GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j μ₀).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) *
              GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) * c t := by
  first | exact @_root_.GlobalTheory.SqStepK.seesaw_first_reduction | exact _root_.GlobalTheory.SqStepK.seesaw_first_reduction | (intros; apply _root_.GlobalTheory.SqStepK.seesaw_first_reduction <;> assumption)
end
