import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorOfStageTriangleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageExtensionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageSuccessorCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStepCharIdealValueEqBaseMulRootOfUnity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharTrivialUniformizers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFiniteMulSupportIdealFac

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

theorem idealVal_mul_chr (χ ψ : Chr F E) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
    idealVal (χ * ψ) 𝔞 = idealVal χ 𝔞 * idealVal ψ 𝔞 := by
  unfold idealVal
  simp_rw [val_mul, mul_zpow]
  exact finprod_mul_distrib (GlobalTheory.SqStepIdeal.mulSupport_finite _ 𝔞) (GlobalTheory.SqStepIdeal.mulSupport_finite _ 𝔞)

theorem idealVal_prime (χ : Chr F E) (w : HeightOneSpectrum (𝓞 E)) :
    idealVal χ (w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = val χ w := by
  unfold idealVal
  rw [finprod_eq_single _ w, FractionalIdeal.count_self, zpow_one]
  intro v hv
  rw [FractionalIdeal.count_maximal_coprime E v hv.symm, zpow_zero]

theorem idealVal_one (χ : Chr F E) : idealVal χ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = 1 := by
  unfold idealVal
  simp [FractionalIdeal.count_one]

theorem exists_idealVal_eq {ξ : Chr F E} (hξ : IsHecke F E ξ) (hu : ∀ᶠ w in Filter.cofinite, UnrAt ξ w) {n : ℕ} (hn : 0 < n)
    (hv : ∀ w, val ξ w ^ n = 1) (k : (AE F E)ˣ) :
    ∃ 𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E, 𝔞 ≠ 0 ∧ idealVal ξ 𝔞 = Circle.toUnits (ξ k) := by
  let H : Subgroup ℂˣ :=
    { carrier := {z | ∃ 𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E, 𝔞 ≠ 0 ∧ idealVal ξ 𝔞 = z}
      mul_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a * b, mul_ne_zero ha hb, GlobalTheory.EulerIdeal.idealVal_mul ξ ha hb⟩
      one_mem' := ⟨1, one_ne_zero, idealVal_one ξ⟩
      inv_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨a⁻¹, inv_ne_zero ha, GlobalTheory.EulerIdeal.idealVal_inv ξ a⟩ }
  haveI : NeZero n := ⟨hn.ne'⟩
  have h1 : H ≤ rootsOfUnity n ℂ := by
    rintro _ ⟨a, -, rfl⟩
    unfold idealVal
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := (GlobalTheory.SqStepIdeal.mulSupport_finite (val ξ) a).toFinset) (by simp)]
    exact Subgroup.prod_mem _ fun w _ => Subgroup.zpow_mem _ ((mem_rootsOfUnity _ _).2 (hv w)) _
  haveI : Finite H := Finite.of_injective _ (Subgroup.inclusion_injective h1)
  have hc : 0 < Nat.card H := Nat.card_pos
  haveI : NeZero (Nat.card H) := ⟨hc.ne'⟩
  have h2 : H ≤ rootsOfUnity (Nat.card H) ℂ := fun z hz => by
    rw [mem_rootsOfUnity]
    have := congrArg Subtype.val (pow_card_eq_one' (x := (⟨z, hz⟩ : H)))
    rwa [SubmonoidClass.coe_pow] at this
  have h3 : H = rootsOfUnity (Nat.card H) ℂ := by
    refine Subgroup.eq_of_le_of_card_ge h2 ?_
    exact card_rootsOfUnity ℂ (Nat.card H)
  have h4 : ξ ^ Nat.card H = 1 := by
    refine GlobalTheory.HeckeUnifApprox.eq_one_of_unif_cofinite _ ⟨?_, fun x => ?_⟩ (hu.mono fun w hw ϖ hϖ => ?_)
    · exact hξ.1.pow _
    · rw [MonoidHom.pow_apply, hξ.2 x, one_pow]
    · have e1 : val ξ w ∈ H := ⟨w.asIdeal, FractionalIdeal.coeIdeal_ne_zero.2 w.ne_bot, idealVal_prime ξ w⟩
      have e2 := (mem_rootsOfUnity _ _).1 (h2 e1)
      rw [← hw.locChar_eq_val hϖ] at e2
      have e3 : Circle.toUnits (ξ (locIdele F w ϖ) ^ Nat.card H) = Circle.toUnits 1 := by
        rw [map_pow, map_one]; exact e2
      rw [MonoidHom.pow_apply]
      exact Circle.ext (congrArg Units.val e3)
  have h5 : Circle.toUnits (ξ k) ∈ H := by
    rw [h3, mem_rootsOfUnity, ← map_pow, ← MonoidHom.pow_apply, h4, MonoidHom.one_apply, map_one]
  exact h5

theorem nu_good {B : Base F E} {X : Chars F E} {a a' : ℕ} (h : X.IsGood B a a') :
    IsHecke F E X.ν ∧ ∀ᶠ w in Filter.cofinite, UnrAt X.ν w := by
  refine ⟨⟨h.heckeα.1.div' h.heckeβ.1, fun x => by
    simp only [Chars.ν, MonoidHom.div_apply, h.heckeα.2 x, h.heckeβ.2 x, div_one]⟩, ?_⟩
  have hf : (above E (X.T : Set (Pl F))).Finite :=
    (Set.Finite.biUnion X.T.finite_toSet fun v _ => Formalism.L2.Host.finite_aboveF (L := E) F v).subset fun w hw =>
      Set.mem_biUnion hw rfl
  refine Filter.eventually_cofinite.2 (hf.subset fun w hw => ?_)
  by_contra hn
  refine hw ?_
  rw [Chars.ν, div_eq_mul_inv]
  exact (h.unrα w hn).mul (h.unrβ w hn).inv

theorem exists_stepFac_twist (B : Base F E) {X Y : Chars F E} (hξ : IsHecke F E (X.ν / Y.ν))
    (hu : ∀ᶠ w in Filter.cofinite, UnrAt (X.ν / Y.ν) w) {n : ℕ} (hn : 0 < n) (hv : ∀ w, val (X.ν / Y.ν) w ^ n = 1)
    (e₁ e₂ s : ℤˣ) (𝔟 𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (z : ℤ) (k : (AE F E)ˣ) :
    ∃ (𝔟' : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (r : ℂ), r ≠ 0 ∧
      stepFac B X e₁ e₂ s 𝔟' 𝔠 z = ((X.ν k / Y.ν k : Circle) : ℂ) * r * stepFac B X e₁ e₂ s 𝔟 𝔠 z ∧
      stepFac B Y e₁ e₂ s 𝔟' 𝔠 z = r * stepFac B Y e₁ e₂ s 𝔟 𝔠 z := by
  obtain ⟨𝔟₀, h0, e0⟩ : ∃ 𝔟₀ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E, 𝔟₀ ≠ 0 ∧
      ∀ χ : Chr F E, idealVal χ 𝔟₀ = idealVal χ 𝔟 := by
    by_cases h : 𝔟 = 0
    · refine ⟨1, one_ne_zero, fun χ => ?_⟩
      rw [idealVal_one, h]
      unfold idealVal
      simp [FractionalIdeal.count_zero]
    · exact ⟨𝔟, h, fun _ => rfl⟩
  obtain ⟨𝔞, ha, e⟩ := exists_idealVal_eq hξ hu hn hv (k ^ (e₁ : ℤ))
  have e1 : idealVal X.ν 𝔞 ^ (e₁ : ℤ) = Circle.toUnits (X.ν k / Y.ν k) * idealVal Y.ν 𝔞 ^ (e₁ : ℤ) := by
    have : idealVal X.ν 𝔞 = idealVal (X.ν / Y.ν) 𝔞 * idealVal Y.ν 𝔞 := by
      rw [← idealVal_mul_chr, div_mul_cancel]
    rw [this, e, mul_zpow, map_zpow, map_zpow, ← zpow_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, zpow_one,
      MonoidHom.div_apply]
  refine ⟨𝔞 * 𝔟₀, (idealVal Y.ν 𝔞 ^ (e₁ : ℤ) : ℂˣ), Units.ne_zero _, ?_, ?_⟩
  · unfold stepFac
    rw [GlobalTheory.EulerIdeal.idealVal_mul _ ha h0, e0, mul_zpow, e1]
    simp only [Units.val_mul, mul_assoc]
    rfl
  · unfold stepFac
    rw [GlobalTheory.EulerIdeal.idealVal_mul _ ha h0, e0, mul_zpow]
    simp only [Units.val_mul, mul_assoc]

end Values

theorem val_quot_pow {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T} (hL : Lc.Is μ₀)
    (W : G.Weil) (S : GridChoice W Set.univ) (hN : NumbersIn D.what₂.embLL S μ₀) (i j : Fin D.R.m) (t : T) :
    ∃ n : ℕ, 0 < n ∧ ∀ w, GlobalTheory.LFun.val ((GlobalTheory.SqStep.chs G i j t).ν / (GlobalTheory.SqStep.chs G i j μ₀).ν) w ^ n = 1 := by
  have e : ∀ s, (GlobalTheory.SqStep.chs G i j s).ν = G.nu s i (j + 1) := fun s => by
    show (Lc.mu s (j + 1) * Lc.eta ^ _) / (G.ch.chi _ * Lc.eta ^ _) = _
    rw [mul_div_mul_right_eq_div]
    rfl
  have hν : (GlobalTheory.SqStep.chs G i j t).ν / (GlobalTheory.SqStep.chs G i j μ₀).ν = Lc.xi t * (Lc.xi μ₀)⁻¹ := by
    rw [e, e]
    refine MonoidHom.ext fun x => ?_
    show Lc.mu0 (j + 1) x * Lc.xi t x / G.ch.chi (D.R.m - i) x / (Lc.mu0 (j + 1) x * Lc.xi μ₀ x / G.ch.chi (D.R.m - i) x) =
      Lc.xi t x * (Lc.xi μ₀ x)⁻¹
    rw [div_div_div_cancel_right, mul_div_mul_left_eq_div, div_eq_mul_inv]
  obtain ⟨n, hn, hfin⟩ := hL.xi_fin t
  refine ⟨n, hn, fun w => ?_⟩
  rw [hν, GlobalTheory.LFun.val_mul, GlobalTheory.LFun.val_inv, GlobalTheory.LFun.val_eq_of_chrEq (hL.xi t) w, GlobalTheory.LFun.val_eq_of_chrEq (hL.xi μ₀) w,
    hL.xi_base, show (1 : HChar D.host.E).val w = 1 from rfl, inv_one, mul_one]
  exact (GlobalTheory.SqStepIdeal.val_mem hfin (hN.chars.xi t) w).1

theorem gbig_three {Q₁ Q₂ Q₃ Q : GP} (h₁ : GBig Q₁) (h₂ : GBig Q₂) (h₃ : GBig Q₃)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q₁ G μ₀ C x b → Q₂ G μ₀ C x b → Q₃ G μ₀ C x b → Q G μ₀ C x b) : GBig Q := by
  obtain ⟨F₁, h₁⟩ := h₁
  obtain ⟨F₂, h₂⟩ := h₂
  obtain ⟨F₃, h₃⟩ := h₃
  refine ⟨max F₁ (max F₂ F₃), fun ε CF hCF => ?_⟩
  obtain ⟨C₁, x₁, k₁⟩ := h₁ ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C₂, x₂, k₂⟩ := h₂ ε CF (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCF)
  obtain ⟨C₃, x₃, k₃⟩ := h₃ ε CF (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCF)
  refine ⟨max C₁ (max C₂ C₃), max x₁ (max x₂ x₃), fun C hC D large₂ he hx hR T Lc μ₀ hL G => H G μ₀ C _ _ ?_ ?_ ?_⟩
  · exact k₁ C (le_trans (le_max_left _ _) hC) D large₂ he (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hL G
  · exact k₂ C (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC) D large₂ he
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hL G
  · exact k₃ C (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC) D large₂ he
      (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hL G

theorem gbig_three_is {Q₁ Q₂ Q₃ Q : GP} (h₁ : GBig Q₁) (h₂ : GBig Q₂) (h₃ : GBig Q₃)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Lc.Is μ₀ → Q₁ G μ₀ C x b → Q₂ G μ₀ C x b → Q₃ G μ₀ C x b → Q G μ₀ C x b) : GBig Q := by
  obtain ⟨F₁, h₁⟩ := h₁
  obtain ⟨F₂, h₂⟩ := h₂
  obtain ⟨F₃, h₃⟩ := h₃
  refine ⟨max F₁ (max F₂ F₃), fun ε CF hCF => ?_⟩
  obtain ⟨C₁, x₁, k₁⟩ := h₁ ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C₂, x₂, k₂⟩ := h₂ ε CF (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCF)
  obtain ⟨C₃, x₃, k₃⟩ := h₃ ε CF (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCF)
  refine ⟨max C₁ (max C₂ C₃), max x₁ (max x₂ x₃), fun C hC D large₂ he hx hR T Lc μ₀ hL G => H G μ₀ C _ _ hL ?_ ?_ ?_⟩
  · exact k₁ C (le_trans (le_max_left _ _) hC) D large₂ he (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hL G
  · exact k₂ C (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC) D large₂ he
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hL G
  · exact k₃ C (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC) D large₂ he
      (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hL G

theorem step_first : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
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
  refine gbig_three_is (GlobalTheory.T.tower_stage_extension_exists hP hK hM) (GlobalTheory.T.tower_stage_successor_coefficients hP hK hM) (GlobalTheory.T.exists_factor_of_stage_triangle hP hK hM) ?_
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
