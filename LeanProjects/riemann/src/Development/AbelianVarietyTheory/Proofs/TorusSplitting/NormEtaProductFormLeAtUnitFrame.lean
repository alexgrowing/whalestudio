import Mathlib
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyUnifWitnessDataOfIsUnf
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeLaws
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardLevGrpAndSpan
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaNullValueExistsUniqueNaturalLinear
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FullLinearLevelCoverBaseChangeTorsor
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EtaValAtExistsUniqueNatural
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.EtaProductRuleValueEqProductFormOfTestRingStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.NormNullValEqNormThetaStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.AhFrameFactorEqNegOnePowRiemannFormStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsTorusOfPeriodHermitianStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.AppellHumbertSectionEntireWithFactorStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ThetaFunctionTorusL2NormStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.FullLinearLevelEqExpPeriodsComplexPointStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.RelabellingGoodEmbeddingIsTypeFnStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.PeriodTorusIsTorusAtFrameStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.NormProdSumThetaLeExpTorusStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaAn.ArchPt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem gen_mod {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pm : D.La →+ (Fin g → ℂ)}
    {Hm : Matrix (Fin g) (Fin g) ℂ} {T : I2.PT E} {ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp T.dim}
    (hP : IsPeriod D ty Pm) (hT : IsTorusOf D ty Pm Hm T ψ) (R : ℕ) {n : ℕ} (a : Fin n → D.La)
    (ha : ∀ u : D.La, ∃ (cf : Fin n → 𝓞 E) (v : D.La), u = ∑ b, cf b • a b + (R ^ 4) • v) :
    ∀ x ∈ T.L, ∃ c : Fin n → 𝓞 E, ∃ y ∈ T.L, x = ∑ b, I2.act (c b) (ψ (Pm (a b))) + (R : ℂ) • y := by
  obtain ⟨-, -, -, hL, hact, -⟩ := hT
  intro x hx
  obtain ⟨u, rfl⟩ := (hL x).1 hx
  obtain ⟨cf, v, rfl⟩ := ha u
  refine ⟨cf, ψ (Pm ((R ^ 3) • v)), (hL _).2 ⟨_, rfl⟩, ?_⟩
  rw [map_add, map_add, map_sum, map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [← hact]
    congr 1
    funext k
    exact hP.1 _ _ _
  · rw [Nat.cast_smul_eq_nsmul, ← map_nsmul ψ, ← map_nsmul Pm, smul_smul, ← pow_succ']

theorem evR_eq {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} (hA : AllTest Xo c)
    {R : ℕ} (hR : Odd R) {J : Type} [Fintype J] {n : ℕ} {cf : J → ℤ} {xs : J → Fin n → LatMod Dw (R ^ 4)}
    {f : Rul Xo c} (hf : IsEtaRule Xo c R cf xs f) (y : FrPt Xo c (CAt σ))
    (ev : LatMod Dw (R ^ 4) → (ptO Xo y.x ⟶ Xo.univ.t.G)) (w : LatMod Dw (R ^ 4) → CAt σ)
    (hev : IsFullLev Xo (R ^ 4) y.x ev) (hw : ∀ q, IsNullVal Xo c (R ^ 2) y (ev q) (w q)) :
    evR Xo c f y = etaExpr (R ^ 4) cf xs w := by
  haveI : _root_.IsReduced (CAt σ) := inferInstanceAs (_root_.IsReduced ℂ)
  have h₁ := (GlobalTheory.T.etaProductRule_value_eq_productForm_of_testRing E H Dw l Xo c R hR J n cf xs f hf (CAt σ) y (hA _ y)).1
  have h₂ : EtaValAt Xo c R cf xs y (etaExpr (R ^ 4) cf xs w) :=
    ⟨CAt σ, inferInstance, inferInstance, AlgHom.id c.F _, y, ev, w,
      RingHom.FaithfullyFlat.of_bijective Function.bijective_id, GlobalTheory.FramedBaseChange.refl y, hev, hw, rfl⟩
  exact ((GlobalTheory.EtaForm.etaValAt_existsUnique_natural GlobalTheory.firstFiveLaws.1 E H Dw l Xo c R hR J n cf xs).1 _ y).unique h₁ h₂

end GlobalTheory.EtaAn.ArchPt

namespace GlobalTheory.EtaAn

theorem norm_productForm_le_at_unit_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → AllTest Xo c → ∀ (R i N : ℕ), Odd R → 1 < R → Nat.card (LevGrp Dw (R ^ 4)) = 2 * R ^ 4 * i → 1 ≤ N → ∀ (J : Type) [Fintype J] (cf : J → ℤ) (xs : J → Fin r → LatMod Dw (R ^ 4)) (f : Rul Xo c), Fintype.card J ≤ R ^ (2 * I2.PT.f E * r ^ 2) → (∀ j, |cf j| ≤ N) → Spans xs → IsEtaRule Xo c R cf xs f → ∀ (DF q m : ℕ) (R0 : ℝ), RunOK E r DF q R0 m → (Dw.p ≤ m ∨ Dw.q ≤ m) → ∀ (k : U.Comp) (x : (U.X k).dom), (∀ τ i, ‖dmin (U.X k).Gm x.1 τ i‖ = 1) → ‖rdU U f k x.1‖ ≤ Real.exp (-(i : ℝ) * (I2.phiFD (U.X k) (I2.th (E := E) q R0) x.1 - p16 E r q m R N)) := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hA R i N hR h1R hcard hN J _ cf xs f hJ hcf hsp hf DF q m R0 hrun hm k x hx
  obtain ⟨Uw⟩ := GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf E H Dw l Xo c σ r U hU
  obtain ⟨Hm, χl, fr, θ, Fd, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, hFd, hl2⟩ := Uw.norm k x hx
  have hy : (U.un k x).x = Uw.F.u (Uw.ik k) (Uw.Pm k x) := (Uw.lie k x).1
  have hP := Uw.period k x
  have hfn : IsFnOf Uw.F (Uw.ik k) (Uw.Pm k x) fr (U.un k x).x (U.un k x).s θ := a₉
  have hAH : AHFrame Uw.F (Uw.ik k) (Uw.Pm k x) Hm χl fr :=
    ⟨a₁, a₂, a₃, a₄, a₅, a₆, fun j hj => by rw [← hy]; exact a₇ j hj, a₈⟩
  have hty := (GlobalTheory.T.relabelling_goodEmbedding_isTypeFn E H Dw l Xo c σ hσ).2.2 Uw.g Uw.e
  have hty' : IsTypeFn H (Uw.F.Di (Uw.ik k)).p (Uw.F.Di (Uw.ik k)).q (fun j => relab c σ (Uw.e j).1) := by
    rw [(Uw.F.sig _).1, (Uw.F.sig _).2]
    exact hty
  obtain ⟨T, ψ, hT⟩ := GlobalTheory.T.exists_torus_of_period_hermitian E H _ _ _ _ Hm hty' hP a₁ a₂ a₃
  obtain ⟨-, hr, hph, hdim⟩ := GlobalTheory.T.periodTorus_isTorusAt_frame E H Dw l Xo c σ r U hσ hU Uw k x Hm T ψ ⟨a₁, a₂, a₃⟩ hT
  have hhol : Differentiable ℂ θ ∧ ∀ a z, θ (z + Uw.Pm k x a) = χl (Uw.Pm k x a) *
      Complex.exp (Real.pi * hermForm Hm z (Uw.Pm k x a) + Real.pi / 2 * hermForm Hm (Uw.Pm k x a) (Uw.Pm k x a)) *
        θ z := by
    have key : ∀ (x₀ : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx x₀)), x₀ = Uw.F.u (Uw.ik k) (Uw.Pm k x) →
        IsFnOf Uw.F (Uw.ik k) (Uw.Pm k x) fr x₀ s θ → Differentiable ℂ θ ∧ ∀ a z, θ (z + Uw.Pm k x a) =
          χl (Uw.Pm k x a) * Complex.exp (Real.pi * hermForm Hm z (Uw.Pm k x a) +
            Real.pi / 2 * hermForm Hm (Uw.Pm k x a) (Uw.Pm k x a)) * θ z := by
      intro x₀ s h₀ hs
      subst h₀
      exact GlobalTheory.T.appellHumbert_section_entire_with_factor E H Dw l Xo _ _ _ Uw.F (Uw.ik k) (Uw.Pm k x) Hm χl fr hP hAH s θ hs
    exact key _ _ hy hfn
  have hchi := GlobalTheory.T.ahFrame_factor_eq_negOnePow_riemannForm E H Dw l Xo _ _ _ Uw.F (Uw.ik k) (Uw.Pm k x) Hm χl fr hP hAH
  obtain ⟨hsec, hl2', hpt⟩ := GlobalTheory.T.theta_function_torus_l2_norm E H _ _ _ _ Hm T ψ θ Fd hT hhol.1
    (fun a z => by rw [hhol.2 a z, hchi a]) hFd
  rw [hl2] at hl2'
  have hR4 : 0 < R ^ 4 := pow_pos hR.pos 4
  obtain ⟨ev, hev⟩ : ∃ ev, IsFullLev Xo (R ^ 4) (U.un k x).x ev :=
    (GlobalTheory.fullLevel_cover_baseChange_torsor GlobalTheory.firstFiveLaws.1 E H Dw l Xo (R ^ 4) hR4).2.2.2 ℂ (U.un k x).x
  obtain ⟨a, ha, hgen⟩ := GlobalTheory.T.fullLinearLevel_eq_exp_periods_complexPoint E H Dw l Xo c σ _ _ Uw.F (Uw.ik k) (Uw.Pm k x) (U.un k x) hP hy (R ^ 4) hR4 ev hev
  have hR2 : Odd (R ^ 2) := hR.pow
  have htors : ∀ q, ev q ^ ((R ^ 2) ^ 2) = 1 := fun q => by rw [← pow_mul]; exact (ha q).2
  choose w hw using fun q =>
    ((GlobalTheory.nullValue_existsUnique_natural_linear GlobalTheory.firstFiveLaws.1 E H Dw l Xo c (R ^ 2) hR2).1 _ (U.un k x) (ev q)
      (htors q)).exists
  have hR0 : (R : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hR.pos.ne'
  let z : LatMod Dw (R ^ 4) → (Fin Uw.g → ℂ) := fun q =>
    ((R ^ 2 : ℕ) : ℂ) • ((R ^ 4 : ℕ) : ℂ)⁻¹ • Uw.Pm k x (a q)
  have hz : ∀ q, ((R : ℂ) ^ 2) • ψ (z q) = ψ (Uw.Pm k x (a q)) := fun q => by
    rw [← map_smul]
    congr 1
    simp only [z, smul_smul]
    have : (R : ℂ) ^ 2 * (((R ^ 2 : ℕ) : ℂ) * ((R ^ 4 : ℕ) : ℂ)⁻¹) = 1 := by
      push_cast
      field_simp
    rw [this, one_smul]
  have hwn : ∀ q, ‖toC (w q)‖ =
      Real.sqrt (T.ptN2 1 (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) (fun _ => ψ (z q))) := fun q => by
    rw [hpt]
    exact GlobalTheory.T.norm_nullVal_eq_norm_theta_alt E H Dw l Xo c σ _ _ Uw.F (Uw.ik k) (Uw.Pm k x) Hm χl fr θ (U.un k x) hP hAH hy hfn (R ^ 2) hR2
      (ev q) _ (w q) (htors q) (ha q).1 (hw q)
  haveI : Finite (LevGrp Dw (R ^ 4)) := (GlobalTheory.EtaCard.card_levGrp_and_span E H Dw R h1R).1
  haveI := Fintype.ofFinite (LevGrp Dw (R ^ 4))
  have hval : rdU U f k x.1 = ∏ g : LevGrp Dw (R ^ 4), ∑ j, (cf j : ℂ) * ∏ b, toC (w (g (xs j b))) := by
    have e₁ : rdU U f k x.1 = toC (evR Xo c f (U.un k x)) := dif_pos x.2
    rw [e₁, ArchPt.evR_eq hA hR hf (U.un k x) ev w hev hw, etaExpr, finprod_eq_prod_of_fintype]
    rfl
  obtain ⟨P, hq, hR0', hm'⟩ := hrun T hr (hdim m hm)
  rw [hval, ← hph, ← hq, ← hR0', ← hm']
  have hspan : ∀ (g : LevGrp Dw (R ^ 4)) j, Submodule.span (𝓞 E) (Set.range fun b => g (xs j b)) = ⊤ := fun g j => by
    have : (Set.range fun b => g (xs j b)) = g.toLinearMap '' Set.range (xs j) := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, hsp j, Submodule.map_top, LinearEquiv.range]
  have hgen' : ∀ (g : LevGrp Dw (R ^ 4)) j, ∀ v ∈ T.L, ∃ c : Fin r → 𝓞 E, ∃ y ∈ T.L,
      v = ∑ b, I2.act (c b) (((R : ℂ) ^ 2) • ψ (z (g (xs j b)))) + (R : ℂ) • y := fun g j => by
    simp only [hz]
    exact ArchPt.gen_mod hP hT R (fun b => a (g (xs j b))) (hgen r _ (hspan g j))
  have hmem : ∀ q, ((R : ℂ) ^ 2) • ψ (z q) ∈ T.L := fun q => by
    rw [hz]
    exact (hT.2.2.2.1 _).2 ⟨_, rfl⟩
  have key : ∀ (r : ℕ), T.r = r → Fintype.card J ≤ R ^ (2 * I2.PT.f E * r ^ 2) →
      ∀ (w : LevGrp Dw (R ^ 4) → J → Fin r → ℂ) (a : LevGrp Dw (R ^ 4) → J → Fin r → I2.Vsp T.dim),
      (∀ g j b, ((R : ℂ) ^ 2) • a g j b ∈ T.L) →
      (∀ g j, ∀ x ∈ T.L, ∃ c : Fin r → 𝓞 E, ∃ y ∈ T.L,
        x = ∑ b, I2.act (c b) (((R : ℂ) ^ 2) • a g j b) + (R : ℂ) • y) →
      (∀ g j b, ‖w g j b‖ =
        Real.sqrt (T.ptN2 1 (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) fun _ => a g j b)) →
      ‖∏ g, ∑ j, (cf j : ℂ) * ∏ b, w g j b‖ ≤
        Real.exp (-(i : ℝ) * (T.ph (I2.th (E := E) P.q P.R0) - p16 E r P.q P.m R N)) := by
    intro r' hr' hJ' w' a'
    subst hr'
    exact GlobalTheory.T.norm_prod_sum_theta_le_exp_torus E T DF P R i N h1R hN _ hsec hl2' (LevGrp Dw (R ^ 4)) J
      (by rw [← Nat.card_eq_fintype_card, hcard]) hJ' cf w' a' hcf
  exact key r hr hJ (fun g j b => toC (w (g (xs j b)))) (fun g j b => ψ (z (g (xs j b))))
    (fun g j b => hmem _) hgen' (fun g j b => hwn _)

end GlobalTheory.EtaAn
