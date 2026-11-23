import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BudgetAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyUnifWitnessDataOfIsUnf
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeLaws
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardLevGrpAndSpan
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaNullValueExistsUniqueNaturalLinear
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FullLinearLevelCoverBaseChangeTorsor
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EtaValAtExistsUniqueNatural
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.NormNullValEqNormThetaStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.AhFrameFactorEqNegOnePowRiemannFormStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsTorusOfPeriodHermitianStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.AppellHumbertSectionEntireWithFactorStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ThetaFunctionTorusL2NormStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.FullLinearLevelEqExpPeriodsComplexPointStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.RelabellingGoodEmbeddingIsTypeFnStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.PeriodTorusIsTorusAtFrameStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsBorelOrthonormalFlagFrameStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.NormProdSumThetaLeExpTorusStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.NormEtaProductFormLeAtUnitFrame

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaConst.ArchBound

theorem norm_pow_le_at_unit_frame (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r)
    (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (hA : AllTest Xo c) (R : ℕ) (hR : Odd R)
    (h1R : 1 < R) (xs : Fin r → LatMod Dw (R ^ 4)) (f : Rul Xo c)
    (hsp : Submodule.span (𝓞 E) (Set.range xs) = ⊤)
    (hf : GlobalTheory.ThetaConst.IsTauRule Xo c R (fun _ : Unit => 1) (fun _ => xs) f) (DF q m : ℕ) (R0 : ℝ)
    (hrun : RunOK E r DF q R0 m) (hm : Dw.p ≤ m ∨ Dw.q ≤ m) (k : U.Comp) (x : (U.X k).dom)
    (hx : ∀ τ i, ‖dmin (U.X k).Gm x.1 τ i‖ = 1) :
    ‖Formalism.L2.PjFree.toC (evR Xo c f (U.un k x))‖ ^ (2 * R ^ 4) ≤
      Real.exp (-((1 : ℕ) : ℝ) * (I2.phiFD (U.X k) (I2.th (E := E) q R0) x.1 - p16 E r q m R 1)) := by
  obtain ⟨Uw⟩ := GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf E H Dw l Xo c σ r U hU
  obtain ⟨Hm, χl, fr, θ, Fd, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, hFd, hl2⟩ := Uw.norm k x hx
  have hy : (U.un k x).x = Uw.F.u (Uw.ik k) (Uw.Pm k x) := (Uw.lie k x).1
  have hP := Uw.period k x
  have hfn : IsFnOf Uw.F (Uw.ik k) (Uw.Pm k x) fr (U.un k x).x (U.un k x).s θ := a₉
  have hAH : AHFrame Uw.F (Uw.ik k) (Uw.Pm k x) Hm χl fr :=
    ⟨a₁, a₂, a₃, a₄, a₅, a₆, fun j hj => by rw [← hy]; exact a₇ j hj, a₈⟩
  have hty := (GlobalTheory.T.relabelling_goodEmbedding_isTypeFn E H Dw l Xo c σ hσ).2.2 Uw.g Uw.e
  have hty' : IsTypeFn H (Uw.F.Di (Uw.ik k)).p (Uw.F.Di (Uw.ik k)).q
      (fun j => Formalism.L2.PjFree.relab c σ (Uw.e j).1) := by
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

  have hval₀ := hf.tauValAt_evR hR (hA _ (U.un k x))
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  obtain ⟨ev, hevL⟩ := GlobalTheory.ThetaConst.exists_isLevOf_geometric Xo c hval₀.dvd (U.un k x).x
  have hev : IsFullLev Xo (R ^ 4) (U.un k x).x ev := hevL.2.1
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
  have hwn : ∀ q, ‖Formalism.L2.PjFree.toC (w q)‖ =
      Real.sqrt (T.ptN2 1 (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) (fun _ => ψ (z q))) := fun q => by
    rw [hpt]
    exact GlobalTheory.T.norm_nullVal_eq_norm_theta_alt E H Dw l Xo c σ _ _ Uw.F (Uw.ik k) (Uw.Pm k x) Hm χl fr θ (U.un k x) hP hAH hy hfn (R ^ 2) hR2
      (ev q) _ (w q) (htors q) (ha q).1 (hw q)

  have hval : evR Xo c f (U.un k x) = ∏ b, w (xs b) := by
    rw [hval₀.unique hR (GlobalTheory.ThetaConst.tauValAt_self hevL hw), GlobalTheory.ThetaConst.tauExpr]
    simp
  obtain ⟨P, hq, hR0', hm'⟩ := hrun T hr (hdim m hm)
  rw [hval, ← hph, ← hq, ← hR0', ← hm']
  have hgen' : ∀ (g : Fin (2 * R ^ 4)) (j : Unit), ∀ v ∈ T.L, ∃ c : Fin r → 𝓞 E, ∃ y ∈ T.L,
      v = ∑ b, I2.act (c b) (((R : ℂ) ^ 2) • ψ (z (xs b))) + (R : ℂ) • y := fun g j => by
    simp only [hz]
    exact GlobalTheory.EtaAn.ArchPt.gen_mod hP hT R (fun b => a (xs b)) (hgen r _ hsp)
  have hmem : ∀ q, ((R : ℂ) ^ 2) • ψ (z q) ∈ T.L := fun q => by
    rw [hz]
    exact (hT.2.2.2.1 _).2 ⟨_, rfl⟩
  have key : ∀ (r : ℕ), T.r = r → Fintype.card Unit ≤ R ^ (2 * I2.PT.f E * r ^ 2) →
      ∀ (w : Fin (2 * R ^ 4) → Unit → Fin r → ℂ) (a : Fin (2 * R ^ 4) → Unit → Fin r → I2.Vsp T.dim),
      (∀ g j b, ((R : ℂ) ^ 2) • a g j b ∈ T.L) →
      (∀ g j, ∀ x ∈ T.L, ∃ c : Fin r → 𝓞 E, ∃ y ∈ T.L,
        x = ∑ b, I2.act (c b) (((R : ℂ) ^ 2) • a g j b) + (R : ℂ) • y) →
      (∀ g j b, ‖w g j b‖ =
        Real.sqrt (T.ptN2 1 (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) fun _ => a g j b)) →
      ‖∏ g, ∑ j, ((fun _ : Unit => (1 : ℤ)) j : ℂ) * ∏ b, w g j b‖ ≤
        Real.exp (-((1 : ℕ) : ℝ) * (T.ph (I2.th (E := E) P.q P.R0) - p16 E r P.q P.m R 1)) := by
    intro r' hr' hJ' w' a'
    subst hr'
    exact GlobalTheory.T.norm_prod_sum_theta_le_exp_torus E T DF P R 1 1 h1R le_rfl _ hsec hl2' (Fin (2 * R ^ 4)) Unit
      (by simp) hJ' (fun _ => 1) w' a' (fun _ => by simp)
  have hJ : Fintype.card Unit ≤ R ^ (2 * I2.PT.f E * r ^ 2) := by
    rw [Fintype.card_unit]; exact Nat.one_le_pow _ _ hR.pos
  have := key r hr hJ (fun g j b => Formalism.L2.PjFree.toC (w (xs b))) (fun g j b => ψ (z (xs b)))
    (fun g j b => hmem _) hgen' (fun g j b => hwn _)
  have e : ‖Formalism.L2.PjFree.toC (∏ b, w (xs b))‖ = ∏ b, ‖Formalism.L2.PjFree.toC (w (xs b))‖ := by
    rw [← norm_prod]; rfl
  rw [e]
  simpa [Finset.prod_const, norm_pow] using this

end GlobalTheory.ThetaConst.ArchBound

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.ThetaConst

theorem normSq_thetaConst_le_exp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (x : ℝ), GoodEmb c σ → IsUnf U → ∀ R : ℕ, Odd R → 1 < R → ∀ (xs : Fin (Dw.p + Dw.q) → GlobalTheory.EtaForm.LatMod Dw (R ^ 4)) (f : Rul Xo c), Submodule.span (𝓞 E) (Set.range xs) = ⊤ → GlobalTheory.ThetaConst.IsTauRule Xo c R (fun _ : Unit => 1) (fun _ => xs) f → ∀ (DF q m : ℕ) (R0 : ℝ), GlobalTheory.EtaAn.RunOK E r DF q R0 m → (Dw.p ≤ m ∨ Dw.q ≤ m) → ∀ z : Σ k, Frame (U.X k).Ψ r, z.2 ∈ (U.X z.1).dom → homN U x (wtZ 0 (2 * (Dw.p + Dw.q))) (f ^ 2) z ≤ Real.exp ((GlobalTheory.EtaAn.p16 E r q m R 1 - ReciprocityTheory.ChartRestriction.G.I2.phiFD (U.X z.1) (ReciprocityTheory.ChartRestriction.G.I2.th (E := E) q R0) z.2) / (R : ℝ) ^ 4) := by
  intro E _ _ _ H Dw l Xo c σ r U x hσ hU R hR h1R xs f hsp hf DF q m R0 hrun hm z hz
  obtain ⟨k, y⟩ := z
  have hr := hU.1
  subst hr
  have hA : AllTest Xo c :=
    GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c
  have hsec1 : f ∈ sec Xo c 0 (Dw.p + Dw.q) := hf.mem_sec hR
  have hsec : f ^ 2 ∈ sec Xo c 0 (2 * (Dw.p + Dw.q)) := by
    have := sec_mul Xo c 0 0 _ _ hsec1 hsec1
    rw [add_zero, ← two_mul] at this
    rwa [sq]
  have hS : (U.X k).IsSec (laU U 0 (2 * (Dw.p + Dw.q)) k) (rdU U (f ^ 2) k) :=
    hU.2.2.2.2.1 0 _ ⟨fun _ => antitone_const, even_two_mul _⟩ (f ^ 2) hsec k
  obtain ⟨b, -, hb, hun, -, hphi, hp⟩ := GlobalTheory.T.exists_borel_orthonormal_flag_frame E _ (U.X k) y hz
  have hN : homN U x (wtZ 0 (2 * (Dw.p + Dw.q))) (f ^ 2) ⟨k, y⟩ = ‖rdU U f k (rmul y b)‖ ^ 2 := by
    have h1 : lieFacZ Dw x (wtZ 0 (2 * (Dw.p + Dw.q))) = 1 := by simp [lieFacZ, wtZ]
    unfold homN ptN
    rw [modelWt_wtZ, h1, _root_.one_mul]
    show (U.X k).pnorm (laU U 0 (2 * (Dw.p + Dw.q)) k) (rdU U (f ^ 2) k) y = _
    rw [hp _ _ hS, sq f, GlobalTheory.AllWt.rdU_mul, Pi.mul_apply, Pi.mul_apply, norm_mul, sq]
  rw [hN, ← hphi _]
  have hv : rdU U f k (rmul y b) =
      Formalism.L2.PjFree.toC (evR Xo c f ((Formalism.L2.PjFree.Unf.ofPj U).un k ⟨rmul y b, hb⟩)) := dif_pos hb
  have key := ArchBound.norm_pow_le_at_unit_frame E H Dw l Xo c σ _ (Formalism.L2.PjFree.Unf.ofPj U) hσ
    ((Formalism.L2.PjFree.isUnf_ofPj U).2 hU) hA R hR h1R xs f hsp hf DF q m R0 hrun hm k ⟨rmul y b, hb⟩ hun
  rw [hv]
  have hn : R ^ 4 ≠ 0 := pow_ne_zero _ hR.pos.ne'
  have hR4 : (R : ℝ) ^ 4 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hR.pos.ne')
  rw [← pow_le_pow_iff_left₀ (sq_nonneg _) (Real.exp_pos _).le hn, ← pow_mul, ← Real.exp_nat_mul]
  refine le_of_le_of_eq key ?_
  congr 1
  push_cast
  rw [mul_div_cancel₀ _ hR4]
  show -((1 : ℝ)) * (I2.phiFD (U.X k) (I2.th (E := E) q R0) (rmul y b) - p16 E (Dw.p + Dw.q) q m R 1) = _
  ring

end GlobalTheory.ThetaConst
