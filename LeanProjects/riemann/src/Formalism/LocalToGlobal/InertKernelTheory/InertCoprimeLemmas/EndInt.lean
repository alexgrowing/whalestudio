import Formalism.LocalToGlobal.InertKernelTheory.DefsBeW
import Formalism.LocalToGlobal.InertKernelTheory.DefsSigma
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.VarChange
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FormalExponentialAgree
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.PowerSeriesEmbedding
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.PadicNormTwoHundredSixteenEqOneOfFiveLe
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SigmaAlg
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.PhNormFromDatum
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveSecondLogDerivative
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CubeThreeR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.EndIntegral
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ShortWIntModel
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.LatITopBasis
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.LeadingConstantNeZero
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.OkpDict

noncomputable section

namespace Formalism.L2.KerInert.IwahoriBlocks

open NumberField Formalism.BasicNotions Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric

abbrev RB (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] := Formalism.G.unitBall ℂ_[p]

section Norms

variable {p : ℕ} [Fact p.Prime]

theorem norm_two_three (h5 : 5 ≤ p) : ‖(2 : ℂ_[p])‖ = 1 ∧ ‖(3 : ℂ_[p])‖ = 1 := by
  have hp : p.Prime := Fact.out
  have c2 : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
  have c3 : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp).mpr (by omega)
  exact ⟨by simpa using Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.norm_nat_coprime p c2,
    by simpa using Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.norm_nat_coprime p c3⟩

theorem norm_u_of (C : WeierstrassCurve.VariableChange ℂ_[p]) (h : ‖((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])‖ = 1) :
    ‖((C.u : ℂ_[p]ˣ) : ℂ_[p])‖ = 1 := by
  have h1 : ‖((C.u : ℂ_[p]ˣ) : ℂ_[p])‖ * ‖((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])‖ = 1 := by
    rw [← norm_mul, Units.mul_inv, norm_one]
  rw [h, mul_one] at h1
  exact h1

theorem vc_params (h5 : 5 ≤ p) (W0 : WeierstrassCurve ℂ_[p]) (h01 : W0.a₁ = 0) (h02 : W0.a₂ = 0) (h03 : W0.a₃ = 0)
    (hΔ0 : ‖W0.Δ‖ = 1) (C : WeierstrassCurve.VariableChange ℂ_[p]) (i1 : ‖(C • W0).a₁‖ ≤ 1)
    (i2 : ‖(C • W0).a₂‖ ≤ 1) (i3 : ‖(C • W0).a₃‖ ≤ 1) (hΔ : ‖(C • W0).Δ‖ = 1) :
    ‖((C.u : ℂ_[p]ˣ) : ℂ_[p])‖ = 1 ∧ ‖((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])‖ = 1 ∧ ‖C.r‖ ≤ 1 ∧ ‖C.s‖ ≤ 1 ∧ ‖C.t‖ ≤ 1 := by
  obtain ⟨h2, h3⟩ := norm_two_three h5
  have hv : ‖((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])‖ = 1 := by
    have h12 := hΔ
    rw [WeierstrassCurve.variableChange_Δ, norm_mul, norm_pow, hΔ0, mul_one] at h12
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp h12
  have hs : ‖C.s‖ ≤ 1 := by
    have h := i1
    rw [WeierstrassCurve.variableChange_a₁, h01, zero_add, norm_mul, norm_mul, hv, h2, one_mul,
      one_mul] at h
    exact h
  have ht : ‖C.t‖ ≤ 1 := by
    have h := i3
    simp only [WeierstrassCurve.variableChange_a₃, h03, h01, mul_zero, zero_add] at h
    rw [norm_mul, norm_pow, hv, one_pow, one_mul, norm_mul, h2, one_mul] at h
    exact h
  have hr : ‖C.r‖ ≤ 1 := by
    have ha2 : ‖3 * C.r - C.s ^ 2‖ ≤ 1 := by
      have h := i2
      simp only [WeierstrassCurve.variableChange_a₂, h02, h01, mul_zero, sub_zero, zero_add] at h
      rw [norm_mul, norm_pow, hv, one_pow, one_mul] at h
      exact h

    have h3r : ‖3 * C.r‖ ≤ 1 := by
      have e : 3 * C.r = (3 * C.r - C.s ^ 2) + C.s ^ 2 := by ring
      rw [e]
      refine (PadicComplex.isNonarchimedean p _ _).trans (max_le ha2 ?_)
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hs
    rwa [norm_mul, h3, one_mul] at h3r
  exact ⟨norm_u_of C hv, hv, hr, hs, ht⟩

end Norms

section G

variable {p : ℕ} [Fact p.Prime]

theorem mulBy_g (g : G1 p) (hOk : g.Ok) (c : ℂ_[p]) :
    (g.mulBy c (Xv ()) : MvPowerSeries Unit ℂ_[p]) =
      Formalism.L2.Th1.C.mulBy (Formalism.L2.Th1.A.logSer g.W) (Formalism.L2.Th1.A.expSer g.W) c := by
  have hl : g.l = Formalism.L2.Th1.A.logSer g.W := Formalism.L2.KerInert.Dict.formal_logarithm_agree p g.W g.wq hOk.2.1
  have he : g.ex = Formalism.L2.Th1.A.expSer g.W := Formalism.L2.KerInert.Dict.formal_exponential_agree p g hOk
  have hX : PowerSeries.subst (Xv () : MvPowerSeries Unit ℂ_[p]) g.l = g.l := by
    show PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[p]) g.l = g.l
    rw [← one_smul ℂ_[p] (PowerSeries.X : PowerSeries ℂ_[p]), ← PowerSeries.rescale_eq_subst,
      PowerSeries.rescale_one, RingHom.id_apply]
  unfold G1.mulBy G1.pt G1.lg Formalism.L2.Th1.C.mulBy
  rw [hX, hl, he]
  rfl

theorem coeffIn_g (g : G1 p) (hOk : g.Ok) : Formalism.L2.Th1.C.CoeffIn (RB p) g.W := by
  obtain ⟨⟨h1, h2, h3, h4, h6, -⟩, -⟩ := hOk
  exact ⟨h1, h2, h3, h4, h6⟩

theorem integralMv_of_endInt (g : G1 p) (hOk : g.Ok) (c : ℂ_[p])
    (h : Formalism.L2.Th1.C.EndInt (RB p) (Formalism.L2.Th1.A.logSer g.W) (Formalism.L2.Th1.A.expSer g.W) c) :
    IntegralMv (g.mulBy c (Xv ()) : MvPowerSeries Unit ℂ_[p]) := by
  rw [mulBy_g g hOk c]
  unfold Formalism.L2.Th1.C.EndInt Formalism.L2.Th1.C.IntPS at h
  unfold IntegralMv
  intro n
  have hn : n = Finsupp.single () (n ()) := Finsupp.ext fun u => by
    cases u
    simp
  rw [hn]
  exact h (n ())

end G

section Main

theorem endInt_omega (hInv : Formalism.L2.KerInert.Sigma.InvAlg) (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K))
    (δ : ℂ) (g : G1 p) (hAt : At D cc δ g) (h5 : 5 ≤ p) (hIn : InertK D p) (hOW : ModelOverW g.lam g.abelian₂ g.C) :
    ∃ ι : ℂ ≃+* ℂ_[p], Formalism.L2.KerInert.IotaExt g.lam ι ∧
      Formalism.L2.Th1.C.EndInt (RB p) (Formalism.L2.Th1.A.logSer g.W) (Formalism.L2.Th1.A.expSer g.W) (ι (Formalism.L2.Th1.CM.omegaK D.host.d)) := by
  obtain ⟨hcurve, -, hδ12, hLam, hOk⟩ := hAt
  have hcc : cc ≠ ⊥ := hcurve.1
  have hδ : δ ≠ 0 := by
    intro h0
    obtain ⟨⟨L1, hL1⟩, -⟩ := Formalism.L2.Th1.F2.lamOfLat D cc 1 hcc one_ne_zero
    obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L1 (congrArg (fun A : AddSubgroup ℂ => (A : Set ℂ)) hL1)
    have hd := Formalism.L2.Th1.F.discNeZero L1
    apply hd
    have h12 := hδ12
    unfold Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice Formalism.MainNotions.TaylorLogMetric.discr at h12
    rw [h0, e2, e3] at h12
    rw [← h12]; norm_num
  obtain ⟨⟨L, hL⟩, hCM⟩ := Formalism.L2.Th1.F2.lamOfLat D cc δ hcc hδ
  have hLg : g.abelian₂ = L.lattice.toAddSubgroup := hLam.trans hL.symm
  obtain ⟨hg2, hg3⟩ := hInv D cc δ hcurve hδ12 L hL
  set a2 : Qbar := ⟨L.g₂, hg2⟩ with ha2
  set a3 : Qbar := ⟨L.g₃, hg3⟩ with ha3
  obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L (congrArg (fun A : AddSubgroup ℂ => (A : Set ℂ)) hLg.symm)
  have hp : p.Prime := Fact.out
  have hdp : D.host.d.Prime := D.host.hyp.2.1
  have hd4 : D.host.d % 4 = 3 := by have := D.host.hyp.2.2.2.1; omega
  have hns : ¬ IsSquare ((-(D.host.d : ℤ) : ℤ) : ZMod p) := ZMod.nonsquare_of_jacobiSym_eq_neg_one hIn
  have hsq' : ¬ ∃ a : ZMod p, a ^ 2 = -(D.host.d : ZMod p) := by
    rintro ⟨a, ha⟩; apply hns; exact ⟨a, by push_cast; rw [← ha]; ring⟩
  have hpd : ¬ p ∣ D.host.d := by
    intro h; apply hsq'; refine ⟨0, ?_⟩
    rw [(ZMod.natCast_eq_zero_iff _ _).2 h]; ring
  have hcmby : Formalism.L2.Th1.CM.HasCMBy D.host.d L := by
    intro ω hω
    have h1 := hCM ω (by rw [← hL]; exact hω)
    rw [← hL] at h1
    have e : Formalism.L2.Th1.CM.omegaK D.host.d = Formalism.L2.Th1.F.cmTheta 1 D.host.d := by
      unfold Formalism.L2.Th1.CM.omegaK Formalism.L2.Th1.F.cmTheta; push_cast; ring
    rw [e]; exact h1
  obtain ⟨ι, hι⟩ := Formalism.L2.KerInert.lamExt p g.lam
  have hιg2 : ι L.g₂ = g.lam a2 := hι a2
  have hιg3 : ι L.g₃ = g.lam a3 := hι a3

  have hwm : wModel g.lam g.abelian₂ = Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃) := by
    have e4 : lamC g.lam (-(g2 g.abelian₂) / 4) = -(g.lam a2) / 4 := by
      have : -(g2 g.abelian₂) / 4 = ((-a2 / 4 : Qbar) : ℂ) := by rw [e2]; push_cast; rfl
      rw [this, Formalism.L2.KerInert.Sigma.lamC_coe, map_div₀, map_neg, map_ofNat]
    have e6 : lamC g.lam (-(g3 g.abelian₂) / 4) = -(g.lam a3) / 4 := by
      have : -(g3 g.abelian₂) / 4 = ((-a3 / 4 : Qbar) : ℂ) := by rw [e3]; push_cast; rfl
      rw [this, Formalism.L2.KerInert.Sigma.lamC_coe, map_div₀, map_neg, map_ofNat]
    rw [hιg2, hιg3]
    ext <;> simp [wModel, Formalism.L2.Th1.A.shortW, e4, e6]

  set ε : ℂ_[p] := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hε
  have hεne : ε ≠ 0 := Units.ne_zero _
  set g2' : ℂ_[p] := ε ^ 4 * ι L.g₂ with hg2'
  set g3' : ℂ_[p] := ε ^ 6 * ι L.g₃ with hg3'
  let Cε : WeierstrassCurve.VariableChange ℂ_[p] := ⟨g.C.u, 0, 0, 0⟩
  have hW0 : Cε • Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃) = Formalism.L2.Th1.A.shortW g2' g3' := by
    ext <;> simp [Cε, Formalism.L2.Th1.A.shortW, WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄, WeierstrassCurve.variableChange_a₆, hg2', hg3', hε] <;> ring
  have hgW : g.W = (g.C * Cε⁻¹) • Formalism.L2.Th1.A.shortW g2' g3' := by
    rw [G1.W, hwm, mul_smul, ← hW0, inv_smul_smul]
  obtain ⟨i1, i2, i3, i4, i6, hΔ⟩ := hOk.1
  obtain ⟨w1, w2, w3, w4, w6⟩ := hOW
  obtain ⟨k2, k3, n2, n3, nd⟩ := Formalism.L2.KerInert.Sigma.inv_good g.W h5 i1 i2 i3 i4 i6 hΔ w1 w2 w3 w4 w6
  have hW0' := Formalism.L2.KerInert.Sigma.wModel_g g.lam g.abelian₂ a2 a3 e2 e3
  obtain ⟨c2, c3⟩ := Formalism.L2.KerInert.Sigma.g_change g.C (wModel g.lam g.abelian₂)
  have gW2 : Formalism.L2.Th1.A.g₂ g.W = g2' := by
    rw [hg2', hιg2, ← hW0'.1]; exact c2
  have gW3 : Formalism.L2.Th1.A.g₃ g.W = g3' := by
    rw [hg3', hιg3, ← hW0'.2]; exact c3
  rw [gW2] at k2 n2
  rw [gW3] at k3 n3
  rw [gW2, gW3] at nd
  have hgood : Formalism.L2.Th1.CM.IsGoodModel p L ι g2' g3' := ⟨k2, k3, n2, n3, nd, ε, hεne, rfl, rfl⟩
  have hEnd0 := ReciprocityTheory.ChartRestriction.L1.end_integral D.host.d L hd4 hcmby p h5 hpd hsq' ι g2' g3' hgood
  rw [ReciprocityTheory.ChartRestriction.L1.lgS_eq_logSer, Formalism.L2.Th1.A.uSerEq ℂ_[p] g2' g3'] at hEnd0
  have hE0 : Formalism.L2.Th1.C.EndInt (RB p) (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW g2' g3'))
      (Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW g2' g3')) (ι (Formalism.L2.Th1.CM.omegaK D.host.d)) := fun n => hEnd0 n

  obtain ⟨t2, -⟩ := norm_two_three (p := p) h5
  have t4 : ‖(4 : ℂ_[p])‖ = 1 := by
    rw [show (4 : ℂ_[p]) = 2 * 2 by norm_num, norm_mul, t2, one_mul]
  have hΔ0 : ‖(Formalism.L2.Th1.A.shortW g2' g3').Δ‖ = 1 := by
    have e : (Formalism.L2.Th1.A.shortW g2' g3').Δ = g2' ^ 3 - 27 * g3' ^ 2 := by
      simp only [Formalism.L2.Th1.A.shortW, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      ring
    rw [e]; exact nd
  have hcoef0 : Formalism.L2.Th1.C.CoeffIn (RB p) (Formalism.L2.Th1.A.shortW g2' g3') := by
    refine ⟨(RB p).zero_mem, (RB p).zero_mem, (RB p).zero_mem, ?_, ?_⟩
    · show ‖-g2' / 4‖ ≤ 1
      rw [norm_div, norm_neg, t4, div_one]; exact n2
    · show ‖-g3' / 4‖ ≤ 1
      rw [norm_div, norm_neg, t4, div_one]; exact n3
  have j1 : ‖((g.C * Cε⁻¹) • Formalism.L2.Th1.A.shortW g2' g3').a₁‖ ≤ 1 := by rw [← hgW]; exact i1
  have j2 : ‖((g.C * Cε⁻¹) • Formalism.L2.Th1.A.shortW g2' g3').a₂‖ ≤ 1 := by rw [← hgW]; exact i2
  have j3 : ‖((g.C * Cε⁻¹) • Formalism.L2.Th1.A.shortW g2' g3').a₃‖ ≤ 1 := by rw [← hgW]; exact i3
  have jΔ : ‖((g.C * Cε⁻¹) • Formalism.L2.Th1.A.shortW g2' g3').Δ‖ = 1 := by rw [← hgW]; exact hΔ
  obtain ⟨hu, hui, hr, hs, ht⟩ := vc_params h5 (Formalism.L2.Th1.A.shortW g2' g3') rfl rfl rfl hΔ0 (g.C * Cε⁻¹) j1 j2 j3 jΔ
  refine ⟨ι, hι, ?_⟩
  rw [hgW]
  exact Formalism.L2.KerInert.VC.endInt_varChange _ hcoef0 _ hu.le hui.le hr hs ht _ hE0

open Formalism.L2.Th1.C.Pts in

theorem endInt_OK (D : D7) (p : ℕ) [Fact p.Prime] (g : G1 p) (hOk : g.Ok) (ι : ℂ ≃+* ℂ_[p])
    (hι : Formalism.L2.KerInert.IotaExt g.lam ι)
    (hEg : Formalism.L2.Th1.C.EndInt (RB p) (Formalism.L2.Th1.A.logSer g.W) (Formalism.L2.Th1.A.expSer g.W)
      (ι (Formalism.L2.Th1.CM.omegaK D.host.d))) (a : 𝓞 D.host.K) :
    Formalism.L2.Th1.C.EndInt (RB p) (Formalism.L2.Th1.A.logSer g.W) (Formalism.L2.Th1.A.expSer g.W) (tauK D g.lam (a : D.host.K)) := by
  obtain ⟨hLP, -, -, hFG, -⟩ := Formalism.L2.Th1.C.curveFrame ℂ_[p] (RB p) g.W (coeffIn_g g hOk)
  have hint : ∀ m : ℤ, Formalism.L2.Th1.C.EndInt (RB p) (Formalism.L2.Th1.A.logSer g.W) (Formalism.L2.Th1.A.expSer g.W) (m : ℂ_[p]) := by
    intro m
    induction m using Int.induction_on with
    | zero => simpa using endInt_zero (R := RB p) hLP
    | succ i ih => push_cast; exact endInt_add hLP hFG ih (endInt_one hLP)
    | pred i ih =>
      have e : ((-(i : ℤ) - 1 : ℤ) : ℂ_[p]) = ((-(i : ℤ) : ℤ) : ℂ_[p]) + -1 := by push_cast; ring
      rw [e]; exact endInt_add hLP hFG ih (endInt_neg hLP hFG (endInt_one hLP))
  obtain ⟨ω, hω, hspan⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.covA_span D.host.K D.host.d (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.discriminant_mod_four D)
    ⟨D.host.sqrtMinusD, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_sqrt_mem D⟩ (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_sqrt_sq D)
    (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_finrank_K D)
  have hρι : ∀ x : D.host.K, Formalism.MainNotions.Ext.tauKp D g.lam x = ι (D.host.φ₀ (x : D.host.E)) := by
    intro x
    rw [Formalism.MainNotions.Ext.tauKp_apply]
    exact (Formalism.L2.KerInert.lamCIota p g.lam ι hι).1 _ (Formalism.MainNotions.Ext.test_vector_mem_schwartz_bruhat D _)
  set xs : D.host.K := ⟨D.host.sqrtMinusD, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_sqrt_mem D⟩ with hxs
  have hx2 : (D.host.φ₀ (xs : D.host.E)) ^ 2 = -(D.host.d : ℂ) := by
    have h := congrArg (fun y : D.host.K => D.host.φ₀ (y : D.host.E)) (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_sqrt_sq D)
    rw [← hxs] at h
    push_cast at h
    rw [map_pow] at h
    rw [h, map_neg, map_natCast]
  have hom : (2 * Formalism.L2.Th1.CM.omegaK D.host.d - 1) ^ 2 = -(D.host.d : ℂ) := by
    unfold Formalism.L2.Th1.CM.omegaK
    have hsq : ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 = (D.host.d : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; push_cast; rfl
    linear_combination (-1 : ℂ) * hsq + (((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2) * Complex.I_sq
  have h2E : ((2 : D.host.K) : D.host.E) = 2 := by
    rw [show (2 : D.host.K) = 1 + 1 by norm_num]; push_cast; norm_num
  have hωφ : D.host.φ₀ ((ω : D.host.K) : D.host.E) = (1 + D.host.φ₀ (xs : D.host.E)) / 2 := by
    rw [hω]; push_cast; simp only [map_div₀, map_add, map_one]; rw [h2E, map_ofNat]
  have hρω : Formalism.L2.Th1.C.EndInt (RB p) (Formalism.L2.Th1.A.logSer g.W) (Formalism.L2.Th1.A.expSer g.W)
      (Formalism.MainNotions.Ext.tauKp D g.lam (ω : D.host.K)) := by
    rw [hρι, hωφ]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hx2.trans hom.symm) with h | h
    · have e : (1 + D.host.φ₀ (xs : D.host.E)) / 2 = Formalism.L2.Th1.CM.omegaK D.host.d := by
        rw [h]; ring
      rw [e]; exact hEg
    · have e : ι ((1 + D.host.φ₀ (xs : D.host.E)) / 2) = 1 + -ι (Formalism.L2.Th1.CM.omegaK D.host.d) := by
        have e' : (1 + D.host.φ₀ (xs : D.host.E)) / 2 = 1 - Formalism.L2.Th1.CM.omegaK D.host.d := by
          rw [h]; ring
        rw [e', map_sub, map_one]; ring
      rw [e]; exact endInt_add hLP hFG (endInt_one hLP) (endInt_neg hLP hFG hEg)
  have hc : ∀ k : ℤ, ((k : 𝓞 D.host.K) : D.host.K) = (k : D.host.K) := fun k => by
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap, map_intCast]
  have htau : tauK D g.lam (a : D.host.K) = Formalism.MainNotions.Ext.tauKp D g.lam (a : D.host.K) :=
    (Formalism.MainNotions.Ext.tauKp_apply D g.lam _).symm
  rw [htau]
  obtain ⟨m, n, rfl⟩ := hspan a
  have e : (((m : 𝓞 D.host.K) + (n : 𝓞 D.host.K) * ω : 𝓞 D.host.K) : D.host.K) =
      (m : D.host.K) + (n : D.host.K) * (ω : D.host.K) := by
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap, map_add, map_mul, map_intCast, map_intCast,
      ← NumberField.RingOfIntegers.coe_eq_algebraMap]
  rw [e, map_add, map_mul, map_intCast, map_intCast]
  exact endInt_add hLP hFG (hint m) (endInt_mul hLP (hint n) hρω)

theorem endIntInert_of (hInv : Formalism.L2.KerInert.Sigma.InvAlg) : EndIntInert := by
  intro D p _ cc δ g hAt h5 hIn hOW α hα
  have hOk : g.Ok := hAt.2.2.2.2
  obtain ⟨ι, hι, hEg⟩ := endInt_omega hInv D p cc δ g hAt h5 hIn hOW
  obtain ⟨hLP, -, -, -, -⟩ := Formalism.L2.Th1.C.curveFrame ℂ_[p] (RB p) g.W (coeffIn_g g hOk)
  have hRB : IsClosed ((RB p : Subring ℂ_[p]) : Set ℂ_[p]) :=
    isClosed_le continuous_norm continuous_const
  have hcl := Formalism.L2.Th1.C.endIntClosed ℂ_[p] (RB p) hRB (Formalism.L2.Th1.A.logSer g.W) (Formalism.L2.Th1.A.expSer g.W) hLP.1
  have hmaps : Set.MapsTo Prod.fst (Set.range fun a : 𝓞 D.host.K =>
      (tauK D g.lam (a : D.host.K), tauKc D g.lam (a : D.host.K)))
      {c : ℂ_[p] | Formalism.L2.Th1.C.EndInt (RB p) (Formalism.L2.Th1.A.logSer g.W) (Formalism.L2.Th1.A.expSer g.W) c} := by
    rintro _ ⟨a, rfl⟩
    exact endInt_OK D p g hOk ι hι hEg a
  exact integralMv_of_endInt g hOk α.1 (hcl.closure_subset (map_mem_closure continuous_fst hα hmaps))

end Main

end Formalism.L2.KerInert.IwahoriBlocks

namespace Formalism.L2.KerInert

theorem endomorphisms_integral_inert : EndIntInert := by
  exact IwahoriBlocks.endIntInert_of Sigma.invAlg'

end Formalism.L2.KerInert
