import Formalism.LocalToGlobal.InertKernelTheory.GenusOneModelExistsLattice
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.PadicNormTwoHundredSixteenEqOneOfFiveLe
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowTwoTorsionWp
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CubeThreeR
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.CurveIdealPrimeReduction

noncomputable section

namespace Formalism.L2.KerInert.GenusOneDatumExistence

open Formalism.MainNotions.GL3Theta Formalism.L2.G.Pend PowerSeries

section Gen

variable {p : ℕ} [Fact p.Prime]

theorem mem_Wp_of_kur {x : ℂ_[p]} (hx : x ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) (h1 : ‖x‖ ≤ 1) : x ∈ Wp p := by
  have hp : p.Prime := Fact.out
  have hB := ((Formalism.L2.Th1.D.kurIntegers p).1 x).2 ⟨hx, h1⟩
  have hS : Formalism.L2.Th1.D.muPrime p = {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ ζ ^ n = 1} := by
    ext ζ
    simp only [Formalism.L2.Th1.D.muPrime, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, h0, hn, h⟩
      exact ⟨n, h0, Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hn), h⟩
    · rintro ⟨n, h0, hn, h⟩
      exact ⟨n, h0, (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.coprime_comm.mp hn), h⟩
  unfold Formalism.L2.Th1.D.ringB Formalism.L2.Th1.D.ringA at hB
  rw [hS] at hB
  exact hB

theorem logF_eq : logF p = Formalism.L2.Th1.CM.ltLog ℂ_[p] p := by
  have hp : p.Prime := Fact.out
  have hinj : Function.Injective (fun j : ℕ => p ^ (2 * j)) := by
    intro a b h
    have := Nat.pow_right_injective hp.two_le h
    simpa using this
  ext n
  simp only [logF, Formalism.L2.Th1.CM.ltLog, coeff_mk]
  split_ifs with h
  · have hj := Nat.find_spec h
    set j0 := Nat.find h
    have hn : n = p ^ (2 * j0) := by rw [hj, ← pow_mul]
    rw [Finset.sum_eq_single j0]
    · rw [if_pos hn]
    · intro j _ hne
      rw [if_neg]
      intro h'
      exact hne (hinj (h'.symm.trans hn))
    · intro hj0
      exfalso
      apply hj0
      rw [Finset.mem_range, hn]
      have : j0 < p ^ j0 := Nat.lt_pow_self hp.one_lt
      have h2 : p ^ j0 ≤ p ^ (2 * j0) := Nat.pow_le_pow_right hp.pos (by omega)
      omega
  · apply Finset.sum_eq_zero
    intro j _
    rw [if_neg]
    intro h'
    exact h ⟨j, by rw [h', pow_mul]⟩

theorem isWq_wU (W : WeierstrassCurve ℂ_[p]) : Formalism.MainNotions.TaylorLogMetric.IsWq W (Formalism.L2.Th1.A.wU W) := by
  have hF := (Formalism.L2.Th1.A.CurveSer.wSer_fixed W).2
  rw [Formalism.L2.Th1.A.CurveSer.wSer_eq] at hF
  unfold Formalism.MainNotions.TaylorLogMetric.IsWq
  simp only [PowerSeries.algebraMap_eq]
  apply mul_left_cancel₀ (pow_ne_zero 3 (X_ne_zero (R := ℂ_[p])))
  linear_combination hF

theorem norm_four (h5 : 5 ≤ p) : ‖(4 : ℂ_[p])‖ = 1 := by
  have hp : p.Prime := Fact.out
  have h := Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd (K := ℂ_[p]) (m := 4) hp
    (Formalism.L2.Th1.D.UnramifiedCompletion.normL_lt_one p) (by
      intro hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega)
  exact_mod_cast h

theorem datum_of_short (h5 : 5 ≤ p) (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
    (C : WeierstrassCurve.VariableChange ℂ_[p]) (g2 g3 : ℂ_[p])
    (hW : C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ = Formalism.L2.Th1.A.shortW g2 g3)
    (k2 : g2 ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) (k3 : g3 ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) (n2 : ‖g2‖ ≤ 1) (n3 : ‖g3‖ ≤ 1)
    (nd : ‖g2 ^ 3 - 27 * g3 ^ 2‖ = 1) (ε : ℂ_[p]) (hε1 : ‖ε‖ = 1)
    (hint : ∀ n : ℕ,
      PowerSeries.coeff n ((Formalism.L2.Th1.CM.uSer g2 g3).subst (PowerSeries.C ε * Formalism.L2.Th1.CM.ltLog ℂ_[p] p)) ∈
          Formalism.L2.Th1.CM.MaximalUnramifiedExtension p ∧
        ‖PowerSeries.coeff n ((Formalism.L2.Th1.CM.uSer g2 g3).subst
          (PowerSeries.C ε * Formalism.L2.Th1.CM.ltLog ℂ_[p] p))‖ ≤ 1) :
    ∃ g : G1 p, g.lam = lam ∧ g.abelian₂ = Λ ∧ g.C = C ∧ g.Ok ∧ ModelOverW g.lam g.abelian₂ g.C ∧ LTIso g := by
  set S := Formalism.L2.Th1.A.shortW g2 g3 with hS
  let g : G1 p := ⟨lam, Λ, C, Formalism.L2.Th1.A.wU S, Formalism.L2.Th1.A.expSer S⟩
  have hgW : g.W = S := hW
  have h4 := norm_four (p := p) h5
  have hWq : Formalism.MainNotions.TaylorLogMetric.IsWq g.W g.wq := by
    rw [hgW]; exact isWq_wU S
  obtain ⟨hx0, -, hLE, hEL, -⟩ := Formalism.L2.Th1.A.expSpec ℂ_[p] S
  have hfl : Formalism.MainNotions.TaylorLogMetric.flog S (Formalism.L2.Th1.A.wU S) = Formalism.L2.Th1.A.logSer S :=
    Formalism.L2.KerInert.Dict.formal_logarithm_agree p S _ (isWq_wU S)
  have hΔ : S.Δ = g2 ^ 3 - 27 * g3 ^ 2 := (Formalism.L2.Th1.A.shortInv ℂ_[p] g2 g3).2.2.2
  have na4 : ‖S.a₄‖ ≤ 1 := by
    simp only [hS, Formalism.L2.Th1.A.shortW, norm_div, norm_neg, h4, div_one]; exact n2
  have na6 : ‖S.a₆‖ ≤ 1 := by
    simp only [hS, Formalism.L2.Th1.A.shortW, norm_div, norm_neg, h4, div_one]; exact n3
  have hU : IsModelU lam Λ C := by
    show Formalism.MainNotions.TaylorLogMetric.IsIntP (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₁ ∧ Formalism.MainNotions.TaylorLogMetric.IsIntP (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₂ ∧
      Formalism.MainNotions.TaylorLogMetric.IsIntP (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₃ ∧ Formalism.MainNotions.TaylorLogMetric.IsIntP (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₄ ∧
      Formalism.MainNotions.TaylorLogMetric.IsIntP (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₆ ∧ ‖(C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).Δ‖ = 1
    rw [hW]
    refine ⟨?_, ?_, ?_, na4, na6, by rw [hΔ]; exact nd⟩ <;> simp [Formalism.MainNotions.TaylorLogMetric.IsIntP, hS, Formalism.L2.Th1.A.shortW]
  have hOk : g.Ok := by
    refine ⟨hU, hWq, hx0, ?_⟩
    show PowerSeries.subst (Formalism.L2.Th1.A.expSer S) (Formalism.MainNotions.TaylorLogMetric.flog g.W (Formalism.L2.Th1.A.wU S)) = PowerSeries.X
    rw [hgW, hfl]
    exact hLE
  have hM : ModelOverW lam Λ C := by
    show (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₁ ∈ Wp p ∧ (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₂ ∈ Wp p ∧
      (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₃ ∈ Wp p ∧ (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₄ ∈ Wp p ∧
      (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₆ ∈ Wp p
    rw [hW]
    refine ⟨by simp [hS, Formalism.L2.Th1.A.shortW], by simp [hS, Formalism.L2.Th1.A.shortW],
      by simp [hS, Formalism.L2.Th1.A.shortW], mem_Wp_of_kur ?_ na4, mem_Wp_of_kur ?_ na6⟩
    · simp only [hS, Formalism.L2.Th1.A.shortW]
      exact div_mem (neg_mem k2) (ofNat_mem _ 4)
    · simp only [hS, Formalism.L2.Th1.A.shortW]
      exact div_mem (neg_mem k3) (ofNat_mem _ 4)
  have hpt : (g.pt (MvPowerSeries.C ε * logF p) : MvPowerSeries Unit ℂ_[p]) =
      (Formalism.L2.Th1.CM.uSer g2 g3).subst (PowerSeries.C ε * Formalism.L2.Th1.CM.ltLog ℂ_[p] p) := by
    show PowerSeries.subst (MvPowerSeries.C ε * logF p) (Formalism.L2.Th1.A.expSer S) = _
    rw [hS, ← Formalism.L2.Th1.A.uSerEq, logF_eq]
    rfl
  have hΘ : IntegralW (g.pt (MvPowerSeries.C ε * logF p) : MvPowerSeries Unit ℂ_[p]) := by
    intro n
    rw [hpt, Finsupp.unique_single n]
    exact mem_Wp_of_kur (hint (n ())).1 (hint (n ())).2
  exact ⟨g, rfl, rfl, rfl, hOk, hM, ltIso_of' g hOk hε1 hΘ⟩

end Gen

open NumberField Formalism.BasicNotions

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in

theorem genus_one_datum_exists (hInv : Formalism.L2.KerInert.Sigma.InvAlg) : Formalism.L2.KerInert.GenusOneModelExists := by
  intro D cc δ hcurve hδ12 p _ hcop h5 hIn lam
  have hp : p.Prime := Fact.out
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
  obtain ⟨hg2, hg3⟩ := hInv D cc δ hcurve hδ12 L hL
  obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L (congrArg (fun A : AddSubgroup ℂ => (A : Set ℂ)) hL)
  set a2 : Formalism.MainNotions.TaylorLogMetric.Qbar := ⟨L.g₂, hg2⟩ with ha2
  set a3 : Formalism.MainNotions.TaylorLogMetric.Qbar := ⟨L.g₃, hg3⟩ with ha3
  obtain ⟨ι, hι⟩ := Formalism.L2.KerInert.lamExt p lam

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

  obtain ⟨g2', g3', hGood⟩ := Formalism.L2.Th1.CM.cm2 D.host.d L hdp.squarefree hd4 hcmby p h5 hpd ι
  obtain ⟨ε, -, hε1, hεint⟩ :=
    Formalism.L2.Th1.CM.cm3 D.host.d L hdp.squarefree hd4 hcmby p h5 hpd hsq' ι g2' g3' hGood
  obtain ⟨k2, k3, n2, n3, nd, μ, hμ, hg2', hg3'⟩ := hGood

  let C : WeierstrassCurve.VariableChange ℂ_[p] := ⟨(Units.mk0 μ hμ)⁻¹, 0, 0, 0⟩
  have ea4 : Formalism.MainNotions.TaylorLogMetric.lamC lam (-(Formalism.MainNotions.TaylorLogMetric.g2 (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ)) / 4) = -(ι L.g₂) / 4 := by
    have : -(Formalism.MainNotions.TaylorLogMetric.g2 (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ)) / 4 = ((-a2 / 4 : Formalism.MainNotions.TaylorLogMetric.Qbar) : ℂ) := by
      rw [e2]; push_cast; rfl
    rw [this, Formalism.L2.KerInert.Sigma.lamC_coe, map_div₀, map_neg, map_ofNat, ← hι a2]
  have ea6 : Formalism.MainNotions.TaylorLogMetric.lamC lam (-(Formalism.MainNotions.TaylorLogMetric.g3 (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ)) / 4) = -(ι L.g₃) / 4 := by
    have : -(Formalism.MainNotions.TaylorLogMetric.g3 (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ)) / 4 = ((-a3 / 4 : Formalism.MainNotions.TaylorLogMetric.Qbar) : ℂ) := by
      rw [e3]; push_cast; rfl
    rw [this, Formalism.L2.KerInert.Sigma.lamC_coe, map_div₀, map_neg, map_ofNat, ← hι a3]
  have hW : C • Formalism.MainNotions.TaylorLogMetric.wModel lam (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) = Formalism.L2.Th1.A.shortW g2' g3' := by
    have hw : Formalism.MainNotions.TaylorLogMetric.wModel lam (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) = ⟨0, 0, 0, -(ι L.g₂) / 4, -(ι L.g₃) / 4⟩ := by
      simp only [Formalism.MainNotions.TaylorLogMetric.wModel, ea4, ea6]
    rw [hw]
    ext <;> simp [C, Formalism.L2.Th1.A.shortW, hg2', hg3', WeierstrassCurve.variableChange_a₁,
      WeierstrassCurve.variableChange_a₂, WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆] <;> ring
  obtain ⟨g, hgl, hgL, -, hOk, hM, hLT⟩ :=
    datum_of_short h5 lam (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) C g2' g3' hW k2 k3 n2 n3 nd ε hε1 hεint
  exact ⟨g, hgl, ⟨hcurve, hcop, hδ12, hgL, hOk⟩, hM, hLT⟩

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in

theorem genus_one_datum_exists_lattice (hInv : Formalism.L2.KerInert.Sigma.InvAlg) : Formalism.L2.KerInert.GenusOneModelExistsLattice := by
  intro D cc δ hcurve hδ12 p _ h5 hIn lam
  obtain ⟨cc', δ', hc', hd', hcop, hlat⟩ := Formalism.L2.KerInert.curve_ideal_prime D cc δ hcurve hδ12 p hIn
  obtain ⟨g, hgl, hAt, hM, hLT⟩ := genus_one_datum_exists hInv D cc' δ' hc' hd' p hcop h5 hIn lam
  exact ⟨cc', δ', g, hc', hd', hlat.symm, hgl, hAt, hM, hLT⟩

end Formalism.L2.KerInert.GenusOneDatumExistence
