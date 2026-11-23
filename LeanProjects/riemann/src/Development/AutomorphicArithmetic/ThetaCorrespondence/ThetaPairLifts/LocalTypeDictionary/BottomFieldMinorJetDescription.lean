import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodAlgebraicIdealExpansion
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KernelEqSumOfJets
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodAlgebraicIdealExpansionStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.BottomFieldDict
theorem vacuum_translate_minor_jet_alt : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ → IsBottomTri W i j X →
    ∀ n : D.what₂.Tau → ℕ, ∃ Ω : ℂ, Ω ≠ 0 ∧ ∃ (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) (e0 : TaylorLogMetric.VC D A'.rank WW.rank → ℂ),
      StandardLatticesGL3.Crv D cc δ ∧ GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc δ) t0 ∧ StandardLatticesGL3.oddE0 D cc δ t0 A'.rank WW.rank e0 ∧
      ∃ Qf : GlobalTheory.NormSum.Tup D A'.rank WW.rank n → MvPolynomial (GL3Theta.Idx D A'.rank WW.rank) ℂ,
        (∀ U α, IsAlgebraic ℚ ((Qf U).coeff α)) ∧
        ∀ w : WO A' WW, w.map (infPart D) = 0 → (∃ m : ℕ, 0 < m ∧ m • w ∈ latO A' WW X.rA'.Λ X.rW.Λ fun _ => True) →
          ∃ (ζ : ℂ) (s : TaylorLogMetric.VC D A'.rank WW.rank), IsAlgebraic ℚ ζ ∧
            StandardLatticesGL3.LaQ D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D A'.rank) (StandardLatticesGL3.stdL D WW.rank) s ∧
            ∀ U : GlobalTheory.NormSum.Tup D A'.rank WW.rank n,
              pureTensorO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.B X.rW.B (heisO W.ψ A' WW w X.vac') (GlobalTheory.NormSum.minorPol D U) 0 =
                Ω * (ζ * GL3Theta.applyAt0 D (Qf U) (TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) s e0)) := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ _ hX n
  obtain ⟨δ, hc, hδ⟩ := GlobalTheory.FunObj.exists_delta D
  obtain ⟨t0, ht0⟩ := (GlobalTheory.TwoTorsionPt.exists_point D D.host.ccK δ hc).1
  have hd : Even WW.rank := by
    rw [← hX.is.rank, hX.rank, hX.rank']
    obtain ⟨h1, h2, h3⟩ := SqNum.ranks_exact D i j
    exact ⟨SqNum.halfRank D i j - (D.R.m - (j + 1)) / 2 - (D.R.m - j) / 2, by omega⟩
  obtain ⟨e0, he0, he0ne⟩ := GlobalTheory.Vacuum.exists_vacuum D D.host.ccK δ hc t0 ht0 A'.rank WW.rank (hd.mul_left _)
  have hon : ∀ {V : HSp D}, V.gram = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin V.rank) D.host.E).1 *
      V.gram * (1 : GL (Fin V.rank) D.host.E).1 = 1 := by
    intro V hV
    rw [hV]
    simp [Formalism.UG.cT]
  have hfr : ∀ {V : HSp D} {r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V}, r.IsStd → r.B = GlobalTheory.FockPos.frAt (1 : GL (Fin V.rank) D.host.E) := by
    intro V r hr
    funext τ
    rw [(hr.2.2 τ).2]
    simp [GlobalTheory.FockPos.frAt]
  have hS := hon hX.std'.1
  have hT := hon hX.stdW.1
  have hcS := fun τ => (hX.is.rigA'.2.2 τ).1
  have hcT := fun τ => (hX.is.rigW.2.2 τ).1
  have hv := hX.is.isVac'
  have hv1 := hv
  rw [lat_eq_colLat hX.std', lat_eq_colLat hX.stdW] at hv1
  obtain ⟨Θ, hΘ, hΘ0, hj⟩ := GlobalTheory.FockPos.fock_jets_eq_theta W.ψ W.θ A' WW _ _ 1 1 hS hT hcS hcT δ hc hδ _ hv1
  have hG1 := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨c, hce⟩ := (GlobalTheory.ThetaLine.theta_line D hG1 _ δ hc _ _ _
    (Or.inr ⟨_, _, GlobalTheory.FinWeil.Vacuum.sd_std D _, GlobalTheory.FinWeil.Vacuum.sd_std D _, rfl⟩)).1 Θ hΘ e0 he0.1 he0ne
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hΘ0 (by rw [hce, zero_smul])
  set p : ℂ := δ * (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) with hp
  have hper : ∀ τ : D.what₂.Tau, GlobalTheory.FunObj.period δ τ = p := fun τ => by
    rw [GlobalTheory.FunObj.period, GlobalTheory.AdTh.Fock.norm_embedding_hostFormConstant_eq, div_eq_mul_inv]
  have hp0 : p ≠ 0 := by
    refine mul_ne_zero hδ (inv_ne_zero ?_)
    have hx : 0 < Formalism.L2.Pj.xiR D := GlobalTheory.SupDict.xiR_pos D
    exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne'
  have hprod : ∀ k : GL3Theta.Idx D A'.rank WW.rank →₀ ℕ,
      (k.prod fun v e => GlobalTheory.FunObj.period δ v.1 ^ e) = p ^ (k.sum fun _ e => e) := fun k => by
    simp only [hper, Finsupp.prod, Finsupp.sum]
    exact Finset.prod_pow_eq_pow_sum _ _ _
  refine ⟨c * p ^ (A'.rank * ∑ τ, n τ), mul_ne_zero hc0 (pow_ne_zero _ hp0), D.host.ccK, δ, t0, e0, hc, ht0, he0,
    fun U => GlobalTheory.NormSum.minorPol D U, fun U α => minorPol_coeff_isAlgebraic U α, ?_⟩
  rintro w - ⟨m, hm, hw⟩
  rw [lat_eq_inV hX.std', lat_eq_inV hX.stdW] at hv hw
  obtain ⟨ζ, s, hζ, hs, hk⟩ := GlobalTheory.HeisTrans.core W.ψ W.θ A' WW _ _ 1 1 hS hT hcS hcT _ _
    (GlobalTheory.FinWeil.Vacuum.sd_std D _) (GlobalTheory.FinWeil.Vacuum.sd_std D _) δ hδ e0 he0.1.1 c X.vac' hv (fun k => by
      have h := hj k
      rw [hce, GlobalTheory.FunObj.TopJet.applyAt0_monomial, GlobalTheory.FunObj.TopJet.taylor_const_smul D e0 he0.1.1] at h
      rw [GlobalTheory.FunObj.TopJet.applyAt0_monomial]
      refine h.trans ?_
      ring) m hm w hw
  obtain ⟨ζ', hζ', -⟩ := GlobalTheory.HeisTrans.qbar_of_root hζ
  refine ⟨ζ, s, hζ' ▸ mem_algebraicClosure_iff.1 ζ'.2, ⟨m, hm, hs⟩, fun U => ?_⟩
  have hUd : Differentiable ℂ (TaylorLogMetric.U D (TaylorLogMetric.tor0 D D.host.ccK δ) s e0) := by
    have h : Differentiable ℂ (fun z : TaylorLogMetric.VC D A'.rank WW.rank => TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D D.host.ccK δ) z s) := by
      unfold TaylorLogMetric.Hf
      fun_prop
    have h0 : Differentiable ℂ e0 := he0.1.1
    unfold TaylorLogMetric.U
    fun_prop
  rw [hfr hX.std', hfr hX.stdW]
  refine apply_minorPol U ((LinearMap.proj (0 : WO A' WW)).comp (pureTensorO W.ψ W.θ A' WW X.rA'.s X.rW.s
    (GlobalTheory.FockPos.frAt 1) (GlobalTheory.FockPos.frAt 1) (heisO W.ψ A' WW w X.vac'))) c p ζ _ fun k => ?_
  have h := hk k
  rw [hprod k, GlobalTheory.FunObj.TopJet.applyAt0_monomial] at h
  have e : (fun z => ζ * TaylorLogMetric.U D (TaylorLogMetric.tor0 D D.host.ccK δ) s e0 z) = ζ • TaylorLogMetric.U D (TaylorLogMetric.tor0 D D.host.ccK δ) s e0 := rfl
  rw [e, GlobalTheory.FunObj.TopJet.taylor_const_smul D _ hUd] at h
  rw [GlobalTheory.FunObj.TopJet.applyAt0_monomial]
  refine h.trans ?_
  ring
theorem kernel_minor_polynomial_eq_jet : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∀ n : D.what₂.Tau → ℕ, ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ (t : T), ∀ x ∈ GfC A', ∀ h ∈ GfC WW,
      ∃ (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) (e0 : TaylorLogMetric.VC D A'.rank WW.rank → ℂ) (k : ℕ) (c : Fin k → ℂ)
        (s : Fin k → TaylorLogMetric.VC D A'.rank WW.rank),
        StandardLatticesGL3.Crv D cc δ ∧ GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc δ) t0 ∧ StandardLatticesGL3.oddE0 D cc δ t0 A'.rank WW.rank e0 ∧
        (∀ l, IsAlgebraic ℚ (c l)) ∧ (∀ l, StandardLatticesGL3.LaQ D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D A'.rank) (StandardLatticesGL3.stdL D WW.rank) (s l)) ∧
        ∀ U : GlobalTheory.NormSum.Tup D A'.rank WW.rank n, ∃ Q : MvPolynomial (GL3Theta.Idx D A'.rank WW.rank) ℂ,
          (∀ α, IsAlgebraic ℚ (Q.coeff α)) ∧
          X.ker' W.ψ W.θ t (GlobalTheory.NormSum.minorPol D U) h x = Ω * GL3Theta.applyAt0 D Q (StandardLatticesGL3.comb D (TaylorLogMetric.tor0 D cc δ) c s e0) := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX n
  obtain ⟨Ω, hΩ, cc, δ, t0, e0, hc, ht0, he0, Qf, hQf, H⟩ :=
    _root_.GlobalTheory.BottomFieldDict.vacuum_translate_minor_jet_alt hP hI hL hX n
  refine ⟨Ω, hΩ, fun t x hx h hh => ?_⟩
  obtain ⟨k, c, w, hca, hwf, hwl, hexp⟩ := _root_.GlobalTheory.BotExpand.kernel_eq_sum_of_jets hP hI hL hX t x hx h hh
  choose ζ s hζ hs hζeq using fun l => H (w l) (hwf l) (hwl l)
  have hd : Differentiable ℂ e0 := he0.1.1
  have hU : ∀ l, Differentiable ℂ (TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) (s l) e0) := fun l => by
    have h1 : Differentiable ℂ (fun z : TaylorLogMetric.VC D A'.rank WW.rank => TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) z (s l)) := by
      unfold TaylorLogMetric.Hf
      fun_prop
    unfold TaylorLogMetric.U
    fun_prop
  refine ⟨cc, δ, t0, e0, k, fun l => c l * ζ l, s, hc, ht0, he0, fun l => (hca l).mul (hζ l), hs,
    fun U => ⟨Qf U, hQf U, ?_⟩⟩
  rw [hexp]
  unfold StandardLatticesGL3.comb
  rw [GlobalTheory.LiftTypePrime.Jets.applyAt0_comb Finset.univ _ _ hU, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hζeq l U]
  ring
end GlobalTheory.BottomFieldDict
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_field_minor_jet_description : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∀ n : D.what₂.Tau → ℕ, ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ (t : T), ∀ x ∈ GfC A', ∀ h ∈ GfC WW,
      ∃ (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) (e0 : TaylorLogMetric.VC D A'.rank WW.rank → ℂ) (k : ℕ) (c : Fin k → ℂ)
        (s : Fin k → TaylorLogMetric.VC D A'.rank WW.rank),
        StandardLatticesGL3.Crv D cc δ ∧ GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc δ) t0 ∧ StandardLatticesGL3.oddE0 D cc δ t0 A'.rank WW.rank e0 ∧
        (∀ l, IsAlgebraic ℚ (c l)) ∧ (∀ l, StandardLatticesGL3.LaQ D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D A'.rank) (StandardLatticesGL3.stdL D WW.rank) (s l)) ∧
        ∀ U : GlobalTheory.NormSum.Tup D A'.rank WW.rank n, ∃ Q : MvPolynomial (GL3Theta.Idx D A'.rank WW.rank) ℂ,
          (∀ α, IsAlgebraic ℚ (Q.coeff α)) ∧
          X.ker' W.ψ W.θ t (GlobalTheory.NormSum.minorPol D U) h x = Ω * GL3Theta.applyAt0 D Q (StandardLatticesGL3.comb D (TaylorLogMetric.tor0 D cc δ) c s e0) := by
  first | exact @_root_.GlobalTheory.BottomFieldDict.kernel_minor_polynomial_eq_jet | exact _root_.GlobalTheory.BottomFieldDict.kernel_minor_polynomial_eq_jet | (intros; apply _root_.GlobalTheory.BottomFieldDict.kernel_minor_polynomial_eq_jet <;> assumption)
end
