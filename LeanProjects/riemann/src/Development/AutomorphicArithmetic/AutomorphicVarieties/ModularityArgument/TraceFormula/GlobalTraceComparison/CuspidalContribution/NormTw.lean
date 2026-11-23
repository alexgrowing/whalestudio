import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.LevShrink
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CuspSupportOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieCentralElementTraceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceOperatorEigenvalueSumStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralEigenExponentialStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AuxiliaryCuspLemmaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitTwistBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatAbsoluteCharacter
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpTwA
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStringStepB
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.LogAbsEqLogIdeleNorm

open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.LFun UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp

open GlobalTheory.Mem.Chr.CharModel
open scoped nonZeroDivisors

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E]

private theorem log_norm_coord (t : (Af E)ˣ) (w : HeightOneSpectrum (𝓞 E)) :
    Real.log ‖(t : Af E) w‖ = -((GlobalTheory.Idele.ord_vw t w : ℝ) * Real.log (Ideal.absNorm w.asIdeal : ℕ)) := by
  have hq : ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ≠ 0 := by
    simpa [Ideal.absNorm_eq_zero_iff] using w.ne_bot
  have e : ∀ (n : ℤ) (h : WithZero.exp n ≠ 0), Multiplicative.toAdd (WithZero.unzero h) = n := fun _ _ => rfl
  rw [FinitePlace.norm_def, GlobalTheory.Idele.valued_idele, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, e]
  simp [Real.log_zpow]

private theorem logFin_eq (t : (Af E)ˣ) : logFin E t = -∑ᶠ w, Real.log ‖(t : Af E) w‖ := by
  classical
  have hfin := Filter.eventually_cofinite.1 (GlobalTheory.Idele.ord_vw_eventually_zero t)
  have h1 : GlobalTheory.Idele.idealOf t = ∏ v ∈ hfin.toFinset, (v.asIdeal : FractionalIdeal (𝓞 E)⁰ E) ^ GlobalTheory.Idele.ord_vw t v := by
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    simp only [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    intro h0
    exact hv (by simp [h0])
  have h2 : ∑ᶠ w, Real.log ‖(t : Af E) w‖ = ∑ w ∈ hfin.toFinset, Real.log ‖(t : Af E) w‖ := by
    refine finsum_eq_sum_of_support_subset _ fun v hv => ?_
    simp only [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    intro h0
    apply hv
    change Real.log ‖(t : Af E) v‖ = 0
    rw [log_norm_coord, h0]
    simp
  have hq : ∀ v : HeightOneSpectrum (𝓞 E), ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ≠ 0 := fun v => by
    simpa [Ideal.absNorm_eq_zero_iff] using v.ne_bot
  rw [logFin, h1, map_prod, Rat.cast_prod, Real.log_prod, h2, ← Finset.sum_neg_distrib]
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [log_norm_coord, neg_neg, map_zpow₀, FractionalIdeal.coeIdeal_absNorm]
    push_cast
    rw [Real.log_zpow]
  · intro v _
    rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm]
    push_cast
    exact zpow_ne_zero _ (hq v)

end SlopeTestRemainingChoices

section Aux2

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem logAbs_eq_logNorm (u : (Ad E)ˣ) : PositivityTheory.Rg.BcB.logAbs (u : Ad E) = logNorm E u := by
  rw [logNorm, logFin_eq, PositivityTheory.Rg.BcB.logAbs, logInf, sub_neg_eq_add]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Real.log_pow, DiscreteGroups.T1.G.norm_cV_eq, DiscreteGroups.T1.G.mult_eq_two]
  rfl

end Aux2

section Aux3

open UpperTheory.V.Cj.S (Pl)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

private theorem det_coord_le {bad : Set (Pl E)} {K : Subgroup (GL (Fin N) (Af E))} (hK : Lev bad K)
    {x : GL (Fin N) (Af E)} (hx : x ∈ K) (w : HeightOneSpectrum (𝓞 E)) :
    Valued.v (((GeneralLinearGroup.det x : (Af E)ˣ) : Af E) w) ≤ 1 := by
  obtain ⟨a, ha⟩ := hK.int x hx w
  have e1 : ((GeneralLinearGroup.det x : (Af E)ˣ) : Af E) w = (GeneralLinearGroup.map (pLoc E w) x).val.det :=
    RingHom.map_det (pLoc E w) x.val
  rw [e1, ← ha]
  have e2 : (bc (Ov E w).subtype a).val.det = (Ov E w).subtype a.val.det :=
    (RingHom.map_det (Ov E w).subtype a.val).symm
  rw [e2]
  exact a.val.det.2

private theorem chi_fin {bad : Set (Pl E)} {K : Subgroup (GL (Fin N) (Af E))} (hK : Lev bad K) (z : ℂ)
    {u : GL (Fin N) (Af E)} (hu : u ∈ K) : ((chiDet N (Model.absC E z) (finGL E N u) : ℂˣ) : ℂ) = 1 := by
  have h0 : logFin E (GeneralLinearGroup.det u) = 0 := by
    refine GlobalTheory.CompanionTheory.LimV.logFin_eq_zero_of_integral _ (GroundTheory.Global.mem_integralFiniteAdeles.2 fun w => det_coord_le hK hu w)
      (GroundTheory.Global.mem_integralFiniteAdeles.2 fun w => ?_)
    rw [← map_inv]
    exact det_coord_le hK (inv_mem hu) w
  rw [PositivityTheory.Rg.Rs.ExponentTwist.chiDet_absC_val, det_finGL, GlobalTheory.CompanionTheory.LimV.logNorm_finId, h0]
  simp

private theorem chi_inf (z : ℂ) (k : Kinf E N) :
    ((chiDet N (Model.absC E z) (infGL E N (Unitary.toUnits k)) : ℂˣ) : ℂ) = 1 := by
  have h := GlobalTheory.CompanionTheory.LimV.chiDet_absC_cf (E := E) N z k (c := 1) (one_mem _)
  rw [PositivityTheory.Rg.Rs.InducedTensorMap.cf, map_one, mul_one] at h
  rw [h, Units.val_one]

end Aux3

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp

open GlobalTheory.Mem.Chr.CharModel in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp.normTw :
    NormTw := by
  intro E _ _ _ N hN bad K W hK π φ m hφ hφ0 hT hm
  obtain ⟨s, hs⟩ := GlobalTheory.T.aux_statement_20 E N hN π fun τ => ⟨_, hm τ⟩
  have hψ : mulChi N (Model.absC E s) φ ∈ (π.twist (Model.absC E s)).V := ⟨φ, hφ, rfl⟩
  have hψ0 : mulChi N (Model.absC E s) φ ≠ 0 := fun e => hφ0 ((mulChi N (Model.absC E s)).map_eq_zero_iff.1 e)
  have htw : ∀ t, (π.twist (Model.absC E s)).HasInfChar t ((m t).map (· + s)) := fun t => by
    have h1 := (hm t).twist (Model.absC E s)
    rwa [Model.expo_absC] at h1
  refine ⟨π.twist (Model.absC E s), -s, hs, ?_, ⟨_, hψ, hψ0, ?_, ?_⟩, fun t => ?_, ?_, _, hψ, -s, fun g => ?_⟩
  · rw [← CuspSub.twist_mul, ← PositivityTheory.Rg.Rs.StrStepB.absC_add, add_neg_cancel, PositivityTheory.Rg.Rs.StrStepB.absC_zero,
      CuspSub.twist_one]
  · intro u hu g
    rw [mulChi_apply, mulChi_apply, hT.1 u hu g, map_mul, Units.val_mul, chi_fin hK s hu, mul_one]
  · intro g
    have e : (fun k : Kinf E N => (mulChi N (Model.absC E s) φ).1 (g * infGL E N (Unitary.toUnits k))) =
        ((chiDet N (Model.absC E s) g : ℂˣ) : ℂ) • fun k : Kinf E N => φ.1 (g * infGL E N (Unitary.toUnits k)) := by
      funext k
      rw [mulChi_apply, map_mul, Units.val_mul, chi_inf, mul_one, Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [e]
    exact W.smul_mem _ (hT.2 g)
  · simpa only [sub_neg_eq_add] using htw t
  · obtain ⟨g₀, hg₀⟩ : ∃ g, (mulChi N (Model.absC E s) φ).1 g ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hψ0 (Subtype.ext (funext hcon))
    have hsum : ∀ τ : E →+* ℂ, (∑ i : Fin N, Eop τ i i) (mulChi N (Model.absC E s) φ) =
        ((m τ).sum + N * s) • mulChi N (Model.absC E s) φ := fun τ => by
      rw [GlobalTheory.T.trace_operator_eigenvalue_sum E N _ τ _ (htw τ) _ hψ, Multiset.sum_map_add]
      simp [(hm τ).1]
    have hlie : lie E N (oneL E N) (mulChi N (Model.absC E s) φ) =
        (∑ τ : E →+* ℂ, ((m τ).sum + N * s)) • mulChi N (Model.absC E s) φ := by
      rw [GlobalTheory.T.lie_central_element_trace E N, LinearMap.sum_apply, Finset.sum_congr rfl fun τ _ => hsum τ, ← Finset.sum_smul]
    have hz : ∑ τ : E →+* ℂ, ((m τ).sum + N * s) = 0 := by
      refine GlobalTheory.CompanionTheory.TotalTrace.eq_zero_of_exp_mul_eq_one fun t => ?_
      have h1 := GlobalTheory.T.central_eigen_exponential E N _ _ hlie t g₀
      rw [hs _ hψ t g₀] at h1
      have h2 : Complex.exp ((∑ τ : E →+* ℂ, ((m τ).sum + N * s)) * t) * (mulChi N (Model.absC E s) φ).1 g₀ =
          1 * (mulChi N (Model.absC E s) φ).1 g₀ := by rw [one_mul]; exact h1.symm
      exact mul_right_cancel₀ hg₀ h2
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hz
    linear_combination hz
  · have e : PositivityTheory.Rg.BcB.logAbs g.val.det = logNorm E (GeneralLinearGroup.det g) :=
      logAbs_eq_logNorm (GeneralLinearGroup.det g)
    rw [mulChi_apply, PositivityTheory.Rg.Rs.ExponentTwist.chiDet_absC_val, e, mul_assoc, ← Complex.exp_add]
    simp
