import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsGaussEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalDarbouxOrientedPairTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchLineApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtHeisenbergOperatorThetaTransformRealLi

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.VacTransfer

open GlobalTheory.ThetaTransform

noncomputable section

namespace GlobalTheory.LineDerivTransfer

theorem hasDerivAt_heisV_of {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)]
    (ψ : AddChar (AF F) ℂ) (hF : IsTotallyReal F) (hψ : IsCharAF F ψ) {Φ Φ' : (Fin N → AF F) → ℂ}
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F (Fin N)) (hΦ'm : Φ' ∈ GlobalTheory.WeilM.schA F (Fin N)) {M : ℝ →+ VA F N} (hM : IsRealLine M)
    (hΦ'd : ∀ z, HasDerivAt (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) Φ z) (Φ' z) 0) (w : VA F N) :
    HasDerivAt (fun t : ℝ => heisV ψ (M t) (thV ψ Φ) w) (thV ψ Φ' w) 0 := by
  have hnorm : ∀ x, ‖ψ x‖ = 1 := hψ.2.1
  have hM0 : M 0 = 0 := map_zero M
  set ω : Set (Fin N → AF F) := (fun s : ℝ => w.1 + (M s).1) '' Set.Icc (-1) 1 with hω
  have hωc : IsCompact ω := isCompact_Icc.image (continuous_const.add (continuous_fst.comp hM.1))
  obtain ⟨C, c, hcs, hc0, hcb⟩ := GlobalTheory.ThetaDeriv.decay_majorant hF (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N Φ' hΦ'm) ω hωc
  obtain ⟨C₀, c₀, hcs₀, hc0₀, hcb₀⟩ :=
    GlobalTheory.ThetaDeriv.decay_majorant hF (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N Φ hΦ) {w.1} isCompact_singleton
  set ph : (Fin N → F) → ℂ := fun ξ => ψ (GlobalTheory.SWQ.rat ξ ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) with hph
  have e : (fun t : ℝ => heisV ψ (M t) (thV ψ Φ) w) =
      fun t => ∑' ξ : Fin N → F, ph ξ * GlobalTheory.WeilM.schr ψ (M t) Φ (GlobalTheory.SWQ.rat ξ + w.1) := by
    funext t
    rw [← thV_schr]
    rfl
  have hv : thV ψ Φ' w = ∑' ξ : Fin N → F, ph ξ * GlobalTheory.WeilM.schr ψ (M 0) Φ' (GlobalTheory.SWQ.rat ξ + w.1) := by
    rw [hM0]
    refine tsum_congr fun ξ => ?_
    simp [ph, GlobalTheory.WeilM.schr]
    rfl
  rw [e, hv]
  have hmem : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine hasDerivAt_tsum_of_isPreconnected (hcs.mul_left C) isOpen_Ioo isPreconnected_Ioo
    (fun ξ t _ => (GlobalTheory.ThetaDeriv.hasDerivAt_schr hF ψ hM hΦ'd (GlobalTheory.SWQ.rat ξ + w.1) t).const_mul (ph ξ))
    (fun ξ t ht => ?_) hmem ?_ hmem
  · have hy : w.1 + (M t).1 ∈ ω := ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
    have := hcb ξ _ hy
    simp only [ph, GlobalTheory.WeilM.schr, norm_mul, hnorm, one_mul]
    simpa [add_assoc] using this
  · refine Summable.of_norm_bounded (hcs₀.mul_left C₀) fun ξ => ?_
    have := hcb₀ ξ w.1 rfl
    simpa [hM0, GlobalTheory.WeilM.schr, ph, norm_mul, hnorm] using this

theorem thV_smul {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ)
    (c : ℂ) (Φ : (Fin N → AF F) → ℂ) : thV ψ (c • Φ) = c • thV ψ Φ := by
  funext w
  simp only [thV, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  exact tsum_congr fun η => mul_left_comm _ _ _

end GlobalTheory.LineDerivTransfer

open GlobalTheory.LineDerivTransfer in

theorem GlobalTheory.LineDerivTransfer.schr_deriv_of_heisO_deriv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E),
      ξ • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ∀ (κ : Type) [Fintype κ]
      (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F T.gramᵀ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB)) κ),
      (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
        co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F x) =
          (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
    ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ L L' : ℝ →+ WO S T,
      Continuous L → (∀ t, (L t).map (finPart D) = 0) → Continuous L' → (∀ t, (L' t).map (finPart D) = 0) →
    ∀ c : ℂ, (fun w => deriv (fun t : ℝ => heisO ψ S T (L' t) (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) w) 0) =
        c • (fun w => deriv (fun t : ℝ => heisO ψ S T (L t) (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) w) 0) →
      ∀ x, deriv (fun t : ℝ => GlobalTheory.WeilM.schr ψ (co.e (L' t)) Φ x) 0 =
        c * deriv (fun t : ℝ => GlobalTheory.WeilM.schr ψ (co.e (L t)) Φ x) 0 := by
  intro D ψ hψ S T JB ξ hB κ _ co hrat Φ hΦ L L' hL hL0 hL' hL0' c hrel x
  have hR : IsTotallyReal D.host.F := inferInstance
  let σ := Fintype.equivFin κ
  let e := numCoord co σ
  have he : ∀ w w', symplO S T w w' = symV (e w) (e w') := fun w w' => by
    rw [symplO_eq_symp rfl hB, co.form]
    simp only [e, symV, numCoord_apply, comp_equiv_dotProduct_comp_equiv]
  obtain ⟨-, -, hfin, -⟩ := GlobalTheory.T.adelicLinearCoordinates_continuous_keep_parts D T.rank S.rank _ e
  have hc : Continuous e := (GlobalTheory.T.adelicLinearCoordinates_continuous_keep_parts D T.rank S.rank _ e).1
  have hΦσ := comp_mem_schA σ hΦ
  have key : ∀ L : ℝ →+ WO S T, Continuous L → (∀ t, (L t).map (finPart D) = 0) →
      ∃ Φ' ∈ GlobalTheory.WeilM.schA D.host.F (Fin (Fintype.card κ)),
        (∀ x, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.schr ψ (co.e (L t)) Φ x) (Φ' (x ∘ σ.symm)) 0) ∧
        (fun w => deriv (fun t : ℝ => heisO ψ S T (L t) (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) w) 0) =
          thV ψ Φ' ∘ e := by
    intro L hL hL0
    have hM : IsRealLine (e.toLinearMap.toAddMonoidHom.comp L) := ⟨hc.comp hL, fun t => (hfin _).1 (hL0 t)⟩
    obtain ⟨Φ', hm, hd⟩ := GlobalTheory.ThetaDeriv.exists_deriv_schr hR ψ hψ.1 hM hΦσ
    refine ⟨Φ', hm, fun x => ?_, funext fun w => ?_⟩
    · have h : (fun t : ℝ => GlobalTheory.WeilM.schr ψ (co.e (L t)) Φ x) =
          fun t => GlobalTheory.WeilM.schr ψ (e.toLinearMap.toAddMonoidHom.comp L t) (fun y => Φ (y ∘ σ)) (x ∘ σ.symm) := by
        funext t
        simp only [GlobalTheory.WeilM.schr, AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
          LinearEquiv.coe_coe, e, numCoord_apply, comp_equiv_dotProduct_comp_equiv]
        congr 2
        funext i
        simp
      rw [h]
      exact hd _
    · rw [thetaTr_eq co σ]
      have h : (fun t : ℝ => heisO ψ S T (L t) (thV ψ (fun y => Φ (y ∘ σ)) ∘ e) w) =
          fun t => heisV ψ (e.toLinearMap.toAddMonoidHom.comp L t) (thV ψ (fun y => Φ (y ∘ σ))) (e w) :=
        funext fun t => congrFun (heisO_comp he (L t) _) w
      rw [show numCoord co σ = e from rfl, h]
      exact (hasDerivAt_heisV_of ψ hR hψ.1 hΦσ hm hM hd (e w)).deriv
  obtain ⟨Φ₁, hm₁, hd₁, hh₁⟩ := key L hL hL0
  obtain ⟨Φ₂, hm₂, hd₂, hh₂⟩ := key L' hL' hL0'
  rw [hh₁, hh₂] at hrel
  have h2 : thV ψ Φ₂ = thV ψ (c • Φ₁) := by
    rw [thV_smul]
    funext v
    obtain ⟨w, rfl⟩ := e.surjective v
    exact congrFun hrel w
  have h3 := thV_injOn hR hψ.1 hm₂ (Submodule.smul_mem _ c hm₁) h2
  rw [(hd₂ x).deriv, (hd₁ x).deriv, h3]
  rfl
