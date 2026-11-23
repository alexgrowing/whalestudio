import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RankOneTensors

noncomputable section

namespace Formalism.L2.SG.Pf.FormAllPf

open MeasureTheory Set
open scoped ENNReal

section Gen

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

theorem decomp (μR : Measure G) (R : Set G) (hR : μR Rᶜ = 0) (Γ0 : Subgroup G) [Countable Γ0]
    (P Q : Set G) (hP : MeasurableSet P) (hQ : MeasurableSet Q) (hQu : ∀ r ∈ R, ∃! s, s ∈ Γ0 ∧ s * r ∈ Q) :
    μR P = ∑' s : Γ0, μR (P ∩ (fun x => (s : G) * x) ⁻¹' Q) := by
  classical
  have hmeas : ∀ s : Γ0, MeasurableSet (P ∩ (fun x => (s : G) * x) ⁻¹' Q) :=
    fun s => hP.inter (measurable_const_mul (s : G) hQ)
  have hdisj : Pairwise (Function.onFun (AEDisjoint μR)
      (fun s : Γ0 => P ∩ (fun x => (s : G) * x) ⁻¹' Q)) := by
    intro s t hst
    show μR ((P ∩ (fun x => (s : G) * x) ⁻¹' Q) ∩ (P ∩ (fun x => (t : G) * x) ⁻¹' Q)) = 0
    refine measure_mono_null ?_ hR
    intro x hx
    rw [Set.mem_compl_iff]
    intro hxR
    obtain ⟨y, _, huniq⟩ := hQu x hxR
    apply hst
    have e1 : (s : G) = y := huniq s ⟨s.2, hx.1.2⟩
    have e2 : (t : G) = y := huniq t ⟨t.2, hx.2.2⟩
    exact Subtype.ext (e1.trans e2.symm)
  have hRae : ∀ᵐ x ∂μR, x ∈ R := by
    first
      | exact ae_iff.2 hR
      | exact (mem_ae_iff.2 hR : R ∈ ae μR)
      | simpa [ae_iff] using hR
  have hae : P =ᵐ[μR] ⋃ s : Γ0, (P ∩ (fun x => (s : G) * x) ⁻¹' Q) := by
    filter_upwards [hRae] with x hx
    apply propext
    constructor
    · intro hxP
      obtain ⟨s, hs, hsQ⟩ := (hQu x hx).exists
      exact Set.mem_iUnion.2 ⟨⟨s, hs⟩, hxP, hsQ⟩
    · intro h
      obtain ⟨s, hs⟩ := Set.mem_iUnion.1 h
      exact hs.1
  rw [measure_congr hae, measure_iUnion₀ hdisj fun s => (hmeas s).nullMeasurableSet]

theorem fd_meas_eq (μR : Measure G) (R : Set G) (hR : μR Rᶜ = 0) (Γ0 : Subgroup G) [Countable Γ0]
    (hinv : ∀ s ∈ Γ0, μR.map (fun x => s * x) = μR) (A K : Set G) (hA : MeasurableSet A) (hK : MeasurableSet K)
    (hAu : ∀ r ∈ R, ∃! s, s ∈ Γ0 ∧ s * r ∈ A) (hKu : ∀ r ∈ R, ∃! s, s ∈ Γ0 ∧ s * r ∈ K) : μR A = μR K := by
  rw [decomp μR R hR Γ0 A K hA hK hKu, decomp μR R hR Γ0 K A hK hA hAu,
    ← (Equiv.inv Γ0).tsum_eq (fun s : Γ0 => μR (K ∩ (fun x => (s : G) * x) ⁻¹' A))]
  refine tsum_congr fun s => ?_
  show μR (A ∩ (fun x => (s : G) * x) ⁻¹' K) = μR (K ∩ (fun x => ((s : G))⁻¹ * x) ⁻¹' A)
  have hB : MeasurableSet (K ∩ (fun x => ((s : G))⁻¹ * x) ⁻¹' A) :=
    hK.inter (measurable_const_mul _ hA)
  have hpre : (fun x => (s : G) * x) ⁻¹' (K ∩ (fun x => ((s : G))⁻¹ * x) ⁻¹' A) =
      A ∩ (fun x => (s : G) * x) ⁻¹' K := by
    ext x
    simp only [Set.mem_preimage, Set.mem_inter_iff, inv_mul_cancel_left]
    exact and_comm
  rw [← hpre, ← Measure.map_apply (measurable_const_mul _) hB, hinv s s.2]

def invSigma {G : Type*} [Group G] (m0 : MeasurableSpace G) (R : Set G) : MeasurableSpace G where
  MeasurableSet' := fun B => MeasurableSet[m0] B ∧ ∀ r ∈ R, (fun x => r * x) ⁻¹' B = B
  measurableSet_empty := ⟨@MeasurableSet.empty G m0, fun r _ => preimage_empty⟩
  measurableSet_compl := fun B hB => ⟨hB.1.compl, fun r hr => by rw [preimage_compl, hB.2 r hr]⟩
  measurableSet_iUnion := fun B hB => ⟨MeasurableSet.iUnion fun i => (hB i).1,
    fun r hr => by rw [preimage_iUnion]; exact iUnion_congr fun i => (hB i).2 r hr⟩

theorem integral_eq_of_inv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V] [CompleteSpace V] (μ μ' : Measure G) (R : Set G) (f : G → V) (hf : Measurable f)
    (hfi : ∀ r ∈ R, ∀ x, f (r * x) = f x)
    (hmeas : ∀ B, MeasurableSet B → (∀ r ∈ R, (fun x => r * x) ⁻¹' B = B) → μ B = μ' B) :
    ∫ x, f x ∂μ = ∫ x, f x ∂μ' := by
  have hm : invSigma ‹MeasurableSpace G› R ≤ ‹MeasurableSpace G› := by
    intro B hB
    exact And.left hB
  have hfm : Measurable[invSigma ‹MeasurableSpace G› R] f := by
    intro B hB
    exact (⟨hf hB, fun r hr => by ext x; simp [hfi r hr x]⟩ :
      MeasurableSet[‹MeasurableSpace G›] (f ⁻¹' B) ∧ ∀ r ∈ R, (fun x => r * x) ⁻¹' (f ⁻¹' B) = f ⁻¹' B)
  have hsm : StronglyMeasurable[invSigma ‹MeasurableSpace G› R] f := hfm.stronglyMeasurable
  have htrim : μ.trim hm = μ'.trim hm := by
    refine @Measure.ext G (invSigma ‹MeasurableSpace G› R) _ _ fun B hB => ?_
    rw [trim_measurableSet_eq hm hB, trim_measurableSet_eq hm hB]
    exact hmeas B (And.left hB) (And.right hB)
  rw [integral_trim hm hsm, integral_trim hm hsm, htrim]

end Gen

end Formalism.L2.SG.Pf.FormAllPf

namespace Formalism.L2.SG.Pf

open MeasureTheory Set Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.Vanish
  NumberField
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FormAllC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (μR ν : Measure X.B.I.Ginf) (K : Set X.B.I.Ginf),
    (∀ r ∈ Rset t, X.psiInfU u r = X.psiInfU u' (t.pt.1⁻¹ * r * t.pt.1)) →
    IsHaarOnSet X.B.I (Rset t) μR → IsQuotMeasS X.B.I μR ν →
    MeasurableSet K → (∀ r ∈ Rset t, ∃! s, s ∈ ROinf t ∧ s * r ∈ K) →
    haveI := FiniteDimensional.complete ℂ (X.Vpi u)
    OOt t = (μR K).toReal • OO ν Set.univ (X.Wu u) (X.Wu u') t.pt.1

theorem formAllC_holds : FormAllC := by
  intro D X Y u u' t μR ν K hchi hH hQ hKm hKu
  haveI := FiniteDimensional.complete ℂ (X.Vpi u)

  have hFE : ∃ Ω, IsSFund X.B.I (ROinf t) Ω := fundExistsC_holds D X Y u u' t
  have hFO : IsSFund X.B.I (ROinf t) (FundOf t) := by
    unfold FundOf; rw [dif_pos hFE]; exact hFE.choose_spec

  set Γ0 := ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin with hΓ0
  have hΓc : Countable Γ0 := by
    have := ROsub_discrete X (X.Fu u) (X.Fu u') t.lam t.lam' ((Y.rowsOK u).1 t.lam t.mem).1.1 t.lin
    exact countable_of_discrete Γ0
  have hΓR : ∀ s ∈ Γ0, s ∈ Rset t := by
    rintro _ ⟨x, n, hxn, rfl, hn, hn'⟩
    refine ⟨nLamNinf_holds D X u _ x n hxn hn, ?_⟩
    have hrep : RatLink X t.pt t.lin := t.rep.2.1
    have h2 := ratLink_mul X (ratLink_mul X (ratLink_inv X hrep) hxn) hrep
    have h3 := nLamNinf_holds D X u' _ _ _ h2 hn'
    simpa [Prod.fst_mul, Prod.fst_inv] using h3
  have hμinv : ∀ s ∈ Γ0, μR.map (fun x => s * x) = μR := fun s hs => hH.2.2.2 s (hΓR s hs)

  have hsec : ∀ x, μR ((fun s => s * x) ⁻¹' FundOf t) = μR K := by
    intro x
    refine FormAllPf.fd_meas_eq μR (Rset t) hH.2.2.1 Γ0 hμinv _ K (hFO.1.preimage (measurable_mul_const x)) hKm
      (fun r _ => ?_) hKu
    obtain ⟨s, hs, hsx⟩ := hFO.2.1 (r * x)
    refine ⟨s, ⟨hs, by simpa [mul_assoc] using hsx⟩, fun s' ⟨hs', hs'x⟩ => ?_⟩
    have h1 : s' * r * x ∈ FundOf t := hs'x
    have h2 : (s * s'⁻¹) * (s' * r * x) ∈ FundOf t := by simpa [mul_assoc] using hsx
    have := hFO.2.2 _ h1 _ (Γ0.mul_mem hs (Γ0.inv_mem hs')) h2
    exact (mul_inv_eq_one.1 this).symm

  set f : X.B.I.Ginf → (X.Vpi u' →L[ℂ] X.Vpi u) := fun x => rk1 (X.Wu u x) (X.Wu u' (t.pt.1⁻¹ * x)) with hfdef
  have hfc : Continuous f :=
    Formalism.L2.SG.RealObj.RankOneTensors.continuous_rankOneOperator (X.Wu_spec u).2.2.1
      ((X.Wu_spec u').2.2.1.comp (continuous_const.mul continuous_id))
  have hfi : ∀ r ∈ Rset t, ∀ x, f (r * x) = f x := by
    intro r hr x
    simp only [hfdef]
    rw [wu_N X u hr.1 x, show t.pt.1⁻¹ * (r * x) = (t.pt.1⁻¹ * r * t.pt.1) * (t.pt.1⁻¹ * x) by group,
      wu_N X u' hr.2 _, ← hchi r hr]
    exact rankOneInnerOperator_smul_smul_eq_mul_conj_smul _ (Formalism.L2.SG.RealObj.InfCut.norm_psiInfU X u r) _ _
  letI : MeasurableSpace (X.Vpi u' →L[ℂ] X.Vpi u) := borel _
  haveI : BorelSpace (X.Vpi u' →L[ℂ] X.Vpi u) := ⟨rfl⟩
  haveI : SecondCountableTopology (X.Vpi u' →L[ℂ] X.Vpi u) := inferInstance
  have hfm : Measurable f := hfc.measurable

  have hB : ∀ B, MeasurableSet B → (∀ r ∈ Rset t, (fun x => r * x) ⁻¹' B = B) →
      ((Formalism.L2.SG.ProjRows.muInf X.B.I).restrict (FundOf t)) B = ((μR K) • ν) B := by
    intro B hBm hBi
    rw [Measure.restrict_apply hBm, Measure.smul_apply, smul_eq_mul]
    have hq := hQ ((B ∩ FundOf t).indicator 1) ((measurable_const).indicator (hBm.inter hFO.1))
    rw [lintegral_indicator_one (hBm.inter hFO.1)] at hq
    rw [hq, ← lintegral_indicator_const hBm]
    refine lintegral_congr fun x => ?_
    have e1 : (fun s => (B ∩ FundOf t).indicator (1 : X.B.I.Ginf → ℝ≥0∞) (s * x)) =
        ((fun s => s * x) ⁻¹' (B ∩ FundOf t)).indicator 1 := by
      funext s; rfl
    rw [e1, lintegral_indicator_one ((hBm.inter hFO.1).preimage (measurable_mul_const x)),
      ← measure_inter_conull (t := Rset t) hH.2.2.1]
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, ← hsec x, ← measure_inter_conull (s := (fun s => s * x) ⁻¹' FundOf t) hH.2.2.1]
      congr 1
      ext s
      simp only [mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h2, h3⟩
      · rintro ⟨h2, h3⟩
        refine ⟨⟨?_, h2⟩, h3⟩
        have := congrArg (fun S => x ∈ S) (hBi s h3)
        simp only [mem_preimage] at this
        exact this ▸ hx
    · rw [Set.indicator_of_notMem hx]
      have hempty : (fun s => s * x) ⁻¹' (B ∩ FundOf t) ∩ Rset t = ∅ := by
        ext s
        refine ⟨fun hs => ?_, fun h => h.elim⟩
        obtain ⟨⟨h1, -⟩, h3⟩ := hs
        have := congrArg (fun S => x ∈ S) (hBi s h3)
        simp only [mem_preimage] at this
        exact absurd (this ▸ h1) hx
      rw [hempty, measure_empty]

  show OO (Formalism.L2.SG.ProjRows.muInf X.B.I) (FundOf t) (X.Wu u) (X.Wu u') t.pt.1 = _
  unfold OO
  rw [Measure.restrict_univ, ← integral_smul_measure]
  exact FormAllPf.integral_eq_of_inv _ _ (Rset t) f hfm hfi hB

end Formalism.L2.SG.Pf
