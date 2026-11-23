import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCRefTraceCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCSecMove

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem radial_gauge_move : GTRMove := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk μ0 h0 e0 he0
  have hz := Bs.z_mem
  have hz' := Bs.z'_mem
  have hT : Tz P.k P.r Bs.z = P.T := hpl.2.2.2.1
  have hT' : Tz P.k P.r Bs.z' = P.T' := hpl.2.2.2.2.1
  have hTT : ∀ ζ : ℂ, P.TT < Complex.normSq ζ → Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    intro ζ hζ
    rw [hT, hT']
    exact hζ
  set c1 : Fin P.r → ℂ := fun _ => 1 with hc1def
  have hc1 : c1 ∈ OmX P.r := fun _ => one_ne_zero

  have hRB : NF.RadBase P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' :=
    ⟨Bs.k_pos, hz, hz', Bs.T_pos, Bs.T'_pos, h0, Bs.π_rep, Bs.π'_rep, Bs.π_cont, Bs.π'_cont⟩

  have hφ : ∀ ρ : M.Ty P, (NF.QR P.k P.r Bs.z Bs.z').indicator (fun q => e0 ρ q.2) ∈
      NF.RadSec P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' := by
    intro ρ
    refine ⟨?_, ?_, ?_⟩
    · have hc : ContDiffOn ℝ ∞ (fun q : (Fin P.r → ℂ) × ℂ => e0 ρ q.2) (NF.QR P.k P.r Bs.z Bs.z') := by
        refine (he0.1 ρ).comp contDiff_snd.contDiffOn fun q hq => ?_
        show P.TT < Complex.normSq q.2
        have := hq.2
        rw [hT, hT'] at this
        exact this
      exact hc.congr fun q hq => Set.indicator_of_mem hq _
    · intro q hq
      rw [Set.indicator_of_mem hq]
      have hq2 : P.TT < Complex.normSq q.2 := by
        have := hq.2
        rw [hT, hT'] at this
        exact this
      exact (he0.2 q.2 hq2).1 ρ
    · intro q hq
      exact Set.indicator_of_notMem hq _
  choose Φr hΦr hrad using fun ρ => Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' hRB _ (hφ ρ)
  obtain ⟨e, he_def⟩ : ∃ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp),
      e = fun ρ ζ => (Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (NF.muZ P.k P.r Bs.μsec ζ) := ⟨_, rfl⟩

  have hdom : ∀ ζ : ℂ, P.TT < Complex.normSq ζ →
      (c1, NF.muZ P.k P.r Bs.μsec ζ) ∈ Q.DomR P.k P.r Bs.z Bs.z' :=
    fun ζ hζ => Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec (q := (c1, ζ)) ⟨hc1, hTT ζ hζ⟩
  have hdom0 : ∀ ζ : ℂ, P.TT < Complex.normSq ζ → (c1, NF.muZ P.k P.r μ0 ζ) ∈ Q.DomR P.k P.r Bs.z Bs.z' :=
    fun ζ hζ => Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' h0 (q := (c1, ζ)) ⟨hc1, hTT ζ hζ⟩
  have hdec : ∀ ζ : ℂ, P.TT < Complex.normSq ζ → ∃ h ∈ UWset P.k P.r Bs.z, ∃ h' ∈ UWset P.k P.r Bs.z',
      NF.muZ P.k P.r Bs.μsec ζ = h * NF.muZ P.k P.r μ0 ζ * h' := by
    intro ζ hζ
    obtain ⟨h, hh, h', hh', he⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.decomp Bs.k_pos hz hz' Bs.T_pos Bs.T'_pos h0
      (hdom ζ hζ).2.1 (hdom ζ hζ).2.2
    rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hz hz' Bs.sec (hTT ζ hζ)] at he
    exact ⟨h, hh, h', hh', he⟩

  have hrad0 : ∀ ρ ζ, P.TT < Complex.normSq ζ → (Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (NF.muZ P.k P.r μ0 ζ) = e0 ρ ζ := by
    intro ρ ζ hζ
    have hq : (c1, ζ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc1, hTT ζ hζ⟩
    have h1 := congrFun (hrad ρ) (c1, ζ)
    unfold NF.radR at h1
    rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq] at h1
    exact h1

  have htr : ∀ ρ ζ, P.TT < Complex.normSq ζ → ∀ h ∈ UWset P.k P.r Bs.z, ∀ h' ∈ UWset P.k P.r Bs.z',
      NF.muZ P.k P.r Bs.μsec ζ = h * NF.muZ P.k P.r μ0 ζ * h' →
      e ρ ζ = (Bs.π h).comp ((e0 ρ ζ).comp (Bs.π' h')) := by
    intro ρ ζ hζ h hh h' hh' hd
    rw [he_def]
    show (Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (NF.muZ P.k P.r Bs.μsec ζ) = _
    rw [hd, ← hrad0 ρ ζ hζ]
    exact (hΦr ρ).2.2 (c1, NF.muZ P.k P.r μ0 ζ) (hdom0 ζ hζ) h hh h' hh'

  have hsmooth : ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e ρ) {ζ : ℂ | P.TT < Complex.normSq ζ} := by
    intro ρ
    rw [he_def]
    have hmZ : ContDiffOn ℝ ∞ (fun ζ : ℂ => (c1, NF.muZ P.k P.r Bs.μsec ζ)) {ζ : ℂ | P.TT < Complex.normSq ζ} :=
      contDiffOn_const.prodMk ((Formalism.FourierDecayAlt.P.NFRadRedA.muZ_contDiffOn Bs.sec).mono fun ζ hζ => hTT ζ hζ)
    have hopen : IsOpen {ζ : ℂ | P.TT < Complex.normSq ζ} :=
      isOpen_lt continuous_const Complex.continuous_normSq
    refine contDiffOn_of_locally_contDiffOn fun ζ₀ hζ₀ => ?_
    obtain ⟨U, F, hU, hx₀U, hF, hΦF⟩ := (hΦr ρ).2.1 _ (hdom ζ₀ hζ₀)
    refine ⟨{ζ : ℂ | P.TT < Complex.normSq ζ} ∩ (fun ζ : ℂ => (c1, NF.muZ P.k P.r Bs.μsec ζ)) ⁻¹' U,
      hmZ.continuousOn.isOpen_inter_preimage hopen hU, ⟨hζ₀, hx₀U⟩, ?_⟩
    have hc : ContDiffOn ℝ ∞ (fun ζ : ℂ => F (c1, NF.muZ P.k P.r Bs.μsec ζ))
        ({ζ : ℂ | P.TT < Complex.normSq ζ} ∩
          ({ζ : ℂ | P.TT < Complex.normSq ζ} ∩ (fun ζ : ℂ => (c1, NF.muZ P.k P.r Bs.μsec ζ)) ⁻¹' U)) :=
      hF.comp (hmZ.mono fun ζ hζ => hζ.1) fun ζ hζ => hζ.2.2
    exact hc.congr fun ζ hζ => hΦF _ hζ.2.2 (hdom ζ hζ.1).2.1

  have hrep := Bs.π_rep
  have hrep' := Bs.π'_rep
  have pmi : ∀ h ∈ UWset P.k P.r Bs.z, (Bs.π h).comp (Bs.π h⁻¹) = 1 := by
    intro h hh
    rw [← hrep.2 h hh h⁻¹ (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh), Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh, hrep.1]
  have pim' : ∀ h' ∈ UWset P.k P.r Bs.z', (Bs.π' h'⁻¹).comp (Bs.π' h') = 1 := by
    intro h' hh'
    rw [← hrep'.2 h'⁻¹ (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh') h' hh', Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh', hrep'.1]

  have hframe : IsFrameB P Bs e := by
    refine ⟨hsmooth, fun ζ hζ => ⟨?_, ?_, ?_⟩⟩
    · intro ρ p hp
      rw [he_def]
      show (Bs.π p.1).comp (((Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (NF.muZ P.k P.r Bs.μsec ζ)).comp (Bs.π' p.2)) =
        (Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (NF.muZ P.k P.r Bs.μsec ζ)
      rw [← (hΦr ρ).2.2 (c1, NF.muZ P.k P.r Bs.μsec ζ) (hdom ζ hζ) p.1 hp.1 p.2 hp.2.1]
      show (Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (p.1 * NF.muZ P.k P.r Bs.μsec ζ * p.2) = _
      rw [hp.2.2]
    · intro ρ ρ'
      obtain ⟨h, hh, h', hh', hd⟩ := hdec ζ hζ
      rw [htr ρ ζ hζ h hh h' hh' hd, htr ρ' ζ hζ h hh h' hh' hd, sm_inner_conj Bs hh hh']
      exact (he0.2 ζ hζ).2.1 ρ ρ'
    · intro X hX
      obtain ⟨h, hh, h', hh', hd⟩ := hdec ζ hζ
      have hhi := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh
      have hhi' := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh'
      set X0 := (Bs.π h⁻¹).comp (X.comp (Bs.π' h'⁻¹)) with hX0def
      have e1 : ∀ Y : B.Mat P.k P.r, h⁻¹ * (h * Y) = Y := fun Y => by
        rw [← Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh, Matrix.one_mul]
      have e2 : ∀ Y : B.Mat P.k P.r, h' * (h'⁻¹ * Y) = Y := fun Y => by
        rw [← Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh', Matrix.one_mul]
      have hX0 : X0 ∈ NF.Fib P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' ζ := by
        intro p hp
        have hp1 := hp.1
        have hp2 := hp.2.1
        have hp3 := hp.2.2
        have ht1 : h * p.1 * h⁻¹ ∈ UWset P.k P.r Bs.z :=
          Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul (Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul hh hp1) hhi
        have ht2 : h'⁻¹ * p.2 * h' ∈ UWset P.k P.r Bs.z' :=
          Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul (Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul hhi' hp2) hh'
        have e3 : ∀ Y : B.Mat P.k P.r, p.1 * (NF.muZ P.k P.r μ0 ζ * (p.2 * Y)) = NF.muZ P.k P.r μ0 ζ * Y := by
          intro Y
          conv_rhs => rw [← hp3]
          simp only [Matrix.mul_assoc]
        have ht : (h * p.1 * h⁻¹, h'⁻¹ * p.2 * h') ∈ NF.Stab P.k P.r Bs.z Bs.z' Bs.μsec ζ := by
          refine ⟨ht1, ht2, ?_⟩
          show h * p.1 * h⁻¹ * NF.muZ P.k P.r Bs.μsec ζ * (h'⁻¹ * p.2 * h') = NF.muZ P.k P.r Bs.μsec ζ
          rw [hd]
          simp only [Matrix.mul_assoc, e1, e2, e3]
        have hXt := hX _ ht
        have hA : (Bs.π p.1).comp (Bs.π h⁻¹) = (Bs.π h⁻¹).comp (Bs.π (h * p.1 * h⁻¹)) := by
          rw [← hrep.2 _ hp1 _ hhi, ← hrep.2 _ hhi _ ht1]
          congr 1
          simp only [Matrix.mul_assoc, e1]
        have hB : (Bs.π' h'⁻¹).comp (Bs.π' p.2) = (Bs.π' (h'⁻¹ * p.2 * h')).comp (Bs.π' h'⁻¹) := by
          rw [← hrep'.2 _ hhi' _ hp2, ← hrep'.2 _ ht2 _ hhi']
          congr 1
          simp only [Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh', Matrix.mul_one]
        calc (Bs.π p.1).comp (X0.comp (Bs.π' p.2))
            = ((Bs.π p.1).comp (Bs.π h⁻¹)).comp (X.comp ((Bs.π' h'⁻¹).comp (Bs.π' p.2))) := by
              simp only [hX0def, ContinuousLinearMap.comp_assoc]
          _ = ((Bs.π h⁻¹).comp (Bs.π (h * p.1 * h⁻¹))).comp
                (X.comp ((Bs.π' (h'⁻¹ * p.2 * h')).comp (Bs.π' h'⁻¹))) := by rw [hA, hB]
          _ = (Bs.π h⁻¹).comp (((Bs.π (h * p.1 * h⁻¹)).comp (X.comp (Bs.π' (h'⁻¹ * p.2 * h')))).comp
                (Bs.π' h'⁻¹)) := by simp only [ContinuousLinearMap.comp_assoc]
          _ = X0 := by rw [hXt]
      have hXX : X = (Bs.π h).comp (X0.comp (Bs.π' h')) := by
        have : (Bs.π h).comp (X0.comp (Bs.π' h')) =
            ((Bs.π h).comp (Bs.π h⁻¹)).comp (X.comp ((Bs.π' h'⁻¹).comp (Bs.π' h'))) := by
          simp only [hX0def, ContinuousLinearMap.comp_assoc]
        rw [this, pmi h hh, pim' h' hh']
        ext v
        rfl
      have hc : ∀ ρ, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X) = inner ℂ (B.hsVec (e0 ρ ζ)) (B.hsVec X0) := by
        intro ρ
        rw [htr ρ ζ hζ h hh h' hh' hd]
        conv_lhs => rw [hXX]
        exact sm_inner_conj Bs hh hh' _ _
      have hsp0 := (he0.2 ζ hζ).2.2 X0 hX0
      have hrhs : ∑ ρ, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X) • e ρ ζ =
          ∑ ρ, inner ℂ (B.hsVec (e0 ρ ζ)) (B.hsVec X0) • (Bs.π h).comp ((e0 ρ ζ).comp (Bs.π' h')) :=
        Finset.sum_congr rfl fun ρ _ => by rw [hc ρ, htr ρ ζ hζ h hh h' hh' hd]
      rw [hrhs]
      conv_lhs => rw [hXX, hsp0]
      ext v
      simp only [ContinuousLinearMap.comp_apply, FunLike.coe_sum, Finset.sum_apply,
        FunLike.coe_smul, Pi.smul_apply, map_sum, map_smul]
  refine ⟨e, hframe, fun Φ => ?_⟩
  funext ρ
  unfold trR
  congr 1
  funext q
  have hζ : P.TT < Complex.normSq q.1.2 := q.2.2
  obtain ⟨h, hh, h', hh', hd⟩ := hdec q.1.2 hζ
  unfold rawR
  congr 1
  rw [htr ρ q.1.2 hζ h hh h' hh' hd, hd]
  have hq : (q.1.1, NF.muZ P.k P.r μ0 q.1.2) ∈ Q.DomR P.k P.r Bs.z Bs.z' :=
    Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' h0 (q := (q.1.1, q.1.2)) ⟨q.2.1, hTT q.1.2 hζ⟩
  rw [Φ.2.2.2 _ hq h hh h' hh']
  exact sm_inner_conj Bs hh hh' _ _

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
