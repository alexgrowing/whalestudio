import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_GCore_GenTransferKapCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeVLem
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedF

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GTK

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge

section hs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem hs_expand (A C : Wq →L[ℂ] Wp) :
    inner ℂ (B.hsVec A) (B.hsVec C) =
      ∑ i, inner ℂ (A (stdOrthonormalBasis ℂ Wq i)) (C (stdOrthonormalBasis ℂ Wq i)) := by
  simp only [B.hsVec, PiLp.inner_apply, PiLp.toLp_apply]

theorem hs_comp_right (A C : Wq →L[ℂ] Wp) (Q : Wq →L[ℂ] Wq) (hQ : ∀ v w, inner ℂ (Q v) w = inner ℂ v (Q w)) :
    inner ℂ (B.hsVec A) (B.hsVec (C.comp Q)) = inner ℂ (B.hsVec (A.comp Q)) (B.hsVec C) := by
  rw [hs_expand, hs_expand]
  set b := stdOrthonormalBasis ℂ Wq
  have hQe : ∀ i, Q (b i) = ∑ j, inner ℂ (b j) (Q (b i)) • b j := fun i => (b.sum_repr' _).symm
  simp only [ContinuousLinearMap.comp_apply]
  conv_lhs => arg 2; ext i; rw [hQe i, map_sum, inner_sum]
  conv_rhs => arg 2; ext j; rw [hQe j, map_sum, sum_inner]
  simp only [map_smul, inner_smul_right, inner_smul_left]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [inner_conj_symm, hQ]

theorem hs_comp_sum {ι : Type} [Fintype ι] (A C : Wq →L[ℂ] Wp) (Q : ι → (Wq →L[ℂ] Wq)) (f : ι → ℂ) :
    inner ℂ (B.hsVec A) (B.hsVec (C.comp (∑ σ, f σ • Q σ))) =
      ∑ σ, f σ * inner ℂ (B.hsVec A) (B.hsVec (C.comp (Q σ))) := by
  simp only [hs_expand, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, map_sum, map_smul, inner_sum, inner_smul_right, Finset.mul_sum]
  exact Finset.sum_comm

theorem comp_sum_eq {ι : Type} [Fintype ι] (C : Wq →L[ℂ] Wp) (Q : ι → (Wq →L[ℂ] Wq)) :
    C.comp (∑ σ, Q σ) = ∑ σ, C.comp (Q σ) := by
  ext v
  simp [ContinuousLinearMap.sum_apply, map_sum]

end hs

theorem gauge_kappa_of_point_line : GTKapOfCut := by
  intro hPt hLine Wp Wq _ _ _ _ _ _ P Bs X d hH
  obtain ⟨Qr, hQ⟩ := hPt Wp Wq P Bs X d hH
  have hQQ := hQ.1
  have hQ1 := hQ.2.1
  have hQs := hQ.2.2.1
  have hQk := hQ.2.2.2
  have hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' := hH.1
  have hcs : CSec P.k P.r Bs.z Bs.z' Bs.μsec := hH.2.2.1
  have hTz : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := by
    rw [hpl.2.2.2.1, hpl.2.2.2.2.1]; rfl

  set ζ0 : ℂ := ((Real.sqrt P.TT + 1 : ℝ) : ℂ) with hζ0def
  have hTT : 0 < P.TT := mul_pos hpl.1.T_pos hpl.1.T'_pos
  have hζ0 : P.TT < Complex.normSq ζ0 := by
    rw [hζ0def, Complex.normSq_ofReal]
    have hs := Real.sq_sqrt hTT.le
    nlinarith [Real.sqrt_nonneg P.TT]

  have hFib : ∀ ζ : ℂ, P.TT < Complex.normSq ζ →
      NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ = NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ0 := by
    intro ζ hζ
    have hS : NF.Stab P.k P.r Bs.z Bs.z' Bs.μsec ζ = NF.Stab P.k P.r Bs.z Bs.z' Bs.μsec ζ0 :=
      hcs.2 ζ ζ0 (by rw [hTz]; exact hζ) (by rw [hTz]; exact hζ0)
    unfold NF.Fib
    rw [hS]
  choose E hEF hEQ hE1 hEu using fun ρ => hLine Wp Wq P Bs X d hH Qr hQ ζ0 hζ0 ρ

  have hRB : NF.RadBase P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' :=
    ⟨hpl.1.k_pos, hpl.2.1, hpl.2.2.1, by rw [hpl.2.2.2.1]; exact hpl.1.T_pos,
      by rw [hpl.2.2.2.2.1]; exact hpl.1.T'_pos, Bs.sec, hpl.2.2.2.2.2.1.2.1, hpl.2.2.2.2.2.2.2.1,
      hpl.2.2.2.2.2.1.2.2.1, hpl.2.2.2.2.2.2.2.2.1⟩
  have hcomp : ∀ Z ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ0, ∀ ρ,
      Z.comp (Qr ρ) ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ0 := by
    intro Z hZ ρ
    let φ : (Fin P.r → ℂ) × ℂ → (Wq →L[ℂ] Wp) := (NF.QR P.k P.r Bs.z Bs.z').indicator fun _ => Z
    have hφ : φ ∈ NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
      refine ⟨(contDiffOn_const (c := Z)).congr fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
      · simp [φ, Set.indicator_of_mem hx]
      · simp only [φ, Set.indicator_of_mem hx]
        rw [hFib x.2 (by rw [← hTz]; exact hx.2)]; exact hZ
      · simp [φ, Set.indicator_of_notMem hx]
    obtain ⟨Φ, hΦ, hrad⟩ := Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB φ hφ
    let c0 : Fin P.r → ℂ := fun _ => 1
    have hc0 : c0 ∈ OmX P.r := fun _ => one_ne_zero
    have hq0 : ((c0, ζ0) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc0, by rw [hTz]; exact hζ0⟩
    have hval : Φ c0 (NF.muZ P.k P.r Bs.μsec ζ0) = Z := by
      have h := congrFun hrad (c0, ζ0)
      simp only [NF.radR, Set.indicator_of_mem hq0, φ] at h
      exact h
    let q0 : MA.Qp P.r P.TT := ⟨(c0, ζ0), ⟨hc0, hζ0⟩⟩
    let f : M.Ty P → ℂ := fun σ => if σ = ρ then 1 else 0
    have hk := hQk f ⟨Φ, hΦ⟩ q0
    have hsum : (∑ σ, f σ • Qr σ) = Qr ρ := by
      simp [f, Finset.sum_ite_eq']
    rw [hsum] at hk
    have hmem := Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _
      ((d.κ f).1 ⟨Φ, hΦ⟩).2
    have h2 := hmem.2.1 (c0, ζ0) hq0
    simp only [NF.radR, Set.indicator_of_mem hq0] at h2
    have hk' : (((d.κ f).1 ⟨Φ, hΦ⟩ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0
        (NF.muZ P.k P.r Bs.μsec ζ0) = Z.comp (Qr ρ) := by
      rw [← hval]; exact hk
    rw [hk'] at h2
    exact h2
  refine ⟨fun ρ _ => E ρ, ⟨fun ρ => contDiffOn_const, fun ζ hζ => ⟨fun ρ => ?_, fun ρ ρ' => ?_, fun Z hZ => ?_⟩⟩, ?_⟩
  · rw [hFib ζ hζ]; exact hEF ρ
  · split_ifs with h
    · subst h; exact hE1 ρ
    · calc inner ℂ (B.hsVec (E ρ)) (B.hsVec (E ρ'))
          = inner ℂ (B.hsVec (E ρ)) (B.hsVec ((E ρ').comp (Qr ρ'))) := by rw [hEQ ρ']
        _ = inner ℂ (B.hsVec ((E ρ).comp (Qr ρ'))) (B.hsVec (E ρ')) := hs_comp_right _ _ _ (hQs ρ')
        _ = 0 := by
          have h0 : (E ρ).comp (Qr ρ') = 0 := by
            rw [← hEQ ρ, ContinuousLinearMap.comp_assoc, hQQ ρ ρ', if_neg h, ContinuousLinearMap.comp_zero]
          rw [h0, VLem.hsV_zero, inner_zero_left]
  · have hZ0 : Z ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ0 := by rw [← hFib ζ hζ]; exact hZ
    have hdec : Z = ∑ ρ, Z.comp (Qr ρ) := by
      rw [← comp_sum_eq, hQ1]; rfl
    conv_lhs => rw [hdec]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    have hfix : (Z.comp (Qr ρ)).comp (Qr ρ) = Z.comp (Qr ρ) := by
      rw [ContinuousLinearMap.comp_assoc, hQQ ρ ρ, if_pos rfl]
    rw [hEu ρ _ (hcomp Z hZ0 ρ) hfix, hs_comp_right _ _ _ (hQs ρ), hEQ ρ]
  · intro f Φ
    funext ρ
    have hraw : rawR P Bs.μsec (fun ρ _ => E ρ)
        (((d.κ f).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ =
        f ρ • rawR P Bs.μsec (fun ρ _ => E ρ) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ := by
      funext q
      simp only [rawR, Pi.smul_apply, smul_eq_mul]
      rw [hQk f Φ q, hs_comp_sum]
      have hterm : ∀ σ, f σ * inner ℂ (B.hsVec (E ρ))
          (B.hsVec (((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2)).comp (Qr σ))) =
          if σ = ρ then f ρ * inner ℂ (B.hsVec (E ρ))
            (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2))) else 0 := by
        intro σ
        rw [hs_comp_right _ _ _ (hQs σ)]
        split_ifs with h
        · subst h; rw [hEQ σ]
        · have h0 : (E ρ).comp (Qr σ) = 0 := by
            rw [← hEQ ρ, ContinuousLinearMap.comp_assoc, hQQ ρ σ, if_neg (Ne.symm h), ContinuousLinearMap.comp_zero]
          rw [h0, VLem.hsV_zero, inner_zero_left, mul_zero]
      simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    show MA.toSm P (rawR P Bs.μsec (fun ρ _ => E ρ)
        (((d.κ f).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ) = _
    rw [hraw, VLem.toSm_smul]
    have hkap : MA.kap P (MA.DQ P) f = Matrix.diagonal fun σ => algebraMap ℂ (MA.DQ P).Pr (f σ) := rfl
    rw [hkap, VLem.actA_diag]
    rfl

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GTK
