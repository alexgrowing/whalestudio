import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCModConst
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSPointwise

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.SR

noncomputable section

def c1 (r : ℕ) : Fin r → ℂ := fun _ => 1

theorem constant_one_mem_nonvanishing (r : ℕ) : c1 r ∈ OmX r := fun _ => one_ne_zero

def AtCSec : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → Gauge.GC.CSec P.k P.r Bs.z Bs.z' Bs.μsec →
    ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr → ∀ π : M.Ty P,
    ∀ ζ ∈ Gauge.GC.Ann P, ∀ X0 ∈ Line P Bs Pr π ζ,
      ∃ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
        (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c1 P.r) (NF.muZ P.k P.r Bs.μsec ζ) = X0 ∧
        ‖B.hsVec ((((d.SS l).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c1 P.r)
            (NF.muZ P.k P.r Bs.μsec ζ))‖ ^ 2 = M.Nrm P l π * ‖B.hsVec X0‖ ^ 2 ∧
        ∀ ρ : M.Ty P, M.Up P l π ρ →
          (((d.SS l).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c1 P.r)
            (NF.muZ P.k P.r Bs.μsec ζ) ∈ Line P Bs Pr ρ ζ

def LineMove : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (μ' : ℂ → Matrix (Fin (P.k + 1)) (Fin (P.k + 1)) ℂ) (hμ' : IsSection P.k P.r Bs.z Bs.z' μ'),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → ∀ ζ ∈ Gauge.GC.Ann P, ∀ h ∈ UWset P.k P.r Bs.z, ∀ h' ∈ UWset P.k P.r Bs.z',
    NF.muZ P.k P.r Bs.μsec ζ = h * NF.muZ P.k P.r μ' ζ * h' →
    ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr → ∀ σ : M.Ty P,
    ∀ Y ∈ Line P { Bs with μsec := μ', sec := hμ' } Pr σ ζ, (Bs.π h).comp (Y.comp (Bs.π' h')) ∈ Line P Bs Pr σ ζ

section aux

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem conj_back {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) {h h' : B.Mat k r} (hh : h ∈ UWset k r Bs.z)
    (hh' : h' ∈ UWset k r Bs.z') (Y : Wq →L[ℂ] Wp) :
    (Bs.π h⁻¹).comp (((Bs.π h).comp (Y.comp (Bs.π' h'))).comp (Bs.π' h'⁻¹)) = Y := by
  have hhi := LieBracketMultiplication.uw_inv hh
  have hh'i := LieBracketMultiplication.uw_inv hh'
  have e1 : (Bs.π h⁻¹).comp (Bs.π h) = 1 := by
    rw [← Bs.π_rep.2 _ hhi _ hh, NFRadRedS.uw_inv_mul hh, Bs.π_rep.1]
  have e2 : (Bs.π' h').comp (Bs.π' h'⁻¹) = 1 := by
    rw [← Bs.π'_rep.2 _ hh' _ hh'i, NFRadRedS.uw_mul_inv hh', Bs.π'_rep.1]
  ext v
  have k1 := DFunLike.congr_fun e1 (Y (Bs.π' h' (Bs.π' h'⁻¹ v)))
  have k2 := DFunLike.congr_fun e2 v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at k1 k2 ⊢
  rw [k1, k2]

theorem conj_fwd {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) {h h' : B.Mat k r} (hh : h ∈ UWset k r Bs.z)
    (hh' : h' ∈ UWset k r Bs.z') (Y : Wq →L[ℂ] Wp) :
    (Bs.π h).comp (((Bs.π h⁻¹).comp (Y.comp (Bs.π' h'⁻¹))).comp (Bs.π' h')) = Y := by
  have hhi := LieBracketMultiplication.uw_inv hh
  have hh'i := LieBracketMultiplication.uw_inv hh'
  have e1 : (Bs.π h).comp (Bs.π h⁻¹) = 1 := by
    rw [← Bs.π_rep.2 _ hh _ hhi, NFRadRedS.uw_mul_inv hh, Bs.π_rep.1]
  have e2 : (Bs.π' h'⁻¹).comp (Bs.π' h') = 1 := by
    rw [← Bs.π'_rep.2 _ hh'i _ hh', NFRadRedS.uw_inv_mul hh', Bs.π'_rep.1]
  ext v
  have k1 := DFunLike.congr_fun e1 (Y (Bs.π' h'⁻¹ (Bs.π' h' v)))
  have k2 := DFunLike.congr_fun e2 v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at k1 k2 ⊢
  rw [k2] at k1
  rw [k2, k1]

end aux

theorem core (hC : AtCSec) (hM : LineMove) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hk : 2 ≤ P.k) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (hA : ActHyp P Bs X d)
    (l : ℕ) (hl : l ∈ Finset.Icc 1 (P.k - 1)) (S : ℂ → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)))
    (hS : IsSSPt P Bs d l S) (Pr : M.Ty P → (Fin (2 * P.r + P.k + 1) → ℂ) → (Wp →L[ℂ] Wp))
    (hPr : PRho.PRhoSpec P Bs.z Bs.π Pr) (π : M.Ty P) (ζ : ℂ) (hζ : ζ ∈ Gauge.GC.Ann P)
    (Xf : Wq →L[ℂ] Wp) (hXf : Xf ∈ Line P Bs Pr π ζ) :
    ‖B.hsVec (S ζ Xf)‖ ^ 2 = M.Nrm P l π * ‖B.hsVec Xf‖ ^ 2 ∧
      ∀ ρ : M.Ty P, M.Up P l π ρ → S ζ Xf ∈ Line P Bs Pr ρ ζ := by
  have hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' := hA.1
  have hz := Bs.z_mem
  have hz' := Bs.z'_mem
  have hTz : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := Gauge.GC.tz_TT P Bs hpl
  have hcs0 := Formalism.FourierDecayAlt.P.TheSecStab.theSection_csec (k := P.k) (r := P.r) (by omega) Bs.z_mem Bs.z'_mem
    Bs.T_pos Bs.T'_pos
  set μ0 := TheSec.theSection P.k P.r Bs.z Bs.z' with hμ0
  let Bs0 : B.RealPlaceData P.k P.r Wp Wq := { Bs with μsec := μ0, sec := hcs0.1 }
  have hq : ((c1 P.r, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' :=
    ⟨constant_one_mem_nonvanishing P.r, by rw [hTz]; exact hζ⟩
  have hdom := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec hq
  have hdom0 := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hcs0.1 hq
  obtain ⟨h, hh, h', hh', he⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.decomp Bs.k_pos hz hz' Bs.T_pos Bs.T'_pos hcs0.1
    hdom.2.1 hdom.2.2
  rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hz hz' Bs.sec hq.2] at he
  change NF.muZ P.k P.r Bs.μsec ζ = h * NF.muZ P.k P.r μ0 ζ * h' at he
  change ((c1 P.r, NF.muZ P.k P.r μ0 ζ) : (Fin P.r → ℂ) × Q.Mx P.k P.r) ∈ Q.DomR P.k P.r Bs.z Bs.z' at hdom0
  have hhi := LieBracketMultiplication.uw_inv hh
  have hh'i := LieBracketMultiplication.uw_inv hh'
  have hback : NF.muZ P.k P.r μ0 ζ = h⁻¹ * NF.muZ P.k P.r Bs.μsec ζ * h'⁻¹ := by
    rw [he, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh, Matrix.one_mul,
      Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh', Matrix.mul_one]
  set X0 := (Bs.π h⁻¹).comp (Xf.comp (Bs.π' h'⁻¹)) with hX0def
  have hX0 : X0 ∈ Line P Bs0 Pr π ζ :=
    hM Wp Wq P Bs0 Bs.μsec Bs.sec hpl ζ hζ h⁻¹ hhi h'⁻¹ hh'i hback Pr hPr π Xf hXf
  obtain ⟨Φ, hΦ, hN, hL⟩ := hC Wp Wq P Bs0 hk hcs0 X d hA l hl Pr hPr π ζ hζ X0 hX0
  have hΦf : (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c1 P.r) (NF.muZ P.k P.r Bs.μsec ζ) = Xf := by
    rw [he, Φ.2.2.2 (c1 P.r, NF.muZ P.k P.r μ0 ζ) hdom0 h hh h' hh']
    change (Bs.π h).comp (((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c1 P.r) (NF.muZ P.k P.r Bs0.μsec ζ)).comp (Bs.π' h')) = Xf
    rw [hΦ, hX0def]
    exact conj_fwd Bs hh hh' Xf
  set Y0 := ((((d.SS l).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c1 P.r)
    (NF.muZ P.k P.r μ0 ζ)) with hY0def
  have hSv : S ζ Xf = (Bs.π h).comp (Y0.comp (Bs.π' h')) := by
    rw [← hΦf, ← hS Φ (c1 P.r) (constant_one_mem_nonvanishing P.r) ζ hζ, he]
    exact ((d.SS l).1 Φ).2.2.2 (c1 P.r, NF.muZ P.k P.r μ0 ζ) hdom0 h hh h' hh'
  have hnX : ‖B.hsVec X0‖ = ‖B.hsVec Xf‖ := Formalism.FourierDecayAlt.P.CutBP.hsVec_norm_CinL Bs hhi hh' Xf
  have hnY : ‖B.hsVec Y0‖ = ‖B.hsVec (S ζ Xf)‖ := by
    have e : Y0 = Dx2.VV.CinL Bs h⁻¹ h' (S ζ Xf) := by
      rw [Dx2.VV.CinL_apply, hSv]
      exact (conj_back Bs hh hh' Y0).symm
    rw [e]
    exact Formalism.FourierDecayAlt.P.CutBP.hsVec_norm_CinL Bs hhi hh' _
  refine ⟨?_, fun ρ hUp => ?_⟩
  · rw [← hnY, ← hnX]
    exact hN
  · rw [hSv]
    exact hM Wp Wq P Bs μ0 hcs0.1 hpl ζ hζ h hh h' hh' he Pr hPr ρ Y0 (hL ρ hUp)

theorem sRaise_of (hC : AtCSec) (hM : LineMove) : SRaise := by
  intro Wp Wq _ _ _ _ _ _ P Bs hk X d hA l hl S hS Pr hPr π ρ hUp ζ hζ Xf hXf
  exact (core hC hM P Bs hk X d hA l hl S hS Pr hPr π ζ hζ Xf hXf).2 ρ hUp

theorem sNorm_of (hC : AtCSec) (hM : LineMove) : SNorm := by
  intro Wp Wq _ _ _ _ _ _ P Bs hk X d hA l hl S hS Pr hPr π ζ hζ Xf hXf
  exact (core hC hM P Bs hk X d hA l hl S hS Pr hPr π ζ hζ Xf hXf).1

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.SR
