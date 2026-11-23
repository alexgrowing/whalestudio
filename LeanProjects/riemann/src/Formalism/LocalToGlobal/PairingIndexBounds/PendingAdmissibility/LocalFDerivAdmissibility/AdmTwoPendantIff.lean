import Formalism.LocalToGlobal.PairingIndexBounds.PendingAdmissibility.LocalFDerivAdmissibility.CentralCharacterOfAdmTwo

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend

namespace Formalism.L2.PairingIndexBounds.PowerSeriesNecessity

variable {p : ℕ} [Fact p.Prime]

theorem subst_C_mul' {σ τ R : Type} [CommRing R] {a : σ → MvPowerSeries τ R} (ha : MvPowerSeries.HasSubst a) (c : R)
    (f : MvPowerSeries σ R) : MvPowerSeries.subst a (MvPowerSeries.C c * f) = MvPowerSeries.C c * MvPowerSeries.subst a f := by
  rw [← MvPowerSeries.smul_eq_C_mul, MvPowerSeries.subst_smul ha, MvPowerSeries.smul_eq_C_mul]

theorem K1gen_C_mul {ι : Type} [Fintype ι] {K1 : Type} [Field K1] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) K1] {R1 : Subring K1}
    {be : MvPowerSeries (Fin 2) (Formalism.MainNotions.FormalGroupSystem.K0 p)} {Th : MvPowerSeries (ι ⊕ ι) K1} {c : K1} (hc : c ∈ R1)
    (h : ExtensionGeneratorCondition p K1 R1 be Th) : ExtensionGeneratorCondition p K1 R1 be (MvPowerSeries.C c * Th) := by
  unfold ExtensionGeneratorCondition at h ⊢
  obtain ⟨Ph, U, hTh, hU, h1, h2, h3⟩ := h
  refine ⟨Ph, MvPowerSeries.C c * U, ?_, ?_, h1, h2, h3⟩
  · rw [hTh]
    ring
  · intro n
    have key : inParamK p K1 (MvPowerSeries.C c * U) = MvPowerSeries.C c * inParamK p K1 U := by
      unfold inParamK
      exact subst_C_mul' (hasSubst_logX K1) c U
    rw [key, MvPowerSeries.coeff_C_mul]
    exact R1.mul_mem hc (hU n)

theorem K1gen_C_mul_iff {ι : Type} [Fintype ι] {K1 : Type} [Field K1] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) K1] {R1 : Subring K1}
    {be : MvPowerSeries (Fin 2) (Formalism.MainNotions.FormalGroupSystem.K0 p)} {Th : MvPowerSeries (ι ⊕ ι) K1} {c : K1} (hc : c ∈ R1) (hc' : c⁻¹ ∈ R1)
    (hc0 : c ≠ 0) : ExtensionGeneratorCondition p K1 R1 be (MvPowerSeries.C c * Th) ↔ ExtensionGeneratorCondition p K1 R1 be Th := by
  constructor
  · intro h'
    have h2 := K1gen_C_mul hc' h'
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul] at h2
  · exact K1gen_C_mul hc

theorem adm_two_pendant_iff (D : Formalism.BasicNotions.D7) (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : LTIso g) {T : Type}
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) :
    letI := wittFractionAlgebraCp p
    letI := algKfC E.toCEmb
    adm2b D X (pendT X E hfin hst hLT pos F) ↔
      ∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
        ∀ φ : Frm X j La La', ExtensionGeneratorCondition p ℂ_[p] (OcC p) (beLT hLT)
          (thA ℂ_[p] φ (SA X ℂ_[p] j (gamAt X j La.1 (delt X hfin j La.1 La.2))
            (thFOf X pos F j (La.1, (X.Lv.lev j La.1).smul (delt X hfin j La.1 La.2)⁻¹ La.2) La'))) := by
  let _ := wittFractionAlgebraCp p
  let _ := algKfC E.toCEmb
  have key : ∀ j (La : X.Lt j) (La' : X.Lt (j + 1)) (φ : Frm X j La La'),
      (pendT X E hfin hst hLT pos F).ThA j La La' φ = MvPowerSeries.C (chiN X ℂ_[p] hfin j La) *
        thA ℂ_[p] φ (SA X ℂ_[p] j (gamAt X j La.1 (delt X hfin j La.1 La.2))
          (thFOf X pos F j (La.1, (X.Lv.lev j La.1).smul (delt X hfin j La.1 La.2)⁻¹ La.2) La')) := by
    intro j La La' φ
    exact subst_C_mul' (hasSubst_invF ℂ_[p] φ) _ _
  have hn : ∀ j (La : X.Lt j), ‖chiN X ℂ_[p] hfin j La‖ = 1 := fun j La => norm_chiN X E.toCEmb hfin j La
  constructor
  · intro h j hj La La' hL hL' φ
    have h1 := h j hj La La' hL hL' φ
    change ExtensionGeneratorCondition p ℂ_[p] (OcC p) (beLT hLT) ((pendT X E hfin hst hLT pos F).ThA j La La' φ) at h1
    rw [key] at h1
    refine (K1gen_C_mul_iff ?_ ?_ ?_).1 h1
    · show ‖_‖ ≤ 1; rw [hn]
    · show ‖_‖ ≤ 1; rw [norm_inv, hn, inv_one]
    · intro h0; have := hn j La; rw [h0, norm_zero] at this; exact zero_ne_one this
  · intro h j hj La La' hL hL' φ
    change ExtensionGeneratorCondition p ℂ_[p] (OcC p) (beLT hLT) ((pendT X E hfin hst hLT pos F).ThA j La La' φ)
    rw [key]
    refine K1gen_C_mul ?_ (h j hj La La' hL hL' φ)
    show ‖_‖ ≤ 1; rw [hn]

end Formalism.L2.PairingIndexBounds.PowerSeriesNecessity
