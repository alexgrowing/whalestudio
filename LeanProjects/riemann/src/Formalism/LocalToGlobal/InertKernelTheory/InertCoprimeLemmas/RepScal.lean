import Formalism.LocalToGlobal.InertKernelTheory.DefsRep
import Formalism.LocalToGlobal.PairingIndexBounds.PendingAdmissibility.LocalFDerivAdmissibility.IteratedFDerivConstSmul

noncomputable section

namespace Formalism.L2.KerInert.Rep

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
open Formalism.MainNotions.FormalGroupSystem (Sys)

theorem isComb_smul (D : D7) (T : Tor D) (e : FamE D) {N N' p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    {F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]} (h : IsComb D T e lam L L' F) {c : ℂ_[p]}
    (hc : ‖c‖ ≤ 1) : IsComb D T e lam L L' (c • F) := by
  obtain ⟨m, r, t, L₁, L₁', hr, ht, hL, rfl⟩ := h
  refine ⟨m, fun k => c * r k, t, L₁, L₁', fun k => ?_, ht, hL, ?_⟩
  · have := hr k
    simp only [IsIntP] at this ⊢
    rw [norm_mul]
    exact mul_le_one₀ hc (norm_nonneg _) this
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, map_mul, mul_assoc]

theorem isComb_scalar (D : D7) (T : Tor D) (e : FamE D) {N N' p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (G : VC D N N' → ℂ) (h : IsComb D T e lam L L' (pSer D lam G)) {s : ℂ} (hs : s ∈ Qbar) (k : ℤ)
    (hk : ‖(p : ℂ_[p]) ^ k * lamC lam s‖ ≤ 1) :
    IsComb D T e lam L L' (((p : ℂ_[p]) ^ k) • pSer D lam (fun z => s * G z)) := by
  have e1 : ((p : ℂ_[p]) ^ k) • pSer D lam (fun z => s * G z) = ((p : ℂ_[p]) ^ k * lamC lam s) • pSer D lam G := by
    rw [Formalism.L2.PairingIndexBounds.PowerSeriesNecessity.pSer_const_mul D lam hs, Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]
    rfl
  rw [e1]
  exact isComb_smul D T e lam h hk

theorem combAt_scalar {p : ℕ} [Fact p.Prime] (X : Sys p) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))
    (T : Tor D) (e : FamE D) (lam : Qbar →+* ℂ_[p])
    (G : ∀ j, X.Lt j → X.Lt (j + 1) → VC D ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
    (s : ∀ j, X.Lt j → X.Lt (j + 1) → ℂ) (k : ∀ j, X.Lt j → X.Lt (j + 1) → ℤ)
    (h : CombAt X hfin D large₂ Lg' (fun j La La' => pSer D lam (G j La La')) T e lam)
    (hs : ∀ j (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1),
      (X.Pj (j + 1)).IsLatTup La'.2 → s j L0 La' ∈ Qbar ∧ ‖(p : ℂ_[p]) ^ k j L0 La' * lamC lam (s j L0 La')‖ ≤ 1) :
    CombAt X hfin D large₂ Lg'
      (fun j La La' => ((p : ℂ_[p]) ^ k j La La') • pSer D lam (fun z => s j La La' * G j La La' z)) T e lam := by
  intro j L0 h0 La' hL'
  obtain ⟨hA, hC⟩ := h j L0 h0 La' hL'
  exact ⟨hA, isComb_scalar D T e lam _ hC (hs j L0 h0 La' hL').1 _ (hs j L0 h0 La' hL').2⟩

end Formalism.L2.KerInert.Rep
