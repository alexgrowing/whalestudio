import Formalism.LocalToGlobal.InertKernelTheory.DefsRepLt
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepFrame
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepTwLat
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepAsm
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepScal
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepDataRec
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepTrace

noncomputable section

open scoped Matrix

namespace Formalism.L2.KerInert.RepLt

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.KerInert.RepFrame Formalism.L2.KerInert.RepTwLat
open Formalism.L2.G.Pend (Frm)
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

section Lat

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7)
  (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
  (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
  (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))

end Lat

section Int

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
  (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
  (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7)
  (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
  (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))

theorem frameIntLt_of (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v) (hM : MInv X M) (hT : TwInt X E)
    (hL : FrameLatMapLt X M hfin D large₂ Lg' ρ) : FrameIntLt X E hfin D large₂ Lg' M ρ := by
  intro j hj L0 hL0 La' hLa' φ r b hb ho i v s b0 a0
  obtain ⟨h1, h2⟩ := hL j hj L0 hL0 La' hLa' φ r b hb ho i v
  constructor
  · obtain ⟨w, hw⟩ := entry_int (W := X.G.P.W v) (Gm X M φ v) (Gmi X M φ v) (Gmi_mul_Gm X M φ (hM j L0) v)
      ((b i).map (fun y => ρ v (D.host.conj y)))ᵀ (Gp X M φ v) h2 a0 b0
    have e1 : ∑ B, ∑ A, ρ v (D.host.conj (b i B A)) * Gp X M φ v B b0 * Gmi X M φ v a0 A =
        (Gmi X M φ v * ((b i).map (fun y => ρ v (D.host.conj y)))ᵀ * Gp X M φ v) a0 b0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun B _ => ?_
      rw [Matrix.mul_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun A _ => ?_
      simp only [Matrix.transpose_apply, Matrix.map_apply]
      ring
    rw [e1, hw]
    exact hT v s w
  · obtain ⟨w, hw⟩ := entry_int (W := X.G.P.W v) (Gp X M φ v) (Gpi X M φ v) (Gpi_mul_Gp X M φ (hM (j + 1) La') v)
      ((b i).map (ρ v)) (Gm X M φ v) h1 b0 a0
    have e1 : ∑ B, ∑ A, ρ v (b i B A) * Gm X M φ v A a0 * Gpi X M φ v b0 B =
        (Gpi X M φ v * (b i).map (ρ v) * Gm X M φ v) b0 a0 := by
      rw [Matrix.mul_apply, Finset.sum_comm]
      refine Finset.sum_congr rfl fun B _ => ?_
      rw [Matrix.mul_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun A _ => ?_
      simp only [Matrix.map_apply]
      ring
    rw [e1, hw]
    exact hT v s w

end Int

end Formalism.L2.KerInert.RepLt

namespace Formalism.L2.KerInert.RepLt

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.Th1.Top Formalism.L2.KerInert.K1 Formalism.L2.KerInert.RepFrame
open Formalism.InvariantFactorPaths.G7 (UnrOK)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.G.Pend (Frm)
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
  (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
  (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
  (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))
  (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))

theorem hypCoordLt_of (lam : Qbar →+* ℂ_[p]) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v)
    (hT : LamTraceLt X hfin D large₂ Lg' lam) (hρ : LamPosG X E D pos lam ρ) (hF : FrobTw X E)
    (hev : ∀ v, Even (X.G.P.n' v)) (hconj : ∀ x, D.host.conj (D.host.conj x) = x) (hM : MInv X M)
    (hI : FrameIntLt X E hfin D large₂ Lg' M ρ) :
    HypCoordLt X E hfin D pos large₂ Lg' M lam 1 := by
  intro j hj L0 hL0 La' hLa' r b hb ho φ
  obtain ⟨σ, twK, wK, hσ, htwK, hσtw, hwK, hσw, hwn⟩ := hF
  have hL := hT j hj L0 hL0 La' hLa' r b hb ho
  have hH : IsHypPair σ (fK X D M φ b ρ twK wK) (fK' X D M φ b ρ twK wK) := by
    unfold IsHypPair
    refine ⟨fun e i => ⟨?_, ?_⟩, fun e i => ⟨?_, ?_⟩, fun e e' => ?_, fun e e' => ?_, fun e e' => ?_⟩
    · exact norm_fK X E D M φ b ρ twK wK htwK hwn
        (fun i v s b0 a0 => (hI j hj L0 hL0 La' hLa' φ r b hb ho i v s b0 a0).1) e i
    · exact sigma2_fK X D M φ b ρ twK wK σ hσtw hσw hev hconj e i
    · exact norm_fK' X E D M φ b ρ twK wK htwK hconj hwn
        (fun i v s b1 a1 => (hI j hj L0 hL0 La' hLa' φ r b hb ho i v s b1 a1).2) e i
    · exact sigma2_fK' X D M φ b ρ twK wK σ hσtw hσw hev hconj e i
    · exact iso_fK X E D pos lam M φ b ρ twK wK hρ htwK σ hσtw hσw hev hconj hL e e'
    · exact iso_fK' X E D pos lam M φ b ρ twK wK hρ htwK σ hσtw hσw hev hconj hL e e'
    · rw [dual_fK X E D pos lam M φ b ρ twK wK hρ htwK σ hσtw hσw hev hconj hL (hM j L0) (hM (j + 1) La') e e']
  refine ⟨σ, fK X D M φ b ρ twK wK, fK' X D M φ b ρ twK wK, hσ, hH, fun e i => ?_, fun e i => ?_⟩
  · rw [inv_one, one_mul]
    exact coe_fK X E D pos lam M φ b ρ twK wK hρ htwK hwK e i
  · rw [inv_one, one_mul]
    exact coe_fK' X E D pos lam M φ b ρ twK wK hρ htwK hwK hconj e i

theorem frameStdLt_of (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p]) (hc0 : c ≠ 0) (h1 : OnbExLt X hfin D large₂ Lg')
    (h2 : LamTraceLt X hfin D large₂ Lg' lam) (h3 : HypCoordLt X E hfin D pos large₂ Lg' M lam c) :
    FrameStdLt X E hfin D pos large₂ Lg' M lam c := by
  intro j hj L0 hL0 La' hLa' φ
  obtain ⟨r, b, hb, ho⟩ := h1 j hj L0 hL0 La' hLa'
  obtain ⟨σ, f, f', hσ, hH, hf, hf'⟩ := h3 j hj L0 hL0 La' hLa' r b hb ho φ
  have hL := h2 j hj L0 hL0 La' hLa' r b hb ho
  refine ⟨r, b, hb, ho, σ, f, f', hσ, hH, fun k => ?_⟩
  rw [(isLin_stdLin X E pos M φ k).repr, Fintype.sum_sum_type]
  simp only [hypLin, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun i e => MvPowerSeries.C (c * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) *
        (MvPowerSeries.C (f e i : ℂ_[p]) * MvPowerSeries.X (Sum.inl e))),
    Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun i e => MvPowerSeries.C (c * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) *
        (MvPowerSeries.C (f' e i : ℂ_[p]) * MvPowerSeries.X (Sum.inr e)))]
  congr 1
  · refine Finset.sum_congr rfl fun e _ => ?_
    simp only [← mul_assoc, ← map_mul]
    rw [← Finset.sum_mul, ← map_sum]
    congr 2
    simp only [hf]
    exact (coord_recon D lam b hL hc0 (fun k' => frVec X E pos M φ (Sum.inl e) k') k).symm
  · refine Finset.sum_congr rfl fun e _ => ?_
    simp only [← mul_assoc, ← map_mul]
    rw [← Finset.sum_mul, ← map_sum]
    congr 2
    simp only [hf']
    exact (coord_recon D lam b hL hc0 (fun k' => frVec X E pos M φ (Sum.inr e) k') k).symm

theorem frameLinLt_of_std (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p]) (h : FrameStdLt X E hfin D pos large₂ Lg' M lam c) :
    FrameLinLt X E hfin D pos large₂ Lg' (fun j La La' => subGen X E pos M j La La') lam c := by
  intro j hj L0 hL0 La' hLa' φ
  obtain ⟨r, b, hb, ho, σ, f, f', hσ, hH, hk⟩ := h j hj L0 hL0 La' hLa' φ
  exact ⟨r, b, hb, ho, σ, f, f', hσ, hH, fun k => (linFrame_subGen X E pos M φ k).trans (hk k)⟩

theorem frameHypLt_of_lin (S : ∀ j, X.Lt j → X.Lt (j + 1) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) → ℂ_[p])
    (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p]) (h : FrameLinLt X E hfin D pos large₂ Lg' S lam c)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) :
    FrameHypLt X E hfin D pos large₂ Lg' F S lam c := by
  intro j hj L0 hL0 La' hLa' φ
  obtain ⟨r, b, hb, ho, σ, f, f', hσ, hH, hk⟩ := h j hj L0 hL0 La' hLa' φ
  refine ⟨r, b, hb, ho, σ, f, f', hσ, hH, ?_⟩
  rw [thA_thFOf_linSub X E pos φ S F, subst_hypLin_thOrth]
  congr 1
  funext k
  exact hk k

theorem onbExLt_of (hO : Formalism.L2.KerInert.OrthBasisExists) (h5 : 5 ≤ p) (hin : jacobiSym (-(D.host.d : ℤ)) p = -1)
    (hadm : ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1),
      (X.Pj (j + 1)).IsLatTup La'.2 → admitted D _ _ (large₂ j L0 La') (Lg' j L0 La')) :
    OnbExLt X hfin D large₂ Lg' :=
  fun j hj L0 hL0 La' hLa' => hO D p h5 hin _ _ _ _ (hadm j hj L0 hL0 La' hLa')

theorem rankTieLt_of (hadm : ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1),
      (X.Pj (j + 1)).IsLatTup La'.2 → admitted D _ _ (large₂ j L0 La') (Lg' j L0 La')) :
    RankTieLt X hfin D large₂ Lg' :=
  fun j hj L0 hL0 La' hLa' _ b hb =>
    rank_of_locBasis _ _ (hadm j hj L0 hL0 La' hLa').2.2.1 (hadm j hj L0 hL0 La' hLa').2.2.2 b hb

theorem lamTraceLt_of (lam : Qbar →+* ℂ_[p]) (h1 : RankTieLt X hfin D large₂ Lg') (h2 : ColTie X hfin D large₂ Lg' lam) :
    LamTraceLt X hfin D large₂ Lg' lam :=
  fun j hj L0 hL0 La' hLa' r b hb ho =>
    lamONB_of_cols D lam b (h1 j hj L0 hL0 La' hLa' r b hb) (h2 j L0 hL0 La' hLa' r b hb ho)

theorem frameHypLt_of_lat (lam : Qbar →+* ℂ_[p]) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v)
    (h1 : OnbExLt X hfin D large₂ Lg') (hT : LamTraceLt X hfin D large₂ Lg' lam) (hρ : LamPosG X E D pos lam ρ)
    (hF : FrobTw X E) (hM : MInv X M) (hTw : TwInt X E) (hL : FrameLatMapLt X M hfin D large₂ Lg' ρ)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) :
    FrameHypLt X E hfin D pos large₂ Lg' F (fun j La La' => subGen X E pos M j La La') lam 1 :=
  frameHypLt_of_lin X E hfin D pos large₂ Lg' _ lam 1
    (frameLinLt_of_std X E hfin D pos large₂ Lg' M lam 1
      (frameStdLt_of X E hfin D pos large₂ Lg' M lam 1 one_ne_zero h1 hT
        (hypCoordLt_of X E hfin D pos large₂ Lg' M lam ρ hT hρ hF (fun v => (X.G.P.setting v).even) (conj_conj D) hM
          (frameIntLt_of X E M hfin D large₂ Lg' ρ hM hTw hL)))) F

end Formalism.L2.KerInert.RepLt

namespace Formalism.L2.KerInert.RepLt

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H Formalism.L2.KerInert.RepComb

theorem combAtLt_of_dataRec {p : ℕ} [Fact p.Prime] (X : Formalism.MainNotions.FormalGroupSystem.Sys p) [IsFractionRing X.G.O X.G.Kf]
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)
    (χ : TaylorLogMetric.IdE D → ℂ) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (lam : TaylorLogMetric.Qbar →+* ℂ_[p])
    (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hAlg : B.AlgT χ)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))
    (Ξ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
    (hD : Formalism.L2.KerInert.RepRec.DataRec X D cl Ξ)
    (hA : ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1),
      (X.Pj (j + 1)).IsLatTup La'.2 → TaylorLogMetric.admitted D _ _ (large₂ j L0 La') (Lg' j L0 La')) :
    CombAtLt X hfin D large₂ Lg'
      (fun j La La' => Formalism.L2.PairingIndexBounds.F.serP lam (Formalism.L2.PairingIndexBounds.F.kerTh B χ SS cl (large₂ j La La') (Lg' j La La') (Ξ j La La')))
      B.tor (B.eNat χ) lam := by
  obtain ⟨S, hS, hpS, hΞ⟩ := hD
  have hTA : TransAlg D B.tor (B.eNat χ) :=
    transcendence_algebraic_eigen D cc δ B χ hcc hδ (KS.Lat.delta_ne hcc hδ) (B.stdOK hcc hδ) hAlg
  intro j hj L0 h0 La' hL'
  have h := hA j hj L0 h0 La' hL'
  exact ⟨h, combined_kernel_twisted D cc δ B χ _ _ SS cl _ _ _ S p lam h h.2.2.2.1 h.2.2.1.2.1 (aaOf_fg cc)
    (laFacts_of_adm B hcc hδ h) hS.1 hS (hΞ j L0 La') hpS (lambda_in_lattice_pair cc δ _ _) hTA⟩

theorem combAtLt_scalar {p : ℕ} [Fact p.Prime] (X : Formalism.MainNotions.FormalGroupSystem.Sys p) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))
    (T : TaylorLogMetric.Tor D) (e : TaylorLogMetric.FamE D) (lam : TaylorLogMetric.Qbar →+* ℂ_[p])
    (G : ∀ j, X.Lt j → X.Lt (j + 1) → TaylorLogMetric.VC D ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
    (s : ∀ j, X.Lt j → X.Lt (j + 1) → ℂ) (k : ∀ j, X.Lt j → X.Lt (j + 1) → ℤ)
    (h : CombAtLt X hfin D large₂ Lg' (fun j La La' => TaylorLogMetric.pSer D lam (G j La La')) T e lam)
    (hs : ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1),
      (X.Pj (j + 1)).IsLatTup La'.2 → s j L0 La' ∈ TaylorLogMetric.Qbar ∧ ‖(p : ℂ_[p]) ^ k j L0 La' * TaylorLogMetric.lamC lam (s j L0 La')‖ ≤ 1) :
    CombAtLt X hfin D large₂ Lg'
      (fun j La La' => ((p : ℂ_[p]) ^ k j La La') • TaylorLogMetric.pSer D lam (fun z => s j La La' * G j La La' z)) T e lam := by
  intro j hj L0 h0 La' hL'
  obtain ⟨hA, hC⟩ := h j hj L0 h0 La' hL'
  exact ⟨hA, Formalism.L2.KerInert.Rep.isComb_scalar D T e lam _ hC (hs j hj L0 h0 La' hL').1 _ (hs j hj L0 h0 La' hL').2⟩

end Formalism.L2.KerInert.RepLt

namespace Formalism.L2.KerInert.RepLt

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.Th1.Top Formalism.L2.KerInert.K1 Formalism.L2.KerInert.Rep
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (cob UnrOK IsLawOfLog)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.G.Pend (k0ToC wittFractionAlgebraCp OcC Frm thA thFOf)
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

theorem firstKernelLawSmallSteps_of_curve_orthAllLt {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) (X : Sys p) [IsFractionRing X.G.O X.G.Kf]
    (E : Formalism.L2.G.Pend.CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (be : MvPowerSeries (Fin 2) (K0 p))
    {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])
    (hB : BeProp p be) (g2 g3 ε s2 : MaximalUnramifiedExtension p) (hC : CurveAt p be g2 g3 ε s2)
    (hO : OrthAllLt X E hfin pos F g2 g3 s2 ε) :
    FirstKernelLawLocalPowerSeries X E hfin be pos F := by
  intro j hj L0 h0 La' hL' φ
  exact k1gen_of_orth h5 hB hC (hO j hj L0 h0 La' hL' φ)

theorem K1_representatives_LT_of_dictionary (hCD : CurveDict) (hInt : Formalism.L2.KerInert.IntInert) (D : D7) {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p)
    (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses)
    {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : Formalism.L2.G.Pend.LTIso g)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hA : Formalism.MainNotions.GL3Theta.At D cc δ g) (hIn : Formalism.MainNotions.GL3Theta.InertK D p)
    (hM : Formalism.MainNotions.GL3Theta.ModelOverW g.lam g.abelian₂ g.C) (B : Base D cc δ) (hcc : IsCurveIdeal D cc) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    (χ : IdE D → ℂ) (hχ : IsChi D χ) (hin : jacobiSym (-(D.host.d : ℤ)) p = -1) (hLam : g.abelian₂ = B.tor.abelian₂)
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))
    (F Fr : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])
    (hFr : ∀ j La La', Fr j La La' =
      sclY (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹) (F j La La'))
    (S : ∀ j, X.Lt j → X.Lt (j + 1) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) → ℂ_[p])
    (hB : BeProp p (Formalism.L2.G.Pend.beLT hLT))
    (hComb : CombAtLt X hfin D large₂ Lg' F B.tor (B.eNat χ) g.lam)
    (hFH : FrameHypLt X E hfin D pos large₂ Lg' Fr S g.lam 1) :
    FirstKernelLawLocalPowerSeries X E hfin (Formalism.L2.G.Pend.beLT hLT) pos (fun j La La' => linSub (S j La La') (Fr j La La')) := by
  obtain ⟨g2, g3, ε, s2, hC, hD⟩ := curveDict_data hCD D cc δ hLT hA h5 hIn hM
  have hD' : DictInt D g.lam B.tor.abelian₂ (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹) g2 g3 s2 ε := by
    rw [← hLam]
    exact hD D
  obtain ⟨C, wq, hMod, hW, hDi⟩ := hD'
  refine firstKernelLawSmallSteps_of_curve_orthAllLt h5 X E hfin _ pos _ hB g2 g3 ε s2 hC ?_
  intro j hj L0 h0 La' hL' φ
  obtain ⟨r, b, hLB, hON, σ, f, f', hσ, hP, hEq⟩ := hFH j hj L0 h0 La' hL' φ
  obtain ⟨hAdm, hCb⟩ := hComb j hj L0 h0 La' hL'
  refine ⟨r, thOrth D g.lam (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹) b (F j L0 La'), σ, f, f', hσ,
    hP, ?_, hDi _ _ r b _ (hInt D cc δ B hcc hδ χ hχ p h5 hin g.lam _ _ _ _ hAdm (F j L0 La') hCb C wq r b hMod hW hLB hON)⟩
  rw [hEq, hFr, thOrth_sclY]

end Formalism.L2.KerInert.RepLt

set_option pp.fullNames true
