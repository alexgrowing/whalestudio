import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.FdProps

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.Cx3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem stepD (j : ℕ) (p q : ℤ) {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg]
    [BorelSpace Kg] (μ : Measure Kg) [IsFiniteMeasure μ] [IsFiniteMeasureOnCompacts μ]
    (ι : Kg → M2 n) (hι : Continuous ι) (hιG : ∀ k, InG (ι k)) (ρ : Kg → ℂ) (hρ : Continuous ρ)
    (hC : ∀ g, InG g → ∫ k, hF j p q (ι k * g) * ρ k ∂μ = 0) :
    ∀ (N : ℕ) (W : Fin N → M2 n) (g : M2 n), InG g →
      ∫ k, iteratedFDeriv ℂ N (hF j p q) (ι k * g) (fun i => ι k * g * W i) * ρ k ∂μ = 0 := by
  intro N W g hg
  set Ω : Set (M2 n) := {x | ∀ k, ι k * x ∈ Dom n} with hΩ
  have hΩo : IsOpen Ω := isOpen_domK Kg ι hι
  have hGΩ : GSet n ⊆ Ω := fun x hx k => gset_sub_dom (inG_mul (hιG k) hx)
  have hF0 : ContDiffOn ℂ ∞ (hF (n := n) j p q) (Dom n) := contDiffOn_hF j p q
  have hsm : ∀ k, ContDiffOn ℂ ∞ (fun x => hF j p q (ι k * x) * ρ k) Ω := fun k =>
    (hF0.comp (contDiff_mulLeft (ι k)).contDiffOn (fun x (hx : x ∈ Ω) => hx k)).mul contDiffOn_const
  have hH := holInt n Kg μ Ω (fun k x => hF j p q (ι k * x) * ρ k) hΩo
    (fun N => continuousOn_iteratedFDeriv_translate (hF j p q) (Dom n) isOpen_dom hF0 Kg ι hι ρ hρ N) hsm
  have hz := holZero n Ω (fun x => ∫ k, hF j p q (ι k * x) * ρ k ∂μ) hΩo hGΩ hH.1
    (fun g hg => hC g hg) N g hg
  have key := hH.2 N g (fun i => g * W i) (hGΩ hg)
  rw [hz] at key
  simp only [_root_.zero_apply] at key
  rw [key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  have hk : ι k * g ∈ Dom n := hGΩ hg k
  show iteratedFDeriv ℂ N (hF j p q) (ι k * g) (fun i => ι k * g * W i) * ρ k =
    iteratedFDeriv ℂ N (fun x => hF j p q (ι k * x) * ρ k) g (fun i => g * W i)
  rw [iteratedFDeriv_mul_const_of (fun x => hF j p q (ι k * x)) Ω hΩo
    (hF0.comp (contDiff_mulLeft (ι k)).contDiffOn (fun x (hx : x ∈ Ω) => hx k)) (ρ k) g (hGΩ hg) N,
    iteratedFDeriv_left_mul (hF j p q) (Dom n) isOpen_dom hF0 (ι k) g hk N]
  simp only [mul_assoc]

theorem stepC (hFd : FdProps) (hDj : DjFd) (hSph : SphU) (hFz : FzHol) (m j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n)
    (ha1 : deriv (fun z : ℂ => (∏ i ∈ Finset.range j, ((i : ℂ) - z)) *
      (∏ i ∈ Finset.range (n - j), ((i : ℂ) - m - z))) 0 ≠ 0)
    {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg]
    [BorelSpace Kg] (μ : Measure Kg) [IsFiniteMeasure μ] [IsFiniteMeasureOnCompacts μ]
    (ι : Kg → M2 n) (hι : Continuous ι) (hιG : ∀ k, InG (ι k)) (ρ : Kg → ℂ) (hρ : Continuous ρ)
    (hB : ∀ g, InG g → detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
      ∫ k, Fd m (ι k * (g * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1)) * ρ k ∂μ)) = 0) :
    ∀ g, InG g → ∫ k, hF j (m : ℤ) 0 (ι k * g) * ρ k ∂μ = 0 := by
  intro g hg
  have hGZ : GSet n ⊆ DomZ n := (hFz n m 0).2.1
  have hkg : ∀ k, ι k * g ∈ DomZ n := fun k => hGZ (inG_mul (hιG k) hg)
  have hFdc : ContDiffOn ℂ ⊤ (Fd (n := n) m) (DomZ n) := (hFd n m).1
  have hS := hSph n (Fd m) (DomZ n) (hFz n m 0).1 hFdc μ ι hι ρ hρ (LQ (blkA j)) (LR (blkB j))
    (fun M x T => by rw [LQ_apply, LQ_apply, mul_assoc]) (fun M x S => by rw [LR_apply, LR_apply, mul_assoc]) g hkg
  have e1 : (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
      ∫ k, Fd m (ι k * (g * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1)) * ρ k ∂μ)) =
      fun T => detD (fun S => ∫ k, Fd m (ι k * (g + LQ (blkA j) g T + LR (blkB j) g S)) * ρ k ∂μ) := by
    funext T; congr 1; funext S
    rw [mul_mX, LQ_apply, LR_apply]
  have e2 : ∀ k, detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
      Fd m (ι k * g + LQ (blkA j) (ι k * g) T + LR (blkB j) (ι k * g) S))) * ρ k =
      deriv (fun z : ℂ => (∏ i ∈ Finset.range j, ((i : ℂ) - z)) *
        (∏ i ∈ Finset.range (n - j), ((i : ℂ) - m - z))) 0 * (hF j (m : ℤ) 0 (ι k * g) * ρ k) := by
    intro k
    have r : (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
        Fd m (ι k * g + LQ (blkA j) (ι k * g) T + LR (blkB j) (ι k * g) S))) =
        fun T => detD (fun S => Fd m ((ι k * g) * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1)) := by
      funext T; congr 1; funext S
      rw [mul_mX, LQ_apply, LR_apply]
    rw [r, hDj n m j (ι k * g) hj1 hjn (hkg k)]
    ring
  have h := hB g hg
  rw [e1, hS, integral_congr_ae (Filter.Eventually.of_forall e2), integral_const_mul] at h
  exact (mul_eq_zero.1 h).resolve_left ha1

end PositivityTheory.Rg.Sw.HSt.Cx3
