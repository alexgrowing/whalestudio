import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopFormTDM
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

namespace Formalism.FourierDecayAlt.P.CutBP.TDM

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section loc

variable {k r : ℕ} {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]

theorem dop_rdV_local {X : B.Mat k r} (hX : B.inLie k r X) {U : Set (B.Mat k r)} (hU : IsOpen U)
    {f f' : B.Mat k r → E₁} (he : ∀ x ∈ U, x ∈ B.GV k r → f x = f' x) {g : B.Mat k r} (hg : g ∈ U)
    (hgG : g ∈ B.GV k r) : Formalism.REAL.RdV X f g = Formalism.REAL.RdV X f' g := by
  show deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0 =
    deriv (fun t : ℝ => f' (g * NormedSpace.exp ((t : ℂ) • X))) 0
  apply Filter.EventuallyEq.deriv_eq
  have hc : Continuous (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) :=
    (Formalism.FourierDecayAlt.P.B5.curve_contDiff g X).continuous
  have hev : ∀ᶠ t : ℝ in nhds (0 : ℝ), g * NormedSpace.exp (((t : ℝ) : ℂ) • X) ∈ U := by
    apply hc.continuousAt.preimage_mem_nhds
    show U ∈ nhds (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X))
    rw [Formalism.FourierDecayAlt.P.B5.curve_zero]
    exact hU.mem_nhds hg
  filter_upwards [hev] with t ht
  exact he _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hgG hX t)

theorem dop_rw_local (w : List (B.Mat k r)) (hw : ∀ X ∈ w, B.inLie k r X) {U : Set (B.Mat k r)} (hU : IsOpen U)
    {f f' : B.Mat k r → E₁} (he : ∀ x ∈ U, x ∈ B.GV k r → f x = f' x) :
    ∀ x ∈ U, x ∈ B.GV k r → B.Rw w f x = B.Rw w f' x := by
  induction w with
  | nil => exact he
  | cons X w ih =>
    intro x hx hxG
    exact dop_rdV_local (hw X (by simp)) hU (ih (fun Y hY => hw Y (by simp [hY]))) hx hxG

theorem dop_rw_zero : ∀ v : List (B.Mat k r), B.Rw v (0 : B.Mat k r → E₁) = 0
  | [] => rfl
  | X :: v => by
    show Formalism.REAL.RdV X (B.Rw v 0) = 0
    rw [dop_rw_zero v]
    funext g
    simp [Formalism.REAL.RdV]

theorem dop_ckOn_ap {UU : Set (B.Mat k r)} {a : B.Mat k r → (E₁ →L[ℂ] E₂)} {Φ : B.Mat k r → E₁}
    (ha : B.CkOn ⊤ UU a) (hΦ : B.CkOn ⊤ UU Φ) : B.CkOn ⊤ UU (fun g => a g (Φ g)) := by
  intro g₀ hg₀
  obtain ⟨U, a', hU, hgU, hc, hff⟩ := ha g₀ hg₀
  obtain ⟨U₂, Φ', hU₂, hgU₂, hc₂, hff₂⟩ := hΦ g₀ hg₀
  refine ⟨U ∩ U₂, fun g => a' g (Φ' g), hU.inter hU₂, ⟨hgU, hgU₂⟩, ?_,
    fun g hg hgG => by simp only [hff g hg.1 hgG, hff₂ g hg.2 hgG]⟩
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun g => ContinuousLinearMap.restrictScalarsL ℂ E₁ E₂ ℝ ℝ (a' g)) (U ∩ U₂) :=
    (ContinuousLinearMap.restrictScalarsL ℂ E₁ E₂ ℝ ℝ).contDiff.comp_contDiffOn
      (hc.mono Set.inter_subset_left)
  exact h1.clm_apply (hc₂.mono Set.inter_subset_right)

theorem dop_ckOn_Rw {UU : Set (B.Mat k r)} {w : List (B.Mat k r)} (hw : ∀ X ∈ w, B.inLie k r X)
    {f : B.Mat k r → E₁} (hf : B.CkOn ⊤ UU f) : B.CkOn ⊤ UU (B.Rw w f) := by
  rw [← Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dw_wR]
  apply Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_Dw (fun x hx => Formalism.FourierDecayAlt.P.BetaSesquilinearity.lie_LR (u := []) (by simp) hw x
    (by simpa [Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL] using hx))
  have e : ((⊤ : ℕ∞) + ((Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR w).length : ℕ∞)) = ⊤ := top_add _
  rw [e]; exact hf

end loc

section op

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem dop_ckOn_opApply {UU : Set (B.Mat k r)} {J : B.Mat k r → (Wq →L[ℂ] Wp)} (hJ : B.CkOn ⊤ UU J) :
    ∀ Θ : B.DiffOp k r Wp Wq, (∀ T ∈ Θ, B.CkOn ⊤ UU T.coef) → B.CkOn ⊤ UU (B.opApply Θ J)
  | [], _ => by
    have e : B.opApply ([] : B.DiffOp k r Wp Wq) J = fun _ => 0 := by funext g; simp [B.opApply]
    rw [e]; exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_zero
  | T :: Θ, h => by
    have e : B.opApply (T :: Θ) J = fun g => T.coef g (B.Rw T.word J g) + B.opApply Θ J g := by
      funext g; simp [B.opApply]
    rw [e]
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add (dop_ckOn_ap (h T (by simp)) (dop_ckOn_Rw T.word_lie hJ))
      (dop_ckOn_opApply hJ Θ (fun T' hT' => h T' (by simp [hT'])))

theorem dop_opApply_zero (Θ : B.DiffOp k r Wp Wq) {O : Set (B.Mat k r)} (hO : IsOpen O)
    {J : B.Mat k r → (Wq →L[ℂ] Wp)} (hJ : ∀ g ∈ O, g ∈ B.GV k r → J g = 0) :
    ∀ g ∈ O, g ∈ B.GV k r → B.opApply Θ J g = 0 := by
  intro g hg hgG
  unfold B.opApply
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨T, _, rfl⟩ := List.mem_map.1 hx
  rw [dop_rw_local T.word T.word_lie hO (f' := 0) hJ g hg hgG, dop_rw_zero]
  simp

end op

theorem diff_operator_in_class_CC : DopCC := by
  intro Wp Wq _ _ _ _ _ _ P p X w Cb hD hX hw e
  obtain ⟨nf, fib, o, κ, Dop, hfib, hDD, -, -, hΘ⟩ := hD w hw e
  set Bs := p.T.base with hBs
  obtain ⟨hXs, ⟨R, hR⟩, ⟨ε, hε, hXε⟩⟩ := hX
  set O : Set (B.Mat P.k P.r) := {g | R < B.gN g} ∪ {g | Gf P.k P.r Bs.z Bs.z' g < ε} with hOdef
  have hO : IsOpen O := (isOpen_lt continuous_const Formalism.FourierDecayAlt.P.B6.gN_continuous).union
    (isOpen_lt (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.gf_cont _ _) continuous_const)
  have hX0 : ∀ g ∈ O, g ∈ B.GV P.k P.r → X g = 0 := by
    intro g hg hgG
    by_contra hne
    rcases hg with h | h
    · exact absurd (hR g hgG hne) (not_le.2 h)
    · exact absurd (hXε g hgG hne) (not_le.2 h)
  set Y : B.Mat P.k P.r → (Wq →L[ℂ] Wp) := B.opApply Dop X with hYdef
  have hY0 : ∀ g ∈ O, g ∈ B.GV P.k P.r → Y g = 0 := dop_opApply_zero Dop hO hX0
  have hYs : B.CkOn ⊤ (B.GV P.k P.r) Y := by
    intro g₀ hg₀
    by_cases hgO : g₀ ∈ O
    · exact ⟨O, 0, hO, hgO, contDiffOn_const, fun g hg hgG => hY0 g hg hgG⟩
    · have hG : ε ≤ Gf P.k P.r Bs.z Bs.z' g₀ := by
        by_contra h; exact hgO (Or.inr (not_le.1 h))
      have hdom : g₀ ∈ C6.domL Bs ∅ := ⟨hg₀, lt_of_lt_of_le hε hG, fun l hl => absurd hl (Finset.notMem_empty l)⟩
      have hXd : B.CkOn ⊤ (C6.domL Bs ∅) X := fun g hg => hXs g hg.1
      exact dop_ckOn_opApply hXd Dop (fun T hT => (hDD.1 T hT).1) g₀ hdom
  refine ⟨Y, fun g hg hG => ?_, fun A => ?_⟩
  · exact (hΘ X g ⟨hg, hG, fun l hl => absurd hl (Finset.notMem_empty l)⟩).symm
  ·
    set K : Set (B.Mat P.k P.r) := B.GV P.k P.r ∩ ({g | B.gN g ≤ R} ∩ {g | ε ≤ Gf P.k P.r Bs.z Bs.z' g}) with hKdef
    have hK : IsCompact K := (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le P.k P.r R).of_isClosed_subset
      (Formalism.FourierDecayAlt.P.B5.GV_closed.inter ((isClosed_le Formalism.FourierDecayAlt.P.B6.gN_continuous continuous_const).inter
        (isClosed_le continuous_const (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.gf_cont _ _))))
      (fun g hg => hg.2.1)
    have hYc : ContinuousOn Y (B.GV P.k P.r) := Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn hYs
    have hfc : ContinuousOn (fun g => B.gN g ^ A * ‖Y g‖) K := by
      refine ContinuousOn.mul ?_ ((hYc.mono Set.inter_subset_left).norm)
      exact (Formalism.FourierDecayAlt.P.B6.gN_continuous.continuousOn).rpow_const
        (fun g hg => Or.inl (ne_of_gt (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_pos hg.1)))
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hfc
    refine ⟨max C 0, ⟨?_, ?_⟩⟩
    · intro g₀ hg₀
      obtain ⟨U, f', hU, hgU, hc, he⟩ := hYs g₀ hg₀
      exact ⟨U, f', hU, hgU, hc.of_le (by exact_mod_cast le_top), he⟩
    · intro u v _ _ huv g hg
      have hu : u = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hv : v = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hu; subst hv
      show B.gN g ^ A * ‖Y g‖ ≤ max C 0
      by_cases hgK : g ∈ K
      · have := hC g hgK
        rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (le_of_lt (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_pos hg)) _)
          (norm_nonneg _))] at this
        exact le_trans this (le_max_left _ _)
      · have hgO : g ∈ O := by
          by_contra hgO
          apply hgK
          refine ⟨hg, ?_, ?_⟩
          · show B.gN g ≤ R
            by_contra h; exact hgO (Or.inl (not_le.1 h))
          · show ε ≤ Gf P.k P.r Bs.z Bs.z' g
            by_contra h; exact hgO (Or.inr (not_le.1 h))
        rw [hY0 g hgO hg, norm_zero, mul_zero]
        exact le_max_right _ _

end

end Formalism.FourierDecayAlt.P.CutBP.TDM
