import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothLevOfCk
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfBetaAdjCOfLemmaBNorm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BaseCutoffIsTruncation

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBE

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section gen

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem ckOn_top_of_nat {f : B.Mat k r → E} (hf : ∀ m : ℕ, B.CkOn (m : ℕ∞) (B.GV k r) f) :
    B.CkOn ⊤ (B.GV k r) f := by
  intro g₀ hG
  refine ⟨P5.Rad.retDom g₀, fun Y => f (P5.Rad.ret g₀ Y), P5.Rad.isOpen_retDom g₀, P5.Rad.self_mem_retDom hG,
    ?_, ?_⟩
  · intro Y hY
    apply ContDiffAt.contDiffWithinAt
    rw [show (((⊤ : ℕ∞) : WithTop ℕ∞)) = ∞ from rfl, contDiffAt_infty]
    intro n
    obtain ⟨U, F, hU, hYU, hF, hfF⟩ := hf n (P5.Rad.ret g₀ Y) (P5.Rad.ret_mem hG hY)
    have hr : ContDiffAt ℝ ∞ (P5.Rad.ret g₀) Y :=
      (P5.Rad.cd_ret g₀).contDiffAt ((P5.Rad.isOpen_retDom g₀).mem_nhds hY)
    have hFa : ContDiffAt ℝ n F (P5.Rad.ret g₀ Y) := by
      have := hF.contDiffAt (hU.mem_nhds hYU)
      exact_mod_cast this
    have hcomp : ContDiffAt ℝ n (fun Y' => F (P5.Rad.ret g₀ Y')) Y := hFa.comp Y (hr.of_le (mod_cast le_top))
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [(P5.Rad.isOpen_retDom g₀).mem_nhds hY, hr.continuousAt.preimage_mem_nhds (hU.mem_nhds hYU)]
      with Y' h1 h2
    exact hfF _ h2 (P5.Rad.ret_mem hG h1)
  · intro Y hY hYG
    show f Y = f (P5.Rad.ret g₀ Y)
    rw [P5.Rad.ret_self hG hYG hY.1]

theorem rdV_congrGV {X : B.Mat k r} (hX : B.inLie k r X) {h₁ h₂ : B.Mat k r → E}
    (hh : ∀ g ∈ B.GV k r, h₁ g = h₂ g) : ∀ g ∈ B.GV k r, RdV X h₁ g = RdV X h₂ g := by
  intro g hg
  unfold RdV
  congr 1
  funext t
  exact hh _ (B5.curve_mem hg hX t)

theorem rw_congrGV : ∀ (v : List (B.Mat k r)), (∀ X ∈ v, B.inLie k r X) → ∀ {h₁ h₂ : B.Mat k r → E},
    (∀ g ∈ B.GV k r, h₁ g = h₂ g) → ∀ g ∈ B.GV k r, B.Rw v h₁ g = B.Rw v h₂ g
  | [], _, _, _, hh => hh
  | X :: v, hv, _, _, hh => by
    show ∀ g ∈ B.GV k r, RdV X (B.Rw v _) g = RdV X (B.Rw v _) g
    exact rdV_congrGV (hv X (by simp)) (rw_congrGV v (fun Y hY => hv Y (by simp [hY])) hh)

theorem rdV_zero_near {X : B.Mat k r} (hX : B.inLie k r X) {h : B.Mat k r → E} {U : Set (B.Mat k r)}
    (hU : IsOpen U) (hh : ∀ g ∈ B.GV k r, g ∈ U → h g = 0) : ∀ g ∈ B.GV k r, g ∈ U → RdV X h g = 0 := by
  intro g hg hgU
  unfold RdV
  have hc : Continuous (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) := (B5.curve_contDiff g X).continuous
  have hU0 : U ∈ 𝓝 (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by
    rw [B5.curve_zero]; exact hU.mem_nhds hgU
  have hev : (fun t : ℝ => h (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [hc.continuousAt.preimage_mem_nhds hU0] with t ht
    exact hh _ (B5.curve_mem hg hX t) ht
  rw [hev.deriv_eq]
  simp

theorem rw_zero_near : ∀ (v : List (B.Mat k r)), (∀ X ∈ v, B.inLie k r X) → ∀ {h : B.Mat k r → E}
    {U : Set (B.Mat k r)}, IsOpen U → (∀ g ∈ B.GV k r, g ∈ U → h g = 0) →
    ∀ g ∈ B.GV k r, g ∈ U → B.Rw v h g = 0
  | [], _, _, _, _, hh => hh
  | X :: v, hv, _, _, hU, hh => by
    show ∀ g ∈ B.GV k r, g ∈ _ → RdV X (B.Rw v _) g = 0
    exact rdV_zero_near (hv X (by simp)) hU (rw_zero_near v (fun Y hY => hv Y (by simp [hY])) hU hh)

end gen

section ops

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem opApply_congrGV (Θ : B.DiffOp k r Wp Wq) {F₁ F₂ : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hh : ∀ g ∈ B.GV k r, F₁ g = F₂ g) : ∀ g ∈ B.GV k r, B.opApply Θ F₁ g = B.opApply Θ F₂ g := by
  intro g hg
  unfold B.opApply
  congr 1
  apply List.map_congr_left
  intro T _
  rw [rw_congrGV T.word T.word_lie hh g hg]

theorem opApply_zero_near (Θ : B.DiffOp k r Wp Wq) {F : B.Mat k r → (Wq →L[ℂ] Wp)} {U : Set (B.Mat k r)}
    (hU : IsOpen U) (hh : ∀ g ∈ B.GV k r, g ∈ U → F g = 0) : ∀ g ∈ B.GV k r, g ∈ U → B.opApply Θ F g = 0 := by
  intro g hg hgU
  unfold B.opApply
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨T, _, rfl⟩ := List.mem_map.1 hx
  rw [rw_zero_near T.word T.word_lie hU hh g hg hgU, map_zero]

end ops

section casts

variable {k : ℕ}

theorem castM_GV {a b : ℕ} (e : a = b) {x : B.Mat k a} (hx : x ∈ B.GV k a) : D.castM e x ∈ B.GV k b := by
  subst e; rwa [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]

theorem gN_castM {a b : ℕ} (e : a = b) (x : B.Mat k a) : B.gN (D.castM e x) = B.gN x := by
  subst e; rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]

theorem Gf_castM {a b : ℕ} (e : a = b) (z z' : Fin (2 * b + k + 1) → ℂ) (x : B.Mat k a) :
    Gf k a (D.castV e.symm z) (D.castV e.symm z') x = Gf k b z z' (D.castM e x) := by
  subst e; rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, Formalism.FourierDecayAlt.P.JCTx6.Link2.castV_self,
    Formalism.FourierDecayAlt.P.JCTx6.Link2.castV_self]

end casts

theorem isCompact_gN_le (k r : ℕ) (R : ℝ) : IsCompact {g : B.Mat k r | B.gN g ≤ R} := by
  have hcl : IsClosed {g : B.Mat k r | B.gN g ≤ R} := isClosed_le Formalism.FourierDecayAlt.P.B6.gN_continuous continuous_const
  refine (isCompact_closedBall (0 : B.Mat k r) R).of_isClosed_subset hcl ?_
  intro g hg
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (Matrix.norm_le_iff ((norm_nonneg _).trans ((Formalism.FourierDecayAlt.P.Dx3.entry_le_gN g 0 0).trans hg))).2 ?_
  intro i j
  exact (Formalism.FourierDecayAlt.P.Dx3.entry_le_gN g i j).trans hg

end Formalism.FourierDecayAlt.P.PBE
