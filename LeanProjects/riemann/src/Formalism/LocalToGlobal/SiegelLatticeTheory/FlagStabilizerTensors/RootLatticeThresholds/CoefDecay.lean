import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CoefDecayA
import Formalism.SharpRestriction.CuspSpanNormBounds.LowestKTypeMultiplicity
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.BetaCut
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundOfCompact

open Matrix Filter Topology
open scoped InnerProductSpace ContDiff

noncomputable section

namespace Formalism.L2.SG.Pf.CoefDecay

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def rk1 (ξ : Wp) (ξ' : Wq) : Wq →L[ℂ] Wp := (innerSL ℂ ξ').smulRight ξ

def cf (σ : B.Mat k r → (H →L[ℂ] H)) (a b : H) (T : Wq →L[ℂ] Wp) : B.Mat k r → (Wq →L[ℂ] Wp) :=
  fun g => ⟪a, σ g b⟫_ℂ • T

theorem coefM_eq (σ : B.Mat k r → (H →L[ℂ] H)) (v v' : H) (ξ : Wp) (ξ' : Wq) :
    Formalism.MainNotions.S.Pv.BetaCut.coefM σ v v' ξ ξ' = cf σ v v' (rk1 ξ ξ') := by
  funext g
  ext x
  simp only [Formalism.MainNotions.S.Pv.BetaCut.coefM, cf, rk1, ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply]
  rw [smul_comm]

variable {σ : B.Mat k r → (H →L[ℂ] H)}

theorem dsigW_smooth (hσ : Formalism.MainNotions.S.IsURepOn (B.GV k r) σ) {v : H}
    (hv : Formalism.MainNotions.S.IsSmoothVec (k := k) (r := r) σ v) (D : List (B.Mat k r))
    (hD : ∀ X ∈ D, Formalism.MainNotions.S.InLieHpk k r X) :
    Formalism.MainNotions.S.IsSmoothVec (k := k) (r := r) σ (Formalism.MainNotions.S.dsigW σ D v) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, h0, hF, hE⟩ :=
    Formalism.MainNotions.LowestKTypeMultiplicity.psiD_smooth hσ hv D hD ((1 : B.Mat k r), g₀) (Formalism.MainNotions.LowestKTypeMultiplicity.UH_one k r) hg₀
  have hc : ContDiff ℝ ∞ (fun g : B.Mat k r => ((1 : B.Mat k r), g)) := contDiff_const.prodMk contDiff_id
  refine ⟨(fun g : B.Mat k r => ((1 : B.Mat k r), g)) ⁻¹' U, fun g => F (1, g), hU.preimage hc.continuous, h0,
    hF.comp hc.contDiffOn (fun x hx => hx), ?_⟩
  intro g hgU hgH
  have := hE (1, g) hgU (Formalism.MainNotions.LowestKTypeMultiplicity.UH_one k r) hgH
  simp only [hσ.1.1, one_apply_eq_self] at this
  exact this

theorem ss_cf {b : H} (hb : Formalism.MainNotions.S.IsSmoothVec (k := k) (r := r) σ b) (a : H) (T : Wq →L[ℂ] Wp) :
    PI.ComplexConjugateDerivative.SS k r (cf σ a b T) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, h0, hF, hE⟩ := hb g₀ hg₀
  let L : H →L[ℝ] (Wq →L[ℂ] Wp) := ((innerSL ℂ a).smulRight T).restrictScalars ℝ
  refine ⟨U, fun g => L (F g), hU, h0, L.contDiff.comp_contDiffOn hF, fun g hgU hgG => ?_⟩
  show ⟪a, σ g b⟫_ℂ • T = L (F g)
  have e := hE g hgU hgG
  simp only at e
  rw [e]
  rfl

theorem hasDeriv_R (hσ : Formalism.MainNotions.S.IsURepOn (B.GV k r) σ) {v' : H}
    (hv' : Formalism.MainNotions.S.IsSmoothVec (k := k) (r := r) σ v') (w : List (B.Mat k r))
    (hw : ∀ X ∈ w, Formalism.MainNotions.S.InLieHpk k r X) {Y : B.Mat k r} (hY : Formalism.MainNotions.S.InLieHpk k r Y) (a : H)
    {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    HasDerivAt (fun t : ℝ => ⟪a, σ (g * NormedSpace.exp ((t : ℂ) • Y)) (Formalism.MainNotions.S.dsigW σ w v')⟫_ℂ)
      ⟪a, σ g (Formalism.MainNotions.S.dsigW σ (Y :: w) v')⟫_ℂ 0 := by
  have h1 := Formalism.MainNotions.LowestKTypeMultiplicity.dsigW_hasDeriv hσ hv' w hw hY
  have h2 := (((innerSL ℂ a).comp (σ g)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  show ⟪a, σ (g * NormedSpace.exp ((t : ℂ) • Y)) (Formalism.MainNotions.S.dsigW σ w v')⟫_ℂ =
    ⟪a, σ g (σ (NormedSpace.exp ((t : ℂ) • Y)) (Formalism.MainNotions.S.dsigW σ w v'))⟫_ℂ
  rw [hσ.1.2 g hg _ (Formalism.MainNotions.LowestKTypeMultiplicity.exp_mem_UH hY t)]
  rfl

theorem inner_exp_move (hσ : Formalism.MainNotions.S.IsURepOn (B.GV k r) σ) {X : B.Mat k r}
    (hX : Formalism.MainNotions.S.InLieHpk k r X) (t : ℝ) (x y : H) :
    ⟪x, σ (NormedSpace.exp (-((t : ℂ) • X))) y⟫_ℂ = ⟪σ (NormedSpace.exp ((t : ℂ) • X)) x, y⟫_ℂ := by
  have he : NormedSpace.exp ((t : ℂ) • X) ∈ B.GV k r := Formalism.MainNotions.LowestKTypeMultiplicity.exp_mem_UH hX t
  have hX' : Formalism.MainNotions.S.InLieHpk k r (-X) := by
    have h : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
    show (-X)ᴴ * Hpk k r + Hpk k r * (-X) = 0
    rw [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, h, neg_zero]
  have he' : NormedSpace.exp (-((t : ℂ) • X)) ∈ B.GV k r := by
    rw [← smul_neg]; exact Formalism.MainNotions.LowestKTypeMultiplicity.exp_mem_UH hX' t
  have e1 : NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp (-((t : ℂ) • X)) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl ((t : ℂ) • X)).neg_right)]
    simp
  let L : H →ₗᵢ[ℂ] H := ⟨(σ (NormedSpace.exp ((t : ℂ) • X)) : H →ₗ[ℂ] H), fun v => hσ.2.1 _ he v⟩
  have h1 : ⟪x, σ (NormedSpace.exp (-((t : ℂ) • X))) y⟫_ℂ =
      ⟪L x, L (σ (NormedSpace.exp (-((t : ℂ) • X))) y)⟫_ℂ := (L.inner_map_map _ _).symm
  rw [h1]
  show ⟪σ (NormedSpace.exp ((t : ℂ) • X)) x,
    σ (NormedSpace.exp ((t : ℂ) • X)) (σ (NormedSpace.exp (-((t : ℂ) • X))) y)⟫_ℂ = _
  have h2 : σ (NormedSpace.exp ((t : ℂ) • X)) (σ (NormedSpace.exp (-((t : ℂ) • X))) y) = y := by
    have := hσ.1.2 _ he _ he'
    rw [e1, hσ.1.1] at this
    have h3 := congrArg (fun T : H →L[ℂ] H => T y) this
    simpa using h3.symm
  rw [h2]

theorem hasDeriv_L (hσ : Formalism.MainNotions.S.IsURepOn (B.GV k r) σ) {v : H}
    (hv : Formalism.MainNotions.S.IsSmoothVec (k := k) (r := r) σ v) (u : List (B.Mat k r))
    (hu : ∀ X ∈ u, Formalism.MainNotions.S.InLieHpk k r X) {X : B.Mat k r} (hX : Formalism.MainNotions.S.InLieHpk k r X) (y : H)
    {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    HasDerivAt (fun t : ℝ => ⟪Formalism.MainNotions.S.dsigW σ u v, σ (NormedSpace.exp (-((t : ℂ) • X)) * g) y⟫_ℂ)
      ⟪Formalism.MainNotions.S.dsigW σ (X :: u) v, σ g y⟫_ℂ 0 := by
  have hX' : Formalism.MainNotions.S.InLieHpk k r (-X) := by
    have h : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
    show (-X)ᴴ * Hpk k r + Hpk k r * (-X) = 0
    rw [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, h, neg_zero]
  have h1 := Formalism.MainNotions.LowestKTypeMultiplicity.dsigW_hasDeriv hσ hv u hu hX
  have h2 := h1.inner ℂ (hasDerivAt_const (0 : ℝ) (σ g y))
  rw [inner_zero_right, zero_add] at h2
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  have he' : NormedSpace.exp (-((t : ℂ) • X)) ∈ B.GV k r := by
    rw [← smul_neg]; exact Formalism.MainNotions.LowestKTypeMultiplicity.exp_mem_UH hX' t
  show ⟪Formalism.MainNotions.S.dsigW σ u v, σ (NormedSpace.exp (-((t : ℂ) • X)) * g) y⟫_ℂ =
    ⟪σ (NormedSpace.exp ((t : ℂ) • X)) (Formalism.MainNotions.S.dsigW σ u v), σ g y⟫_ℂ
  rw [hσ.1.2 _ he' g hg]
  exact inner_exp_move hσ hX t _ _

theorem Rw_cf (hσ : Formalism.MainNotions.S.IsURepOn (B.GV k r) σ) {v' : H}
    (hv' : Formalism.MainNotions.S.IsSmoothVec (k := k) (r := r) σ v') (a : H) (T : Wq →L[ℂ] Wp) :
    ∀ w : List (B.Mat k r), (∀ X ∈ w, Formalism.MainNotions.S.InLieHpk k r X) → ∀ g ∈ B.GV k r,
      B.Rw w (cf σ a v' T) g = cf σ a (Formalism.MainNotions.S.dsigW σ w v') T g
  | [], _, _, _ => rfl
  | Y :: w, hw, g, hg => by
    have hw' : ∀ X ∈ w, Formalism.MainNotions.S.InLieHpk k r X := fun X hX => hw X (List.mem_cons_of_mem _ hX)
    have hY : Formalism.MainNotions.S.InLieHpk k r Y := hw Y List.mem_cons_self
    have hc := PI.ComplexConjugateDerivative.D_congr (E := Wq →L[ℂ] Wp) (b := false) (X := Y)
      (fun y hy => Rw_cf hσ hv' a T w hw' y hy) hg hY
    refine (hc : Formalism.REAL.RdV Y (B.Rw w (cf σ a v' T)) g = Formalism.REAL.RdV Y (cf σ a (Formalism.MainNotions.S.dsigW σ w v') T) g).trans ?_
    have hd := hasDeriv_R hσ hv' w hw' hY a hg
    show deriv (fun t : ℝ => ⟪a, σ (g * NormedSpace.exp ((t : ℂ) • Y)) (Formalism.MainNotions.S.dsigW σ w v')⟫_ℂ • T) 0 =
      ⟪a, σ g (Formalism.MainNotions.S.dsigW σ (Y :: w) v')⟫_ℂ • T
    rw [deriv_smul_const hd.differentiableAt, hd.deriv]

theorem dLR_cf (hσ : Formalism.MainNotions.S.IsURepOn (B.GV k r) σ) {v v' : H}
    (hv : Formalism.MainNotions.S.IsSmoothVec (k := k) (r := r) σ v) (hv' : Formalism.MainNotions.S.IsSmoothVec (k := k) (r := r) σ v')
    (T : Wq →L[ℂ] Wp) :
    ∀ u w : List (B.Mat k r), (∀ X ∈ u, Formalism.MainNotions.S.InLieHpk k r X) → (∀ X ∈ w, Formalism.MainNotions.S.InLieHpk k r X) →
      ∀ g ∈ B.GV k r, B.dLR u w (cf σ v v' T) g = cf σ (Formalism.MainNotions.S.dsigW σ u v) (Formalism.MainNotions.S.dsigW σ w v') T g
  | [], w, _, hw, g, hg => Rw_cf hσ hv' v T w hw g hg
  | X :: u, w, hu, hw, g, hg => by
    have hu' : ∀ Y ∈ u, Formalism.MainNotions.S.InLieHpk k r Y := fun Y hY => hu Y (List.mem_cons_of_mem _ hY)
    have hX : Formalism.MainNotions.S.InLieHpk k r X := hu X List.mem_cons_self
    have hc := PI.ComplexConjugateDerivative.D_congr (E := Wq →L[ℂ] Wp) (b := true) (X := X)
      (fun y hy => dLR_cf hσ hv hv' T u w hu' hw y hy) hg hX
    refine (hc : B.LdV X (B.dLR u w (cf σ v v' T)) g =
      B.LdV X (cf σ (Formalism.MainNotions.S.dsigW σ u v) (Formalism.MainNotions.S.dsigW σ w v') T) g).trans ?_
    have hd := hasDeriv_L hσ hv u hu' hX (Formalism.MainNotions.S.dsigW σ w v') hg
    show deriv (fun t : ℝ => ⟪Formalism.MainNotions.S.dsigW σ u v,
      σ (NormedSpace.exp (-((t : ℂ) • X)) * g) (Formalism.MainNotions.S.dsigW σ w v')⟫_ℂ • T) 0 =
      ⟪Formalism.MainNotions.S.dsigW σ (X :: u) v, σ g (Formalism.MainNotions.S.dsigW σ w v')⟫_ℂ • T
    rw [deriv_smul_const hd.differentiableAt, hd.deriv]

theorem coefM_inCC_of_dec (hσ : Formalism.MainNotions.S.IsURepOn (B.GV k r) σ) {A : ℝ}
    (hdec : ∀ a ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ, ∀ b ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ,
      ∃ C : ℝ, ∀ g ∈ B.GV k r, B.gN g ^ A * ‖⟪a, σ g b⟫_ℂ‖ ≤ C)
    {v v' : H} (hv : v ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ)
    (hv' : v' ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ) (ξ : Wp) (ξ' : Wq) (m : ℕ) :
    B.InCC (k := k) (r := r) A m (Formalism.MainNotions.S.Pv.BetaCut.coefM σ v v' ξ ξ') := by
  rw [coefM_eq]
  refine inCC_of_CCw ⟨ss_cf hv' v _, fun u w hu hw => ?_⟩ m
  have hu' : ∀ X ∈ u, Formalism.MainNotions.S.InLieHpk k r X := fun X hX => (hu X hX).1
  have hw' : ∀ X ∈ w, Formalism.MainNotions.S.InLieHpk k r X := fun X hX => (hw X hX).1
  obtain ⟨C, hC⟩ := hdec _ (dsigW_smooth hσ hv u hu') _ (dsigW_smooth hσ hv' w hw')
  refine ⟨C * ‖rk1 ξ ξ'‖, fun g hg => ?_⟩
  rw [dLR_cf hσ hv hv' _ u w hu' hw' g hg]
  show B.gN g ^ A * ‖⟪Formalism.MainNotions.S.dsigW σ u v, σ g (Formalism.MainNotions.S.dsigW σ w v')⟫_ℂ • rk1 ξ ξ'‖ ≤ _
  rw [norm_smul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hC g hg) (norm_nonneg _)

theorem coefM_inCC {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    (hlam : Formalism.QuantumDeterminants.IsHCParam lam) {h : ℝ} (hgap : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (m' : ℕ)
    (hm' : ReciprocityTheory.ChartRestriction.DS.thrStar ε + m' < h) {A : ℝ} (hA : A ≤ m')
    [CompleteSpace H] (hσ : Formalism.MainNotions.S.IsDSHpk k r ε lam σ) {v v' : H}
    (hv : v ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ) (hv' : v' ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ)
    (ξ : Wp) (ξ' : Wq) (m : ℕ) :
    B.InCC (k := k) (r := r) A m (Formalism.MainNotions.S.Pv.BetaCut.coefM σ v v' ξ ξ') := by
  obtain ⟨C, Ws, -, hC⟩ := ReciprocityTheory.ChartRestriction.DS.DecInf.decSm hlam hgap m' hm' hσ
  refine coefM_inCC_of_dec (Formalism.MainNotions.LowestKTypeMultiplicity.urep_of_DS hσ) (fun a ha b hb =>
    ⟨C * (Ws.map fun w => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w b‖).sum *
      (Ws.map fun w => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w a‖).sum, fun g hg => ?_⟩) hv hv' ξ ξ' m
  have h1 := PI.ComplexConjugateDerivative.one_le_gN hg
  calc B.gN g ^ A * ‖⟪a, σ g b⟫_ℂ‖ ≤ B.gN g ^ (m' : ℝ) * ‖⟪a, σ g b⟫_ℂ‖ :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le h1 hA) (norm_nonneg _)
    _ = B.gN g ^ m' * ‖⟪a, σ g b⟫_ℂ‖ := by rw [Real.rpow_natCast]
    _ ≤ _ := hC b hb a ha g hg

end Formalism.L2.SG.Pf.CoefDecay
