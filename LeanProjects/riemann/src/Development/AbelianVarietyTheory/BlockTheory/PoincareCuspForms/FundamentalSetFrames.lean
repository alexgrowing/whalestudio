import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.QuotientIsHausdorff
import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement

namespace GlobalTheory.IndefiniteRowSideFullHecke.FundamentalSetFrames

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open MeasureTheory
open scoped ENNReal NNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def GapsNonneg (X : Data E r) (la : Wt X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, (∀ i j : Fin r, i ≤ j → (j : ℕ) < X.p0 → la τ j ≤ la τ i) ∧
    (∀ i j : Fin r, X.p0 ≤ (i : ℕ) → i ≤ j → la τ j ≤ la τ i)

def pairing (X : Data E r) (h0 : 0 < X.p0) (h1 : X.p0 < r) (la : Wt X.Ψ r) (τ : X.Ψ) : ℤ :=
  la τ ⟨r - 1, by omega⟩ - la τ ⟨0, by omega⟩

theorem pairing_kapW (X : Data E r) (h0 : 0 < X.p0) (h1 : X.p0 < r) (τ : X.Ψ) :
    pairing X h0 h1 (kapW X) τ = 2 * (r : ℤ) - 2 := by
  have : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by omega
  simp only [pairing, kapW, this]
  push_cast
  ring

def IsInvWeight (X : Data E r) (u : Frame X.Ψ r → EReal) : Prop :=
  Measurable (fun x : X.dom => u x) ∧
  (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, u (lact γ (rmul x b)) = u x) ∧
  ∃ C : ℝ, ∀ x ∈ X.dom, u x ≤ (C : EReal)

theorem isInvWeight_const (X : Data E r) (c : ℝ) : IsInvWeight X fun _ => (c : EReal) :=
  ⟨measurable_const, fun _ _ _ _ _ _ => rfl, c, fun _ _ => le_rfl⟩

theorem continuous_dmin (X : Data E r) (τ : X.Ψ) (i : Fin (r + 1)) :
    Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
  unfold dmin lminor
  refine Continuous.matrix_det (continuous_matrix fun a b => ?_)
  simp only [Matrix.submatrix_apply, gram, Matrix.of_apply, hermC, col, mat]
  fun_prop

theorem isInvWeight_log_norm (X : Data E r) (L : Wt X.Ψ r) (s : Frame X.Ψ r → ℂ)
    (hs : X.IsBddSec L s)
    (hinv : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      X.pnorm L s (lact γ (rmul x b)) = X.pnorm L s x) :
    IsInvWeight X fun x => ENNReal.log (ENNReal.ofReal (X.pnorm L s x ^ 2)) := by
  obtain ⟨hsec, C, hC⟩ := hs
  refine ⟨?_, fun γ hγ x hx b hb => by simp only [hinv γ hγ x hx b hb], (|C| + 1) ^ 2, fun x hx => ?_⟩
  · refine ENNReal.measurable_log.comp (ENNReal.measurable_ofReal.comp (Measurable.pow_const ?_ 2))
    unfold Data.pnorm
    refine Measurable.mul (hsec.1.continuousOn.restrict.measurable.norm) ?_
    refine Finset.measurable_prod _ fun τ _ => Finset.measurable_prod _ fun i _ => ?_
    refine Measurable.pow_const (Measurable.norm (Measurable.div ?_ ?_)) _ <;>
      exact ((continuous_dmin X τ _).comp continuous_subtype_val).measurable
  · have h0 : 0 ≤ X.pnorm L s x := by
      unfold Data.pnorm
      positivity
    have h1 : X.pnorm L s x ^ 2 ≤ (|C| + 1) ^ 2 := by
      have := hC x hx
      have := le_abs_self C
      gcongr
      linarith
    have h2 : 0 < (|C| + 1) ^ 2 := by positivity
    refine (ENNReal.log_monotone (ENNReal.ofReal_le_ofReal h1)).trans ?_
    rw [ENNReal.log_ofReal_of_pos h2]
    exact EReal.coe_le_coe_iff.2 ((Real.log_le_sub_one_of_pos h2).trans (by linarith))

def phi (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (z : V (nd X)) : ℝ :=
  -2 * Real.log (X.nfac la (cpt X x0 z))

def psi (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (u : Frame X.Ψ r → EReal)
    (z : V (nd X)) : EReal :=
  (phi X x0 la z : EReal) + u (cpt X x0 z)

def wsq (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (u : Frame X.Ψ r → EReal)
    (F : V (nd X) → ℂ) (z : V (nd X)) : ℝ≥0∞ :=
  ENNReal.ofReal (‖F z‖ ^ 2) * EReal.exp (-psi X x0 la u z)

def normSq (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) (la : Wt X.Ψ r) (u : Frame X.Ψ r → EReal)
    (F : V (nd X) → ℂ) : ℝ≥0∞ :=
  ∫⁻ z, wsq X x0 la u F z * ENNReal.ofReal (kaF X x0 bb z)⁻¹ ∂muF X x0

def ATilde (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) (la : Wt X.Ψ r) (u : Frame X.Ψ r → EReal) :
    Set (V (nd X) → ℂ) :=
  {F | DifferentiableOn ℂ F (OmF X x0) ∧ normSq X x0 bb la u F < ⊤}

theorem zero_mem_ATilde (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) (la : Wt X.Ψ r)
    (u : Frame X.Ψ r → EReal) : (fun _ => 0) ∈ ATilde X x0 bb la u :=
  ⟨differentiableOn_const 0, by simp [normSq, wsq]⟩

def IsFundSet (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) : Prop :=
  MeasurableSet FF ∧ FF ⊆ OmF X x0 ∧
  (∀ z ∈ FF, ∀ z' ∈ FF, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r,
    lact γ (cpt X x0 z) = rmul (cpt X x0 z') b → γ = 1) ∧
  ∀ᵐ z ∂muF X x0, ∃ γ ∈ X.Γ, ∃ z' ∈ FF, ∃ b ∈ Bor X.Ψ r,
    cpt X x0 z = lact γ (rmul (cpt X x0 z') b)

def fundSq (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (u : Frame X.Ψ r → EReal)
    (FF : Set (V (nd X))) (f : Frame X.Ψ r → ℂ) : ℝ≥0∞ :=
  ∫⁻ z in FF, wsq X x0 la u (fun w => f (cpt X x0 w)) z ∂muF X x0

def ASpace (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (u : Frame X.Ψ r → EReal)
    (FF : Set (V (nd X))) : Set (Frame X.Ψ r → ℂ) :=
  {f | f ∈ X.SS la ∧ fundSq X x0 la u FF f < ⊤}

def IsExt (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (F : V (nd X) → ℂ)
    (P : Frame X.Ψ r → ℂ) : Prop :=
  DifferentiableOn ℂ P X.dom ∧
  (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x) ∧
  ∀ z ∈ OmF X x0, P (cpt X x0 z) = F z

def rhoFrame (X : Data E r) (x0 x : Frame X.Ψ r) : ℝ :=
  ∑ τ, (-Real.log ‖dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ +
    Real.log (‖lminor ((mat x0 τ)⁻¹ * mat x τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ ^ 2))

def kappaFrame (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) (x : Frame X.Ψ r) : ℝ :=
  Real.exp (-bb * rhoFrame X x0 x)

def idFrame (X : Data E r) : Frame X.Ψ r := fun _ a b => if a = b then 1 else 0

def flagBall (X : Data E r) (ε : ℝ) (y : Frame X.Ψ r) : Set (Frame X.Ψ r) :=
  {y' | y' ∈ X.dom ∧ ∃ x, IsOrth X x ∧ (∃ b ∈ Bor X.Ψ r, y = rmul x b) ∧
    ∃ z : Frame X.Ψ r, ‖z‖ < ε ∧ y' = rmul x (idFrame X + z)}

def ballSup (X : Data E r) (ε : ℝ) (u : Frame X.Ψ r → EReal) (y : Frame X.Ψ r) : ℝ≥0∞ :=
  ⨆ y' ∈ flagBall X ε y, EReal.exp (u y') ^ (1 / 2 : ℝ)

def term (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (γ : X.Γ) (x : Frame X.Ψ r) : ℂ :=
  (X.χ la γ.1)⁻¹ * P (lact γ.1 x)

theorem poin_eq (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    poin X la P x = ∑' γ, term X la P γ x := rfl

def ConvergesNormally (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) : Prop :=
  ∀ K : Set (Frame X.Ψ r), IsCompact K → K ⊆ X.dom →
    ∃ M : X.Γ → ℝ, Summable M ∧ ∀ γ, ∀ x ∈ K, ‖term X la P γ x‖ ≤ M γ

def PoincareStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 →
  ∀ bb : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb → ∀ la : Wt X.Ψ r,
    (∀ u, IsInvWeight X u → ∀ F ∈ ATilde X x0 bb la u, ∃ P, IsExt X x0 la F P) ∧
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0, ∀ u, IsInvWeight X u → ∀ F ∈ ATilde X x0 bb la u,
      ∀ P, IsExt X x0 la F P → ∀ y ∈ X.dom,
        ENNReal.ofReal (X.pnorm la P y) ≤ C * normSq X x0 bb la u F ^ (1 / 2 : ℝ) *
          ENNReal.ofReal (Real.sqrt (kappaFrame X x0 bb y)) * ballSup X ε u y ∧
        ENNReal.ofReal (X.pnorm la (poin X la P) y) ≤
          C * normSq X x0 bb la u F ^ (1 / 2 : ℝ) * ballSup X ε u y) ∧
    ∀ u, IsInvWeight X u → ∀ F ∈ ATilde X x0 bb la u, ∀ P, IsExt X x0 la F P →
      ConvergesNormally X la P ∧ X.IsBddSec la (poin X la P) ∧
      (∀ FF, IsFundSet X x0 FF → fundSq X x0 la u FF (poin X la P) < ⊤) ∧
      ∀ (la' : Wt X.Ψ r) (g : Frame X.Ψ r → ℂ), X.IsSec la' g →
        ConvergesNormally X (la' + la) (g * P) ∧
        ∀ x ∈ X.dom, poin X (la' + la) (g * P) x = g x * poin X la P x

def CuspidalStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r), GapsNonneg X la →
    (∀ (h0 : 0 < X.p0) (h1 : X.p0 < r), ∃ τ : X.Ψ, 0 < pairing X h0 h1 la τ) →
    ∀ P, X.IsBddSec la P → P ∈ X.SS la

def PoincareCuspidalStatement (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  PoincareStatement (E := E) ∧ CuspidalStatement (E := E)

theorem poin_mem_ASpace (h : PoincareCuspidalStatement E) (X : Data E r) (x0 : Frame X.Ψ r)
    (hx0 : IsOrth X x0) (bb : ℝ) (hb : 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb) (la : Wt X.Ψ r)
    (hg : GapsNonneg X la)
    (hp : ∀ (h0 : 0 < X.p0) (h1 : X.p0 < r), ∃ τ : X.Ψ, 0 < pairing X h0 h1 la τ)
    (u : Frame X.Ψ r → EReal) (hu : IsInvWeight X u) (F : V (nd X) → ℂ)
    (hF : F ∈ ATilde X x0 bb la u) (P : Frame X.Ψ r → ℂ) (hP : IsExt X x0 la F P)
    (FF : Set (V (nd X))) (hFF : IsFundSet X x0 FF) : poin X la P ∈ ASpace X x0 la u FF := by
  obtain ⟨-, hb', hs, -⟩ := (h.1 r X x0 hx0 bb hb la).2.2 u hu F hF P hP
  exact ⟨h.2 r X la hg hp _ hb', hs FF hFF⟩

end

end GlobalTheory.IndefiniteRowSideFullHecke.FundamentalSetFrames
