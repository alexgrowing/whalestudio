import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpBig
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpOrbOfAmpDD

open MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.S.Pv.LemmaJ

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.Bridge Formalism.MainNotions.S.ThB

def AmpNZCoef : Prop :=
  ∀ Cg cb Cu cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl → ∀ (D : D7) (large₂ : SizeData₂ D),
    Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
    ∀ τ w w', HypTT D w w' → ∀ θ (W : LocW D.R.k D.R.rS) (hW : GoodW D τ w w' θ W)
      (A : LocS W) (hA : GoodS D (lamD D τ) A) (hT : 0 < Tr D w) (hT' : 0 < Tr D w'),
    ∀ μsec, IsSection D.R.k D.R.rS W.z W.z' μsec →
      ∃ f : MatKR D.R.k D.R.rS →
          ((toBessel D τ w w' θ W (lamD D τ) A hW hA hT hT').Wq →L[ℂ] (toBessel D τ w w' θ W (lamD D τ) A hW hA hT hT').Wp),
        OrbEq D hW hA hT hT' f ∧ jNorm2 (toBessel D τ w w' θ W (lamD D τ) A hW hA hT hT') f μsec ≠ 0

theorem ampNZ_of (h : AmpNZCoef) : AmpNZ := by
  intro Cg cb Cu cT CT C0
  obtain ⟨A1, B1, h'⟩ := h Cg cb Cu cT CT C0
  refine ⟨A1, B1, fun C' Cl hC' hCl D large₂ hH τ w w' hTT θ W hW A hA hT hT' μsec hsec => ?_⟩
  obtain ⟨f, hOrb, hne⟩ := h' C' Cl hC' hCl D large₂ hH τ w w' hTT θ W hW A hA hT hT' μsec hsec
  rw [← big_cell_eq D τ w w' θ W hW (lamD D τ) A hA hT hT' f hOrb μsec hsec]
  exact hne

def BetaPosKF : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (w0 : L.Hs) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq),
    Formalism.MainNotions.S.Pv.AmpDD.OnePlaceKF L h μG w0 l l' →
    ∀ v v' : L.Hs, PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v → PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v' →
    ∀ (ξ : L.Wp) (ξ' : L.Wq), ⟪l v, ξ⟫_ℂ ≠ 0 → ⟪ξ', l' v'⟫_ℂ ≠ 0 →
    ∀ μsec, IsSection k r L.z L.z' μsec → jNorm2 L (Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' ξ ξ') μsec ≠ 0

end Formalism.MainNotions.S.Pv.LemmaJ
