import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocOfSmoothOnH
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VLetZeroNear
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralIdentities

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PartialBesselProperness

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section auxC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k n : ℕ}

theorem isOpen_dminNe (z z' : Fin (2 * n + k + 1) → ℂ) (i : ℕ) (hi : i ≤ n) :
    IsOpen {g : Q.Mx k n | Dmin k n z z' g ⟨i, by omega⟩ ≠ 0} :=
  isOpen_ne_fun (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin z z' ⟨i, by omega⟩).continuous continuous_const

theorem uwG_locSupp {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * n + k + 1) → ℂ) (i : ℕ)
    (hi : i ≤ n) {H : B.Mat k n → E} {Cs : Set (B.Mat k n)} (hCs : IsClosed Cs)
    (hL : ∀ g ∈ B.GV k n, Dmin k n z z' g ⟨i, by omega⟩ ≠ 0 → CapelliWordSumExpansion.Loc ⊤ H g)
    (hS : ∀ g ∈ B.GV k n, g ∉ Cs → H g = 0) :
    ∀ (w : List C.Letter) (ew : Wd.Ix (Fin w.length)),
      (∀ g ∈ B.GV k n, Dmin k n z z' g ⟨i, by omega⟩ ≠ 0 → CapelliWordSumExpansion.Loc ⊤ (D.uwG k n z z' H i hi w ew) g) ∧
        ∀ g ∈ B.GV k n, g ∉ Cs → D.uwG k n z z' H i hi w ew g = 0 := by
  set Dm : Set (Q.Mx k n) := {g | Dmin k n z z' g ⟨i, by omega⟩ ≠ 0} with hDm
  have hDo : IsOpen Dm := isOpen_dminNe z z' i hi
  have hH : Q.SmoothLev k n 0 Dm H := by
    intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hE⟩ := hL g₀ hg₀.1.1 hg₀.2
    exact ⟨U, F, hU, hgU, hF, fun g hg hgl => hE g hg hgl.1⟩
  have hSm : ∀ (w : List C.Letter) (ew : Wd.Ix (Fin w.length)),
      Q.SmoothLev k n 0 Dm (D.uwG k n z z' H i hi w ew) := by
    intro w
    induction w with
    | nil => intro ew; exact hH
    | cons l w ih =>
      intro ew
      exact Formalism.FourierDecayAlt.P.SingleEntryHermitianProducts.smooth_vLet z z' i hi l _ hDo (ih _) (fun g hg => hg)
  have hSu : ∀ (w : List C.Letter) (ew : Wd.Ix (Fin w.length)),
      ∀ g ∈ B.GV k n, g ∉ Cs → D.uwG k n z z' H i hi w ew g = 0 := by
    intro w
    induction w with
    | nil => intro ew; exact hS
    | cons l w ih =>
      intro ew g hg hgC
      exact Formalism.FourierDecayAlt.P.PBG.vLet_zero_near z z' i hi l _ _ hCs.isOpen_compl (fun x hx hxG => ih _ x hxG hx) g hgC hg
  intro w ew
  refine ⟨fun g hg hd => ?_, hSu w ew⟩
  obtain ⟨U, F, hU, hgU, hF, hE⟩ := hSm w ew g ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hg, hd⟩
  exact ⟨U, F, hU, hgU, hF, fun x hx hxG => hE x hx (Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hxG)⟩

end auxC

end Formalism.FourierDecayAlt.P.PartialBesselProperness
