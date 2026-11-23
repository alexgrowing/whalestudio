import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopOrthEmb
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepEqTwoThetaColumnLifts
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsPreserveThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.ChiGrid GlobalTheory.Unf GlobalTheory.FunObj GlobalTheory.RowUnf GlobalTheory.RowChain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChain

theorem dbl_hand_of_chars {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T)
    {M : GlobalTheory.FunObj.Vol G} (hM : M.Is t) (σ j : ℕ) (hj : j + 2 * (σ + 1) + 2 = D.R.m) (χz : (AE D)ˣ →* Circle)
    (hz : IsHeckeChar D χz) (hzr : ResEta D χz 1)
    (e1 : G.chrS (.mu t D.R.m j) = G.chrS (.top t j) * χz) (e2 : G.chrT (.mu t D.R.m j) = G.chrT (.top t j))
    (e3 : G.chrS (.mu t D.R.m (j + 1)) = G.chrS (.top t (j + 1)))
    (e4 : G.chrT (.mu t D.R.m (j + 1)) = G.chrT (.top t (j + 1)) * χz) : ∀ (vN : VolN (besDecAt G j (σ + 1) hj))
    (Φ₁ : WO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) → ℂ)
    (Φ₂ : WO (G.V (.grid D.R.m (j + 1))) (G.V (.grid D.R.m (j + 1 + 1))) → ℂ) (φ : GA D (G.V (.top j)) → ℂ),
    IsThetaFunO Wl.ψ _ _ Φ₁ → IsThetaFunO Wl.ψ _ _ Φ₂ → IsContAut (G.V (.top j)) φ →
    ∀ (g : GA D (G.V (.grid D.R.m j))) (h₁ : GA D (G.V (.grid D.R.m (j + 1)))) (h₂ : GA D (G.V (.grid D.R.m (j + 1 + 1)))),
      Chain.hand (stepAt G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)))
        (stepAt G Wl t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)) (besDecAt G (j + 1 + 1) σ (by omega)))
        (linkAt hM j σ hj vN (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some) ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some)
        (B := besAt G hM j (σ + 1) hj vN) (J := jacAt G hM (j + 1) (σ + 1) (by omega))
        (B' := besAt G hM (j + 1 + 1) σ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
        Φ₁ Φ₂ φ g h₁ h₂ =
      GlobalTheory.SeeSaw.biLift (Wl.om (.top t j)) (Wl.om (.top t (j + 1)))
        (volAt hM (.top j) (by show j ≤ D.R.m; omega)) (volAt hM (.top (j + 1)) (by show j + 1 ≤ D.R.m; omega)) φ
        (contr (linkAt hM j σ hj vN (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some) (G.V (.top (j + 1)))
          ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some)
          (flatBF (B := besAt G hM j (σ + 1) hj vN) (J := jacAt G hM (j + 1) (σ + 1) (by omega))
            (stepAt G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)))
            ((stepAt G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))).om
              (g, h₁) Φ₁))
          (flatFB (J := jacAt G hM (j + 1) (σ + 1) (by omega))
            (B := besAt G hM (j + 1 + 1) σ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
            (stepAt G Wl t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
              (besDecAt G (j + 1 + 1) σ (by omega)))
            ((stepAt G Wl t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
              (besDecAt G (j + 1 + 1) σ (by omega))).om (h₁, h₂) Φ₂))) := by
  intro vN Φ₁ Φ₂ φ hΦ₁ hΦ₂ hφ g h₁ h₂
  have rA : Pair.InRange D.R.m (.top t j) := by
    simp [Pair.InRange, Pair.big, Node.InRange]; omega
  have rB : Pair.InRange D.R.m (.top t (j + 1)) := by
    simp [Pair.InRange, Pair.big, Node.InRange]; omega
  have hA := Wl.om_is (.top t j) rA
  have hB := Wl.om_is (.top t (j + 1)) rB
  have hoa : IsWeilDatumO Wl.ψ (G.V (.top j)) (G.V (.top (j + 1))) (G.chrS (.top t j)) (G.chrT (.mu t D.R.m j))
      (Wl.om (.top t j)) := e2 ▸ hA
  have hob : IsWeilDatumO Wl.ψ (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) (G.chrS (.mu t D.R.m (j + 1)))
      (G.chrT (.top t (j + 1))) (Wl.om (.top t (j + 1))) := e3 ▸ hB
  obtain ⟨omz, hoz⟩ := GlobalTheory.WeilDatumExistence.weilDatumExists D (GlobalTheory.SeeSaw.Model.nLine D) (G.V (.top (j + 1))) Wl.ψ χz
    (G.chrT (.mu t D.R.m j)) Wl.ψ_std hz hoa.hecT hzr hoa.resT
  obtain ⟨omz', hoz'⟩ := GlobalTheory.WeilDatumExistence.weilDatumExists D (G.V (.top (j + 1))) (GlobalTheory.SeeSaw.Model.nLine D) Wl.ψ
    (G.chrS (.mu t D.R.m (j + 1))) χz Wl.ψ_std hob.hecS hz hob.resS hzr
  have hth := GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) Wl.ψ
  let B := besAt G hM j (σ + 1) hj vN
  let J := jacAt G hM (j + 1) (σ + 1) (by omega)
  let B' := besAt G hM (j + 1 + 1) σ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN (besDecAt G (j + 1 + 1) σ (by omega))).some
  let s₁ : StepBF Wl.ψ B J :=
    stepAt G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
  let s₂ : StepFB Wl.ψ J B' :=
    stepAt G Wl t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)) (besDecAt G (j + 1 + 1) σ (by omega))
  have hΞ₁ : IsThetaFunO Wl.ψ B.V₀ J.W₀ (flatBF s₁ (s₁.om (g, h₁) Φ₁)) :=
    hth.1 (σ + 1) B J s₁ _ (s₁.weil.om_pres (g, h₁) Φ₁ hΦ₁)
  have hΞ₂ : IsThetaFunO Wl.ψ J.W₀ B'.V₀ (flatFB s₂ (s₂.om (h₁, h₂) Φ₂)) :=
    hth.2 σ J B' s₂ _ (s₂.weil.om_pres (h₁, h₂) Φ₂ hΦ₂)
  funext h₂'
  exact (GlobalTheory.Unf.Contr.contrLaw D Wl.ψ σ B J B' s₁ s₂ (linkAt hM j σ hj vN (by omega) _)
    ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some) (G.chrS (.top t j)) (G.chrT (.top t (j + 1))) χz
    (Wl.om (.top t j)) omz (Wl.om (.top t (j + 1))) omz' e1 e4 hoa hoz hob hoz' φ _ _ hφ hΞ₁ hΞ₂).2.2 h₂'

end GlobalTheory.RowChain
