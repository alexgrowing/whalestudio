import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimET

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def levelZeroRadialIntegral (p : KB.Pl P Wp Wq) (w : List C.Letter) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (q : (Fin P.r → ℂ) × ℂ) : ℂ :=
  (bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') q : ℂ) *
    inner ℂ (B.hsVec (B.JF p.T.base H (bigCell P.k P.r q.1 (p.T.base.μsec q.2))))
      (B.hsVec (B.JF p.T.base (w.foldr (fun a G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G) H)
        (bigCell P.k P.r q.1 (p.T.base.μsec q.2))))

theorem residual_pairing_eq_integral (p : KB.Pl P Wp Wq) {H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hH : B.CkOn ⊤ (B.GV P.k P.r) H)
    {w : List C.Letter} (hw : KB.CutWord P p.l0 w) : p.RR H 0 w [] [] = ∫ q, levelZeroRadialIntegral p w H q := by
  unfold KB.Pl.RR
  rw [Formalism.FourierDecayAlt.P.level_zero_holds _ _ _ _ _ _ _ _ _ _ _ hH (good_positioned_of_cut hw)]
  rfl

def PtwCut (p : KB.Pl P Wp Wq) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) : Prop :=
  ∀ᵐ q : (Fin P.r → ℂ) × ℂ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), levelZeroRadialIntegral p w (D.cutF p.T.base χ F ε) q = levelZeroRadialIntegral p w F q

def DomCut (p : KB.Pl P Wp Wq) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) : Prop :=
  (∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (levelZeroRadialIntegral p w (D.cutF p.T.base χ F ε)) volume) ∧
  ∃ h : (Fin P.r → ℂ) × ℂ → ℝ, Integrable h ∧
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ q : (Fin P.r → ℂ) × ℂ, ‖levelZeroRadialIntegral p w (D.cutF p.T.base χ F ε) q‖ ≤ h q

theorem limEvT_of_cut (p : KB.Pl P Wp Wq) {χ : ℝ → ℝ} (hχ : C6.IsCut0 χ) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hF : B.CkOn ⊤ (B.GV P.k P.r) F) (Y : Finset ℝ) (N : ℕ)
    (hP : ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → PtwCut p χ F w)
    (hD : ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → DomCut p χ F w) : LimEvT p χ F Y N := by
  intro w hw hN
  have e : (fun ε : ℝ => (p.RR (D.cutF p.T.base χ F ε) 0 w [] []).re) =
      fun ε => (∫ q, levelZeroRadialIntegral p w (D.cutF p.T.base χ F ε) q).re :=
    funext fun ε => by rw [residual_pairing_eq_integral p (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hχ hF ε) hw.1]
  rw [e, residual_pairing_eq_integral p hF hw.1]
  obtain ⟨hmeas, h, hint, hb⟩ := hD w hw hN
  have hlim : ∀ᵐ q : (Fin P.r → ℂ) × ℂ, Tendsto (fun ε : ℝ => levelZeroRadialIntegral p w (D.cutF p.T.base χ F ε) q) (𝓝[>] 0)
      (𝓝 (levelZeroRadialIntegral p w F q)) := by
    filter_upwards [hP w hw hN] with q hq
    exact tendsto_const_nhds.congr' (hq.mono fun ε h => h.symm)
  exact (Complex.continuous_re.tendsto _).comp
    (tendsto_integral_filter_of_dominated_convergence h hmeas hb hint hlim)

end place

end

end Formalism.FourierDecayAlt.P.CutBP
