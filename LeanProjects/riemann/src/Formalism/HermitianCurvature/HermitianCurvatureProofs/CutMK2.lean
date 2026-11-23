import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftFubiniNormalizedTower
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartCoefficientHasCompactSupport

noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMK

def HB {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (b b' : U.RC k p ρ → ℝ) (β : (Fin p → Fin p → ℂ) → ℝ)
    (Φ : (Fin p → Fin p → ℂ) → Mt k ρ → (Wq →L[ℂ] Wp)) : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp) :=
  PBI.chartCoefficient b b' (fun Z' y' => ((β Z' : ℝ) : ℂ) • Φ Z' y')

def kapL {k p ρ : ℕ} (z : Fin (2 * ρ + k + 1) → ℂ) (b : U.RC k p ρ → ℝ) : ℂ :=
  ∫ x, (b x : ℂ) * psi k (p + ρ) (liftVec k p ρ z) cStd (U.Rn k p ρ x) ∂(U.muRC k p ρ)

def kapR {k p ρ : ℕ} (z' : Fin (2 * ρ + k + 1) → ℂ) (b' : U.RC k p ρ → ℝ) : ℂ :=
  ∫ x, (b' x : ℂ) * star (psi k (p + ρ) (liftVec k p ρ z') cStd (U.Rn k p ρ x)) ∂(U.muRC k p ρ)

def RightAvg : Prop :=
  ∀ (k p ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq], ρ = 0 →
    ∀ (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq),
    B0.z' = liftVec k p ρ Bj.z' → (∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y)) →
    Bj.μW' Set.univ = 1 → B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl) →
    Bj.μN = D.muN k ρ → B0.μN = D.muN k (p + ρ) →
    ∀ (b b' : U.RC k p ρ → ℝ) (β : (Fin p → Fin p → ℂ) → ℝ) (Φ : (Fin p → Fin p → ℂ) → Mt k ρ → (Wq →L[ℂ] Wp)),
    Continuous b' → HasCompactSupport b' →
    ∀ Z : Fin p → Fin p → ℂ, (Matrix.of Z).det ≠ 0 →
    Integrable (fun v : G.UT p → ℂ => β (Matrix.of.symm (Matrix.of Z * G.upper v))) →
    ∫ v : G.UT p → ℂ, β (Matrix.of.symm (Matrix.of Z * G.upper v)) = 1 →
    ∀ y : Mt k ρ, (Matrix.of y : B.Mat k ρ) ∈ B.GV k ρ →
    (∀ h1 ∈ UWset k ρ Bj.z, ∀ h2 ∈ UWset k ρ Bj.z',
      Φ Z (Matrix.of.symm (h1 * Matrix.of y * h2)) = (Bj.π h1).comp ((Φ Z y).comp (Bj.π' h2))) →
    (∀ (u : G.UT p → ℂ) (y' : Mt k ρ), (Matrix.of y' : B.Mat k ρ) ∈ B.GV k ρ →
      Φ (Matrix.of.symm (Matrix.of Z * G.upper u)) y' =
        psi k (p + ρ) (liftVec k p ρ Bj.z') cStd (U.muP k p ρ (G.upper u)) • Φ Z y') →
    ∀ h ∈ UWset k ρ Bj.z, ∀ a : U.RC k p ρ,
      PBG.Kr B0 (HB b b' β Φ) (U.Rn k p ρ (-a) * U.embG k p ρ h⁻¹ * U.mMap k p ρ (Matrix.of Z) (Matrix.of y)) =
        (((b a : ℝ) : ℂ) * kapR Bj.z' b') • (Bj.π h⁻¹).comp (Φ Z y)

def LeftAvg : Prop :=
  ∀ (k p ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq], ρ = 0 →
    ∀ (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq),
    Bj.μW Set.univ = 1 → Bj.μN = D.muN k ρ →
    ∀ (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp)) (g : B.Mat k (p + ρ)) (b : U.RC k p ρ → ℝ) (c : ℂ)
      (A : Wq →L[ℂ] Wp), Continuous b → HasCompactSupport b →
    (∀ h ∈ UWset k ρ Bj.z, ∀ a : U.RC k p ρ,
      PBG.Kr B0 H (U.Rn k p ρ (-a) * U.embG k p ρ h⁻¹ * g) = (((b a : ℝ) : ℂ) * c) • (Bj.π h⁻¹).comp A) →
    PBQ.pbF Bj B0 rfl H g = (kapL Bj.z b * c) • A

def CoreN : Prop :=
  ∀ (k p ρ n : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (e : p + ρ = n), ρ = 0 →
    ∀ (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq),
    D.castV e (liftVec k p ρ Bj.z') = B0.z' → (∀ y : B.Mat k ρ, Bj.π' y = B0.π' (D.castM e (ιLev k p ρ y))) →
    Bj.μW Set.univ = 1 → Bj.μW' Set.univ = 1 → B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ e) →
    Bj.μN = D.muN k ρ → B0.μN = D.muN k n →
    ∀ (b b' : U.RC k p ρ → ℝ) (β : (Fin p → Fin p → ℂ) → ℝ) (Φ : (Fin p → Fin p → ℂ) → Mt k ρ → (Wq →L[ℂ] Wp)),
    Continuous b → HasCompactSupport b → Continuous b' → HasCompactSupport b' →
    ∀ Z : Fin p → Fin p → ℂ, (Matrix.of Z).det ≠ 0 →
    Integrable (fun v : G.UT p → ℂ => β (Matrix.of.symm (Matrix.of Z * G.upper v))) →
    ∫ v : G.UT p → ℂ, β (Matrix.of.symm (Matrix.of Z * G.upper v)) = 1 →
    ∀ y : Mt k ρ, (Matrix.of y : B.Mat k ρ) ∈ B.GV k ρ →
    (∀ h1 ∈ UWset k ρ Bj.z, ∀ h2 ∈ UWset k ρ Bj.z',
      Φ Z (Matrix.of.symm (h1 * Matrix.of y * h2)) = (Bj.π h1).comp ((Φ Z y).comp (Bj.π' h2))) →
    (∀ (u : G.UT p → ℂ) (y' : Mt k ρ), (Matrix.of y' : B.Mat k ρ) ∈ B.GV k ρ →
      Φ (Matrix.of.symm (Matrix.of Z * G.upper u)) y' =
        psi k (p + ρ) (liftVec k p ρ Bj.z') cStd (U.muP k p ρ (G.upper u)) • Φ Z y') →
    PBQ.pbF Bj B0 e (D.castF e.symm (HB b b' β Φ)) (D.castM e (U.mMap k p ρ (Matrix.of Z) (Matrix.of y))) =
      (kapL Bj.z b * kapR Bj.z' b') • Φ Z y

def TopMk : Prop := CoreN → CutEX.MkTop

section assembly

theorem coreRfl (hR : RightAvg) (hL : LeftAvg) (k p ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] (hρ : ρ = 0) (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq)
    (hz' : B0.z' = liftVec k p ρ Bj.z') (hπ' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y))
    (hW : Bj.μW Set.univ = 1) (hW' : Bj.μW' Set.univ = 1)
    (hW0' : B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl))
    (hNj : Bj.μN = D.muN k ρ) (hN0 : B0.μN = D.muN k (p + ρ))
    (b b' : U.RC k p ρ → ℝ) (β : (Fin p → Fin p → ℂ) → ℝ) (Φ : (Fin p → Fin p → ℂ) → Mt k ρ → (Wq →L[ℂ] Wp))
    (hb : Continuous b) (hbc : HasCompactSupport b) (hb' : Continuous b') (hbc' : HasCompactSupport b')
    (Z : Fin p → Fin p → ℂ) (hZ : (Matrix.of Z).det ≠ 0)
    (hβi : Integrable (fun v : G.UT p → ℂ => β (Matrix.of.symm (Matrix.of Z * G.upper v))))
    (hβ1 : ∫ v : G.UT p → ℂ, β (Matrix.of.symm (Matrix.of Z * G.upper v)) = 1)
    (y : Mt k ρ) (hy : (Matrix.of y : B.Mat k ρ) ∈ B.GV k ρ)
    (hΦL : ∀ h1 ∈ UWset k ρ Bj.z, ∀ h2 ∈ UWset k ρ Bj.z',
      Φ Z (Matrix.of.symm (h1 * Matrix.of y * h2)) = (Bj.π h1).comp ((Φ Z y).comp (Bj.π' h2)))
    (hΦU : ∀ (u : G.UT p → ℂ) (y' : Mt k ρ), (Matrix.of y' : B.Mat k ρ) ∈ B.GV k ρ →
      Φ (Matrix.of.symm (Matrix.of Z * G.upper u)) y' =
        psi k (p + ρ) (liftVec k p ρ Bj.z') cStd (U.muP k p ρ (G.upper u)) • Φ Z y') :
    PBQ.pbF Bj B0 rfl (HB b b' β Φ) (U.mMap k p ρ (Matrix.of Z) (Matrix.of y)) =
      (kapL Bj.z b * kapR Bj.z' b') • Φ Z y := hL k p ρ Wp Wq hρ Bj B0 hW hNj (HB b b' β Φ) (U.mMap k p ρ (Matrix.of Z) (Matrix.of y)) b
    (kapR Bj.z' b') (Φ Z y) hb hbc
    (fun h hh a => hR k p ρ Wp Wq hρ Bj B0 hz' hπ' hW' hW0' hNj hN0 b b' β Φ hb' hbc' Z hZ hβi hβ1 y hy
      hΦL hΦU h hh a)

private theorem embG_eq_ιLev (k p ρ : ℕ) (g : B.Mat k ρ) : U.embG k p ρ g = ιLev k p ρ g := by
  ext i j
  obtain ⟨x, rfl⟩ := (U.eB k p ρ).surjective i
  obtain ⟨w, rfl⟩ := (U.eB k p ρ).surjective j
  simp only [U.embG, U.blk3, ιLev, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases x with (a | a) | a <;> rcases w with (c | c) | c <;>
    simp [U.eB, Matrix.fromBlocks, Matrix.fromRows, Matrix.fromCols, Matrix.one_apply, Fin.ext_iff,
      Sum.elim] <;> split_ifs <;> (try simp_all [Fin.ext_iff]) <;> (try omega)

theorem coreN_of (hR : RightAvg) (hL : LeftAvg) : CoreN := by
  intro k p ρ n Wp Wq _ _ _ _ _ _ e hρ Bj B0 hz' hπ' hW hW' hW0' hNj hN0 b b' β Φ hb hbc hb' hbc' Z hZ hβi hβ1 y hy
    hΦL hΦU
  subst e
  rw [Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl] at hz'
  have hπ'' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y) := fun y => by
    rw [hπ' y, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, Formalism.FourierDecayAlt.P.Dx2.Tower.lev_eq_embG]
  have hF : D.castF (rfl : p + ρ = p + ρ).symm (HB b b' β Φ) = HB b b' β Φ := funext fun x => by
    simp only [D.castF, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  rw [hF, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  exact coreRfl hR hL k p ρ Wp Wq hρ Bj B0 hz'.symm hπ'' hW hW' hW0' hNj hN0 b b' β Φ hb hbc hb' hbc' Z hZ hβi hβ1
    y hy hΦL hΦU

theorem mkTop_of_leaves (hR : RightAvg) (hL : LeftAvg) (hT : TopMk) : CutEX.MkTop := hT (coreN_of hR hL)

end assembly

end Formalism.FourierDecayAlt.P.CutMK
