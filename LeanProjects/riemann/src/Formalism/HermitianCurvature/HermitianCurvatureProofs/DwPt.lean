import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopDensNonnegOfKappa
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SignedCoordinateEqSignSmul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QNFAsm

open Matrix MeasureTheory Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.DiagonalScalarMatrices

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

private lemma scalar_pow_mul_diagonal {A S : Type} [Ring A] [Fintype S] [DecidableEq S] (a : A) (n : ℕ)
    (D : Ix S → A) :
    (Matrix.scalar (Ix S) a) ^ n * Matrix.diagonal D = Matrix.diagonal (fun e => a ^ n * D e) := by
  rw [← map_pow, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal]

theorem dw_pt (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (hD : IsData P z z' π π' X μ L st l0) (ws : List (Letter ℂ S)) (hw : WordOK P z z' π π' st l0 ws)
    (Y₀ : ℝ) (e : Ix S) (p : Polynomial ℂ)
    (hp : ∀ ρ : M.Ty P, p.eval (M.xC P ρ (Y₀ : ℂ)) = Fr.cs (M.x0 P l0 ρ) (M.qC P) ws e)
    (y : Ix S → RadSp P.k P.r z z' π π') (c : Fin P.r → ℂ) (g : Mx P.k P.r) (hx : (c, g) ∈ DomR P.k P.r z z')
    (Bs : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ) (hBs : IsFrameOf P.k P.r [g⁻¹ *ᵥ z, z'] Bs) (v : Wq) :
    (act ((Fr.ofWord L st ws).d L) y e : Fn P.k P.r (Wq →L[ℂ] Wp)) c g v =
      (((Complex.normSq (zetaL P.k P.r z z' (Fin.last P.r) g) * (GGl P.k P.r z z' g)⁻¹ : ℝ) : ℂ) ^ ws.length) •
        (y e : Fn P.k P.r (Wq →L[ℂ] Wp)) c g
          (Polynomial.aeval (qdet (Qr.EB π' Bs) ((Y₀ : ℂ) + ((P.k : ℂ) - 2) / 2)) p v) := by
  have hD' := hD
  obtain ⟨hPl, -, hAL, hQQ, hq, -, -, hLS⟩ := hD'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGG, hGGi, -⟩ := id hAL
  obtain ⟨κ, hκx, hκxi, -⟩ := Formalism.FourierDecayAlt.P5.xKappaOfNF Formalism.FourierDecayAlt.P.normal_form_actual
    Formalism.FourierDecayAlt.P5.kappaFibrePos Wp Wq P z z' π π' X μ L st l0 hD
  let st' : Fr.Start (Pr (RadSp P.k P.r z z' π π')) :=
    { st with xi := fun Y => κ fun ρ => (M.x0 P l0 ρ Y)⁻¹ }
  have hxiw : ∀ l ∈ ws, st'.xi (l.pt + 1) = st.xi (l.pt + 1) ∧ st'.xi (l.pt - 1) = st.xi (l.pt - 1) := by
    intro l hl
    obtain ⟨-, h1, h2, -⟩ := hw.1.2.2.1 l hl
    exact ⟨(hκxi _ h1).symm, (hκxi _ h2).symm⟩
  have hc : (Fr.ofWord L st ws).c =
      Matrix.diagonal fun e => κ fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) ws e := by
    rw [← Formalism.FourierDecayAlt.P5.WordTransvectionCongruences.ofWord_c_congr L st st' rfl rfl ws hxiw,
      (Formalism.FourierDecayAlt.P.c_diagonal _ S P.r L st' (M.Ty P) κ (M.x0 P l0) (fun Y => hκx Y) (fun Y => rfl) ws).2.2,
      ← hq]
  have hd : (Fr.ofWord L st ws).d L = Matrix.diagonal (fun e => (L.ζ * L.ζb * L.GGi) ^ ws.length *
      κ (fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) ws e)) := by
    rw [Fr.FrameData.d, Formalism.FourierDecayAlt.P5.WordTransvectionCongruences.ofWord_N, hc]
    exact scalar_pow_mul_diagonal _ _ _
  set K := κ (fun ρ => M.xC P ρ (Y₀ : ℂ)) with hKdef
  have hs : M.sgn P l0 ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hK : K.1 = X.fn 5 * X.t (Y₀ : ℂ) 1 1 := by
    have t := hLS.tau (Y₀ : ℂ)
    rw [hQQ, hκx, Formalism.FourierDecayAlt.P5.signed_coordinate_eq_sign_smul, map_smul] at t
    have t1 := congrArg (Formalism.FourierDecayAlt.P5.Kfp.fstAlg _) t
    rw [map_mul, map_smul, Matrix.smul_apply, map_smul] at t1
    change M.sgn P l0 • X.t (Y₀ : ℂ) 1 1 = L.GG.1 * (M.sgn P l0 • K.1) at t1
    rw [hGG, mul_smul_comm] at t1
    have h4 : X.fn 4 * K.1 = X.t (Y₀ : ℂ) 1 1 := (smul_right_injective _ hs t1).symm
    have h54 : X.fn 5 * X.fn 4 = 1 := by
      have := congrArg Prod.fst L.GGi_GG
      rw [hGGi, hGG] at this
      exact this
    rw [← h4, ← mul_assoc, h54, one_mul]
  have hκf : κ (fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) ws e) = Polynomial.aeval K p :=
    Formalism.FourierDecayAlt.P5.Kfp.kappa_aeval (NFData.mk L κ (fun _ => 0)) (Y₀ : ℂ) p _ hp
  have hκf1 : (κ (fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) ws e)).1 = Polynomial.aeval K.1 p := by
    rw [hκf]
    exact (Polynomial.aeval_algHom_apply (Formalism.FourierDecayAlt.P5.Kfp.fstAlg _) K p).symm
  have hT : ∀ (Ψ : RadSp P.k P.r z z' π π') (w : Wq),
      ((K.1 Ψ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) c g w =
        (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g (qdet (Qr.EB π' Bs) ((Y₀ : ℂ) + ((P.k : ℂ) - 2) / 2) w) := by
    intro Ψ w
    rw [hK]
    exact Formalism.FourierDecayAlt.P5.Kfp.diagonal_transfer_action X hPl.2.1 hPl.2.2.1 hPl.2.2.2.2.2.2.2.1 hPl.2.2.2.2.2.2.2.2.1 hx Bs hBs _ Ψ w
  have hA := Formalism.FourierDecayAlt.P5.Kfp.aeval_act K.1 _ hT p
  have hpow := Formalism.FourierDecayAlt.P5.WordTransvectionCongruences.pow_apply X L hAL ws.length
    ((κ (fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) ws e)).1 (y e)) (c, g) hx
  have hmul : ∀ a b : Pr (RadSp P.k P.r z z' π π'), (a * b).1 = a.1 * b.1 := fun _ _ => rfl
  rw [hd, Formalism.FourierDecayAlt.P5.WordTransvectionCongruences.act_diagonal, hmul, Module.End.mul_apply, hpow,
    _root_.smul_apply, hκf1, hA]
  congr 1
  simp only [fnVal]
  congr 1
  rw [Complex.ofReal_mul, Complex.ofReal_inv, ← Complex.mul_conj]
  rfl

end

end Formalism.FourierDecayAlt.P.DiagonalScalarMatrices
