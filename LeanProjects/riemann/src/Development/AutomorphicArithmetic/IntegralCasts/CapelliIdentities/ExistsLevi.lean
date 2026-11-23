import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
import Formalism.SatakeDualWeyl.Statement
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HermitianBlockTriangular
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HermitianBlockDiagonal
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HermitianProjectionEq

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
private theorem sigma_sq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨_, _, _, hs⟩ := h
  let t : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  apply t.injective
  rw [hs, hs, star_star]

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
private theorem sigR_sq {F E : Type} [Field F] [Field E] [Algebra F E] (A : Type) [CommRing A] [Algebra F A]
    {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) (x : TensorProduct F A E) :
    sigR A σ (sigR A σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, h]
  | add a b ha hb => simp [ha, hb]

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
private theorem sigR_incl {F E : Type} [Field F] [Field E] [Algebra F E] (A : Type) [CommRing A] [Algebra F A]
    (σ : E →ₐ[F] E) (e : E) : sigR A σ (inclR A e) = inclR A (σ e) := by
  simp [sigR, inclR]

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
private theorem dual_map {F E : Type} [Field F] [Field E] [Algebra F E] (A : Type) [CommRing A] [Algebra F A]
    (σ : E →ₐ[F] E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin r) E) :
    (Formalism.UG.cT (↑σ : E →+* E) X * J).map (inclR A) =
      ((X.map (inclR A)).map (sigR A σ)).transpose * JR A J := by
  rw [Matrix.map_mul]
  congr 1

theorem UpperTheory.Reformulated.B.Gka3.exists_levi :
    ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E]
      [inst_4 : Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}
      {X Y : Matrix (Fin n) (Fin r) E},
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ →
        Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J →
          GlobalTheory.SiegelSet.IsWittFrame σ J X Y →
            ∀ (A : Type) [inst_5 : CommRing A] [inst_6 : Algebra F A] [TopologicalSpace A] (p : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J)
              (B : Matrix (Fin r) (Fin r) (TensorProduct F A E)),
              B.BlockTriangular id →
                (↑((GlobalTheory.AdelicU.matHom A σ J : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J → GL (Fin n) (TensorProduct F A E)) p) :
                                 Matrix (Fin n) (Fin n) (TensorProduct F A E)) *
                      X.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) =
                    X.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) * B →
                  ∃ (m : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J),
                    (↑((GlobalTheory.AdelicU.matHom A σ J : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J → GL (Fin n) (TensorProduct F A E)) m) :
                          Matrix (Fin n) (Fin n) (TensorProduct F A E)) =
                        GlobalTheory.CompanionTheory.KFin.leviMat σ J A X Y
                          (↑((GlobalTheory.AdelicU.matHom A σ J : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J → GL (Fin n) (TensorProduct F A E)) p) :
                            Matrix (Fin n) (Fin n) (TensorProduct F A E)) ∧
                      (∃ (d : Fin r → TensorProduct F A E),
                          (↑((GlobalTheory.AdelicU.matHom A σ J : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J → GL (Fin n) (TensorProduct F A E)) m) :
                                Matrix (Fin n) (Fin n) (TensorProduct F A E)) *
                              X.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) =
                            X.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) * Matrix.diagonal d) ∧
                        (∃ (d' : Fin r → TensorProduct F A E),
                            (↑((GlobalTheory.AdelicU.matHom A σ J : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J → GL (Fin n) (TensorProduct F A E))
                                               m) :
                                  Matrix (Fin n) (Fin n) (TensorProduct F A E)) *
                                Y.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) =
                              Y.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) * Matrix.diagonal d') ∧
                          (∃ (B' : Matrix (Fin r) (Fin r) (TensorProduct F A E)),
                              B'.BlockTriangular id ∧
                                (∀ (i : Fin r), B' i i = (1 : TensorProduct F A E)) ∧
                                  (↑((GlobalTheory.AdelicU.matHom A σ J :
                                                       Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J → GL (Fin n) (TensorProduct F A E))
                                                     (m⁻¹ * p)) :
                                        Matrix (Fin n) (Fin n) (TensorProduct F A E)) *
                                      X.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) =
                                    X.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) * B') ∧
                            ∀ (z : Fin n → TensorProduct F A E),
                              ((Formalism.UG.cT (↑σ : E →+* E) X * J).map
                                              (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E)).mulVec
                                          z =
                                  (0 : Fin r → TensorProduct F A E) →
                                ∃ (a : Fin r → TensorProduct F A E),
                                  ((↑((GlobalTheory.AdelicU.matHom A σ J :
                                                           Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J → GL (Fin n) (TensorProduct F A E))
                                                         (m⁻¹ * p)) :
                                                     Matrix (Fin n) (Fin n) (TensorProduct F A E)) -
                                                   (1 : Matrix (Fin n) (Fin n) (TensorProduct F A E))).mulVec
                                      z =
                                    (X.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E)).mulVec a := by
  intro F E _ _ _ _ _ σ n J r X Y hCM hH hW A _ _ _ p B hB hpX
  obtain ⟨hXX, hYY, hXY, -⟩ := hW
  have hτ := sigR_sq A (sigma_sq hCM)
  let τ := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR A σ
  let ι := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) A
  let JA := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (F := F) A J
  let Xa := X.map ι
  let Ya := Y.map ι
  let Xd := (Formalism.UG.cT (↑σ : E →+* E) X * J).map ι
  let Yd := (Formalism.UG.cT (↑σ : E →+* E) Y * J).map ι
  let g : Matrix (Fin n) (Fin n) (TensorProduct F A E) := ↑(GlobalTheory.AdelicU.matHom A σ J p)
  have hXd : Xd = (Xa.map τ).transpose * JA := dual_map A σ J X
  have hYd : Yd = (Ya.map τ).transpose * JA := dual_map A σ J Y
  have hJh : (JA.map τ).transpose = JA := by
    ext i j
    simp only [JA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Matrix.transpose_apply, Matrix.map_apply, τ]
    rw [sigR_incl]
    exact congrArg _ (hH.1 i j)
  have hJu : IsUnit JA.det := by
    have h1 : JA.det = ι J.det := (RingHom.map_det ι J).symm
    rw [h1]
    exact (isUnit_iff_ne_zero.mpr hH.2).map ι
  have hXX' : Xd * Xa = 0 := by
    simp only [Xd, Xa]
    rw [← Matrix.map_mul, hXX]
    simp
  have hYY' : Yd * Ya = 0 := by
    simp only [Yd, Ya]
    rw [← Matrix.map_mul, hYY]
    simp
  have hXY' : Xd * Ya = 1 := by
    simp only [Xd, Ya]
    rw [← Matrix.map_mul, hXY]
    simp
  have hgJ : (g.map τ).transpose * JA * g = JA := p.2
  obtain ⟨hYX, hYgX, hXg, hdiag⟩ := UpperTheory.hermitian_block_triangular τ hτ JA g Xa Ya B Xd Yd hJh hXd hYd hXY' hgJ hB hpX
  let d : Fin r → TensorProduct F A E := fun i => (Yd * g * Xa) i i
  let e : Fin r → TensorProduct F A E := fun i => (Xd * g * Ya) i i
  let P := 1 - Xa * Yd - Ya * Xd
  let M := GlobalTheory.CompanionTheory.KFin.leviMat σ J A X Y g
  have hM : M = (Xa * Matrix.diagonal d) * Yd + (Ya * Matrix.diagonal e) * Xd + P * g * P := rfl
  have hdB : ∀ i, d i = B i i := fun i => by simp only [d, hYgX]
  have hde : ∀ i, τ (e i) * d i = 1 := fun i => by rw [hdB]; exact hdiag i
  have hdu : ∀ i, IsUnit (d i) := fun i => IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact hde i)
  obtain ⟨hu, hun, hmX, hmY⟩ := UpperTheory.hermitian_block_diagonal τ hτ JA g P M Xa Ya (Xd * g * Ya) Xd Yd d e hJh hJu hXd hYd
    hXX' hYY' hXY' hgJ hXg hde rfl hM
  obtain ⟨⟨B', hB1, hB2, hB3⟩, hz⟩ := UpperTheory.hermitian_projection_eq g P M Xa Ya B (Xd * g * Ya) Xd Yd d e hXX' hYY' hXY' hYX
    hB hpX hXg hdB hdu rfl hM hu
  let m : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J := ⟨Matrix.nonsingInvUnit M hu, hun⟩
  have hmv : (↑(GlobalTheory.AdelicU.matHom A σ J m) : Matrix (Fin n) (Fin n) (TensorProduct F A E)) = M := rfl
  have hinv : (↑(GlobalTheory.AdelicU.matHom A σ J (m⁻¹ * p)) : Matrix (Fin n) (Fin n) (TensorProduct F A E)) = M⁻¹ * g := by
    rw [map_mul, map_inv, Units.val_mul, Matrix.coe_units_inv, hmv]
  refine ⟨m, rfl, ⟨d, hmX⟩, ⟨e, hmY⟩, ⟨B', hB1, hB2, ?_⟩, ?_⟩
  · rw [hinv]
    exact hB3
  · intro z hzz
    rw [hinv]
    exact hz z hzz
