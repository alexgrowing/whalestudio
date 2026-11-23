import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.ThFacts

open Polynomial
namespace UpperTheory.V.Z.Sym.Wt

private theorem map_invT {R : Type} [CommRing R] (f : R →+* ℂ) (d : ℕ) (g : GL (Fin d) R) :
    Matrix.GeneralLinearGroup.map f (invT R d g) = invT ℂ d (Matrix.GeneralLinearGroup.map f g) := by
  ext i k
  rw [Matrix.GeneralLinearGroup.map_apply, invT_val, invT_val, ← map_inv, Matrix.transpose_apply,
    Matrix.transpose_apply, Matrix.GeneralLinearGroup.map_apply]

private theorem map_scal {R : Type} [CommRing R] (f : R →+* ℂ) (d : ℕ) (x : Rˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin d) x) =
      Matrix.GeneralLinearGroup.scalar (Fin d) (Units.map f.toMonoidHom x) := by
  ext i k
  rw [Matrix.GeneralLinearGroup.map_apply]
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply, apply_ite f]

private theorem val_map {R : Type} [CommRing R] (f : R →+* ℂ) (d : ℕ) (g : GL (Fin d) R) :
    ((Matrix.GeneralLinearGroup.map f g : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) = (g : Matrix (Fin d) (Fin d) R).map f := rfl

theorem wtMain_of (h1 : FinMH) (h2 : ThFacts) (h3 : TwineC) (h4 : TrDC) (h5 : Scalars) (h6 : HqKappa) : WtMain := by
  intro R I _ _ em j hj
  classical
  have hWG : ∀ g : GL (Fin 3) R,
      WG em j g = repG I j (fun w => Matrix.GeneralLinearGroup.map (em w) g) := fun _ => rfl
  have hWD : ∀ (n : ℕ) (e : ℤ) (g : GL (Fin 2) R),
      WD em n e g = repD I n e (fun w => Matrix.GeneralLinearGroup.map (em w) g) := fun _ _ _ => rfl
  have hdet : ∀ (w : I) (g : GL (Fin 2) R),
      ((Matrix.GeneralLinearGroup.map (em w) g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det =
        em w (g : Matrix (Fin 2) (Fin 2) R).det := by
    intro w g
    rw [val_map, RingHom.map_det]
    rfl
  have htr : ∀ (w : I) (g : GL (Fin 2) R),
      ((Matrix.GeneralLinearGroup.map (em w) g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace =
        em w (g : Matrix (Fin 2) (Fin 2) R).trace := by
    intro w g
    rw [val_map, AddMonoidHom.map_trace]
  refine
    { finG := ?_, finD := ?_, th_sq := (h2 I j).1, th_rep := ?_, scalG := ?_, scalD := ?_,
      twine := ?_, stable := ?_, kappa := ?_ }
  · haveI : ∀ S : I → Bool, FiniteDimensional ℂ (Bi 3 (dg j S)) := fun S => h1 _ _ _
    infer_instance
  · intro n
    exact h1 _ _ _
  · intro g
    rw [hWG, hWG, (h2 I j).2]
    have hfun : (fun v => invT ℂ 3 (Matrix.GeneralLinearGroup.map (em v) g)) =
        fun w => Matrix.GeneralLinearGroup.map (em w) (invT R 3 g) :=
      funext fun v => (map_invT _ _ _).symm
    rw [hfun]
  · intro x
    rw [hWG]
    have hfun : (fun w => Matrix.GeneralLinearGroup.map (em w) (Matrix.GeneralLinearGroup.scalar (Fin 3) x)) =
        fun w => Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.map (em w).toMonoidHom x) :=
      funext fun w => map_scal _ _ _
    rw [hfun]
    exact (h5 I _).1 j
  · intro n e x
    rw [hWD]
    have hfun : (fun w => Matrix.GeneralLinearGroup.map (em w) (Matrix.GeneralLinearGroup.scalar (Fin 2) x)) =
        fun w => Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (em w).toMonoidHom x) :=
      funext fun w => map_scal _ _ _
    rw [hfun, (h5 I _).2 n e]
    congr 1
    rw [Units.coe_prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [Units.val_zpow_eq_zpow_val, Units.coe_map]
    rfl
  · intro δ τ hch
    rw [hWG]
    refine h3 I j hj (fun w => Matrix.GeneralLinearGroup.map (em w) δ) (fun w => em w τ) ?_
    intro v
    rw [← map_invT, ← map_mul, val_map, Matrix.charpoly_map, hch]
    simp [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_add]
  · intro e γ hγ
    rw [hWD, h4]
    show _ = ∏ w, hq (em w (γ : Matrix (Fin 2) (Fin 2) R).trace) 1 j
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [hdet, htr, hγ, map_one, one_zpow, one_mul]
  · intro z τ htz hdz
    rw [hWD, h4]
    show _ = ∏ w, hq (em w τ) 1 j
    refine Finset.prod_congr rfl fun w _ => ?_
    have hu : em w (z : Matrix (Fin 2) (Fin 2) R).det ≠ 0 := by
      have hz : IsUnit (z : Matrix (Fin 2) (Fin 2) R).det := by
        rw [← Matrix.GeneralLinearGroup.val_det_apply]
        exact Units.isUnit _
      exact (hz.map (em w)).ne_zero
    rw [hdet, htr, htz, hdz, map_add, map_ofNat, h6 j (em w τ)]
    rw [hdz, map_add, map_ofNat] at hu
    rw [zpow_neg, show ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
      inv_mul_cancel_left₀ (pow_ne_zero _ hu)]

end UpperTheory.V.Z.Sym.Wt
