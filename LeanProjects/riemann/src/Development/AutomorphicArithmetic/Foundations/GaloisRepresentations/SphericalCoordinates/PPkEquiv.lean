import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFrameEx
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem rho_ratCast {p : ℕ} [Fact p.Prime] (G : HTGroup p) (w : Fin G.m) (s : ℚ) :
    G.rho w (algebraMap ℚ G.C s) = Matrix.scalar (Fin G.n) (algebraMap ℚ_[p] (G.Fw w) (algebraMap ℚ ℚ_[p] s)) := by
  rw [IsScalarTower.algebraMap_apply ℚ G.F G.C s, G.rho_F w]
  congr 1
  rw [eq_ratCast (algebraMap ℚ G.F) s, eq_ratCast (algebraMap ℚ ℚ_[p]) s, map_ratCast, map_ratCast]

private theorem pairL_move {p : ℕ} [Fact p.Prime] (G : HTGroup p) (M N : ∀ w : Fin G.m, Matrix (Fin G.n) (Fin G.n) (G.Fw w))
    (s : ℚ_[p]) (h : ∀ w, M w * N w = Matrix.scalar (Fin G.n) (algebraMap ℚ_[p] (G.Fw w) s)) (a b : Loc G) :
    pairL (fun w => (M w)ᵀ *ᵥ a w) (fun w => N w *ᵥ b w) = s * pairL a b := by
  unfold pairL
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have e : ((M w)ᵀ *ᵥ a w) ⬝ᵥ (N w *ᵥ b w) = s • (a w ⬝ᵥ b w) := by
    rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h w,
      Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul, Algebra.smul_def]
  rw [e, map_smul, smul_eq_mul]

private theorem mem_move {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {β : G.Cˣ} (A : PFrame L β)
    (u : G.Cˣ) (s : ℚˣ) (hy : (u : G.C) * β * sh G u = algebraMap ℚ G.C s * β) (g g' : Gp G) (x : VQ D)
    (h1 : g'.1 = Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom s * g.1)
    (h2 : ∀ w, g'.2 w = Units.map (G.rho w).toMonoidHom u * g.2 w) :
    A.Mem g' (L.rep (u : G.C) x) ↔ A.Mem g x := by
  have hk : (β : G.C) * sh G u * ((β⁻¹ : G.Cˣ) : G.C) = ((u⁻¹ : G.Cˣ) : G.C) * algebraMap ℚ G.C s := by
    calc (β : G.C) * sh G u * ((β⁻¹ : G.Cˣ) : G.C)
        = ((u⁻¹ : G.Cˣ) : G.C) * ((u : G.C) * β * sh G u) * ((β⁻¹ : G.Cˣ) : G.C) := by
          simp only [_root_.mul_assoc, Units.inv_mul_cancel_left]
      _ = _ := by
          rw [hy]
          simp only [_root_.mul_assoc, Units.mul_inv, _root_.mul_one]
  have hM : ∀ w, G.rho w ((β : G.C) * sh G u * ((β⁻¹ : G.Cˣ) : G.C)) * G.rho w (u : G.C) =
      Matrix.scalar (Fin G.n) (algebraMap ℚ_[p] (G.Fw w) (algebraMap ℚ ℚ_[p] s)) := by
    intro w
    rw [hk, ← map_mul, ← Algebra.commutes, _root_.mul_assoc, Units.inv_mul, _root_.mul_one, rho_ratCast]
  have t1 : ∀ w, (((g'.2 w)⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) *ᵥ A.T (L.rep (u : G.C) x) w =
      (((g.2 w)⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) *ᵥ A.T x w := by
    intro w
    have hu : (((Units.map (G.rho w).toMonoidHom u)⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) *
        G.rho w (u : G.C) = 1 := Units.inv_mul (Units.map (G.rho w).toMonoidHom u)
    rw [h2 w, _root_.mul_inv_rev, Units.val_mul, A.act, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ _ (G.rho w (u : G.C)), hu,
      Matrix.one_mulVec]
  have e1 : ((g'.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * algebraMap ℚ ℚ_[p] s = ((g.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) := by
    have hs : (((Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom s)⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * algebraMap ℚ ℚ_[p] s = 1 :=
      Units.inv_mul (Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom s)
    rw [h1, _root_.mul_inv_rev, Units.val_mul, _root_.mul_assoc, hs, _root_.mul_one]
  have t2 : ∀ z : Loc G, ((g'.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * pairL (A.T' (L.rep (u : G.C) x))
        (fun w => (g'.2 w : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) *ᵥ z w) =
      ((g.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * pairL (A.T' x) (fun w => (g.2 w : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) *ᵥ z w) := by
    intro z
    have a1 : A.T' (L.rep (u : G.C) x) = fun w =>
        (G.rho w ((β : G.C) * sh G u * ((β⁻¹ : G.Cˣ) : G.C)))ᵀ *ᵥ A.T' x w := funext fun w => A.act' _ x w
    have a2 : (fun w => (g'.2 w : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) *ᵥ z w) = fun w =>
        G.rho w (u : G.C) *ᵥ ((g.2 w : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) *ᵥ z w) := by
      funext w
      rw [h2 w, Units.val_mul, ← Matrix.mulVec_mulVec]
      rfl
    rw [a1, a2, pairL_move G _ _ _ hM, ← _root_.mul_assoc, e1]
  refine and_congr (iff_of_eq (congrArg IntL (funext t1))) (forall_congr' fun z => imp_congr_right fun _ => ?_)
  rw [t2 z]

theorem UpperTheory.Gal.W2.pkEquiv_of :
    UpperTheory.Gal.W2.PkEquiv := by
  intro p _ D G L β A y g x
  exact mem_move A y.1.1 y.1.2 y.2.1 g _ x rfl (fun _ => rfl)
