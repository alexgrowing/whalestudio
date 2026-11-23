import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SphericalSplitting.SphericalEisensteinGrowth

noncomputable section

open scoped NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.RegSW PositivityTheory.RegularEisensteinLemmas
open GlobalTheory.Core.Rk.SWLaw (zeroSp)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HyperbolicDecompositionLaw

variable {D : D7} {T T₀ T' : HSp D} {r : ℕ}

theorem mul_eq_one_of_gram {R : Type} [CommRing R] {c x G Gi : R} (hg : G * Gi = 1) (h : c * (G * x) = G) : c * x = 1 := by
  linear_combination Gi * h + (1 - c * x) * hg

theorem nnreal_eq_one_of_sq {x : ℝ≥0} (h : x * x = 1) : x = 1 := by
  rw [← sq] at h
  exact (pow_eq_one_iff_of_nonneg zero_le (n := 2) (by norm_num)).1 h

theorem absA_eq_one_of_conj (u : (AE D)ˣ) (h : conjUnit D.sp.cm.sig u * u = 1) : absA D u = 1 := by
  have h3 := congrArg (absE D.host.F D.host.E) h
  rw [map_mul, absE_conjUnit, map_one] at h3
  exact nnreal_eq_one_of_sq h3

theorem absA_det_matHom (g : GA D T₀) : absA D (Matrix.GeneralLinearGroup.det (matHom T₀ g)) = 1 := by
  have hg : (gA T₀).det * (giA T₀).det = 1 := by rw [← Matrix.det_mul, gA_mul_giA, Matrix.det_one]
  have h := congrArg Matrix.det (mt_unitary T₀ g)
  rw [Matrix.det_mul, Matrix.det_mul] at h
  have hadj : (adj (mt T₀ g)).det = cA D (mt T₀ g).det := by
    rw [adj, Matrix.det_transpose, RingHom.map_det]; rfl
  rw [hadj] at h
  have h2 : conjUnit D.sp.cm.sig (Matrix.GeneralLinearGroup.det (matHom T₀ g)) *
      Matrix.GeneralLinearGroup.det (matHom T₀ g) = 1 := Units.ext (mul_eq_one_of_gram hg h)
  exact absA_eq_one_of_conj _ h2

theorem stabilizer_image_no_dual_component (d : HypDec T T₀ r) (p : stab d) : d.pY ⬝ (mt T p ⬝ d.j0) = 0 := by
  have h := mul_jX d p
  have h1 : adj (onX d p).1 ⬝ (d.pY ⬝ (mt T p ⬝ d.j0)) = 0 := by
    have e : adj (onX d p).1 ⬝ (d.pY ⬝ (mt T p ⬝ d.j0)) = adj (d.jX ⬝ (onX d p).1) ⬝ (gA T ⬝ (mt T p ⬝ d.j0)) := by
      rw [d.pY_eq, adj_mul]; simp only [Matrix.mul_assoc]
    rw [e, ← h, adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA T), ← Matrix.mul_assoc (adj (mt T p)), mt_unitary T p]
    exact d.wittDecomp_gram_X_anisotropic
  have h2 : adj ((onX d p)⁻¹).1 ⬝ adj (onX d p).1 = 1 := by
    rw [← adj_mul, Units.mul_inv, adj_one]
  rw [← Matrix.one_mul (d.pY ⬝ (mt T p ⬝ d.j0)), ← h2, Matrix.mul_assoc, h1, Matrix.mul_zero]

theorem stabilizer_image_hyperbolic (d : HypDec T T₀ r) (p : stab d) :
    mt T p ⬝ d.j0 = d.jX ⬝ (d.pX ⬝ (mt T p ⬝ d.j0)) + d.j0 ⬝ (d.p0 ⬝ (mt T p ⬝ d.j0)) := by
  have h : (d.jX ⬝ d.pX + d.j0 ⬝ d.p0 + d.jY ⬝ d.pY) ⬝ (mt T p ⬝ d.j0) = mt T p ⬝ d.j0 := by
    rw [d.sum_eq_one, Matrix.one_mul]
  rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc d.jX, Matrix.mul_assoc d.j0, Matrix.mul_assoc d.jY, stabilizer_image_no_dual_component,
    Matrix.mul_zero, add_zero] at h
  exact h.symm

theorem rat_lag {n a b : ℕ} (M : Matrix (Fin n) (Fin a) D.host.E) (N : Matrix (Fin n) (Fin b) D.host.E) :
    rat ((Matrix.fromCols M N).submatrix id finSumFinEquiv.symm) =
      (Matrix.fromCols (rat M) (rat N)).submatrix id finSumFinEquiv.symm := by
  funext i j
  change incA D (Matrix.fromCols M N i (finSumFinEquiv.symm j)) = Matrix.fromCols (rat M) (rat N) i (finSumFinEquiv.symm j)
  generalize finSumFinEquiv.symm j = s
  cases s <;> rfl

section Blocks

variable {R : Type} [CommRing R] {n a b : ℕ}

theorem fromCols_mul_fromBlocks (P : Matrix (Fin n) (Fin a) R) (Q : Matrix (Fin n) (Fin b) R)
    (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin a) (Fin b) R) (z : Matrix (Fin b) (Fin b) R) :
    Matrix.fromCols P Q * Matrix.fromBlocks x y 0 z = Matrix.fromCols (P * x) (P * y + Q * z) := by
  ext i (j | j) <;> simp [Matrix.mul_apply, Fintype.sum_sum_type]

theorem exists_gl_block (x : Matrix.GeneralLinearGroup (Fin a) R) (z : Matrix.GeneralLinearGroup (Fin b) R)
    (y : Matrix (Fin a) (Fin b) R) : ∃ B : Matrix.GeneralLinearGroup (Fin (a + b)) R,
      B.1 = (Matrix.fromBlocks x.1 y 0 z.1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm ∧
      Matrix.GeneralLinearGroup.det B = Matrix.GeneralLinearGroup.det x * Matrix.GeneralLinearGroup.det z := by
  have hdet : ((Matrix.fromBlocks x.1 y 0 z.1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm :
      Matrix (Fin (a + b)) (Fin (a + b)) R).det = x.1.det * z.1.det := by
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  have hu : IsUnit ((Matrix.fromBlocks x.1 y 0 z.1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm :
      Matrix (Fin (a + b)) (Fin (a + b)) R).det := by
    rw [hdet]
    exact (Matrix.GeneralLinearGroup.det x * Matrix.GeneralLinearGroup.det z).isUnit
  exact ⟨Matrix.GeneralLinearGroup.mk'' _ hu, rfl, Units.ext hdet⟩

theorem mul_cols_block (X : Matrix (Fin n) (Fin n) R) (P : Matrix (Fin n) (Fin a) R) (Q : Matrix (Fin n) (Fin b) R)
    (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin a) (Fin b) R) (z : Matrix (Fin b) (Fin b) R)
    (c1 : X * P = P * x) (c2 : X * Q = P * y + Q * z) :
    X * (Matrix.fromCols P Q).submatrix id finSumFinEquiv.symm = (Matrix.fromCols P Q).submatrix id finSumFinEquiv.symm *
      (Matrix.fromBlocks x y 0 z).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
  rw [← Matrix.submatrix_mul _ _ _ _ _ finSumFinEquiv.symm.bijective, fromCols_mul_fromBlocks, ← c1, ← c2,
    ← Matrix.mul_fromCols]
  rfl

theorem mul_sum_eq {t : ℕ} {X : Matrix (Fin n) (Fin n) R} {P : Matrix (Fin n) (Fin t) R} {g : Matrix (Fin t) (Fin t) R}
    {Q : Matrix (Fin n) (Fin b) R} {J : Matrix (Fin t) (Fin a) R} {J₀ : Matrix (Fin t) (Fin b) R}
    {y : Matrix (Fin a) (Fin b) R} {z : Matrix (Fin b) (Fin b) R} (e1 : X * P = P * g) (e2 : X * Q = Q * z)
    (h0 : g * J₀ = J * y + J₀ * z) : X * (P * J₀ + Q) = P * J * y + (P * J₀ + Q) * z := by
  rw [Matrix.mul_add, ← Matrix.mul_assoc, e1, Matrix.mul_assoc, h0, e2, Matrix.mul_add, Matrix.add_mul,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, add_assoc]

end Blocks

theorem exists_block (d : HypDec T T₀ r) {jT : Matrix (Fin T'.rank) (Fin T.rank) D.host.E}
    {j₀ : Matrix (Fin T'.rank) (Fin T₀.rank) D.host.E} {d' : HypDec T' (zeroSp D) (r + T₀.rank)}
    {ι : GA D T × GA D T₀ →* GA D T'} {m : stab d →* GA D T₀} (hE : IsEmb jT j₀ ι) (hL : IsLag d jT j₀ d')
    (hM : IsLevi0 d m) (p : stab d) : ∃ B : Matrix.GeneralLinearGroup (Fin (r + T₀.rank)) (AE D),
      mt T' (ι ((p : GA D T), m p)) ⬝ d'.jX = d'.jX ⬝ B.1 ∧
      Matrix.GeneralLinearGroup.det B =
        Matrix.GeneralLinearGroup.det (onX d p) * Matrix.GeneralLinearGroup.det (matHom T₀ (m p)) := by
  obtain ⟨B, hB, hdet⟩ := exists_gl_block (onX d p) (matHom T₀ (m p)) (d.pX ⬝ (mt T p ⬝ d.j0))
  refine ⟨B, ?_, hdet⟩
  have hJ : d'.jX = (Matrix.fromCols (rat jT ⬝ d.jX) (rat jT ⬝ d.j0 + rat j₀)).submatrix id finSumFinEquiv.symm := by
    rw [HypDec.jX, hL, rat_lag, rat_mul, rat_add, rat_mul]; rfl
  have h0 : mt T p ⬝ d.j0 = d.jX ⬝ (d.pX ⬝ (mt T p ⬝ d.j0)) + d.j0 ⬝ mt T₀ (m p) := by
    rw [hM p]; exact stabilizer_image_hyperbolic d p
  obtain ⟨e1, e2⟩ := hE (p : GA D T) (m p)
  rw [hB, hJ]
  refine mul_cols_block _ _ _ _ _ _ ?_ ?_
  · rw [cancel₂ e1, Matrix.mul_assoc, mul_jX d p, Matrix.mul_assoc]
  · exact mul_sum_eq e1 e2 h0

theorem law : Law := by
  intro D T T₀ T' r d jT j₀ d' ι m _ hE hL hM p
  obtain ⟨B, key, hdet⟩ := exists_block d hE hL hM p
  have hmem : ι ((p : GA D T), m p) ∈ stab d' := ⟨B, key⟩
  refine ⟨hmem, ?_⟩
  have hon : onX d' ⟨_, hmem⟩ = B :=
    Units.ext ((eq_of_mul_jX d' (mul_jX d' _)).trans (eq_of_mul_jX d' key).symm)
  change absA D (Matrix.GeneralLinearGroup.det (onX d' ⟨_, hmem⟩)) = absA D (Matrix.GeneralLinearGroup.det (onX d p))
  rw [hon, hdet, map_mul, absA_det_matHom, mul_one]

end GlobalTheory.CompanionTheory.HyperbolicDecompositionLaw

end
