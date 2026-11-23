import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigBaseChange

theorem piScalarRight_lTensor_mulVec {R O : Type} [CommRing R] [CommRing O] [Algebra R O]
    {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (A : Matrix m n R)
    (x : O ⊗[R] (n → R)) :
    TensorProduct.piScalarRight R O O m (LinearMap.lTensor O A.mulVecLin x) =
      (A.map (algebraMap R O)).mulVec (TensorProduct.piScalarRight R O O n x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, Matrix.mulVec_add]
  | tmul o v =>
    ext i
    simp [Matrix.mulVec, dotProduct, Algebra.smul_def, Finset.sum_mul, mul_assoc]

theorem exact_mulVec_map {R O : Type} [CommRing R] [CommRing O] [Algebra R O] [Module.Flat R O]
    {k m n : Type} [Fintype k] [Fintype m] [Fintype n] (A : Matrix m n R) (B : Matrix k m R)
    (h : Function.Exact A.mulVec B.mulVec) :
    Function.Exact (A.map (algebraMap R O)).mulVec (B.map (algebraMap R O)).mulVec := by
  classical
  have h' : Function.Exact A.mulVecLin B.mulVecLin := h
  have h2 := Module.Flat.lTensor_exact O h'
  intro y
  obtain ⟨y, rfl⟩ := (TensorProduct.piScalarRight R O O m).surjective y
  rw [← piScalarRight_lTensor_mulVec, LinearEquiv.map_eq_zero_iff, h2 y]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, (piScalarRight_lTensor_mulVec A x).symm⟩
  · rintro ⟨x, hx⟩
    obtain ⟨x, rfl⟩ := (TensorProduct.piScalarRight R O O n).surjective x
    rw [← piScalarRight_lTensor_mulVec] at hx
    exact ⟨x, (TensorProduct.piScalarRight R O O m).injective hx⟩

theorem transpose_mulVec {R : Type} [CommRing R] {d s : ℕ} (w : Fin s → Fin d → R) (c : Fin s → R) :
    (Matrix.of w).transpose.mulVec c = ∑ i, c i • w i := by
  ext j
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

def eigMat {R : Type} [CommRing R] {d N : ℕ} (L : Fin N → Matrix (Fin d) (Fin d) R)
    (t : Fin N → R) : Matrix (Fin N × Fin d) (Fin d) R :=
  Matrix.of fun p j => (L p.1 - t p.1 • (1 : Matrix (Fin d) (Fin d) R)) p.2 j

theorem eigMat_mulVec_eq_zero {R : Type} [CommRing R] {d N : ℕ}
    (L : Fin N → Matrix (Fin d) (Fin d) R) (t : Fin N → R) (v : Fin d → R) :
    (eigMat L t).mulVec v = 0 ↔ ∀ k, (L k).mulVec v = t k • v := by
  have key : ∀ k i, (eigMat L t).mulVec v (k, i) = ((L k).mulVec v - t k • v) i := by
    intro k i
    have : (eigMat L t).mulVec v (k, i) =
        (L k - t k • (1 : Matrix (Fin d) (Fin d) R)).mulVec v i := rfl
    rw [this, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  constructor
  · intro h k
    rw [← sub_eq_zero]
    ext i
    rw [← key, h]; rfl
  · intro h
    ext ⟨k, i⟩
    rw [key, h k, sub_self]; rfl

theorem eigMat_map {R O : Type} [CommRing R] [CommRing O] (f : R →+* O) {d N : ℕ}
    (L : Fin N → Matrix (Fin d) (Fin d) R) (t : Fin N → R) :
    (eigMat L t).map f = eigMat (fun k => (L k).map f) (fun k => f (t k)) := by
  ext ⟨k, i⟩ j
  by_cases h : i = j <;> simp [eigMat, Matrix.one_apply, h]

theorem eig_of_span {R OE : Type} [CommRing R] [CommRing OE] {d N : ℕ}
    (L : OE → Matrix (Fin d) (Fin d) R) (hL : ∀ a b, L (a + b) = L a + L b) (τ : OE →+* R)
    (g : Fin N → OE) (hg : Submodule.span ℤ (Set.range g) = ⊤) (v : Fin d → R)
    (hv : ∀ k, (L (g k)).mulVec v = τ (g k) • v) (a : OE) : (L a).mulVec v = τ a • v := by
  let L' : OE →+ Matrix (Fin d) (Fin d) R := AddMonoidHom.mk' L hL
  change (L' a).mulVec v = _
  have ha : a ∈ Submodule.span ℤ (Set.range g) := hg ▸ Submodule.mem_top
  induction ha using Submodule.span_induction with
  | mem x hx => obtain ⟨k, rfl⟩ := hx; exact hv k
  | zero => simp
  | add x y _ _ hx hy => simp [Matrix.add_mulVec, hx, hy, add_smul]
  | smul z x _ hx => rw [map_zsmul, map_zsmul, Matrix.smul_mulVec, hx, smul_assoc]

theorem linPart_map {R O : Type} [CommRing R] [CommRing O] (f : R →+* O) {d : ℕ}
    (φ : Fin d → PS R 1 d) :
    linPart (fun i => MvPowerSeries.map f (φ i)) = (linPart φ).map f := by
  ext i j
  simp [linPart, MvPowerSeries.coeff_map]

theorem isEigBasis_map : ∀ (R O : Type) [CommRing R] [CommRing O] [Algebra R O] [Module.Flat R O] (OE : Type) [CommRing OE] [Module.Finite ℤ OE] (d s : ℕ) (act : OE → Fin d → PS R 1 d), (∀ a b, linPart (act (a + b)) = linPart (act a) + linPart (act b)) → ∀ (τ : OE →+* R) (w : Fin s → Fin d → R), IsEigBasis act τ w → IsEigBasis (fun a i => MvPowerSeries.map (algebraMap R O) (act a i)) ((algebraMap R O).comp τ) (fun i j => algebraMap R O (w i j)) := by
  intro R O _ _ _ _ OE _ _ d s act hadd τ w hw
  obtain ⟨N, g, hg⟩ := Module.Finite.exists_fin (R := ℤ) (M := OE)
  have hadd' : ∀ a b, (linPart (act (a + b))).map (algebraMap R O) =
      (linPart (act a)).map (algebraMap R O) + (linPart (act b)).map (algebraMap R O) := by
    intro a b
    rw [hadd, Matrix.map_add _ (map_add _)]
  have hlin : ∀ (c : Fin s → R) a, (linPart (act a)).mulVec (∑ i, c i • w i) = τ a • ∑ i, c i • w i := by
    intro c a
    rw [Matrix.mulVec_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_smul, hw.1, smul_comm]
  have ex1 : Function.Exact (Matrix.of w).transpose.mulVec
      (eigMat (fun k => linPart (act (g k))) (fun k => τ (g k))).mulVec := by
    intro v
    rw [eigMat_mulVec_eq_zero]
    constructor
    · intro h
      obtain ⟨c, hc, -⟩ := hw.2 v (eig_of_span (fun a => linPart (act a)) hadd τ g hg v h)
      exact ⟨c, by rw [transpose_mulVec, hc]⟩
    · rintro ⟨c, rfl⟩ k
      rw [transpose_mulVec]; exact hlin c _
  have ex0 : Function.Exact (0 : Matrix (Fin s) (Fin 0) R).mulVec (Matrix.of w).transpose.mulVec := by
    intro c
    rw [transpose_mulVec]
    constructor
    · intro h
      obtain ⟨c0, -, hu⟩ := hw.2 0 (by simp)
      exact ⟨0, by rw [hu c h, ← hu 0 (by simp)]; simp⟩
    · rintro ⟨x, rfl⟩
      simp
  have ex1' := exact_mulVec_map (O := O) _ _ ex1
  have ex0' := exact_mulVec_map (O := O) _ _ ex0
  have hT : ((Matrix.of w).transpose.map (algebraMap R O)) =
      (Matrix.of fun i j => algebraMap R O (w i j)).transpose := rfl
  rw [hT] at ex1' ex0'
  rw [eigMat_map] at ex1'
  constructor
  · intro i a
    rw [linPart_map]
    ext j
    have := congrArg (algebraMap R O) (congrFun (hw.1 i a) j)
    simpa [Matrix.mulVec, dotProduct] using this
  · intro v hv
    simp only [linPart_map] at hv
    obtain ⟨c, hc⟩ := (ex1' v).1 ((eigMat_mulVec_eq_zero _ _ _).2 fun k => hv (g k))
    rw [transpose_mulVec] at hc
    refine ⟨c, hc, fun c' hc' => ?_⟩
    obtain ⟨x, hx⟩ := (ex0' (c' - c)).1 (by
      rw [Matrix.mulVec_sub, transpose_mulVec, transpose_mulVec]
      exact sub_eq_zero.2 (hc'.trans hc.symm))
    rw [← sub_eq_zero, ← hx]
    simp

end GlobalTheory.EigBaseChange
