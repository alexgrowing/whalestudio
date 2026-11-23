import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

private theorem tri_mul {K : Type} [CommRing K] {r : ℕ} {S T : Matrix (Fin r) (Fin r) K} (hS : IsTri S) (hT : IsTri T) :
    IsTri (S * T) ∧ ∀ i, (S * T) i i = S i i * T i i := by
  refine ⟨fun a i h => ?_, fun i => ?_⟩
  · rw [mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k a with h' | h'
    · rw [hS a k h', zero_mul]
    · rw [hT k i (h.trans_le h'), mul_zero]
  · rw [mul_apply]
    refine Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)
    rcases lt_or_gt_of_ne hk with h' | h'
    · rw [hS i k h', zero_mul]
    · rw [hT k i h', mul_zero]

private def posE (dual : Bool) (r : ℕ) : Equiv.Perm (Fin r) := ⟨pos dual, pos dual, pos_pos dual, pos_pos dual⟩

private theorem tri_lieMat {K : Type} [CommRing K] {r : ℕ} (dual : Bool) {U : Matrix (Fin r) (Fin r) K} (hU : IsTri U)
    (hu : IsUnit U.det) {t : Fin r → Kˣ} (ht : ∀ i, U i i = t i) :
    IsTri ((lieMat dual U).submatrix (pos dual) (pos dual)) ∧
      ∀ i, lieMat dual U i i = ((t i ^ (cond dual (-1) 1 : ℤ) : Kˣ) : K) := by
  cases dual
  · exact ⟨hU, fun i => by simpa [lieMat] using ht i⟩
  · have := invertibleOfIsUnitDet U hu
    have h1 : IsTri U⁻¹ := fun a i h =>
      blockTriangular_inv_of_blockTriangular (b := id) (M := U) (fun a i h => hU a i h) h
    refine ⟨fun a i h => h1 _ _ (Fin.rev_lt_rev.2 h), fun i => ?_⟩
    have h2 := (tri_mul h1 hU).2 i
    rw [nonsing_inv_mul _ hu, one_apply_eq, ht] at h2
    simp only [lieMat, cond_true, transpose_apply, _root_.zpow_neg, zpow_one]
    exact Units.eq_inv_of_mul_eq_one_right h2.symm

private theorem key {R K : Type} [CommRing R] [CommRing K] {r : ℕ} (dual : Bool) (ψ : R →+* K)
    (hψ : Function.Injective ψ) {U A : Matrix (Fin r) (Fin r) K} {Q : Matrix (Fin r) (Fin r) R} (hU : IsTri U)
    (hu : IsUnit U.det) {t : Fin r → Kˣ} (ht : ∀ i, U i i = t i) (hA : IsUnit A.det)
    (hA' : IsTri (A.submatrix (pos dual) id)) (hQ : IsUnit Q.det) (h : Q.map ψ = U * lieMat dual A) :
    IsTri ((lieMat dual Q).submatrix (pos dual) id) ∧ ∀ i, IsUnit (lieMat dual Q (pos dual i) i) ∧
      A (pos dual i) i * ((t (pos dual i) ^ (cond dual (-1) 1 : ℤ) : Kˣ) : K) = ψ (lieMat dual Q (pos dual i) i) := by
  have h1 : (lieMat dual Q).map ψ = lieMat dual U * A := by
    rw [← lieMat_map _ _ hQ, h, lieMat_mul, lieMat_lieMat _ hA]
  have h2 : ((lieMat dual Q).map ψ).submatrix (pos dual) id =
      (lieMat dual U).submatrix (pos dual) (pos dual) * A.submatrix (pos dual) id := by
    rw [h1]
    exact (submatrix_mul_equiv _ _ _ (posE dual r) _).symm
  obtain ⟨h3, h4⟩ := tri_lieMat dual hU hu ht
  obtain ⟨h5, h6⟩ := tri_mul h3 hA'
  rw [← h2] at h5 h6
  have h7 : IsTri ((lieMat dual Q).submatrix (pos dual) id) := fun a i hi =>
    hψ ((h5 a i hi).trans (map_zero ψ).symm)
  have h8 : IsUnit ((lieMat dual Q).submatrix (pos dual) id).det := by
    have := det_permute (posE dual r) (lieMat dual Q)
    change ((lieMat dual Q).submatrix (pos dual) id).det = _ at this
    rw [this]
    refine IsUnit.mul ?_ (isUnit_det_lieMat dual hQ)
    exact (Units.isUnit _).map (Int.castRingHom R)
  rw [det_of_upperTriangular (fun a i hi => h7 a i hi), IsUnit.prod_univ_iff] at h8
  refine ⟨h7, fun i => ⟨h8 i, ?_⟩⟩
  rw [← h4, mul_comm]
  exact (h6 i).symm

theorem UpperTheory.chart_frame_divisor :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (C : FlagCpt Z e) (τ : E →+* ℂ) (X : Scheme.{0}) (j : C.Y.X ⟶ X) (M : X.Modules) (dual : Bool) (A : Chart M (Dw.mult τ) → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) C.Y.Fn) (fl : Vert.Flag M (Dw.mult τ)), IsLie C.f0 τ j dual A → IsFlag (genericPt C.Y ≫ j) dual A fl → ∀ ch : Chart M (Dw.mult τ), IsAdapted fl ch → ∀ y : C.Y.X, j y ∈ ch.U → ∀ (φ : c.F →+* C.Y.X.presheaf.stalk y) (f f' : StalkFrame C.π y φ) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ), f.Tri (toFn y) C.f0 t → Fits C.f0 τ y φ f' (lieMat dual (A ch)) → IsTri ((lieMat dual (f.co f' τ)).submatrix (pos dual) id) ∧ ∀ i, IsUnit (lieMat dual (f.co f' τ) (pos dual i) i) ∧ A ch (pos dual i) i * ((t τ (pos dual i) ^ (cond dual (-1) 1 : ℤ) : C.Y.Fnˣ) : C.Y.Fn) = toFn y (lieMat dual (f.co f' τ) (pos dual i) i) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ _ e C τ X j M dual A fl hL hF ch hch y hy φ f f' t hT hf'
  obtain ⟨k, hk⟩ := exists_isMap_toFn (e := e) f hf'.1
  obtain ⟨h1, h2⟩ := hT.co τ hk
  have h3 : Fits C.f0 τ y φ f (C.f0.co k τ) := (fits_iff hf'.1 hk).2 rfl
  refine key dual (toFn y) (toFn_injective y) (U := k.co C.f0 τ) h1 (k.isUnit_det_co _ τ) h2
    (hL.1.1 ch (gen_le j hy)) (hF ch hch (gen_le j hy)) (f.isUnit_det_co f' τ) ?_
  rw [h3.eq_mul hf', ← Matrix.mul_assoc, EigFrame.co_mul, EigFrame.co_self, Matrix.one_mul]
