import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCls.AdaptMat

open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)

theorem isUnit_det {Y : Scheme.{0}} {N : Y.Modules} {r : ℕ} {U W : Y.Opens} {e : Fin r → Γ(N, U)} (he : IsFrame e)
    (hWU : W ≤ U) {s : Fin r → Γ(N, W)} (hs : IsFrame s) {K : Type} [CommRing K] (φ : Γ(Y, W) →+* K) :
    IsUnit (Matrix.of fun i b => φ ((he.basis hWU).repr (s i) b)).det := by
  have h1 : IsUnit ((he.basis hWU).toMatrix (hs.basis le_rfl)).det :=
    (he.basis hWU).isUnit_det (hs.basis le_rfl)
  have h2 := h1.map φ
  rw [RingHom.map_det, ← Matrix.det_transpose] at h2
  convert h2 using 2
  ext i b
  simp [Module.Basis.toMatrix_apply, resM_self]

theorem exists_comb {Y : Scheme.{0}} {N : Y.Modules} {r : ℕ} (fl : Vert.Flag N r) {U W W' : Y.Opens}
    {e : Fin r → Γ(N, U)} (he : IsFrame e) (hWU : W ≤ U) (hWU' : W' ≤ U) {s : Fin r → Γ(N, W)} (hs : Adapted fl s)
    {K : Type} [CommRing K] (y : Sp K ⟶ Y) (hy : ⊤ ≤ y ⁻¹ᵁ W) (hy' : ⊤ ≤ y ⁻¹ᵁ W') (k : Fin (r + 1))
    (t : Γ(fl.F k, W')) :
    ∃ cf : Fin r → K, (∀ l : Fin r, (k : ℕ) ≤ l → cf l = 0) ∧
      (fun b => TangentOrigin.evalPt y W' hy' ((he.basis hWU').repr ((fl.ι k).app W' t) b)) =
        Matrix.vecMul cf (Matrix.of fun i b => TangentOrigin.evalPt y W hy ((he.basis hWU).repr (s i) b)) := by
  obtain ⟨u, hu, hus⟩ := hs.2 k
  have h0 : ⊤ ≤ y ⁻¹ᵁ (W ⊓ W') := fun p hp => ⟨hy hp, hy' hp⟩
  obtain ⟨a, ha⟩ := (hu (W ⊓ W') inf_le_left).2 (resM (fl.F k) inf_le_right t)
  have hk : (k : ℕ) ≤ r := Nat.lt_succ_iff.1 k.2
  refine ⟨fun l => if h : (l : ℕ) < k then TangentOrigin.evalPt y _ h0 (a ⟨l, h⟩) else 0,
    fun l hl => dif_neg (not_lt.2 hl), ?_⟩
  funext b
  have h1 : resM N (inf_le_right : W ⊓ W' ≤ W') ((fl.ι k).app W' t) =
      ∑ i : Fin k, a i • resM N (inf_le_left : W ⊓ W' ≤ W) (s (Fin.castLE hk i)) := by
    rw [← app_resM, ← ha, Fintype.linearCombination_apply]
    refine (map_sum (QCoh.appLinear (fl.ι k) (W ⊓ W')) _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [map_smul, QCoh.appLinear_apply, app_resM, hus]
  rw [← TangentOrigin.evalPt_res y inf_le_right hy' h0, ← he.repr_resM, h1]
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, map_mul]
  rw [Matrix.vecMul, dotProduct]
  symm
  refine (Finset.sum_of_injOn (Fin.castLE hk) (Fin.castLE_injective hk).injOn (fun _ _ => Finset.mem_univ _)
    (fun l _ hl => ?_) (fun i _ => ?_)).symm
  · rw [dif_neg, zero_mul]
    exact fun h => hl ⟨⟨l, h⟩, Finset.mem_coe.2 (Finset.mem_univ _), rfl⟩
  · rw [dif_pos (show ((Fin.castLE hk i : Fin r) : ℕ) < k from i.2), Matrix.of_apply,
      ← TangentOrigin.evalPt_res y inf_le_left hy h0, ← he.repr_resM]
    rfl

theorem flagMat_of_adapted : ∀ (B Y : Scheme.{0}) (M : B.Modules) (r : ℕ) (hM : IsVB M r) (π : Y ⟶ B) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj M) r) (V : B.Opens) (f : Fin r → Γ(M, V)) (hf : IsFrame f) (K : Type) [CommRing K] (y : Sp K ⟶ Y) (W : Y.Opens) (hWV : W ≤ π ⁻¹ᵁ V) (hy : ⊤ ≤ y ⁻¹ᵁ W) (s : Fin r → Γ((Scheme.Modules.pullback π).obj M, W)), Adapted fl s → FlagMat hM π fl hf y (Matrix.of fun i => coordAt hM π hf y hWV hy (s i)) := by
  intro B Y M r hM π fl V f hf K _ y W hWV hy s hs
  haveI := hM.isQuasicoherent
  exact ⟨isUnit_det (hf.pullback π) hWV hs.1 (TangentOrigin.evalPt y W hy),
    fun k W' hWV' t hy' => exists_comb fl (hf.pullback π) hWV hWV' hs y hy hy' k t⟩

end GlobalTheory.FlagCls.AdaptMat

end
