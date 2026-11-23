import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalAdaptedSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMatrixOfAdaptedCoordinatesStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCls

theorem lower_inv {r : ℕ} {K : Type} [CommRing K] {T : Matrix (Fin r) (Fin r) K} (hT : IsUnit T.det)
    (hT' : ∀ i j, i < j → T i j = 0) : ∀ i j, i < j → T⁻¹ i j = 0 := by
  have := T.invertibleOfIsUnitDet hT
  have hb : T.BlockTriangular OrderDual.toDual := fun a b hab => hT' a b hab
  exact fun i j h => Matrix.blockTriangular_inv_of_blockTriangular hb h

theorem lower_mul {r : ℕ} {K : Type} [CommRing K] {S T : Matrix (Fin r) (Fin r) K}
    (hS : ∀ i j, i < j → S i j = 0) (hT : ∀ i j, i < j → T i j = 0) : ∀ i j, i < j → (S * T) i j = 0 := by
  have hb : T.BlockTriangular OrderDual.toDual := fun a b hab => hT a b hab
  have hc : S.BlockTriangular OrderDual.toDual := fun a b hab => hS a b hab
  exact fun i j h => (hc.mul hb) h

theorem FlagMat.adapted_eq {B Y : Scheme.{0}} {M : B.Modules} {r : ℕ} {hM : IsVB M r} {π : Y ⟶ B}
    {fl : Vert.Flag ((Scheme.Modules.pullback π).obj M) r} {V : B.Opens} {f : Fin r → Γ(M, V)} {hf : IsFrame f}
    {K : Type} [CommRing K] {y : Sp K ⟶ Y} {W : Y.Opens} (hWV : W ≤ π ⁻¹ᵁ V) (hy : ⊤ ≤ y ⁻¹ᵁ W)
    {s : Fin r → Γ((Scheme.Modules.pullback π).obj M, W)} (hs : Adapted fl s) {A : Matrix (Fin r) (Fin r) K}
    (hA : FlagMat hM π fl hf y A) :
    ∃ T : Matrix (Fin r) (Fin r) K, (∀ i j, i < j → T i j = 0) ∧
      (Matrix.of fun i => coordAt hM π hf y hWV hy (s i)) = T * A := by
  have h : ∀ i : Fin r, ∃ cf : Fin r → K, (∀ l : Fin r, i < l → cf l = 0) ∧
      coordAt hM π hf y hWV hy (s i) = Matrix.vecMul cf A := by
    intro i
    obtain ⟨t, -, ht⟩ := hs.2 i.succ
    obtain ⟨cf, h1, h2⟩ := hA.2 i.succ W hWV (t (Fin.last i)) hy
    refine ⟨cf, fun l hl => h1 l hl, ?_⟩
    rw [← h2]
    exact congrArg _ (ht (Fin.last i)).symm
  choose T h1 h2 using h
  refine ⟨Matrix.of T, h1, ?_⟩
  ext i j
  exact congrFun (h2 i) j

theorem flagMat_local (B Y : Scheme.{0}) (M : B.Modules) (r : ℕ) (hM : IsVB M r) (π : Y ⟶ B)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj M) r) (V : B.Opens) (f : Fin r → Γ(M, V)) (hf : IsFrame f)
    (K : Type) [CommRing K] [IsLocalRing K] (y : Sp K ⟶ Y) (hV : ⊤ ≤ (y ≫ π) ⁻¹ᵁ V) :
    (∃ A, FlagMat hM π fl hf y A) ∧
      (∀ A A', FlagMat hM π fl hf y A → FlagMat hM π fl hf y A' →
        ∃ T : Matrix (Fin r) (Fin r) K, IsUnit T.det ∧ (∀ i j, i < j → T i j = 0) ∧ A' = T * A) ∧
      ∀ (K' : Type) [CommRing K'] (ψ : K →+* K') (A : Matrix (Fin r) (Fin r) K),
        FlagMat hM π fl hf y A → FlagMat hM π fl hf (spMap ψ ≫ y) (A.map ψ) := by
  obtain ⟨W, s, hWV, hp, hs⟩ := GlobalTheory.T.exists_local_adapted_sections Y _ r fl (y (IsLocalRing.closedPoint K)) (π ⁻¹ᵁ V)
    (hV (Set.mem_univ (IsLocalRing.closedPoint K)))
  have hy : ⊤ ≤ y ⁻¹ᵁ W := (Scheme.preimage_eq_top_of_closedPoint_mem y hp).ge
  have h0 := GlobalTheory.T.flag_matrix_of_adapted_coordinates B Y M r hM π fl V f hf K y W hWV hy s hs
  have key : ∀ A, FlagMat hM π fl hf y A → ∃ T : Matrix (Fin r) (Fin r) K, IsUnit T.det ∧
      (∀ i j, i < j → T i j = 0) ∧ (Matrix.of fun i => coordAt hM π hf y hWV hy (s i)) = T * A := by
    intro A hA
    obtain ⟨T, h1, h2⟩ := hA.adapted_eq hWV hy hs
    refine ⟨T, ?_, h1, h2⟩
    have := h0.1
    rw [h2, Matrix.det_mul] at this
    exact isUnit_of_mul_isUnit_left this
  refine ⟨⟨_, h0⟩, fun A A' hA hA' => ?_, fun K' _ ψ A hA => ?_⟩
  · obtain ⟨T, u, l, e⟩ := key A hA
    obtain ⟨T', u', l', e'⟩ := key A' hA'
    refine ⟨T'⁻¹ * T, ?_, lower_mul (lower_inv u' l') l, ?_⟩
    · rw [Matrix.det_mul]
      exact (Matrix.isUnit_nonsing_inv_det _ u').mul u
    · rw [Matrix.mul_assoc, ← e, e', ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ u', Matrix.one_mul]
  · obtain ⟨T, u, l, e⟩ := key A hA
    have hy' : ⊤ ≤ (spMap ψ ≫ y) ⁻¹ᵁ W := fun p _ => hy (Set.mem_univ _)
    have h1 := GlobalTheory.T.flag_matrix_of_adapted_coordinates B Y M r hM π fl V f hf K' (spMap ψ ≫ y) W hWV hy' s hs
    have e1 : (Matrix.of fun i => coordAt hM π hf (spMap ψ ≫ y) hWV hy' (s i)) =
        (Matrix.of fun i => coordAt hM π hf y hWV hy (s i)).map ψ := by
      ext i j
      exact TangentOrigin.evalPt_spMap_comp ψ y W hy hy' _
    have e2 : A.map ψ = (T⁻¹).map ψ * (Matrix.of fun i => coordAt hM π hf (spMap ψ ≫ y) hWV hy' (s i)) := by
      rw [e1, ← Matrix.map_mul, e, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ u, Matrix.one_mul]
    rw [e2]
    refine h1.mul ?_ fun i j h => ?_
    · have := (Matrix.isUnit_nonsing_inv_det _ u).map ψ
      rwa [RingHom.map_det] at this
    · rw [Matrix.map_apply, lower_inv u l i j h, map_zero]

end GlobalTheory.FlagCls

end
