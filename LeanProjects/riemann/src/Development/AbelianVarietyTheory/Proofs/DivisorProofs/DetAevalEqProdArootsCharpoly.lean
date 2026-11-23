import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DetAevalRoots

open Polynomial

theorem det_aeval_X_sub_C {Ω : Type} [Field Ω] [IsAlgClosed Ω] {n : ℕ}
    (N : Matrix (Fin n) (Fin n) Ω) (r : Ω) :
    (aeval N (Polynomial.X - C r)).det
      = (N.charpoly.roots.map fun a => (Polynomial.X - C r).eval a).prod := by
  have hs := IsAlgClosed.splits N.charpoly
  have hR : Multiset.card N.charpoly.roots = n := by
    rw [← hs.natDegree_eq_card_roots, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have h : aeval N (Polynomial.X - C r) = -(Matrix.scalar (Fin n) r - N) := by
    simp [Matrix.algebraMap_eq_diagonal]
  rw [h, Matrix.det_neg, Fintype.card_fin, ← Matrix.eval_charpoly]
  conv_lhs => rw [hs.eq_prod_roots_of_monic (Matrix.charpoly_monic N)]
  rw [eval_multiset_prod, Multiset.map_map]
  simp only [Function.comp_def, eval_sub, eval_X, eval_C]
  have e2 : (N.charpoly.roots.map fun x => x - r)
      = (N.charpoly.roots.map fun x => r - x).map Neg.neg := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl (fun _ _ => by simp)
  rw [e2, Multiset.prod_map_neg, Multiset.card_map, hR]

theorem det_aeval_eq_prod_roots {Ω : Type} [Field Ω] [IsAlgClosed Ω] {n : ℕ}
    (N : Matrix (Fin n) (Fin n) Ω) (G : Polynomial Ω) :
    (aeval N G).det = (N.charpoly.roots.map fun a => G.eval a).prod := by
  have hs := IsAlgClosed.splits N.charpoly
  have hR : Multiset.card N.charpoly.roots = n := by
    rw [← hs.natDegree_eq_card_roots, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have key : ∀ (c : Ω) (s : Multiset Ω),
      (aeval N (C c * (s.map fun r => Polynomial.X - C r).prod)).det
        = (N.charpoly.roots.map fun a =>
            (C c * (s.map fun r => Polynomial.X - C r).prod).eval a).prod := by
    intro c s
    induction s using Multiset.induction_on with
    | empty =>
      simp [Matrix.algebraMap_eq_diagonal, Matrix.det_diagonal, hR]
    | cons r s ih =>
      have e : C c * ((r ::ₘ s).map fun r => Polynomial.X - C r).prod
          = (Polynomial.X - C r) * (C c * (s.map fun r => Polynomial.X - C r).prod) := by
        rw [Multiset.map_cons, Multiset.prod_cons]; ring
      rw [e, map_mul, Matrix.det_mul, ih, det_aeval_X_sub_C, ← Multiset.prod_map_mul]
      simp only [eval_mul]
  have hG := C_leadingCoeff_mul_prod_multiset_X_sub_C
    ((IsAlgClosed.splits G).natDegree_eq_card_roots).symm
  rw [← hG]
  exact key _ _

end GlobalTheory.DetAevalRoots

open Polynomial in

theorem GlobalTheory.det_aeval_eq_prod_aroots_charpoly : ∀ (k Ω V : Type) [Field k] [Field Ω] [IsAlgClosed Ω] [Algebra k Ω] [AddCommGroup V] [Module k V] [Module.Finite k V] (φ : V →ₗ[k] V) (F : Polynomial k), algebraMap k Ω (LinearMap.det (Polynomial.aeval φ F)) = ((φ.charpoly.aroots Ω).map (fun a => Polynomial.aeval a F)).prod := by
  intro k Ω V _ _ _ _ _ _ _ φ F
  let b := Module.finBasis k V
  let f := algebraMap k Ω
  have h1 : LinearMap.det (aeval φ F) = (aeval (LinearMap.toMatrix b b φ) F).det := by
    rw [← LinearMap.det_toMatrix b]
    congr 1
    exact (aeval_algHom_apply (LinearMap.toMatrixAlgEquiv b).toAlgHom φ F).symm
  have h2 : f.mapMatrix (aeval (LinearMap.toMatrix b b φ) F)
      = aeval ((LinearMap.toMatrix b b φ).map f) (F.map f) := by
    refine map_aeval_eq_aeval_map (φ := f) (ψ := RingHom.mapMatrix (m := Fin (Module.finrank k V)) f) ?_ F _
    ext x i j
    simp [Matrix.algebraMap_matrix_apply, apply_ite f]
  have h3 : φ.charpoly.aroots Ω = ((LinearMap.toMatrix b b φ).map f).charpoly.roots := by
    rw [Matrix.charpoly_map, LinearMap.charpoly_toMatrix]
  rw [h1, RingHom.map_det, h2, h3, GlobalTheory.DetAevalRoots.det_aeval_eq_prod_roots]
  simp only [eval_map_algebraMap, f]
