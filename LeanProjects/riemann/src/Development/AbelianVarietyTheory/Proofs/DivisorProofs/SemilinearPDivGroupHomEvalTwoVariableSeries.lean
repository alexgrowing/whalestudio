import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalAtNilpotentXEqCoordinateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesAlgHomExtOfIsNilpotentXStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CounitCotangentClassPowerSeriesEvalAtNilpotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedChartEvalSquareVariablesSwapConstantStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem semiHom_ev₂_pull2 : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G) (φ : Fin d → MvPowerSeries (Fin e) k'), (∀ n j, c'.ev n (φ j) = s.app n (c.x n j)) → ∀ n t, c'.ev₂ n (pull2 φ (MvPowerSeries.map σ t)) = (s.app n).two (c.ev₂ n t) := by
  intro p k k' _ _ σ d e G G' c c' s φ hφ n t
  have hev := GlobalTheory.T.connectedChart_evalSquare_variables_swap_constant p k' e G' c' n
  let a : Fin d ⊕ Fin d → MvPowerSeries (Fin e ⊕ Fin e) k' :=
    Sum.elim (fun j => inL (φ j)) (fun j => inR (φ j))
  have ha : ∀ i, constantCoeff (a i) = 0 := by
    intro i
    have hc := hev.2.2.2
    cases i with
    | inl j =>
      change constantCoeff (inL (φ j)) = 0
      rw [← hc, hev.1, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      change Coalgebra.counit (R := k') (c'.ev n (φ j)) = 0
      rw [hφ n j, (s.app n).counit_map, c.aug, map_zero]
    | inr j =>
      change constantCoeff (inR (φ j)) = 0
      rw [← hc, hev.2.1, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      change Coalgebra.counit (R := k') (c'.ev n (φ j)) = 0
      rw [hφ n j, (s.app n).counit_map, c.aug, map_zero]
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  let B := G'.A n ⊗[k'] G'.A n
  letI : Algebra k B := ((algebraMap k' B).comp σ).toAlgebra
  let u : G.A n →ₐ[k] B :=
    { ((Algebra.TensorProduct.includeLeft : G'.A n →ₐ[k'] B) : G'.A n →+* B).comp
        (s.app n).toRingHom with
      commutes' := fun r => by
        change Algebra.TensorProduct.includeLeft (R := k') (S := k') ((s.app n) (algebraMap k (G.A n) r)) = _
        rw [(s.app n).map_algebraMap, AlgHom.commutes]; rfl }
  let v : G.A n →ₐ[k] B :=
    { ((Algebra.TensorProduct.includeRight : G'.A n →ₐ[k'] B) : G'.A n →+* B).comp
        (s.app n).toRingHom with
      commutes' := fun r => by
        change Algebra.TensorProduct.includeRight (R := k') ((s.app n) (algebraMap k (G.A n) r)) = _
        rw [(s.app n).map_algebraMap, AlgHom.commutes]; rfl }
  let T : G.A n ⊗[k] G.A n →ₐ[k] B := Algebra.TensorProduct.lift u v (fun _ _ => Commute.all _ _)
  have hT : ∀ z, T z = (s.app n).two z := fun z => by
    induction z with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul x y =>
      rw [Algebra.TensorProduct.lift_tmul, TensorProduct.map_tmul]
      change ((s.app n) x ⊗ₜ[k'] 1) * (1 ⊗ₜ[k'] (s.app n) y) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]; rfl
  let L : MvPowerSeries (Fin d ⊕ Fin d) k →ₐ[k] B :=
    { (c'.ev₂ n).toRingHom.comp
        ((substAlgHom (R := k') hs).toRingHom.comp
          (MvPowerSeries.map σ)) with
      commutes' := fun r => by
        change c'.ev₂ n (substAlgHom (R := k') hs (MvPowerSeries.map σ (C r))) = algebraMap k' B (σ r)
        rw [MvPowerSeries.map_C, show (C (σ r) : MvPowerSeries (Fin d ⊕ Fin d) k') =
          algebraMap k' _ (σ r) by rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply],
          AlgHom.commutes, AlgHom.commutes] }
  have hL : ∀ f, L f = c'.ev₂ n (pull2 φ (MvPowerSeries.map σ f)) := fun f => by
    change c'.ev₂ n (substAlgHom hs (MvPowerSeries.map σ f)) = _
    rw [coe_substAlgHom]; rfl
  have key : T.comp (c.ev₂ n) = L := by
    refine GlobalTheory.T.mvPowerSeries_algHom_ext_of_isNilpotent_X k (Fin d ⊕ Fin d) B _ _ (fun i => ?_) (fun i => ?_)
    · rw [AlgHom.comp_apply]
      change IsNilpotent (T (evA k (c.x₂ n) (c.nil₂ n) (X i)))
      rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate]; exact (c.nil₂ n i).map T
    · rw [AlgHom.comp_apply, hL, hT, MvPowerSeries.map_X]
      change (s.app n).two (evA k (c.x₂ n) (c.nil₂ n) (X i)) = c'.ev₂ n (subst a (X i))
      rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate, subst_X hs]
      cases i with
      | inl j =>
        change (s.app n).two (c.x n j ⊗ₜ 1) = c'.ev₂ n (inL (φ j))
        rw [hev.1, hφ n j, TensorProduct.map_tmul, SemiBialgHom.lin_apply, SemiBialgHom.lin_apply]
        congr 1; exact map_one (s.app n).toRingHom
      | inr j =>
        change (s.app n).two (1 ⊗ₜ c.x n j) = c'.ev₂ n (inR (φ j))
        rw [hev.2.1, hφ n j, TensorProduct.map_tmul, SemiBialgHom.lin_apply, SemiBialgHom.lin_apply]
        congr 1; exact map_one (s.app n).toRingHom
  rw [← hL, ← key, AlgHom.comp_apply, hT]

end GlobalTheory.Katz
