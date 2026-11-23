import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CounitCotangentClassPowerSeriesEvalAtNilpotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentEvalCommutesSubstAndAlgebraMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesAlgHomExtOfIsNilpotentXStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalAtNilpotentXEqCoordinateStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz

theorem semiHom_constantCoeff_and_ev : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G) (φ : Fin d → MvPowerSeries (Fin e) k'), (∀ n j, c'.ev n (φ j) = s.app n (c.x n j)) → (∀ j, constantCoeff (φ j) = 0) ∧ ∀ n g, c'.ev n (subst φ (MvPowerSeries.map σ g)) = s.app n (c.ev n g) := by
  intro p k k' _ _ σ d e G G' c c' s φ hφ
  have hconst : ∀ j, constantCoeff (φ j) = 0 := fun j => by
    have h1 := (GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k' e (G'.A 0) (c'.x 0) (c'.nil 0) (c'.aug 0) (φ j)).1
    change Coalgebra.counit (R := k') (c'.ev 0 (φ j)) = _ at h1
    rw [← h1, hφ 0 j, (s.app 0).counit_map, c.aug, map_zero]
  refine ⟨hconst, fun n g => ?_⟩
  have hy : ∀ j, IsNilpotent (s.app n (c.x n j)) := fun j => (c.nil n j).map (s.app n).toRingHom
  have h1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k' (Fin d) (G'.A n)).1 (Fin e) (c'.ev n)
    (fun t => by
      change IsNilpotent (evA k' (c'.x n) (c'.nil n) (X t))
      rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate]; exact c'.nil n t) φ hconst _ hy (fun j => hφ n j) (MvPowerSeries.map σ g)
  rw [h1]
  letI : Algebra k (G'.A n) := ((algebraMap k' (G'.A n)).comp σ).toAlgebra
  let S : G.A n →ₐ[k] G'.A n :=
    { (s.app n).toRingHom with commutes' := fun r => (s.app n).map_algebraMap r }
  have h2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d) (G.A n)).2 (G'.A n) S (c.x n) (c.nil n) _ hy (fun _ => rfl) g
  change _ = S (evA k (c.x n) (c.nil n) g)
  rw [h2]
  let M : MvPowerSeries (Fin d) k →ₐ[k] G'.A n :=
    { (evA k' _ hy : MvPowerSeries (Fin d) k' →+* G'.A n).comp (MvPowerSeries.map σ) with
      commutes' := fun r => by
        change evA k' _ hy (MvPowerSeries.map σ (algebraMap k _ r)) = algebraMap k' _ (σ r)
        rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          MvPowerSeries.map_C, ← (evA k' _ hy).commutes (σ r), MvPowerSeries.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply] }
  have hM : M = evA k _ hy := GlobalTheory.T.mvPowerSeries_algHom_ext_of_isNilpotent_X k (Fin d) (G'.A n) M _
    (fun i => by
      change IsNilpotent (evA k' _ hy (MvPowerSeries.map σ (X i)))
      rw [MvPowerSeries.map_X, GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate]; exact hy i)
    (fun i => by
      change evA k' _ hy (MvPowerSeries.map σ (X i)) = _
      rw [MvPowerSeries.map_X, GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate, GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate])
  exact AlgHom.congr_fun hM g

end GlobalTheory.Katz
