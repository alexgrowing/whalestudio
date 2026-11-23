import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniREqUni
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentTriangularFactorUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagFramesTriangularChangeStatement

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB
open GlobalTheory.FlagFibre (Low)

namespace GlobalTheory.FlagCell

theorem low_eq_of_spans_pullCol (X B : Scheme.{0}) (g : X ⟶ B) (E : B.Modules) (m : ℕ) (hE : IsVB E m)
    (U : B.Opens) (e : Fin m → Γ(E, U)) (he : IsFrame e)
    (fl : Vert.Flag ((Scheme.Modules.pullback g).obj E) m) (V : X.Opens) (hV : V ≤ g ⁻¹ᵁ U)
    (n n' : Low m → Γ(X, V)) (h : Spans fl V (pullCol g e hV (uniR n)))
    (h' : Spans fl V (pullCol g e hV (uniR n'))) : n = n' := by
  classical
  haveI := hE.isQuasicoherent
  obtain ⟨M, hM, hdet, hMv⟩ := GlobalTheory.T.flag_frames_triangular_change X _ m fl V _ _ h h'
  have hinj := ((he.pullback g) V hV).1
  have e1 : (fun i => GlobalTheory.Twist.resM ((Scheme.Modules.pullback g).obj E) hV
      (QCoh.pullbackSections g E (le_refl (g ⁻¹ᵁ U)) (e i))) =
      fun i => QCoh.pullbackSections g E hV (e i) :=
    funext fun i => QCoh.res_pullbackSections _ _ _ _ _
  rw [e1] at hinj
  have key : uniR n * M = uniR n' * 1 := by
    rw [Matrix.mul_one]
    refine Matrix.ext fun l j => ?_
    have := hinj (a₁ := fun l => (uniR n * M) l j) (a₂ := fun l => uniR n' l j) (by
      simp only [Fintype.linearCombination_apply]
      have h1 := hMv j
      simp only [pullCol] at h1
      rw [h1]
      simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      rw [mul_comm])
    exact congrFun this l
  exact GlobalTheory.T.unipotent_triangular_factor_unique _ m n n' M 1 hM Matrix.blockTriangular_one hdet key

end GlobalTheory.FlagCell
