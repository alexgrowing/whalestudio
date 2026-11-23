import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.EmDefs

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open PositivityTheory.Rg.Rsw.Em
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.AlgStab

section Gen
variable {R : Type} [CommRing R] {a n : ℕ}

private noncomputable def twoSide [TopologicalSpace R] [IsTopologicalRing R] (h hi : Matrix (Fin a) (Fin a) R)
    (g gi : Matrix (Fin n) (Fin n) R) (h1 : h * hi = 1) (h2 : hi * h = 1) (g1 : g * gi = 1) (g2 : gi * g = 1) :
    Matrix (Fin a) (Fin n) R ≃ₜ Matrix (Fin a) (Fin n) R where
  toFun X := h * X * g
  invFun X := hi * X * gi
  left_inv X := by
    show hi * (h * X * g) * gi = X
    rw [Matrix.mul_assoc h, ← Matrix.mul_assoc hi, h2, Matrix.one_mul, Matrix.mul_assoc, g1, Matrix.mul_one]
  right_inv X := by
    show h * (hi * X * gi) * g = X
    rw [Matrix.mul_assoc hi, ← Matrix.mul_assoc h, h1, Matrix.one_mul, Matrix.mul_assoc, g2, Matrix.mul_one]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

private theorem map_inv {S : Type} [CommRing S] (f : R →+* S) {x y : Matrix (Fin a) (Fin a) R} (h : x * y = 1) :
    x.map f * y.map f = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero f) (map_one f)]

private theorem map_eq_one {S : Type} [CommRing S] (f : R →+* S) {e : R} (he : f e = 0) {x : Matrix (Fin a) (Fin a) R}
    (h : e • (x - 1) = x - 1) : x.map f = 1 := by
  have h0 : (x - 1).map f = 0 := by
    rw [← h]
    ext i j
    simp [he]
  rw [Matrix.map_sub _ (map_sub f), Matrix.map_one _ (map_zero f) (map_one f)] at h0
  exact sub_eq_zero.1 h0

private noncomputable def famEquiv {T : Type} [Fintype T] (h hi : T → Matrix (Fin a) (Fin a) ℂ) (g gi : T → Matrix (Fin n) (Fin n) ℂ)
    (h1 : ∀ τ, h τ * hi τ = 1) (h2 : ∀ τ, hi τ * h τ = 1) (g1 : ∀ τ, g τ * gi τ = 1) (g2 : ∀ τ, gi τ * g τ = 1) :
    (T → Fin a → Fin n → ℂ) ≃L[ℝ] (T → Fin a → Fin n → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun X τ => (h τ * Matrix.of (X τ) * g τ : Matrix (Fin a) (Fin n) ℂ)
      invFun := fun X τ => (hi τ * Matrix.of (X τ) * gi τ : Matrix (Fin a) (Fin n) ℂ)
      map_add' := fun X Y => by
        funext τ
        show h τ * (Matrix.of (X τ) + Matrix.of (Y τ)) * g τ = h τ * Matrix.of (X τ) * g τ + h τ * Matrix.of (Y τ) * g τ
        rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c X => by
        funext τ
        show h τ * (c • Matrix.of (X τ)) * g τ = c • (h τ * Matrix.of (X τ) * g τ)
        rw [Matrix.mul_smul, Matrix.smul_mul]
      left_inv := fun X => funext fun τ => (twoSide (h τ) (hi τ) (g τ) (gi τ) (h1 τ) (h2 τ) (g1 τ) (g2 τ)).left_inv (Matrix.of (X τ))
      right_inv := fun X => funext fun τ => (twoSide (h τ) (hi τ) (g τ) (gi τ) (h1 τ) (h2 τ) (g1 τ) (g2 τ)).right_inv (Matrix.of (X τ)) }

end Gen

private theorem schw {D : D7} (θ : InfFam D) {a n : ℕ} (h : GL (Fin a) (AE D)) (g : GL (Fin n) (AE D)) {Φ : Mx D a n → ℂ}
    (hΦ : Φ ∈ schwartzA θ a n) : (fun X => Φ (mm (mm h.1 X) g.1)) ∈ schwartzA θ a n := by
  induction hΦ using Submodule.span_induction with
  | zero => exact Submodule.zero_mem _
  | add f₁ f₂ _ _ i₁ i₂ => exact Submodule.add_mem _ i₁ i₂
  | smul c f _ i => exact Submodule.smul_mem _ c i
  | mem Φ hm =>
    obtain ⟨f, k, hk, rfl⟩ := hm
    haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) := by first | infer_instance | exact GlobalTheory.AdelicU.isTopologicalRing_tens | exact isTopologicalRing_tens
    let ρ : D.what₂.Tau → (AE D →+* ℂ) := fun τ => (θ τ).comp (infPart D)
    let L := famEquiv (fun τ => h.1.map (ρ τ)) (fun τ => h.2.map (ρ τ)) (fun τ => g.1.map (ρ τ)) (fun τ => g.2.map (ρ τ))
      (fun τ => map_inv _ h.3) (fun τ => map_inv _ h.4) (fun τ => map_inv _ g.3) (fun τ => map_inv _ g.4)
    let H := twoSide (h.1.map (finPart D)) (h.2.map (finPart D)) (g.1.map (finPart D)) (g.2.map (finPart D))
      (map_inv _ h.3) (map_inv _ h.4) (map_inv _ g.3) (map_inv _ g.4)
    refine Submodule.subset_span ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L f, fun y => k (H y),
      ⟨hk.1.comp_continuous H.continuous, hk.2.comp_homeomorph H⟩, ?_⟩
    funext X
    have e1 : (fun τ i j => compAt θ τ (mm (mm h.1 X) g.1) i j) = L (fun τ i j => compAt θ τ X i j) := by
      funext τ
      show (h.1 * X * g.1).map (ρ τ) = h.1.map (ρ τ) * X.map (ρ τ) * g.1.map (ρ τ)
      rw [Matrix.map_mul, Matrix.map_mul]
    have e2 : (fun i j => finPart D (mm (mm h.1 X) g.1 i j)) = H (fun i j => finPart D (X i j)) := by
      show (h.1 * X * g.1).map (finPart D) = h.1.map (finPart D) * X.map (finPart D) * g.1.map (finPart D)
      rw [Matrix.map_mul, Matrix.map_mul]
    show f (fun τ i j => compAt θ τ (mm (mm h.1 X) g.1) i j) * k (fun i j => finPart D (mm (mm h.1 X) g.1 i j)) = _
    rw [e1, e2]
    rfl

end GlobalTheory.CompanionTheory.AlgStab

open GlobalTheory.CompanionTheory.AlgStab in
theorem GlobalTheory.CompanionTheory.AlgStab.algStab : IdemEx → AlgStab := by
  intro _ D θ _ a n S e he h g hh hg Φ hΦ hG hC
  refine ⟨schw θ h g hΦ, fun X => ?_, ?_⟩
  · have hI : IntOff S (mm (mm h.1 X) g.1) ↔ IntOff S X := by
      refine forall_congr' fun v => forall_congr' fun hv => ?_
      have h0 : cv D v e = 0 := by rw [he.2 v, if_neg hv]
      have : (h.1 * X * g.1).map (cv D v) = X.map (cv D v) := by
        rw [Matrix.map_mul, Matrix.map_mul, map_eq_one _ h0 hh, map_eq_one _ h0 hg, Matrix.one_mul, Matrix.mul_one]
      refine forall_congr' fun i => forall_congr' fun j => ?_
      rw [show cv D v (mm (mm h.1 X) g.1 i j) = cv D v (X i j) from congrFun (congrFun this i) j]
    have hs : e • mm (mm h.1 X) g.1 = mm (mm h.1 (e • X)) g.1 := by
      show e • (h.1 * X * g.1) = h.1 * (e • X) * g.1
      rw [Matrix.mul_smul, Matrix.smul_mul]
    have := hG (mm (mm h.1 X) g.1)
    by_cases hX : IntOff S X
    · rw [if_pos (hI.2 hX), hs] at this
      rw [if_pos hX]
      exact this
    · rw [if_neg (fun c => hX (hI.1 c))] at this
      rw [if_neg hX]
      exact this
  · haveI : IsTopologicalRing (AE D) := by first | infer_instance | exact GlobalTheory.AdelicU.isTopologicalRing_tens | exact isTopologicalRing_tens
    exact hC.comp_homeomorph (twoSide h.1 h.2 g.1 g.2 h.3 h.4 g.3 g.4)
