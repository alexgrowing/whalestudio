import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNormDegGCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJmuFacts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormBallVolumes
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.UniformCoefficientBounds.CoefBoundUniform

open Matrix MeasureTheory Set
open scoped ContDiff InnerProductSpace ENNReal

noncomputable section

namespace CompanionTheory.D.Upq.Coef

open CompanionTheory.D.Upq.Sm Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Formalism.FourierDecayAlt.P.CutBP.Jmu Formalism.FourierDecayAlt.P.CutBP.Jmu.NDG

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Deriv

variable {k r : ℕ} {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup E] [NormedSpace ℂ E] {G : Set (B.Mat k r)} {σ : B.Mat k r → (H →L[ℂ] H)}

def cf (σ : B.Mat k r → (H →L[ℂ] H)) (x₀ : E) (a b : H) (g : B.Mat k r) : E := ⟪a, σ g b⟫_ℂ • x₀

theorem rw_cf (h : RepOn G σ) (x₀ : E) (a : H) {b : H} (hb : IsSm G σ b) :
    ∀ {v : List (B.Mat k r)}, LieW G v → ∀ g ∈ G,
      B.Rw v (cf σ x₀ a b) g = cf σ x₀ a (dsW σ v b) g
  | [], _, _, _ => rfl
  | X :: v, hv, g, hg => by
    have hv' : LieW G v := fun Y hY => hv Y (List.mem_cons_of_mem _ hY)
    have hX := hv X List.mem_cons_self
    change deriv (fun t : ℝ => B.Rw v (cf σ x₀ a b) (g * ex X t)) 0 = _
    have e : (fun t : ℝ => B.Rw v (cf σ x₀ a b) (g * ex X t)) =
        fun t => ⟪a, σ g (σ (ex X t) (dsW σ v b))⟫_ℂ • x₀ := by
      ext1 t
      rw [rw_cf h x₀ a hb hv' _ (h.mul_mem _ hg _ (hX t)), cf, h.apply_mul hg (hX t)]
    rw [e]
    have h1 := ((hb.dsW h hv').differentiableAt h hX).hasDerivAt
    let L : H →L[ℝ] E := (((innerSL ℂ a).comp (σ g)).smulRight x₀).restrictScalars ℝ
    exact (L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1).deriv

theorem lw_cf (h : RepOn G σ) (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖) (x₀ : E) {a : H}
    (ha : IsSm G σ a) (b : H) {f : B.Mat k r → E} (hf : ∀ g ∈ G, f g = cf σ x₀ a b g) :
    ∀ {u : List (B.Mat k r)}, LieW G u → ∀ g ∈ G,
      u.foldr B.LdV f g = cf σ x₀ (dsW σ u a) b g
  | [], _, g, hg => hf g hg
  | X :: u, hu, g, hg => by
    have hu' : LieW G u := fun Y hY => hu Y (List.mem_cons_of_mem _ hY)
    have hX := hu X List.mem_cons_self
    change deriv (fun t : ℝ => u.foldr B.LdV f (NormedSpace.exp (-((t : ℂ) • X)) * g)) 0 = _
    have e : (fun t : ℝ => u.foldr B.LdV f (NormedSpace.exp (-((t : ℂ) • X)) * g)) =
        fun t => ⟪σ (ex X t) (dsW σ u a), σ g b⟫_ℂ • x₀ := by
      ext1 t
      have e1 : NormedSpace.exp (-((t : ℂ) • X)) = ex X (-t) := by simp [ex]
      rw [e1, lw_cf h hiso x₀ ha b hf hu' _ (h.mul_mem _ (hX _) _ hg), cf]
      let I : H →ₗᵢ[ℂ] H := ⟨σ (ex X t), hiso _ (hX t)⟩
      rw [← I.inner_map_map]
      change ⟪σ (ex X t) _, σ (ex X t) (σ (ex X (-t) * g) b)⟫_ℂ • x₀ = _
      rw [← h.apply_mul (hX t) (h.mul_mem _ (hX _) _ hg), ← Matrix.mul_assoc, ← ex_add,
        add_neg_cancel, ex_zero, Matrix.one_mul]
    rw [e]
    have h1 := ((ha.dsW h hu').differentiableAt h hX).hasDerivAt
    have h2 := (h1.inner ℂ (hasDerivAt_const (0 : ℝ) (σ g b))).smul_const x₀
    rw [h2.deriv]
    simp [cf, dsW_cons, ds]

theorem dLR_cf (h : RepOn G σ) (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖) (x₀ : E) {a b : H}
    (ha : IsSm G σ a) (hb : IsSm G σ b) {u v : List (B.Mat k r)} (hu : LieW G u) (hv : LieW G v)
    {g : B.Mat k r} (hg : g ∈ G) :
    B.dLR u v (cf σ x₀ a b) g = cf σ x₀ (dsW σ u a) (dsW σ v b) g :=
  lw_cf h hiso x₀ ha _ (rw_cf h x₀ a hb hv) hu g hg

end Deriv

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq]

end CompanionTheory.D.Upq.Coef

end
