import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSchwartzIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatHatOpenAndContinuous

noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompactAvgSchwartz

variable {D : D7}

theorem mt_mul_inv_self (V : HSp D) (g : GA D V) : Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [map_inv]
  exact Units.mul_inv _

theorem map_cancel {R : Type} [CommRing R] (φ : AE D →+* R) (V : HSp D) (g : GA D V) :
    (Formalism.L2.Theta.mt V g).map φ * (Formalism.L2.Theta.mt V g⁻¹).map φ = 1 := by
  rw [← Matrix.map_mul, mt_mul_inv_self, Matrix.map_one _ (map_zero φ) (map_one φ)]

theorem map_mul_entry {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {m n : ℕ} (M : Matrix (Fin m) (Fin m) R)
    (x : Matrix (Fin m) (Fin n) R) : (fun i j => φ ((M * x) i j)) = fun i j => ∑ c, φ (M i c) * φ (x c j) := by
  simp only [Matrix.mul_apply, map_sum, map_mul]

theorem integrable_and_projS_mem {θ : InfFam D} (hθ : IsInfFam θ) {T : HSp D} {n : ℕ} {K : Subgroup (GA D T)}
    (hK : IsCompact (K : Set (GA D T))) (ν : Measure K) [IsFiniteMeasure ν] {Φ : Mx D T.rank n → ℂ}
    (hΦ : Φ ∈ schwartzA θ T.rank n) :
    (∀ x : Mx D T.rank n, Integrable (fun k : K => Φ (Formalism.L2.Theta.mt T (k : GA D T)⁻¹ ⬝ x)) ν) ∧
      projS ν Φ ∈ schwartzA θ T.rank n := by
  induction hΦ using Submodule.span_induction with
  | zero =>
    refine ⟨fun x => integrable_zero _ _ _, ?_⟩
    have e : projS ν (0 : Mx D T.rank n → ℂ) = 0 := funext fun x => integral_zero _ _
    rw [e]
    exact Submodule.zero_mem _
  | add Φ Ψ _ _ h1 h2 =>
    refine ⟨fun x => (h1.1 x).add (h2.1 x), ?_⟩
    have e : projS ν (Φ + Ψ) = projS ν Φ + projS ν Ψ := funext fun x => integral_add (h1.1 x) (h2.1 x)
    rw [e]
    exact Submodule.add_mem _ h1.2 h2.2
  | smul c Φ _ h1 =>
    refine ⟨fun x => (h1.1 x).smul c, ?_⟩
    have e : projS ν (c • Φ) = c • projS ν Φ := funext fun x => integral_smul c _
    rw [e]
    exact Submodule.smul_mem _ c h1.2
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
    haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
    haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
    haveI : OpensMeasurableSpace K := Subtype.opensMeasurableSpace (K : Set (GA D T))
    have c1 : Continuous fun k : K => Formalism.L2.Theta.mt T (k : GA D T) :=
      (GlobalTheory.RealWeil.continuous_mt T).1.comp continuous_subtype_val
    have c2 : Continuous fun k : K => Formalism.L2.Theta.mt T (k : GA D T)⁻¹ :=
      (GlobalTheory.RealWeil.continuous_mt T).2.comp continuous_subtype_val
    obtain ⟨hint, t, F, ht, hF⟩ := integral_tensor_matrix (n := n) ν
      (fun (k : K) τ => compAt θ τ (Formalism.L2.Theta.mt T (k : GA D T)⁻¹))
      (fun (k : K) τ => compAt θ τ (Formalism.L2.Theta.mt T (k : GA D T)))
      (fun τ => (GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp c2)
      (fun τ => (GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp c1)
      (fun k τ => map_cancel ((θ τ).comp (infPart D)) T k)
      (fun k : K => (Formalism.L2.Theta.mt T (k : GA D T)⁻¹).map (finPart D))
      (fun k : K => (Formalism.L2.Theta.mt T (k : GA D T)).map (finPart D))
      (c2.matrix_map (GlobalTheory.Member.continuous_finPart D)) (c1.matrix_map (GlobalTheory.Member.continuous_finPart D))
      (fun k => map_cancel (finPart D) T k) f hg
    have e : ∀ (M : Mx D T.rank T.rank) (x : Mx D T.rank n),
        f (fun τ i j => compAt θ τ (M ⬝ x) i j) * g (fun i j => finPart D ((M ⬝ x) i j)) =
        f (fun τ i j => ∑ c, compAt θ τ M i c * compAt θ τ x c j) *
          g (fun i j => ∑ c, M.map (finPart D) i c * finPart D (x c j)) := fun M x => by
      have e1 := fun τ => map_mul_entry ((θ τ).comp (infPart D)) M x
      have e2 := map_mul_entry (finPart D) M x
      exact congrArg₂ (· * ·) (congrArg f (funext e1)) (congrArg g e2)
    refine ⟨fun x => ?_, ?_⟩
    · simp only [e]
      exact hint (fun τ i j => compAt θ τ x i j) (fun i j => finPart D (x i j))
    · have e2 : projS ν (fun x : Mx D T.rank n => f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))) =
          ∑ g' ∈ t, fun x : Mx D T.rank n => F g' (fun τ i j => compAt θ τ x i j) * g' (fun i j => finPart D (x i j)) := by
        funext x
        rw [Finset.sum_apply]
        simp only [projS, e]
        exact hF (fun τ i j => compAt θ τ x i j) (fun i j => finPart D (x i j))
      rw [e2]
      exact Submodule.sum_mem _ fun g' hg' => Submodule.subset_span ⟨F g', g', ht g' hg', rfl⟩

theorem projS_mem : ∀ (D : D7), ∀ θ : InfFam D, IsInfFam θ → ∀ (T : HSp D) (n : ℕ) (K : Subgroup (GA D T)),
    IsCompact (K : Set (GA D T)) → ∀ ν : Measure K, IsProbabilityMeasure ν → ∀ Φ ∈ schwartzA θ T.rank n,
      projS ν Φ ∈ schwartzA θ T.rank n :=
  fun _ _ hθ _ _ _ hK ν _ _ hΦ => (integrable_and_projS_mem hθ hK ν hΦ).2

end GlobalTheory.CompactAvgSchwartz

end
