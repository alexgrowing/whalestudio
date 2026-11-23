import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TensorLatticeCoordDegree
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsValues
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.PtHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_lattice_coord_degree : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (Ψ : Type) [Fintype Ψ] (Ei : Type) [AddCommGroup Ei] [Module Ω Ei] (Vl : Ψ → Lat ξ Ei) (m : ℕ) (s : Ψ → Fin m → Ei) (a : K → ℤ) (e₀ : Ω) (hall : ∀ q : X, genPt ξ ⤳ q), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ τ, LinearIndependent Ω (s τ)) → (Lat.tens (fun τ => detLat (Vl τ) (s τ)) (fun _ => -1)).IsDegOn Set.univ y a e₀ → ∀ (L : Type) [Field L] [NumberField L] (w : (Σ k, J k) → L) (z : Sp (𝓞 L) ⟶ X) (c₀ : (k : K) → J k) (g : L) (v : FinitePlace L) (b' : Ψ → Fin m → Ei) (T' : Ψ → Matrix (Fin m) (Fin m) Ω) (T : Ψ → Matrix (Fin m) (Fin m) L), CoordsAt ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w → (∀ k, w ⟨k, c₀ k⟩ ≠ 0) → ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (e₀ * chartMono y c₀ a)⁻¹ g → g ≠ 0 → (∀ τ, (Vl τ).IsFrameAt (b' τ) ⟨z (primeOf v), hall _⟩) → (∀ τ k, b' τ k = ∑ k', T' τ k' k • s τ k') → (∀ τ i j, ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (T' τ i j) (T τ i j)) → (∀ τ, (T τ).det ≠ 0) → (∏ τ, v (T τ).det) * GlobalTheory.CompanionTheory.Ar.RootHt.locRatio a w c₀ v = v g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.FinUnit.det_frames_size | exact GlobalTheory.CompanionTheory.Ar.RootHt.FinUnit.det_frames_size | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.FinUnit.det_frames_size <;> assumption)
