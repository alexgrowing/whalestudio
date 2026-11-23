import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteSpanNatCastOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiePairingCanonicalRigidifiedExtensionTangentStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem exists_lie_comp_psi_eq : ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 → ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → LieExact A → (∃ N' : Submodule R (primDR A), IsCompl (PrimitiveSubmodule A) N') → ∀ (G : PDivGroup p R) (t : G.TorsionTower A) (ψ : PrimitiveSubmodule A →ₗ[R] G.omega), (∀ c : PrimitiveSubmodule A, IsCan t c.1 (G.rigOfOmega (ψ c))) → ∀ l : Module.Dual R (PrimitiveSubmodule A), ∃ x : G.Lie, ∀ c, x (ψ c) = l c := by
  intro p _ R _ N hN A _ hab hLE hN' G t ψ hψ l
  obtain ⟨N', hc⟩ := hN'
  let h : HdR A := l ∘ₗ Submodule.projectionOnto (PrimitiveSubmodule A) N' hc
  obtain ⟨v, hv, -⟩ := hLE.1 h
  haveI := isAdicComplete_span_natCast_of_isNilpotent p R ⟨N, hN⟩
  obtain ⟨x, hx, -⟩ := t.existsUnique_lieCorr hv.1
  refine ⟨x, fun c => ?_⟩
  obtain ⟨⟨c, hc1⟩, hc2⟩ := c
  have hc3 : c ∈ F1 (A.hom ≫ 𝟙 _) := hc2
  rw [hodgeFiltration_eq_range] at hc3
  obtain ⟨β, rfl⟩ := hc3
  rw [GlobalTheory.T.lie_pairing_canonical_rigidified_extension_tangent p R N hN A hab G t ψ hψ β hc1 hc2 x v hx, ← hv.2 β hc1]
  change l (Submodule.projectionOnto (PrimitiveSubmodule A) N' hc ⟨_, hc1⟩) = _
  exact congrArg l (Submodule.projectionOnto_apply_left hc ⟨⟨_, hc1⟩, hc2⟩)

end GlobalTheory.PtExt
