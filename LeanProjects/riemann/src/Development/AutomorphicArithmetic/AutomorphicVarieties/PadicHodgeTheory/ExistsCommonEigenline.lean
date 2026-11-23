import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsColumnVector
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BlockConjugation
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ex_col {k : Type} [Field k] {n : ℕ} (v : Fin (n + 1) → k) (hv : v ≠ 0) :
    ∃ q : GL (Fin (n + 1)) k, (q : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ Pi.single 0 1 = v :=
  _root_.UpperTheory.Reformulated.B.ExistsColumnVector.ex_col v hv

theorem UpperTheory.exists_common_eigenline :
    ∀ {H k : Type} [Group H] [TopologicalSpace H] [Field k] [TopologicalSpace k] [IsTopologicalRing k] {n : ℕ} (r : H →* GL (Fin (n + 1)) k) (κ : Fin (n + 1) → H →* kˣ) (v : Fin (n + 1) → k), Continuous r → v ≠ 0 → (∀ g, (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ v = (κ 0 g : k) • v) → ∃ (p : GL (Fin (n + 1)) k) (r₁ : H →* GL (Fin (n + 1)) k) (r' : H →* GL (Fin n) k), (∀ g, r₁ g = p * r g * p⁻¹) ∧ Continuous r₁ ∧ Continuous r' ∧ (∀ g (i : Fin n), (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i.succ 0 = 0) ∧ (∀ g, (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) 0 0 = (κ 0 g : k)) ∧ (∀ g (i j : Fin n), (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i.succ j.succ = (r' g : Matrix (Fin n) (Fin n) k) i j) ∧ (HasFlag r' (fun i => κ i.succ) → HasFlag r κ) :=
  _root_.UpperTheory.Reformulated.B.BlockConjugation.exists_common_eigenline
