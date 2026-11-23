import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicOrbitOrthogonalAtPlace
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplittingSplitOm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_orbit_orthogonal_at_place' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ r s r' s' i₀ i₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (M : Model σ X W),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ v : Pl F,
    (∀ u ∈ iso0 (F := F) n H', At (evFin F v) u → ∀ u' ∈ iso0 (F := F) n H', At (evFin F v) u' →
      (GlobalTheory.LatVac.locCo M.co v u).1 ⬝ᵥ (GlobalTheory.LatVac.locCo M.co v u').2 -
        (GlobalTheory.LatVac.locCo M.co v u').1 ⬝ᵥ (GlobalTheory.LatVac.locCo M.co v u).2 = 0) ∧
    ∀ w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v),
      (∀ u ∈ iso0 (F := F) n H', At (evFin F v) u →
        (GlobalTheory.LatVac.locCo M.co v u).1 ⬝ᵥ w.2 - w.1 ⬝ᵥ (GlobalTheory.LatVac.locCo M.co v u).2 = 0) →
      ∃ u ∈ iso0 (F := F) n H', At (evFin F v) u ∧ ∃ z : Matrix (Fin n) (Fin d₁) (AE F E), At (evFin F v) z ∧
        w = GlobalTheory.LatVac.locCo M.co v u +
          GlobalTheory.LatVac.locCo M.co v (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) := by
  first | exact @GlobalTheory.IsoOrthLoc.isotropic_orbit_orthogonal_at_place | exact GlobalTheory.IsoOrthLoc.isotropic_orbit_orthogonal_at_place | (intros; apply GlobalTheory.IsoOrthLoc.isotropic_orbit_orthogonal_at_place <;> assumption)
