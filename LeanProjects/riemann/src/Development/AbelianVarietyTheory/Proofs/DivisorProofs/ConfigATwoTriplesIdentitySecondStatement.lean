import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigATwoTriplesIdentitySecond
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_a_two_triples_identity_second : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    CfgA B G G₁ H H' → IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K →
    (∀ y : Fin (b + 2) → AE F E, Continuous fun p : KAt K (evI F) × idelesAt E (evI F) =>
        GlobalTheory.ArchUniq.omega (GlobalTheory.ArchUniq.trP F (Fin (b + 2) × Fin (b + 2 + a')))
          (GlobalTheory.ArchUniq.Coord.coordI G.M (shiftA H H' p.2.1))
          (GlobalTheory.ArchUniq.Coord.coordI G.M (Matrix.vecMulVec (mat p.1.1 *ᵥ y) (incV F H'.x)))) →
    ∃ (m : ℕ) (yv : Fin m → Fin (b + 2) → AE F E) (W' : Set (EuclideanSpace ℝ (Fin m))),
      let π : KAt K (evI F) × idelesAt E (evI F) → EuclideanSpace ℝ (Fin m) := fun p =>
        WithLp.toLp 2 fun i => -GlobalTheory.ArchUniq.omega (GlobalTheory.ArchUniq.trP F (Fin (b + 2) × Fin (b + 2 + a')))
          (GlobalTheory.ArchUniq.Coord.coordI G.M (shiftA H H' p.2.1))
          (GlobalTheory.ArchUniq.Coord.coordI G.M (Matrix.vecMulVec (mat p.1.1 *ᵥ yv i) (incV F H'.x)))
      IsOpen W' ∧ π (1, 1) ∈ W' ∧ (∀ S, IsCompact S → S ⊆ W' → IsCompact (π ⁻¹' S)) ∧
      ∀ p, π p = π (1, 1) → mat p.1.1⁻¹ *ᵥ ((p.2.1 : AE F E) • incV F H.x) = incV F H.x := by
  first | exact @GlobalTheory.ConeProper.main | exact GlobalTheory.ConeProper.main | (intros; apply GlobalTheory.ConeProper.main <;> assumption)
