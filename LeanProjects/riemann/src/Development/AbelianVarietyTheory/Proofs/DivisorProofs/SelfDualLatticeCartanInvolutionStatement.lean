import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeCartanInvolution
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_dual_lattice_cartan_involution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (B : Base F E) (n : ℕ) (W : Spc F E n),
    (∀ i j, σ (W.J j i) = -W.J i j) → W.L.IsLattice E →
    (∀ y, y ∈ W.L ↔ ∀ x ∈ W.L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * form σ W.J y x))) →
    (∀ w, IsCartan (Complex.I • W.J.map (B.emb w).1) (W.θ w)) →
    ∀ W₂ : Spc F E (n + n), W₂.J = dblGram finSumFinEquiv W.J → W₂.L = sumLat finSumFinEquiv W.L W.L →
    (∀ w, W₂.θ w = blkMat finSumFinEquiv (W.θ w) (-W.θ w)) →
    ∃ K₂ : Subgroup (UA σ W₂.J), IsStab B K₂ ∧ IwasawaOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K₂ := by
  first | exact @GlobalTheory.SkewDblIwasawa.exists_isStab_iwasawaOf | exact GlobalTheory.SkewDblIwasawa.exists_isStab_iwasawaOf | (intros; apply GlobalTheory.SkewDblIwasawa.exists_isStab_iwasawaOf <;> assumption)
