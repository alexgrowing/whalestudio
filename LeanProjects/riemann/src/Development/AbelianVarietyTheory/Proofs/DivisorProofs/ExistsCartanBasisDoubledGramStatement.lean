import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanBasisDoubledGram
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactAndIwasawaOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasIwasawaOfSmul
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer
open GlobalTheory.SkewDblIwasawa
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cartan_basis_doubled_gram : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (B : Base F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (θ : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ),
    (∀ i j, σ (J j i) = -J i j) → (∀ w, IsCartan (Complex.I • J.map (B.emb w).1) (θ w)) →
    ∀ {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}, Q = dblGram finSumFinEquiv Jᵀ →
    ∃ a : GL (Fin n) (AF F ⊗[F] E), ∀ w : InfinitePlace F,
      HasIwasawa σ Q (KArch σ Q w (Formalism.UG.bc (compInf F E w) a)) ∧
      ∀ k : GArch σ Q w, k ∈ KArch σ Q w (Formalism.UG.bc (compInf F E w) a) ↔
        Commute ((GlobalTheory.AdelicU.matHom w.Completion σ Q k).1.map (infEmb (B.emb w))) (blkMat finSumFinEquiv (θ w) (-θ w)) := by
  first | exact @GlobalTheory.SkewDblIwasawa.arch | exact GlobalTheory.SkewDblIwasawa.arch | (intros; apply GlobalTheory.SkewDblIwasawa.arch <;> assumption)
