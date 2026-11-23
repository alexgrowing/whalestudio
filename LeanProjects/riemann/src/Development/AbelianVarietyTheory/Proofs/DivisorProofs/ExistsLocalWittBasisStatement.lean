import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalWittBasis
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockCentre
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_witt_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (t : E →ₐ[F] Fv F v), ∃ B : GL (Fin n) (Fv F v),
      (∀ (S : Finset (Fin r)), (∀ k ∈ S, ∀ i ≤ k, i ∈ S) → ∀ i ∈ S, ∀ (hi : i.val + 1 ≤ n),
        ∀ g ∈ GlobalTheory.SmGL.unipRad (Fv F v) (blockIndex hi), ∃ x : GLoc σ J v,
          IsCompAt σ J t B g x ∧ emb σ J v x ∈ GlobalTheory.StdPar.unip σ J Xf S) ∧
      (∀ (i : Fin r) (hi : i.val + 1 ≤ n) (ϖ : (Fv F v)ˣ), ∃ (x : GLoc σ J v) (e : (AF F ⊗[F] E)ˣ),
        IsCompAt σ J t B (GlobalTheory.SmGL.leviEmb (Fv F v) (blockIndex hi) (blockScalar₂ (Fv F v) n i ϖ)) x ∧
        GlobalTheory.LeviBlockRealization.IsBlockCentre σ J Xf Yf i e (emb σ J v x) ∧ (GlobalTheory.Doubling.absE F E e : ℝ) = nabs (Fv F v) ϖ) := by
  first | exact @GlobalTheory.LeviBlockFrame.exists_frame_basis | exact GlobalTheory.LeviBlockFrame.exists_frame_basis | (intros; apply GlobalTheory.LeviBlockFrame.exists_frame_basis <;> assumption)
