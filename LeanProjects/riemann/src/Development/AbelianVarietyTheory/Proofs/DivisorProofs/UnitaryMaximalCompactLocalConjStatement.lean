import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryMaximalCompactLocalConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_maximal_compact_local_conj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → GlobalTheory.Published.LanglandsLemmaUnitary →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (t : E →ₐ[F] Fv F v), ∃ B : GL (Fin n) (Fv F v),
    ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K → ∀ (φ : GAd σ J → ℂ), IsAut σ J K φ →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) (Fv F v)) V), IsSmooth π →
    ∀ (m : ℕ) (T : Fin m → V →ₗ[ℂ] (GAd σ J → ℂ)) (x : Fin m → V), (∀ j, IsIntertw σ J t B π (T j)) →
      φ = ∑ j, T j (x j) → ∀ S s, GlobalTheory.StdPar.IsCuspExp σ J Xf Yf S K φ s → (∀ k ∈ S, ∀ i ≤ k, i ∈ S) →
      ∀ i ∈ S, i.val + 1 ≤ n ∧ ∀ (hi : i.val + 1 ≤ n) (ϖ : (Fv F v)ˣ) (L : List ℂ),
        (∀ w, polyAt (jac (blockIndex hi) π (blockScalar₂ (Fv F v) n i ϖ)) L w = 0) →
        ∃ c ∈ L, ‖c‖ = nabs (Fv F v) ϖ ^ (s i).re := by
  first | exact @GlobalTheory.LeviBlockRealization.exists_norm_eq_rpow | exact GlobalTheory.LeviBlockRealization.exists_norm_eq_rpow | (intros; apply GlobalTheory.LeviBlockRealization.exists_norm_eq_rpow <;> assumption)
