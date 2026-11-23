import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LanglandsLemmaUnitaryLocal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockCentre
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.langlands_lemma_unitary_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → GlobalTheory.Published.LanglandsLemmaUnitary →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (t : E →ₐ[F] Fv F v) (B : GL (Fin n) (Fv F v)) (S : Finset (Fin r)),
    (∀ k ∈ S, ∀ i ≤ k, i ∈ S) → ∀ i ∈ S, ∀ (hi : i.val + 1 ≤ n),
    (∀ g ∈ GlobalTheory.SmGL.unipRad (Fv F v) (blockIndex hi), ∃ x : GLoc σ J v,
      IsCompAt σ J t B g x ∧ emb σ J v x ∈ GlobalTheory.StdPar.unip σ J Xf S) →
    ∀ (ϖ : (Fv F v)ˣ) (x₀ : GLoc σ J v) (e : (AF F ⊗[F] E)ˣ),
    IsCompAt σ J t B (GlobalTheory.SmGL.leviEmb (Fv F v) (blockIndex hi) (blockScalar₂ (Fv F v) n i ϖ)) x₀ →
    GlobalTheory.LeviBlockRealization.IsBlockCentre σ J Xf Yf i e (emb σ J v x₀) →
    ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K → ∀ (φ : GAd σ J → ℂ), IsAut σ J K φ →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) (Fv F v)) V), IsSmooth π →
    ∀ (m : ℕ) (T : Fin m → V →ₗ[ℂ] (GAd σ J → ℂ)) (x : Fin m → V), (∀ j, IsIntertw σ J t B π (T j)) →
    φ = ∑ j, T j (x j) → ∀ (φc : GAd σ J → ℂ), GlobalTheory.StdPar.IsCuspComp σ J Xf Yf S K φ φc →
    ∀ (L : List ℂ), (∀ w, polyAt (jac (blockIndex hi) π (blockScalar₂ (Fv F v) n i ϖ)) L w = 0) →
      polyAt (GlobalTheory.LeviBlockRealization.leftTr σ J (emb σ J v x₀))
        (L.map fun c => c * ((deltaHalf (Fv F v) (fun j : Fin (i.val + 2) => Fin (blockSizes₂ n i j))
          (blockScalar₂ (Fv F v) n i ϖ) : ℂˣ) : ℂ)) φc = 0 := by
  first | exact @GlobalTheory.JacRel.polyAt_leftTr_cuspComp_eq_zero | exact GlobalTheory.JacRel.polyAt_leftTr_cuspComp_eq_zero | (intros; apply GlobalTheory.JacRel.polyAt_leftTr_cuspComp_eq_zero <;> assumption)
