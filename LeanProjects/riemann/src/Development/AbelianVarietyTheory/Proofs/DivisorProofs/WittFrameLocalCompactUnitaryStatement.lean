import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameLocalCompactUnitary
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_frame_local_compact_unitary : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → GlobalTheory.Published.LanglandsLemmaUnitary →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (t : E →ₐ[F] Fv F v), ∃ B : GL (Fin n) (Fv F v),
    ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K → ∀ (φ : GAd σ J → ℂ), IsAut σ J K φ →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) (Fv F v)) V), IsSmooth π →
    ∀ (m : ℕ) (T : Fin m → V →ₗ[ℂ] (GAd σ J → ℂ)) (x : Fin m → V), (∀ j, IsIntertw σ J t B π (T j)) →
      φ = ∑ j, T j (x j) → ∀ (S : Finset (Fin r)) (φc : GAd σ J → ℂ), GlobalTheory.StdPar.IsCuspComp σ J Xf Yf S K φ φc → φc ≠ 0 →
      ∀ (l d : ℕ), 1 ≤ d → (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
        (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
        ∃ (hld : l + d ≤ n) (U : Submodule ℂ (Fin m → V)) (Λ : (Fin m → V) →ₗ[ℂ] GlobalTheory.CuspRep.Sm E d),
          (∀ g : GL (Fin d) (Fv F v), ∀ u ∈ U, (fun j => π (GlobalTheory.SmGL.leviEmb (Fv F v) (tripPlace hld) (midHom (Fv F v) l d n g)) (u j)) ∈ U) ∧
          (∃ u ∈ U, Λ u ≠ 0) ∧ (∀ u ∈ U, GlobalTheory.CuspRep.IsCuspForm (Λ u)) ∧
          (∀ g ∈ GlobalTheory.SmGL.unipRad (Fv F v) (tripPlace hld), ∀ u ∈ U, Λ (fun j => π g (u j)) = Λ u) ∧
          ∀ g : GL (Fin d) (Fv F v), ∀ u ∈ U,
            Λ (fun j => π (GlobalTheory.SmGL.leviEmb (Fv F v) (tripPlace hld) (midHom (Fv F v) l d n g)) (u j)) =
              GlobalTheory.CuspRep.finRep E d (GlobalTheory.CuspRep.locGL E d (splitPrime t) (glEquiv d (complEquiv t (splitPrime_under t)) g)) (Λ u) := by
  first | exact @GlobalTheory.BlockForms.block_forms | exact GlobalTheory.BlockForms.block_forms | (intros; apply GlobalTheory.BlockForms.block_forms <;> assumption)
