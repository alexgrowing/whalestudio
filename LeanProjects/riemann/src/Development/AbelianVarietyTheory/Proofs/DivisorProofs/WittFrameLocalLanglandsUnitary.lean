import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameLocalCompactUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubquotientJacUIntertwining
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStableMapCuspSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.CuspBlock.exists_cuspSub_of_jacquet : GlobalTheory.ThK.KP → GlobalTheory.Published.CuspidalSpectrumGL → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → GlobalTheory.Published.LanglandsLemmaUnitary →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (t : E →ₐ[F] Fv F v), ∃ B : GL (Fin n) (Fv F v),
    ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K → ∀ (φ : GAd σ J → ℂ), IsAut σ J K φ →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) (Fv F v)) V), IsSmooth π →
    ∀ (m : ℕ) (T : Fin m → V →ₗ[ℂ] (GAd σ J → ℂ)) (x : Fin m → V), (∀ j, IsIntertw σ J t B π (T j)) →
      φ = ∑ j, T j (x j) → ∀ (S : Finset (Fin r)) (φc : GAd σ J → ℂ), GlobalTheory.StdPar.IsCuspComp σ J Xf Yf S K φ φc → φc ≠ 0 →
      ∀ (l d : ℕ), 1 ≤ d → (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
        (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
        ∃ (hld : l + d ≤ n) (τ : GlobalTheory.CuspRep.CuspSub E d) (W' : Type) (_ : AddCommGroup W') (_ : Module ℂ W')
          (Q : Representation ℂ (GL (Fin d) (Fv F v)) W'),
          IsSubquotient Q ((jacU (tripPlace hld) π).comp (midHom (Fv F v) l d n)) ∧
          ∃ f : Q.IntertwiningMap ((τ.locRep (splitPrime t)).comp
            (glEquiv d (complEquiv t (splitPrime_under t))).toMonoidHom), f ≠ 0 := by
  intro hKP hC F E _ _ _ _ _ _ σ hσ n J hJ r Xf Yf hW hL v t
  obtain ⟨B, hB⟩ := GlobalTheory.T.witt_frame_local_compact_unitary hKP F E σ hσ n J hJ r Xf Yf hW hL v t
  refine ⟨B, fun K hK φ hφ V _ _ π hπ m T x hT hφs S φc hc hc0 l d hd hS1 hS2 hS3 => ?_⟩
  obtain ⟨hld, U, Λ, hU, ⟨u₀, hu₀, hne⟩, hcusp, hN, hM⟩ :=
    hB K hK φ hφ V π hπ m T x hT hφs S φc hc hc0 l d hd hS1 hS2 hS3
  obtain ⟨W, τ, p, hfW, hWst, hp0, hp⟩ := GlobalTheory.CuspQuot.exists_stable_map_cuspSub hC E d (Λ u₀) (hcusp u₀ hu₀) hne
  obtain ⟨W', i1, i2, Q, hQ, f, hf⟩ := GlobalTheory.MidJacquet.exists_subquotient_jacU_intertwining (Fv F v) n l d hld V π hπ m (U ⊓ W.comap Λ)
    (fun g u hu => ⟨hU g u hu.1, by
      change Λ _ ∈ W
      rw [hM g u hu.1]
      exact hWst (.fin _) _ hu.2⟩)
    τ.V ((τ.locRep (splitPrime t)).comp (glEquiv d (complEquiv t (splitPrime_under t))).toMonoidHom) (p ∘ₗ Λ)
    ⟨u₀, ⟨hu₀, hfW⟩, hp0⟩
    (fun g hg u hu => by simp only [LinearMap.comp_apply]; rw [hN g hg u hu.1])
    (fun g u hu => by
      simp only [LinearMap.comp_apply]
      rw [hM g u hu.1]
      exact hp (.fin _) _ hu.2)
  exact ⟨hld, τ, W', i1, i2, Q, hQ, f, hf⟩
