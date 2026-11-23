import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsAdaptedEmpty
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviNormalizesUnipotentVariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbedding
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.OrthogonalSubspaceUnitaryEmbeddingStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousConjBlockEmbeddingStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermRestrictSmoothModerateStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothAutomorphicDerivativeGrowthStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.StandardThreeBlockIndexStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsCuspFunSlice
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermParabolicFiniteTypeStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CasimirAnnihilatedCuspFormsFiniteDimensionalStatement
import GroundTheory.PAdicHodge.NormalizedTrace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Rg

theorem coeffSpan_comp_mem {K K' W : Type} [Group K] [Group K'] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K W) (j : K' →* K) {f : K → ℂ} (hf : f ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) :
    (f ∘ j) ∈ GlobalTheory.Published.AutFin.coeffSpan (ρ.comp j) := by
  induction hf using Submodule.span_induction with
  | mem x h =>
    obtain ⟨ℓ, w, rfl⟩ := h
    exact Submodule.subset_span ⟨ℓ, w, rfl⟩
  | zero => exact (GlobalTheory.Published.AutFin.coeffSpan (ρ.comp j)).zero_mem
  | add a b _ _ ha hb => exact (GlobalTheory.Published.AutFin.coeffSpan (ρ.comp j)).add_mem ha hb
  | smul a b _ hb => exact (GlobalTheory.Published.AutFin.coeffSpan (ρ.comp j)).smul_mem a hb

theorem finite_slices_core : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)), (∀ τ, IsContRep (ρ τ)) → ∀ (c : D.what₂.Tau → ℕ → ℂ) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ T : Finset (Fin m), T.Nonempty → GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.IsAdapted V X Y T ε fr → FiniteDimensional ℂ (Submodule.span ℂ (sliceSet (cuspOn θ V X Y T U ε fr ρ c) (uPart D.sp.cm.sig V.gram X Y T) (levi D.sp.cm.sig V.gram X Y T) 1)) := by
  intro D θ hθ V U hU ε fr hfr W _ _ _ ρ hρ c m X Y hXY T _hT hAd
  obtain ⟨V', ι, hι, hran⟩ := GlobalTheory.T.exists_orthogonal_hermitian_subspace D V m X Y hXY T
  obtain ⟨s, hsc, hsrel, hsq⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D V V' ι hι
  have hs : ∀ h, EmbRel V V' ι (s h) h := fun h => (hsrel h (s h)).2 rfl
  obtain ⟨hsu, hsurj, hsf⟩ := GlobalTheory.T.orthogonal_subspace_unitary_embedding D V m X Y hXY T V' ι hι hran s hs
  obtain ⟨ε', fr', j, hfr', hj, hk⟩ := GlobalTheory.T.frame_adapted_subspace_unitary_group D θ hθ V ε fr hfr m X Y hXY T hAd V' ι hι hran s hs
  obtain ⟨A, hA⟩ := GlobalTheory.T.constant_term_parabolic_eigenfunction D θ hθ V U ε fr W ρ c m X Y hXY T V' ι hι hran s hs
  let U' : Subgroup (GA D V') := U.comap s
  have hU' : IsOpen (U' : Set (GA D V')) := hU.preimage hsc
  let ρ' : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε' τ)) (W τ) := fun τ => (ρ τ).comp (j τ)
  have hρ' : ∀ τ, IsContRep (ρ' τ) := fun τ ℓ w => (hρ τ ℓ w).comp (hj τ)
  let B : Set (GA D V' → ℂ) := {φ | IsAutFunSm θ V' φ ∧ (∀ u ∈ U', u ∈ GfC V' → ∀ g, φ (g * u) = φ g) ∧
    (∀ τ, HasTypeAt θ V' τ (ε' τ) (fr' τ) (ρ' τ) φ) ∧ IsCuspFun V' φ ∧
    ∀ τ, (A τ 1).foldr (fun a f => gelf θ V' τ 1 f - a • f) φ = 0}
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ B) :=
    GlobalTheory.T.constant_term_parabolic_finite_type D θ hθ V' U' hU' ε' fr' hfr' W ρ' hρ' (fun τ => A τ 1)
  have hmem : ∀ ψ ∈ cuspOn θ V X Y T U ε fr ρ c, ∀ y ∈ levi D.sp.cm.sig V.gram X Y T,
      (∀ t ∈ uPart D.sp.cm.sig V.gram X Y T, t * y = y * t) → (fun h => ψ (s h * y)) ∈ B := by
    intro ψ hψ y hy hyc
    obtain ⟨h1, h2, h3, _⟩ := hψ.1
    have hcomm : ∀ h, s h * y = y * s h := fun h => hyc _ (hsu h)
    obtain ⟨hsm, hgr⟩ := GlobalTheory.T.constant_term_restrict_smooth_moderate D θ hθ V V' ι hι s hs _ ψ h1 y hcomm
    have hAF : IsAutFun V' (fun h => ψ (s h * y)) :=
      { left := fun γ hγ g => by
          have hm : s γ ∈ leftSub V X Y T :=
            Subgroup.mem_sup_right ⟨hsq γ hγ, GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.uPart_le_levi D V m X Y T (hsu γ)⟩
          simp only [map_mul]
          rw [mul_assoc]
          exact h1.left _ hm _
        level := ⟨U', hU', fun k hk hk' g => by
          simp only [map_mul]
          rw [mul_assoc, hcomm k, ← mul_assoc]
          exact h2 _ hk (hsf k hk') _⟩
        cont := h1.cont.comp (hsc.mul continuous_const) }
    refine ⟨GlobalTheory.T.smooth_automorphic_derivative_growth D θ hθ V' _ hAF hsm hgr (fun τ k => ⟨A τ k, hA ψ hψ.1 y hy hyc τ k⟩),
      ?_, fun τ x => ?_,
      GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.isCuspFun_slice D θ V U ε fr W ρ c m X Y hXY T V' ι hι hran s hs ψ hψ y hy hyc, fun τ => hA ψ hψ.1 y hy hyc τ 1⟩
    · intro k hk hk' g
      simp only [map_mul]
      rw [mul_assoc, hcomm k, ← mul_assoc]
      exact h2 _ hk (hsf k hk') _
    · have e : (fun k => ψ (s (x * kAt θ V' τ (ε' τ) (fr' τ) k) * y)) =
          (fun k0 => ψ ((s x * y) * kAt θ V τ (ε τ) (fr τ) k0)) ∘ j τ := by
        funext k
        simp only [Function.comp, map_mul]
        rw [mul_assoc, hcomm, ← mul_assoc, ← hk τ k]
      rw [e]
      exact coeffSpan_comp_mem (ρ τ) (j τ) (h3 τ (s x * y))
  let s' : GA D V' → uPart D.sp.cm.sig V.gram X Y T := fun h => ⟨s h, hsu h⟩
  have hs' : Function.Surjective s' := fun g => by
    obtain ⟨h, hh⟩ := hsurj g.1 g.2
    exact ⟨h, Subtype.ext hh⟩
  let Φ := LinearMap.funLeft ℂ ℂ s'
  have hΦ : Function.Injective Φ := LinearMap.funLeft_injective_of_surjective _ _ _ hs'
  set P := Submodule.span ℂ (sliceSet (cuspOn θ V X Y T U ε fr ρ c) (uPart D.sp.cm.sig V.gram X Y T)
    (levi D.sp.cm.sig V.gram X Y T) 1)
  have hle : P.map Φ ≤ Submodule.span ℂ B := by
    rw [Submodule.map_span_le]
    rintro f ⟨ψ, hψ, y, hy, hyc, rfl⟩
    apply Submodule.subset_span
    have := hmem ψ hψ y hy hyc
    convert this using 1
    funext h
    simp [Φ, s', LinearMap.funLeft]
  haveI : FiniteDimensional ℂ (P.map Φ) := Submodule.finiteDimensional_of_le hle
  exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective Φ hΦ P).symm

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Rg
end
