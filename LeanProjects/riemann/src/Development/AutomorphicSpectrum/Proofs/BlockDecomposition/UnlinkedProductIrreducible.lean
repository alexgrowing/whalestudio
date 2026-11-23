import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspStdSubGeneric
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjacentQuotientOfTwoSegment
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwoSegmentNongenericQuotient
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.BZSeg.Unlinked

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def subIncl (π : Representation ℂ (GL (Fin N) k) V) (S : Subrepresentation π) :
    S.toRepresentation.IntertwiningMap π where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' := fun _ => rfl

def quotProj {W : Type} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V)
    (σ : Representation ℂ (GL (Fin N) k) W) (f : σ.IntertwiningMap π) :
    π.IntertwiningMap (GlobalTheory.CompanionTheory.BZSeg.TwoSeg.quotRep π σ f) where
  toLinearMap := (LinearMap.range f.toLinearMap).mkQ
  isIntertwining' := fun _ => rfl

theorem isIrreducible_of_generic {ψ : AddChar k Circle} (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    (π : Representation ℂ (GL (Fin N) k) V) [Nontrivial V] (hπ : IsSmooth π)
    (hr : Module.rank ℂ (TwJacquet π (unipB k (Fin N)) (whitChar ψ N)) ≤ 1)
    (hsub : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W)
      (f : σ.IntertwiningMap π), Function.Injective f → Nontrivial W → IsGeneric σ)
    (hquo : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GL (Fin N) k) W)
      (f : π.IntertwiningMap τ), Function.Surjective f → Nontrivial W → IsGeneric τ) :
    π.IsIrreducible := by
  have hbt : (⊥ : Subrepresentation π) ≠ ⊤ := by
    intro e
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h2 : v ∈ (⊤ : Subrepresentation π).toSubmodule := trivial
    rw [← e] at h2
    exact hv h2
  haveI : Nontrivial (Subrepresentation π) := ⟨⟨⊥, ⊤, hbt⟩⟩
  refine ⟨fun S => ?_⟩
  by_contra hc
  push Not at hc
  obtain ⟨hb, ht⟩ := hc
  have hinj : Function.Injective (subIncl π S) := Subtype.val_injective
  have hSn : Nontrivial S.toSubmodule := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    refine hb (Subrepresentation.toSubmodule_injective ?_)
    refine (Submodule.eq_bot_iff _).2 fun v hv => ?_
    exact congrArg Subtype.val (Subsingleton.elim (⟨v, hv⟩ : S.toSubmodule) 0)
  have hrange : LinearMap.range (subIncl π S).toLinearMap = S.toSubmodule := Submodule.range_subtype _
  have hQn : Nontrivial (V ⧸ LinearMap.range (subIncl π S).toLinearMap) := by
    refine Submodule.Quotient.nontrivial_iff.2 ?_
    rw [hrange]
    intro e
    exact ht (Subrepresentation.toSubmodule_injective e)
  have hσ := hsub _ S.toRepresentation (subIncl π S) hinj hSn
  exact GlobalTheory.CompanionTheory.BZSeg.TwoSeg.not_isGeneric_quotRep hψ h1 π _ (subIncl π S) hinj hπ hr hσ
    (hquo _ _ (quotProj π _ (subIncl π S)) (Submodule.mkQ_surjective _) hQn)

theorem lUnlinkedIrr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.BZSeg.StdSubGeneric k → GlobalTheory.BZSeg.StdQuotGeneric k → GlobalTheory.BZSeg.WhitRankStd k →
    GlobalTheory.BZSeg.ProdIrrFiniteLength k → GlobalTheory.BZSeg.LUnlinkedIrr k := by
  intro k _ _ _ _ hS hQ hR _ h N Δ x hd hun hL
  obtain ⟨ψ, hψ, h1⟩ := exists_continuous_addChar_ne_one k
  haveI := GlobalTheory.CompanionTheory.AdjQuot.nontrivial_prodIrr x hd
  exact isIrreducible_of_generic hψ h1 (prodIrr x hd) (isSmooth_prodIrr x hd) (hR ψ hψ h1 h N x hd)
    (fun W _ _ σ f hf hW => hS h N Δ x hd hL (fun i j _ hp => hun i j hp.1) W σ f hf hW)
    (fun W _ _ τ f hf hW => hQ h N Δ x hd hL (fun i j _ hp => hun j i hp.1) W τ f hf hW)

end GlobalTheory.CompanionTheory.BZSeg.Unlinked

end
