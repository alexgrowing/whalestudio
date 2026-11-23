import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInSupportOfMultiProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleTensorOfJacquetSubquotient
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalTwistOfJacquetConstituentEmptyBlock
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.SmGL.Relabel

section General

variable {F G H V : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H]

def indPull {P : Subgroup G} {Q : Subgroup H}
    {σ : Representation F P V} {τ : Representation F Q V} (φ : H →* G) (hφ : Continuous φ)
    (h : ∀ q : Q, ∃ p : P, (p : G) = φ q ∧ σ p = τ q) :
    smoothPart (ind P σ) →ₗ[F] smoothPart (ind Q τ) where
  toFun f := ⟨⟨fun g => f.1.1 (φ g), fun q g => by
      obtain ⟨p, hp, hs⟩ := h q
      show f.1.1 (φ (q * g)) = τ q (f.1.1 (φ g))
      rw [map_mul, ← hp, f.1.2 p, hs]⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset
      (IsOpen.mem_nhds (IsOpen.preimage hφ f.2) (by simp)) fun g hg => by
        have hg' : ind P σ (φ g) f.1 = f.1 := hg
        apply Subtype.ext
        funext x
        have := congrFun (congrArg Subtype.val hg') (φ x)
        show f.1.1 (φ (x * g)) = f.1.1 (φ x)
        rw [map_mul]
        exact this)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem smInd_equiv_comp {P : Subgroup G} {Q : Subgroup H}
    {σ : Representation F P V} {τ : Representation F Q V} (φ : G →* H) (φ' : H →* G)
    (hφ : Continuous φ) (hφ' : Continuous φ') (h1 : ∀ x, φ (φ' x) = x) (h2 : ∀ x, φ' (φ x) = x)
    (h : ∀ q : Q, ∃ p : P, (p : G) = φ' q ∧ σ p = τ q)
    (h' : ∀ p : P, ∃ q : Q, (q : H) = φ p ∧ τ q = σ p) :
    Nonempty ((smInd P σ).Equiv ((smInd Q τ).comp φ)) := by
  refine ⟨.mk (LinearEquiv.ofLinear (indPull φ' hφ' h) (indPull φ hφ h') ?_ ?_) fun g => ?_⟩
  · refine LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => ?_))
    show f.1.1 (φ (φ' x)) = f.1.1 x
    rw [h1]
  · refine LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => ?_))
    show f.1.1 (φ' (φ x)) = f.1.1 x
    rw [h2]
  · refine LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => ?_))
    show f.1.1 (φ' x * g) = f.1.1 (φ' (x * φ g))
    rw [map_mul, h2]

end General

section Blocks

open GlobalTheory.EmptyFirstBlock

variable {R : Type} [CommRing R] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem continuous_reindexGL [TopologicalSpace R] (ψ : n ≃ n') :
    Continuous (reindexGL (R := R) ψ) :=
  Continuous.units_map _ (continuous_pi fun i => continuous_pi fun j =>
    continuous_apply_apply (ψ.symm i) (ψ.symm j))

theorem reindexGL_symm_reindexGL (ψ : n ≃ n') (g : GL n R) :
    reindexGL ψ.symm (reindexGL ψ g) = g :=
  Units.ext (Matrix.ext fun i j => by simp [val_reindexGL])

variable {α : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]

theorem exists_parab_reindexGL {e : (Σ a, m a) ≃ n} {e' : (Σ a, m a) ≃ n'} (ψ : n ≃ n')
    (h : ∀ x, ψ.symm (e' x) = e x) (p : parab R e) :
    ∃ q : parab R e', (q : GL n' R) = reindexGL ψ p ∧ leviProj R e' q = leviProj R e p := by
  refine ⟨⟨reindexGL ψ p, mem_parab_iff.2 fun a b i j hab => ?_⟩, rfl, ?_⟩
  · rw [val_reindexGL, h, h]
    exact mem_parab_iff.1 p.2 a b i j hab
  · funext a
    ext i j
    show (reindexGL ψ (p : GL n R) : Matrix n' n' R) (e' ⟨a, i⟩) (e' ⟨a, j⟩) =
      ((p : GL n R) : Matrix n n R) (e ⟨a, i⟩) (e ⟨a, j⟩)
    rw [val_reindexGL, h, h]

end Blocks

theorem parInd_reindex : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (α : Type) [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (e : (Σ a, m a) ≃ n) (ψ : n ≃ n')
    (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W),
    Nonempty ((parInd e ρ).Equiv ((parInd (e.trans ψ) ρ).comp (GlobalTheory.EmptyFirstBlock.reindexGL (R := k) ψ))) := by
  intro k _ _ _ _ α _ _ m _ _ n n' _ _ _ _ e ψ W _ _ ρ
  refine smInd_equiv_comp _ (GlobalTheory.EmptyFirstBlock.reindexGL (R := k) ψ.symm)
    (continuous_reindexGL ψ) (continuous_reindexGL ψ.symm)
    (reindexGL_symm_reindexGL ψ.symm) (reindexGL_symm_reindexGL ψ) (fun q => ?_) (fun p => ?_)
  · obtain ⟨p, hp, hl⟩ := exists_parab_reindexGL (e' := e) ψ.symm (fun x => rfl) q
    exact ⟨p, hp, congrArg (twist ρ (deltaHalf k m)) hl⟩
  · obtain ⟨q, hq, hl⟩ := exists_parab_reindexGL (e' := e.trans ψ) ψ (fun x => by simp) p
    exact ⟨q, hq, congrArg (twist ρ (deltaHalf k m)) hl⟩

end GlobalTheory.SmGL.Relabel
