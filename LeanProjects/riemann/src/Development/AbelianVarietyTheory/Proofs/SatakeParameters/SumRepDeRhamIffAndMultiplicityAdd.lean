import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DirectSumDeRhamCrystallineJumpsAdd
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DirectSumLocal

open Module

noncomputable def splitEquiv (k : Type) [Field k] (a b : ℕ) : (Fin (a + b) → k) ≃ₗ[k] (Fin a → k) × (Fin b → k) :=
  (LinearEquiv.funCongrLeft k k finSumFinEquiv).trans (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) k k)

theorem splitEquiv_sumRep {Γ k : Type} [Group Γ] [Field k] {a b : ℕ} (r₁ : Γ →* GL (Fin a) k)
    (r₂ : Γ →* GL (Fin b) k) (g : Γ) (v : Fin (a + b) → k) :
    splitEquiv k a b ((Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂ g : Matrix _ _ k).mulVec v) =
      (((r₁ g : Matrix _ _ k)).mulVec (splitEquiv k a b v).1, ((r₂ g : Matrix _ _ k)).mulVec (splitEquiv k a b v).2) := by
  ext i
  · simp [splitEquiv, Formalism.MainNotions.SumRepresentations.At.sumRep, Formalism.MainNotions.SumRepresentations.At.blkHom, Matrix.mulVec, dotProduct, Fin.sum_univ_add, Matrix.fromBlocks]
    rfl
  · simp [splitEquiv, Formalism.MainNotions.SumRepresentations.At.sumRep, Formalism.MainNotions.SumRepresentations.At.blkHom, Matrix.mulVec, dotProduct, Fin.sum_univ_add, Matrix.fromBlocks]
    rfl

end GlobalTheory.DirectSumLocal

namespace GlobalTheory.DirectSumLocal

theorem isdRE_sumRep_and_multE_add : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (LL' : FinExt l) (a b : ℕ) (r₁ : ↥Gw →* GL (Fin a) ↥LL'.1) (r₂ : ↥Gw →* GL (Fin b) ↥LL'.1), (Bw.IsdRE P LL' (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) ↔ Bw.IsdRE P LL' r₁ ∧ Bw.IsdRE P LL' r₂) ∧ ∀ (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) (c : ℤ), Bw.multE P LL' (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) τ' c = Bw.multE P LL' r₁ τ' c + Bw.multE P LL' r₂ τ' c := by
  intro l _ P AI hT E Ω _ _ _ Gw O _ _ _ Bw LL' a b r₁ r₂
  obtain ⟨T⟩ := hT
  have he : ∀ g v, splitEquiv (↥LL'.1) a b (Bw.repE LL' (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) g v) =
      (Bw.repE LL' r₁ g (splitEquiv (↥LL'.1) a b v).1, Bw.repE LL' r₂ g (splitEquiv (↥LL'.1) a b v).2) := by
    intro g v
    exact splitEquiv_sumRep r₁ r₂ _ v
  obtain ⟨h1, -, h3⟩ := GlobalTheory.Per.DirectSumHT.directSum_hodgeTate l P AI T Bw.Kw LL' (Fin (a + b) → ↥LL'.1)
    (Bw.repE LL' (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂)) (Fin a → ↥LL'.1) (Bw.repE LL' r₁) (Fin b → ↥LL'.1)
    (Bw.repE LL' r₂) (splitEquiv (↥LL'.1) a b) he
  refine ⟨?_, fun τ' c => h3 τ' c⟩
  unfold Formalism.BasicNotions.LocBridge.IsdRE
  unfold Formalism.MainNotions.N.IsDR at h1
  simpa only [Module.finrank_fin_fun] using h1

end GlobalTheory.DirectSumLocal
