import Mathlib
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LocGram
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.CharacterAugmentationSubspaceQuotientActionTop
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ExistsBasisCols
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.CompanionTheory.IwaDbl

namespace GlobalTheory.CompanionTheory.IwaDbl

theorem hasIwasawa_arch : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ {J : Matrix (Fin n) (Fin n) E} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}, Q = dblGram finSumFinEquiv J → ∀ (w : InfinitePlace F) (b : GL (Fin n) (w.Completion ⊗[F] E)) (ε : Fin n → Bool), locGram σ J b = Matrix.diagonal (fun i => if ε i then 1 else -1) → HasIwasawa σ Q (KArch σ Q w b) := by
  intro F E _ _ _ _ _ n σ hc J Q hQ w b ε hb
  exact GlobalTheory.Core.Rk.IwArch.hasIwasawa_KArch hc hQ w b ε hb

end GlobalTheory.CompanionTheory.IwaDbl

end
