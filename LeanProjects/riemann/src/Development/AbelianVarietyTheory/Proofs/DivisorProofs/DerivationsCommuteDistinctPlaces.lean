import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralOperatorCommutesLineDerivative
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.LeviHC.PlaceComm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
  {w w' : InfinitePlace F} {τ : EmbOver E w} {τ' : EmbOver E w'} {Z Z' : Matrix (Fin n) (Fin n) ℂ}
  {γ δ : ℝ → GAd σ J}

theorem line_commute (hw : w ≠ w') (hγ : IsLineOf σ J τ Z γ) (hδ : IsLineOf σ J τ' Z' δ) (s t : ℝ) :
    γ s * δ t = δ t * γ s := by
  obtain ⟨y, e, -⟩ := hγ s
  obtain ⟨y', e', -⟩ := hδ t
  rw [e, e']
  exact (commute_embArch σ J y (projArch_embArch_ne σ J hw y')).eq

theorem lineDer_comm (h : IsCMExt F E σ) (hw : w ≠ w') (hγ : IsLineOf σ J τ Z γ) (hδ : IsLineOf σ J τ' Z' δ)
    {φ : GAd σ J → ℂ} (hφ : IsSm σ J φ) :
    GlobalTheory.SiegelSet.lineDer γ (GlobalTheory.SiegelSet.lineDer δ φ) = GlobalTheory.SiegelSet.lineDer δ (GlobalTheory.SiegelSet.lineDer γ φ) := by
  funext g
  have hu := GlobalTheory.UAut.CentralComm.isSmFamily_translate hφ (hγ.isRealLine h)
  have e := hu.deriv_lineDer (hδ.isRealLine h) g
  refine Eq.trans ?_ e
  simp only [GlobalTheory.SiegelSet.lineDer]
  congr 1; funext s; congr 1; funext t
  rw [mul_assoc, mul_assoc, line_commute hw hγ hδ]

theorem der_comm_lines (h : IsCMExt F E σ) (hw : w ≠ w')
    {D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmG σ J)} (hD : IsDer σ J τ D)
    {D' : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmG σ J)} (hD' : IsDer σ J τ' D')
    (hγ : IsLineOf σ J τ Z γ) (hδ : IsLineOf σ J τ' Z' δ) : Commute (D Z) (D' Z') := by
  refine LinearMap.ext fun f => Subtype.ext ?_
  simp only [Module.End.mul_apply]
  rw [hD.2 Z γ hγ, hD'.2 Z' δ hδ, hD'.2 Z' δ hδ, hD.2 Z γ hγ]
  exact lineDer_comm h hw hγ hδ f.2

end GlobalTheory.LeviHC.PlaceComm

namespace GlobalTheory.LeviHC

theorem der_comm_of_ne : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) (D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmG σ J)), IsDer σ J τ D →
    ∀ (w' : InfinitePlace F) (τ' : EmbOver E w') (D' : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmG σ J)),
    IsDer σ J τ' D' → w ≠ w' → ∀ X X', D X * D' X' = D' X' * D X := by
  intro F E _ _ _ _ _ σ h n J hJ w τ D hD w' τ' D' hD' hw X X'
  obtain ⟨γ₁, γ₂, e1, e2, hX⟩ := exists_lines h hJ τ X
  obtain ⟨δ₁, δ₂, f1, f2, hX'⟩ := exists_lines h hJ τ' X'
  have c : ∀ {Z Z' : Matrix (Fin n) (Fin n) ℂ} {γ δ : ℝ → GAd σ J}, IsLineOf σ J τ Z γ → IsLineOf σ J τ' Z' δ →
      Commute (D Z) (D' Z') := fun hγ hδ => PlaceComm.der_comm_lines h hw hD hD' hγ hδ
  have key : Commute (D X) (D' X') := by
    rw [hX, hX']
    rw [map_add, map_add, LinearMap.map_smul D Complex.I _, LinearMap.map_smul D' Complex.I _]
    exact ((c e1 f1).add_right ((c e1 f2).smul_right Complex.I)).add_left
      (((c e2 f1).add_right ((c e2 f2).smul_right Complex.I)).smul_left Complex.I)
  exact key.eq

end GlobalTheory.LeviHC

end
