import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemThInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasConstTermConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicPlaneComplementIdeal
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.ThK.SkewChain

open GlobalTheory.ThK.TowerInt

theorem skew_step {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} (hB : B.IsGood σ) {m m₁ r s : ℕ} {Y Z : Spc F E m} {Y₁ : Spc F E m₁}
    {P : Plane E m m₁} (h : (reJ Y Z).IsSkew σ B r s) (hP : IsIsoPlane σ B P Y Y₁) :
    ∃ (Z₁ : Spc F E m₁) (r₁ s₁ : ℕ), (reJ Y₁ Z₁).IsSkew σ B r₁ s₁ := by
  obtain ⟨_, Z₁, _, _, hsk, _⟩ := GlobalTheory.ThK.Relat.exists_adapted hB h hP
  exact ⟨Z₁, _, _, hsk⟩

theorem skew_chain : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (Y : Spc F E n) (W : Spc F E d)
    (Mo : Model σ Y W) (χX χW : Chr F E) (om : Rep σ Y W) (r s r' s' : ℕ), IsPair B Mo χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (sp : ∀ j : ℕ, Spc F E (d₁ - 2 * j))
    (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))) (p : ℕ), H'.IsAdapted σ B W (sp 0) i₀ i₁ →
    (∀ i < p, IsIsoPlane σ B (pl i) (sp i) (sp (i + 1))) → ∀ i < p,
      ∃ (Z : Spc F E (d₁ - 2 * i)) (r₁ s₁ : ℕ), (GlobalTheory.ThK.TowerInt.reJ (sp i) Z).IsSkew σ B r₁ s₁ := by
  intro F E _ _ _ _ _ σ B n d Y W Mo χX χW om r s r' s' hpair d₁ H' i₀ i₁ sp pl p hH hiso i
  induction i with
  | zero =>
    intro h0
    have hIP : IsIsoPlane σ B H' W (sp 0) := IsIsoPlane.of_adapted hH hpair.skew.cartan (hiso 0 h0).2.2.2.2.2.2.1
    exact skew_step hpair.base (Z := W) (P := H') hpair.skew hIP
  | succ i ih =>
    intro hi
    obtain ⟨Z, r₁, s₁, h⟩ := ih (by omega)
    exact skew_step hpair.base h (hiso i (by omega))

end GlobalTheory.ThK.SkewChain

end
