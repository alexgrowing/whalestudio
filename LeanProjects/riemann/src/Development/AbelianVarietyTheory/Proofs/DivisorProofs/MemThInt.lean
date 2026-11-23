import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag

noncomputable section

namespace GlobalTheory.ThK.TowerInt

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

abbrev reJ {m : ℕ} (Y Z : Spc F E m) : Spc F E m := ⟨Y.J, Z.L, Z.θ, Z.bas⟩

variable (σ) in

def ThInt (B : Base F E) (χX χW : Chr F E) {m : ℕ} (Y : Spc F E m) (n r s : ℕ) : Set (UA σ Y.J → ℂ) :=
  {T | ∃ (X : Spc F E n) (Z : Spc F E m) (M : Model σ X (reJ Y Z)) (om : Rep σ X (reJ Y Z)) (r' s' : ℕ),
    IsPair B M χX χW om r s r' s' ∧ ∃ Φ ∈ schA F (Fin n × Fin m), T = M.I om Φ}

variable (σ) in

def towerSpan (B : Base F E) (χX χW : Chr F E) {m : ℕ} (Y : Spc F E m) (a p j : ℕ) : Submodule ℂ (UA σ Y.J → ℂ) :=
  Submodule.span ℂ {T | ∃ r ≤ j, T ∈ ThInt σ B χX χW Y (a - 2 * r) (a - p - r) (p - r)}

theorem mem_thInt {B : Base F E} {χX χW : Chr F E} {n m r s r' s' : ℕ} {X : Spc F E n} {Y : Spc F E m} {M : Model σ X Y}
    {om : Rep σ X Y} (h : IsPair B M χX χW om r s r' s') {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin m)) :
    M.I om Φ ∈ ThInt σ B χX χW Y n r s :=
  ⟨X, Y, M, om, r', s', h, Φ, hΦ, rfl⟩

end GlobalTheory.ThK.TowerInt

end
