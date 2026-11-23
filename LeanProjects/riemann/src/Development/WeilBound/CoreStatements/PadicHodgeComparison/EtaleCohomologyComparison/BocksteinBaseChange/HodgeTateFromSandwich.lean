import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.SemistableModelSemistable
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtSide

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open Formalism.Per6 GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst GlobalTheory.LogCris

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

set_option maxHeartbeats 1000000 in

structure ComparisonOn (G : Model l K → Prop) where
  c : ∀ (M : Model l K) (n : ℕ), M.V n →+ (Module.Dual K (HdR M.q n) →+ BdR l)
  lin : ∀ (M : Model l K) (n : ℕ) (z : ℚ_[l]) (v : M.V n) (φ : Module.Dual K (HdR M.q n)), c M n (z • v) φ = qQ l z * c M n v φ
  lin' : ∀ (M : Model l K) (n : ℕ) (k : K) (v : M.V n) (φ : Module.Dual K (HdR M.q n)), c M n v (k • φ) = oK k * c M n v φ
  fin : ∀ (M : Model l K) (n : ℕ), G M → FiniteDimensional ℚ_[l] (M.V n) ∧ FiniteDimensional K (HdR M.q n) ∧ ∀ x ∈ FilR M.q n (n + 1), x = 0

  equi : ∀ (M : Model l K) (n : ℕ), G M → ∀ (σ : K.fixingSubgroup) (v : M.V n) (φ : Module.Dual K (HdR M.q n)),
    c M n (M.act n σ v) φ = σD σ.1 (c M n v φ)

  inj : ∀ (M : Model l K) (n : ℕ), G M → ∀ {a : ℕ} (b : Module.Basis (Fin a) ℚ_[l] (M.V n)) (z : Fin a → BdR l),
    (∀ φ, ∑ i, z i * c M n (b i) φ = 0) → z = 0

  fil : ∀ (M : Model l K) (n : ℕ), G M → ∀ (r : ℕ) (v : M.V n) (φ : Module.Dual K (HdR M.q n)),
    (∀ x ∈ FilR M.q n (r + 1), φ x = 0) → ∃ y : BdRp l, tQ l ^ r * c M n v φ = algebraMap (BdRp l) (BdR l) y

  strict : ∀ (M : Model l K), G M →
    ∀ (n : ℕ) {a : ℕ} (b : Module.Basis (Fin a) ℚ_[l] (M.V n)) (z : Fin a → BdR l),
    (∀ (r : ℕ) (φ : Module.Dual K (HdR M.q n)), (∀ x ∈ FilR M.q n (r + 1), φ x = 0) →
      ∃ y : BdRp l, tQ l ^ r * ∑ i, z i * c M n (b i) φ = algebraMap (BdRp l) (BdR l) y) →
    ∀ i, ∃ y : BdRp l, z i = algebraMap (BdRp l) (BdR l) y

  nat : ∀ (M N : Model l K) (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n : ℕ), G M → G N →
    ∀ (v : N.V n) (φ : Module.Dual K (HdR M.q n)),
    c M n (Model.pullV u hu n v) φ = c N n v (φ ∘ₗ pullR n (Model.genMap u hu) (Model.genMap_q u hu))

def DeRhamComparisonSmooth : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
    Nonempty (ComparisonOn (Model.Sm (l := l) (K := K)))

def DeRhamComparisonSemistable : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
    Nonempty (ComparisonOn (Model.Good (l := l) (K := K)))

theorem DeRhamComparisonSemistable.dr (h : DeRhamComparisonSemistable) : FilteredDeRhamComparison := fun l _ K _ =>
  (h l K).elim fun C => ⟨⟨C.c, C.lin, C.lin', C.fin, C.equi, C.inj, C.fil, fun M hM _ => C.strict M hM, C.nat⟩⟩

end CrystallineSemistableComparison
