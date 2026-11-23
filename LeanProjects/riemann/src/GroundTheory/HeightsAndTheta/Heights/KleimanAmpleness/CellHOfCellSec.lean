import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellMeets
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MemChartSecOverOfMem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

noncomputable section

section CechSide

variable (S : Type) [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N : ℕ}

def omegaRes (x : Fin (N + 1) → Ω) :
    ∀ I J : Kleiman.Chart x, I.1 ⊆ J.1 → (Ω →ₗ[S] Ω) :=
  fun _ _ _ => LinearMap.id

def CechAugExact {x : Fin (N + 1) → Ω} (G : Kleiman.Chart x → Submodule S Ω) (B : Submodule S Ω) : Prop :=
  (∀ J, B ≤ G J) ∧
  (∀ s ∈ Kleiman.Cech.Cdeg (fun _ : Kleiman.Chart x => Ω) G 0,
      Kleiman.Cech.d (fun _ : Kleiman.Chart x => Ω) (omegaRes S x) 0 s = 0 → ∃ b ∈ B, ∀ J, s J = b) ∧
  ∀ p : ℕ, ∀ s ∈ Kleiman.Cech.Cdeg (fun _ : Kleiman.Chart x => Ω) G (p + 1),
    Kleiman.Cech.d (fun _ : Kleiman.Chart x => Ω) (omegaRes S x) (p + 1) s = 0 →
      ∃ t ∈ Kleiman.Cech.Cdeg (fun _ : Kleiman.Chart x => Ω) G p,
        Kleiman.Cech.d (fun _ : Kleiman.Chart x => Ω) (omegaRes S x) p t = s

end CechSide

section CellSide

variable (S : Type) [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
  [Field Ω] [Algebra S Ω]

def cellCOf (G : (∀ k, Finset (ι k)) → Submodule S Ω) (n : ℕ) :
    Submodule S (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω) :=
  Submodule.pi Set.univ fun I => G I.1

variable [LinearOrder K] [∀ k, LinearOrder (ι k)]

def cellZOf (y : (Σ k, ι k) → Ω) (G : (∀ k, Finset (ι k)) → Submodule S Ω) (n : ℕ) :
    Submodule S (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω) :=
  cellCOf S G n ⊓ LinearMap.ker (cellD S y n)

def cellBOf (y : (Σ k, ι k) → Ω) (G : (∀ k, Finset (ι k)) → Submodule S Ω) :
    (n : ℕ) → Submodule S (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω)
  | 0 => ⊥
  | n + 1 => (cellCOf S G n).map (cellD S y n)

abbrev cellHOf (y : (Σ k, ι k) → Ω) (G : (∀ k, Finset (ι k)) → Submodule S Ω) (n : ℕ) : Type :=
  ↥(cellZOf S y G n) ⧸ (cellBOf S y G n).comap (cellZOf S y G n).subtype

def CellAugExact (y : (Σ k, ι k) → Ω) (G : (∀ k, Finset (ι k)) → Submodule S Ω) (A : Submodule S Ω) : Prop :=
  (∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → CellMeets y I → A ≤ G I) ∧
  (∀ s ∈ cellCOf S G 0, cellD S y 0 s = 0 →
    ∃ a ∈ A, ∀ c : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0, CellMeets y c.1 → s c = a) ∧
  ∀ q : ℕ, ∀ s ∈ cellCOf S G (q + 1), cellD S y (q + 1) s = 0 →
    ∃ t ∈ cellCOf S G q, cellD S y q t = s

variable [DecidableEq K]

def baseCell (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) (J : Finset (Fin (N + 1))) (I : ∀ k, Finset (ι k)) :
    ∀ k, Finset (ι k) :=
  Function.update I k₀ (I k₀ ∪ J.map e.symm.toEmbedding)

end CellSide

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
