import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.ShFam.Hor.LogCh

theorem IsLatFam.pullback_analytic : ∀ (m n g : ℕ) (B : Set (Fin n → ℂ)) (B' : Set (Fin m → ℂ))
    (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (φ : (Fin m → ℂ) → Fin n → ℂ),
    GlobalTheory.ShFam.Hor.LogCh.IsLatFam B K → IsOpen B' → AnalyticOnNhd ℂ φ B' → Set.MapsTo φ B' B →
      GlobalTheory.ShFam.Hor.LogCh.IsLatFam B' (fun b => K (φ b)) := by
  intro m n g B B' K φ hK hB' hφ hmaps
  obtain ⟨_, h2, h3, h4⟩ := hK
  let Ψ : (Fin m → ℂ) × (Fin g → ℂ) → (Fin n → ℂ) × (Fin g → ℂ) := fun q => (φ q.1, q.2)
  refine ⟨hB', fun b hb => h2 (φ b) (hmaps hb), ?_, ?_⟩
  · have hcont : ContinuousOn Ψ (B' ×ˢ (Set.univ : Set (Fin g → ℂ))) :=
      (hφ.continuousOn.comp continuousOn_fst (fun q hq => hq.1)).prodMk continuousOn_snd
    have hopen := hcont.isOpen_inter_preimage (hB'.prod isOpen_univ) h3
    convert hopen using 1
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, and_true, Set.mem_preimage, Ψ]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, hmaps h1, h2⟩
    · rintro ⟨h1, _, h2⟩
      exact ⟨h1, h2⟩
  · intro b₀ hb₀ w₀ hw₀
    obtain ⟨ζ, hζ0, hζa, hev⟩ := h4 (φ b₀) (hmaps hb₀) w₀ hw₀
    refine ⟨fun b => ζ (φ b), hζ0, hζa.comp (hφ b₀ hb₀), ?_⟩
    have hΨ : ContinuousAt Ψ (b₀, w₀) :=
      ((hφ b₀ hb₀).continuousAt.comp continuousAt_fst).prodMk continuousAt_snd
    exact hΨ.tendsto.eventually hev

end GlobalTheory.ShFam.Hor.LogCh
