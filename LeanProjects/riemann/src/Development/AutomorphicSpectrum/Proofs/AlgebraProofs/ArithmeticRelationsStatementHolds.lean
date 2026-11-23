import Mathlib
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.RelationsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UniformizerModelPermModuleLatticeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DescentRelationsFromModelsStatement

namespace GlobalTheory.CompanionTheory.Ar.Num.TopRel

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

theorem relations : GlobalTheory.CompanionTheory.Ar.Num.RelationsStatement := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x _ ϖ hϖ d hmod hfn F _ _ _ n Sg _ r s p hp w χ φ D hD Lie W Om OmHT hB lie om hflag
  have hck := GlobalTheory.T.lattice_family_ckRelations O Ω K ι x d hmod hfn p hp w χ φ D hD Lie W Om OmHT hB
  have hp0 : (p : O) ≠ 0 := hD.char.1
  have hw0 : w ≠ 0 := by
    rintro rfl
    obtain ⟨u, hu, he⟩ := hD.char.2.1
    have h1 : p - 1 ≠ 0 := by have := hp.two_le; omega
    rw [zero_pow h1] at he
    exact hp0 (by
      rcases mul_eq_zero.mp he.symm with h | h
      · exact absurd h hu.ne_zero
      · exact h)
  have hsame : ∀ τ, SameGeneric O x (Lie τ) (W τ) ∧ SameGeneric O x (Om τ) (OmHT τ) := by
    intro τ
    constructor
    · intro c hc
      obtain ⟨h1, h2, -, -⟩ := hB τ c hc
      have hinc := ((hD.base c hc).incl τ)
      rw [h1, h2]
      refine ⟨fun v hv => ⟨1, one_ne_zero, ?_⟩, fun v hv => ⟨w, hw0, ?_⟩⟩
      · simpa using hinc.1 hv
      · exact hinc.2.1 hv
    · intro c hc
      obtain ⟨-, -, h3, h4⟩ := hB τ c hc
      have hinc := ((hD.base c hc).incl τ)
      rw [h3, h4]
      refine ⟨fun v hv => ⟨w, hw0, ?_⟩, fun v hv => ⟨1, one_ne_zero, ?_⟩⟩
      · exact hinc.2.2.2 hv
      · simpa using hinc.2.2.1 hv
  exact GlobalTheory.T.uniformizer_model_perm_module_lattice O Ω K ι x ϖ hϖ d hmod p hp0 φ (VL := fun τ => Fin (r τ) → Ω)
    (VO := fun τ => Fin (s τ) → Ω) Lie W Om OmHT hsame hck lie om hflag

end GlobalTheory.CompanionTheory.Ar.Num.TopRel
