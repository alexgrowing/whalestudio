import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SymInt
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.EdgePlane

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.Pf14

theorem wittVector_prime_ne_zero (p n' : ℕ) [Fact p.Prime] : ((p : ℕ) : WF p n') ≠ 0 := by
  intro h
  have h1 := WittVector.coeff_p_one (p := p) (R := GaloisField p n')
  rw [h] at h1
  simp at h1

theorem planeAt : PlaneAt := by
  intro p n' _ W Qq _ _ _ _ _ m φ h g g' e e' hfr hg hg' he he' hpl
  have hp0 : (p : W) ≠ 0 := by
    intro h0
    apply wittVector_prime_ne_zero p n'
    apply φ.injective
    rw [map_natCast, h0, map_zero]
  have hpQ : (p : Qq) ≠ 0 := by
    rw [← map_natCast (algebraMap W Qq)]
    exact fun h1 => hp0 ((IsFractionRing.injective W Qq) (by rw [h1, map_zero]))
  obtain ⟨-, hs, ht⟩ := he
  obtain ⟨-, hs', ht'⟩ := he'
  rw [src_eq φ g hg h] at hs
  rw [src_eq φ g' hg' h] at hs'
  rw [matQ_inv φ g hg] at ht
  rw [matQ_inv φ g' hg'] at ht'
  change e.tgt = colSpan W (h * (Ng φ g).map (algebraMap W Qq) * dD Qq p 1 (m + 1)) at ht
  change e'.tgt = colSpan W (h * (Ng φ g').map (algebraMap W Qq) * dD Qq p 1 (m + 1)) at ht'
  obtain ⟨s, t⟩ := e
  obtain ⟨s', t'⟩ := e'
  simp only at hs hs' ht ht'
  rw [Edge.mk.injEq]
  refine ⟨by rw [hs, hs'], ?_⟩
  rw [ht, ht']
  apply le_antisymm
  · exact tgt_le_of_plane φ 1 hpQ g' g hg' hg h hpl.le
  · exact tgt_le_of_plane φ 1 hpQ g g' hg hg' h hpl.ge

end Formalism.MainNotions.ColumnSystems.Pf
