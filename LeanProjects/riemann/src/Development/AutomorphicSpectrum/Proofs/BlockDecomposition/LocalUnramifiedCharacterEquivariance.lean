import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SummableUnitBounds.SBoundOf
open GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LocalChar

theorem sPsi : Ad3.LU.SPsi := by
  intro F _ _ _ _ ψ hψ x hx
  obtain ⟨hc, h1, h0⟩ := hψ
  have hb : x ∈ valBall F (addCharConductor ψ) := by
    rw [h0]
    have : x ∈ (valBall F 0 : Set F) := by
      rw [coe_valBall_zero]; exact hx
    exact this
  have := isTrivialOn_addCharConductor hc h1 x hb
  simp [this]

end GlobalTheory.CompanionTheory.LocalChar
