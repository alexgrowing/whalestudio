import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsHaarOnIffGroupsUnitaryUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsHarishChandraParamOfTypeOfUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsQuotientMeasureBesselPeriodSubgroupUnitaryStatement

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem besselSide_of_isType (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (u : ℕ → ℝ) (μW μN μG : Measure (Formalism.QuantumDeterminants.Mt k r)) (hk : 1 ≤ k) (hz : Formalism.QuantumDeterminants.inWb k r z)
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hW : B.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : B.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) (hG : B.IsHaarOn (GG k r) μG) (hπ : Q.IsType k r z π u) :
    ∃ νq, SideG k r z π u μW μN μG νq := by
  have hW' := ((GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r μW).2.2 z hz hT hk).2 hW
  have hN' := (GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r μN).2.1.2 hN
  have hG' := (GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r μG).1.2 hG
  obtain ⟨νq, hν⟩ := GlobalTheory.T.exists_quotientMeasure_besselPeriodSubgroup_unitary k r z μW μN μG hz hT hW' hN' hG'
  exact ⟨νq, hz, hT, GlobalTheory.T.exists_harishChandraParam_of_typeOfUnitaryW k r Wp z π u hz hT hπ, hπ.2.2.2.2.2, hW', hN', hG', hν⟩

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
private theorem exists_quotient_side_of_isType_lemma (k r : ℕ) (W : Type) [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (hk : 1 ≤ k)
    (z : Fin (2 * r + k + 1) → ℂ) (π : _root_.Formalism.FourierDecayAlt.B.Mat k r → W →L[ℂ] W) (u : ℕ → ℝ)
    (μW μN μG : Measure (_root_.Formalism.QuantumDeterminants.Mt k r)) (hz : _root_.Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < _root_.Formalism.QuantumDeterminants.Tz k r z)
    (hW : _root_.Formalism.FourierDecayAlt.B.IsHaarOn (_root_.Formalism.QuantumDeterminants.UWset k r z) μW) (hN : _root_.Formalism.FourierDecayAlt.B.IsHaarOn (_root_.Formalism.QuantumDeterminants.Nset k r) μN)
    (hG : _root_.Formalism.FourierDecayAlt.B.IsHaarOn (_root_.BranchingSupport.GG k r) μG) (hπ : _root_.Formalism.FourierDecayAlt.Q.IsType k r z π u) :
    ∃ ν, _root_.BranchingSupport.SideG k r z π u μW μN μG ν := by
  have hW' : _root_.PI.BesselPeriodGGP.IsHaarOn (_root_.Formalism.QuantumDeterminants.UWset k r z) μW :=
    ((_root_.GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μW).2.2 z hz hT hk).2 hW
  have hN' : _root_.PI.BesselPeriodGGP.IsHaarOn (_root_.Formalism.QuantumDeterminants.Nset k r) μN :=
    ((_root_.GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μN).2.1).2 hN
  have hG' : _root_.PI.BesselPeriodGGP.IsHaarOn (_root_.BranchingSupport.GG k r) μG :=
    ((_root_.GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μG).1).2 hG
  obtain ⟨ν, hν⟩ :=
    _root_.GlobalTheory.exists_isQuotMeas_bessel_subgroup k r z μW μN μG hz hT hW' hN' hG'
  obtain ⟨u₀, hu₀⟩ := _root_.GlobalTheory.besType_hcParam k r W z π u hz hT hπ
  exact ⟨ν, hz, hT, ⟨u₀, hu₀⟩, hπ.2.2.2.2.2, hW', hN', hG', hν⟩

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in

theorem _root_.GlobalTheory.exists_sideG_both_of_isType : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type)
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq]
    (D : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (u u' : ℕ → ℝ), _root_.Formalism.FourierDecayAlt.Q.IsType k r D.z D.π u →
    _root_.Formalism.FourierDecayAlt.Q.IsType k r D.z' D.π' u' → ∃ νq νq',
      _root_.BranchingSupport.SideG k r D.z D.π u D.μW D.μN D.μG νq ∧
        _root_.BranchingSupport.SideG k r D.z' D.π' u' D.μW' D.μN D.μG νq' := by
  intro k r Wp _ _ _ _ Wq _ _ _ _ D u u' hp hq
  obtain ⟨z, z', π, π', μG, μW, μN, μW', _, _, hk, hz, hz', hT, hT', _, _, _, _, _, _, hG, hW,
    hN, hW', _, _, _, _⟩ := D
  obtain ⟨ν, hν⟩ := exists_quotient_side_of_isType_lemma k r Wp hk z π u μW μN μG hz hT hW hN hG hp
  obtain ⟨ν', hν'⟩ :=
    exists_quotient_side_of_isType_lemma k r Wq hk z' π' u' μW' μN μG hz' hT' hW' hN hG hq
  exact ⟨ν, ν', hν, hν'⟩

end GlobalTheory
