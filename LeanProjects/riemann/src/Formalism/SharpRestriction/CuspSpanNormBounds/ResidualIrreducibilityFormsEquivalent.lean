import Formalism.SharpRestriction.CuspSpanNormBounds.ChoiceOfModulusAndDiscriminant
import Formalism.SharpRestriction.CuspSpanNormBounds.RadialRules
import Formalism.SharpRestriction.CuspSpanNormBounds.RadialChainStatements
import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEstimateTheorem
import Formalism.SharpRestriction.CuspSpanNormBounds.HereditaryPositivity
import Formalism.SharpRestriction.CuspSpanNormBounds.RadialLemmaE
import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
import Formalism.FormalDegreeBessel.FinalIO
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra

namespace Formalism.MainNotions

section Parts25
variable {D : Formalism.BasicNotions.D7} {C : ℝ}
theorem ChoiceOfModulusAndDiscriminant.gauge_of (h : ChoiceOfModulusAndDiscriminant.aux₃ D C) : ChoiceOfModulusAndDiscriminant.RadialGauge D := h.1.1
theorem ChoiceOfModulusAndDiscriminant.herm_of (h : ChoiceOfModulusAndDiscriminant.aux₃ D C) : ChoiceOfModulusAndDiscriminant.RadialPartHermitian D C := h.1.2.1
theorem ChoiceOfModulusAndDiscriminant.capelli_of (h : ChoiceOfModulusAndDiscriminant.aux₃ D C) : ChoiceOfModulusAndDiscriminant.RadialCapelli D := h.1.2.2.1
theorem ChoiceOfModulusAndDiscriminant.top_of (h : ChoiceOfModulusAndDiscriminant.aux₃ D C) : ChoiceOfModulusAndDiscriminant.RadialHighestLevel D := h.1.2.2.2.1
theorem ChoiceOfModulusAndDiscriminant.signs_of (h : ChoiceOfModulusAndDiscriminant.aux₃ D C) : ChoiceOfModulusAndDiscriminant.RadialSigns D := h.1.2.2.2.2
theorem ChoiceOfModulusAndDiscriminant.rtt_of (h : ChoiceOfModulusAndDiscriminant.aux₃ D C) : ChoiceOfModulusAndDiscriminant.RadialRTTRelation D := h.2.1.1
theorem ChoiceOfModulusAndDiscriminant.det_of (h : ChoiceOfModulusAndDiscriminant.aux₃ D C) : ChoiceOfModulusAndDiscriminant.RadialDeterminant D := h.2.1.2
theorem ChoiceOfModulusAndDiscriminant.module_of (h : ChoiceOfModulusAndDiscriminant.aux₃ D C) : ChoiceOfModulusAndDiscriminant.WordModuleHermitian D C := h.2.2.1.1
theorem ChoiceOfModulusAndDiscriminant.rrherm_of (h : ChoiceOfModulusAndDiscriminant.aux₃ D C) : ChoiceOfModulusAndDiscriminant.ModuleFormHermitian D C := h.2.2.1.2.1
theorem ChoiceOfModulusAndDiscriminant.tele_of (h : ChoiceOfModulusAndDiscriminant.aux₃ D C) : ChoiceOfModulusAndDiscriminant.ModuleTelescoping D := h.2.2.1.2.2.1
theorem ChoiceOfModulusAndDiscriminant.entry_of (h : ChoiceOfModulusAndDiscriminant.aux₃ D C) : ChoiceOfModulusAndDiscriminant.CornerEntryProduct D := h.2.2.1.2.2.2.1
theorem ChoiceOfModulusAndDiscriminant.dual_of (h : ChoiceOfModulusAndDiscriminant.aux₃ D C) : ChoiceOfModulusAndDiscriminant.ModuleDualityInequality D C := h.2.2.1.2.2.2.2.1
theorem ChoiceOfModulusAndDiscriminant.wave_of (h : ChoiceOfModulusAndDiscriminant.aux₃ D C) : ChoiceOfModulusAndDiscriminant.ModulePlaneWave D := h.2.2.1.2.2.2.2.2
theorem ChoiceOfModulusAndDiscriminant.frame_of (h : ChoiceOfModulusAndDiscriminant.aux₃ D C) : ChoiceOfModulusAndDiscriminant.ThetaAdjointPositiveScalar D C := h.2.2.2.1
theorem ChoiceOfModulusAndDiscriminant.pos_of (h : ChoiceOfModulusAndDiscriminant.aux₃ D C) : ChoiceOfModulusAndDiscriminant.ConclusionE D C := h.2.2.2.2
end Parts25

theorem RadialRules.level_tools_of_admitted (D : Formalism.BasicNotions.D7) (C : ℝ) (h : ChoiceOfModulusAndDiscriminant.aux₃ D C) : RadialRules.adm7 D C := h.1

theorem RadialRules.lemma_M_prime_hypothesis (D : Formalism.BasicNotions.D7) (C : ℝ) (h : ChoiceOfModulusAndDiscriminant.aux₃ D C) : RadialRules.adm8 D := h.2.1

theorem RadialRules.crystalline_lift_of_theorem_c (D : Formalism.BasicNotions.D7) (C : ℝ) (h : ChoiceOfModulusAndDiscriminant.aux₃ D C) : RadialRules.adm9 D C := h.2.2.1

theorem RadialRules.condition_iff_additive_maps (D : Formalism.BasicNotions.D7) : RadialRules.adm5 D ↔ ChoiceOfModulusAndDiscriminant.adm5 D := Iff.rfl
theorem RadialRules.residualIrreducibility_forms_equivalent (D : Formalism.BasicNotions.D7) : RadialRules.adm6 D ↔ ChoiceOfModulusAndDiscriminant.adm6 D := Iff.rfl

theorem ChoiceOfModulusAndDiscriminant.subgroup_admissible_holds (D : Formalism.BasicNotions.D7) : ChoiceOfModulusAndDiscriminant.adm3 D :=
  ⟨Formalism.QuantumDeterminants.capCentralH, Formalism.QuantumDeterminants.capLeftH, Formalism.QuantumDeterminants.capHWH, Formalism.QuantumDeterminants.capComatrix, Formalism.QuantumDeterminants.qMinorLeft,
    Formalism.QuantumDeterminants.glRelAd, Formalism.QuantumDeterminants.eabHGl, Formalism.QuantumDeterminants.eabHTransport⟩

theorem RadialRules.subgroup_admissible_holds (D : Formalism.BasicNotions.D7) : RadialRules.adm3 D := ChoiceOfModulusAndDiscriminant.subgroup_admissible_holds D

section RadialChainStatements
variable (D : Formalism.BasicNotions.D7) (C : ℝ)

theorem RadialChainStatements.restriction_dimension_of_division (h : ChoiceOfModulusAndDiscriminant.aux₃ D C) : RadialChainStatements.adm6 D C := ⟨ChoiceOfModulusAndDiscriminant.module_of h, ChoiceOfModulusAndDiscriminant.rrherm_of h⟩

theorem RadialChainStatements.level_tools_of_admitted (h : ChoiceOfModulusAndDiscriminant.aux₃ D C) : RadialChainStatements.adm7 D := ⟨ChoiceOfModulusAndDiscriminant.tele_of h, ChoiceOfModulusAndDiscriminant.entry_of h⟩

end RadialChainStatements

theorem RadialChainStatements.killer_conditions_of_stable (D : Formalism.BasicNotions.D7) (CB Cv C1 C2 : ℝ) (hC1 : 0 < C1) (h : RadialRules.aux₃ D CB Cv C1 C2) :
    RadialChainStatements.adm11 D CB Cv C1 C2 := ⟨hC1, h⟩

section BlockEstimateTheorem
variable (D : Formalism.BasicNotions.D7) (C : ℝ)

theorem BlockEstimateTheorem.restriction_dimension_of_division (h : ChoiceOfModulusAndDiscriminant.aux₃ D C) : BlockEstimateTheorem.adm6 D C := ⟨ChoiceOfModulusAndDiscriminant.module_of h, ChoiceOfModulusAndDiscriminant.rrherm_of h⟩

theorem BlockEstimateTheorem.level_tools_of_admitted (h : ChoiceOfModulusAndDiscriminant.aux₃ D C) : BlockEstimateTheorem.adm7 D := ⟨ChoiceOfModulusAndDiscriminant.tele_of h, ChoiceOfModulusAndDiscriminant.entry_of h⟩

end BlockEstimateTheorem

theorem BlockEstimateTheorem.killer_conditions_of_stable (D : Formalism.BasicNotions.D7) (CB Cv C1 C2 : ℝ) (hC1 : 0 < C1) (h : RadialRules.aux₃ D CB Cv C1 C2) :
    BlockEstimateTheorem.adm11 D CB Cv C1 C2 := ⟨hC1, h⟩

section HereditaryPositivity
variable (D : Formalism.BasicNotions.D7) (C : ℝ)

theorem HereditaryPositivity.restriction_dimension_of_division (h : ChoiceOfModulusAndDiscriminant.aux₃ D C) : HereditaryPositivity.adm6 D C := ⟨ChoiceOfModulusAndDiscriminant.module_of h, ChoiceOfModulusAndDiscriminant.rrherm_of h⟩

theorem HereditaryPositivity.level_tools_of_admitted (h : ChoiceOfModulusAndDiscriminant.aux₃ D C) : HereditaryPositivity.adm7 D := ⟨ChoiceOfModulusAndDiscriminant.tele_of h, ChoiceOfModulusAndDiscriminant.entry_of h⟩

end HereditaryPositivity

theorem HereditaryPositivity.killer_conditions_of_stable (D : Formalism.BasicNotions.D7) (CB Cv C1 C2 : ℝ) (hC1 : 0 < C1) (h : RadialRules.aux₃ D CB Cv C1 C2) :
    HereditaryPositivity.adm11 D CB Cv C1 C2 := ⟨hC1, h⟩

section RadialRuleConsequences
variable (D : Formalism.BasicNotions.D7) (C : ℝ)

theorem RadialRuleConsequences.restriction_dimension_of_division (h : ChoiceOfModulusAndDiscriminant.aux₃ D C) : RadialRuleConsequences.adm6 D C := ⟨ChoiceOfModulusAndDiscriminant.module_of h, ChoiceOfModulusAndDiscriminant.rrherm_of h⟩

theorem RadialRuleConsequences.level_tools_of_admitted (h : ChoiceOfModulusAndDiscriminant.aux₃ D C) : RadialRuleConsequences.adm7 D := ⟨ChoiceOfModulusAndDiscriminant.tele_of h, ChoiceOfModulusAndDiscriminant.entry_of h⟩

end RadialRuleConsequences

theorem RadialRuleConsequences.killer_conditions_of_stable (D : Formalism.BasicNotions.D7) (CB Cv C1 C2 : ℝ) (hC1 : 0 < C1) (h : RadialRules.aux₃ D CB Cv C1 C2) :
    RadialRuleConsequences.adm11 D CB Cv C1 C2 := ⟨hC1, h⟩

section OnePlaceEstimates
variable (D : Formalism.BasicNotions.D7) (C : ℝ)

theorem OnePlaceEstimates.integrality_of_commutation (h : ChoiceOfModulusAndDiscriminant.aux₃ D C) : OnePlaceEstimates.adm3 D := ⟨ChoiceOfModulusAndDiscriminant.top_of h, ChoiceOfModulusAndDiscriminant.signs_of h⟩

theorem OnePlaceEstimates.restriction_dimension_of_division (h : ChoiceOfModulusAndDiscriminant.aux₃ D C) : OnePlaceEstimates.adm6 D := ⟨ChoiceOfModulusAndDiscriminant.tele_of h, ChoiceOfModulusAndDiscriminant.entry_of h⟩

theorem OnePlaceEstimates.crystalline_lift_of_theorem_c (h : ChoiceOfModulusAndDiscriminant.aux₃ D C) : OnePlaceEstimates.adm9 D C := ⟨ChoiceOfModulusAndDiscriminant.pos_of h, ChoiceOfModulusAndDiscriminant.frame_of h⟩

variable (Gm : HereditaryPositivity.GM) (Ks : ℕ) (E₀ Eg E₁ E₂ E₃ : ℝ)

theorem OnePlaceEstimates.column_lemma_of_definite_form (h : HereditaryPositivity.aux₃ D Gm Ks E₀ Eg E₁ E₂ E₃) : OnePlaceEstimates.adm17 D Gm Ks E₀ Eg E₁ E₂ E₃ := h.2.2.2

end OnePlaceEstimates

open Filter Topology in

def HereditaryPositivity.EnergyBridge (D : Formalism.BasicNotions.D7) (Ks : ℕ) (C₀ Cg : ℝ) : Prop :=
  ∀ (k0 : ℕ) (X : S.GramWordSpace.Dat D k0), X.Std Ks C₀ Cg → ∀ χ : ℝ → ℝ, S.IsCutoff χ → ∀ w : S.GramWordSpace.GWord D, X.admitted w →
    S.GramWordSpace.Len (S.GramWordSpace.NN D Ks) w → ∀ ε : ℝ, 0 < ε → ∀ v,
      X.gramLow v 0 (Nat.zero_le _) (w v) (X.Fv χ ε v) S.GramWordSpace.pt0 S.GramWordSpace.pt0 =
        RadialRuleConsequences.energy (X.B v) (X.μsec v) (X.I v) (w v) (RadialRuleConsequences.cutF (X.B v).z (X.B v).z' χ ε (X.f v))

open Filter Topology in

theorem HereditaryPositivity.baseChange_preserves_unitary_of (D : Formalism.BasicNotions.D7) (Ks : ℕ) (C₀ Cg : ℝ) (hC : 0 ≤ C₀) (hbr : HereditaryPositivity.EnergyBridge D Ks C₀ Cg)
    (h : RadialRuleConsequences.Conclusion1 D Cg C₀) : HereditaryPositivity.Conclusion1 D Ks C₀ Cg := by
  intro k0 X hS χ hχ w hA hL
  have hlim : ∀ v, Tendsto (fun ε : ℝ => RadialRuleConsequences.energy (X.B v) (X.μsec v) (X.I v) (w v)
      (RadialRuleConsequences.cutF (X.B v).z (X.B v).z' χ ε (X.f v))) (𝓝[>] 0)
      (𝓝 ((S.brkW (X.B v).lam ((w v).map Prod.snd) : ℂ) * (X.B v).beta (X.μsec v) (X.f v) (X.f v))) := by
    intro v
    obtain ⟨hK, hv⟩ := hS
    obtain ⟨e1, e2, e3, e4, ⟨_, _, hab, _⟩, e6, _, _, _, e10, e11, e12, e13, e14, _, _⟩ := hv v
    refine h k0 X.hk (X.B v) (X.μsec v) (X.I v) (S.GramWordSpace.NN D Ks) (X.f v) χ (w v) ⟨e1, e2, e3, e4, e6⟩ e10 e11 e13
      ?_ ?_ e14 hχ (hA v) (hL v)
    · exact Nat.le_mul_of_pos_left _ (by omega)
    · have hI : sSup (X.I v) - sInf (X.I v) = X.b v - X.a v := by
        simp [S.GramWordSpace.Dat.I, csSup_Icc hab, csInf_Icc hab]
      rw [hI]
      refine le_trans (mul_le_mul_of_nonneg_left ?_ hC) e12
      have : (0 : ℝ) ≤ ((S.GramWordSpace.NN D Ks : ℕ) : ℝ) ^ 3 := by positivity
      linarith
  have hprod := tendsto_finsetProd Finset.univ (fun v _ => hlim v)
  have htgt : ((X.brk w : ℝ) : ℂ) * X.jn2 =
      ∏ v, ((S.brkW (X.B v).lam ((w v).map Prod.snd) : ℂ) * (X.B v).beta (X.μsec v) (X.f v) (X.f v)) := by
    unfold S.GramWordSpace.Dat.brk S.GramWordSpace.Dat.jn2
    rw [Finset.prod_mul_distrib]
    push_cast
    rfl
  rw [htgt]
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  unfold S.GramWordSpace.Dat.energy
  exact (Finset.prod_congr rfl (fun v _ => hbr k0 X hS χ hχ w hA hL ε hε v)).symm

section P07aE
variable (D : Formalism.BasicNotions.D7) (Gm : HereditaryPositivity.GM) (Ks : ℕ) (E₀ Eg E₁ E₂ E₃ : ℝ)

end P07aE

def RadialRuleConsequences.Rest (D : Formalism.BasicNotions.D7) (CB Co Cd Cs c C₁ : ℝ) : Prop :=
  RadialRuleConsequences.adm1 D CB ∧ RadialRuleConsequences.CapelliEigenvalueAlt D ∧ RadialRuleConsequences.adm3b D ∧ RadialRuleConsequences.ArithmeticRiemannRochThetaCond D ∧ RadialRuleConsequences.DualityForLists D CB Co Cd ∧ RadialRuleConsequences.adm9 D ∧
    RadialRuleConsequences.PlaneWaveLetters D ∧ RadialRuleConsequences.SliceBoundC D Cs ∧ RadialRuleConsequences.SmoothnessTheoremP D CB ∧ RadialRuleConsequences.SliceBoundE D Cs ∧ RadialRuleConsequences.adm13 D c C₁ ∧ RadialRuleConsequences.adm14 D ∧ RadialRuleConsequences.adm15 D ∧
    RadialRuleConsequences.adm16 D ∧ RadialRuleConsequences.adm17 D ∧ RadialRuleConsequences.adm18 D

theorem RadialRuleConsequences.Adm_of (D : Formalism.BasicNotions.D7) (CB Co Cd Cv C1 C2 Cs c C₁ : ℝ) (hC1 : 0 < C1) (h : ChoiceOfModulusAndDiscriminant.aux₃ D CB)
    (hb : RadialRules.aux₃ D CB Cv C1 C2) (hR : RadialRuleConsequences.Rest D CB Co Cd Cs c C₁) :
    RadialRuleConsequences.admitted D CB Co Cd Cv C1 C2 Cs c C₁ := by
  obtain ⟨r1, r2d, r3b, r4a, r8b, r9, r10a, r12c, r12d, r12e, r13, r14, r15, r16, r17, r18⟩ := hR
  exact ⟨r1, ⟨ChoiceOfModulusAndDiscriminant.gauge_of h, ChoiceOfModulusAndDiscriminant.herm_of h, ChoiceOfModulusAndDiscriminant.capelli_of h, r2d⟩, ⟨ChoiceOfModulusAndDiscriminant.top_of h, r3b, ChoiceOfModulusAndDiscriminant.signs_of h⟩,
    ⟨r4a, ChoiceOfModulusAndDiscriminant.rtt_of h⟩, ChoiceOfModulusAndDiscriminant.det_of h, RadialRuleConsequences.restriction_dimension_of_division D CB h, RadialRuleConsequences.level_tools_of_admitted D CB h, ⟨ChoiceOfModulusAndDiscriminant.dual_of h, r8b⟩, r9,
    ⟨r10a, ChoiceOfModulusAndDiscriminant.wave_of h⟩, RadialRuleConsequences.killer_conditions_of_stable D CB Cv C1 C2 hC1 hb, ⟨ChoiceOfModulusAndDiscriminant.frame_of h, ChoiceOfModulusAndDiscriminant.pos_of h, r12c, r12d, r12e⟩, r13, r14,
    r15, r16, r17, r18⟩

def RadialChainStatements.Rest (D : Formalism.BasicNotions.D7) (CB Co Cd Cs c C₁ Cg₁ Cg₂ : ℝ) : Prop :=
  RadialChainStatements.adm1 D CB ∧ RadialChainStatements.CapelliEigenvalueAlt D ∧ RadialChainStatements.adm3b D ∧ RadialChainStatements.ArithmeticRiemannRochThetaCond D ∧ RadialChainStatements.DualityForLists D CB Co Cd ∧ RadialChainStatements.adm9 D ∧
    RadialChainStatements.PlaneWaveLetters D ∧ RadialChainStatements.SliceBoundC D Cs ∧ RadialChainStatements.SmoothnessTheoremP D CB ∧ RadialChainStatements.SliceBoundE D Cs ∧ RadialChainStatements.adm13 D c C₁ ∧ RadialChainStatements.adm14 D ∧
    RadialChainStatements.adm15 D ∧ RadialChainStatements.adm16 D ∧ RadialChainStatements.adm17 D Cg₁ Cg₂ ∧ RadialChainStatements.adm18 D

theorem RadialChainStatements.Adm_of (D : Formalism.BasicNotions.D7) (CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ : ℝ) (hC1 : 0 < C1) (h : ChoiceOfModulusAndDiscriminant.aux₃ D CB)
    (hb : RadialRules.aux₃ D CB Cv C1 C2) (hR : RadialChainStatements.Rest D CB Co Cd Cs c C₁ Cg₁ Cg₂) :
    RadialChainStatements.admitted D CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ := by
  obtain ⟨r1, r2d, r3b, r4a, r8b, r9, r10a, r12c, r12d, r12e, r13, r14, r15, r16, r17, r18⟩ := hR
  exact ⟨r1, ⟨ChoiceOfModulusAndDiscriminant.gauge_of h, ChoiceOfModulusAndDiscriminant.herm_of h, ChoiceOfModulusAndDiscriminant.capelli_of h, r2d⟩, ⟨ChoiceOfModulusAndDiscriminant.top_of h, r3b, ChoiceOfModulusAndDiscriminant.signs_of h⟩,
    ⟨r4a, ChoiceOfModulusAndDiscriminant.rtt_of h⟩, ChoiceOfModulusAndDiscriminant.det_of h, RadialChainStatements.restriction_dimension_of_division D CB h, RadialChainStatements.level_tools_of_admitted D CB h, ⟨ChoiceOfModulusAndDiscriminant.dual_of h, r8b⟩, r9,
    ⟨r10a, ChoiceOfModulusAndDiscriminant.wave_of h⟩, RadialChainStatements.killer_conditions_of_stable D CB Cv C1 C2 hC1 hb, ⟨⟨ChoiceOfModulusAndDiscriminant.frame_of h, ChoiceOfModulusAndDiscriminant.pos_of h, r12c, r12d⟩, r12e⟩, r13,
    r14, r15, r16, r17, r18⟩

def HereditaryPositivity.Rest (D : Formalism.BasicNotions.D7) (Gm : HereditaryPositivity.GM) (CB Co Cd Cs c C₁ : ℝ) (Ks : ℕ) (C₀ Cg : ℝ) : Prop :=
  HereditaryPositivity.adm1 D CB ∧ HereditaryPositivity.CapelliEigenvalueAlt D ∧ HereditaryPositivity.adm3b D ∧ HereditaryPositivity.ArithmeticRiemannRochThetaCond D ∧ HereditaryPositivity.DualityForLists D CB Co Cd ∧ HereditaryPositivity.adm9 D ∧
    HereditaryPositivity.PlaneWaveLetters D ∧ HereditaryPositivity.SliceBoundC D Cs ∧ HereditaryPositivity.SmoothnessTheoremP D CB ∧ HereditaryPositivity.SliceBoundE D Gm Ks C₀ Cg ∧ HereditaryPositivity.TopLevelPlaneWave D Gm Ks C₀ Cg ∧
    HereditaryPositivity.LowerLevelPositivity D Ks C₀ Cg ∧ HereditaryPositivity.adm13 D c C₁ ∧ HereditaryPositivity.adm14 D ∧ HereditaryPositivity.adm15 D ∧ HereditaryPositivity.adm16 D ∧ HereditaryPositivity.adm17 D ∧ HereditaryPositivity.adm18 D

theorem HereditaryPositivity.Adm_of (D : Formalism.BasicNotions.D7) (Gm : HereditaryPositivity.GM) (CB Co Cd Cv C1 C2 Cs c C₁ : ℝ) (Ks : ℕ) (C₀ Cg : ℝ)
    (hC1 : 0 < C1) (h : ChoiceOfModulusAndDiscriminant.aux₃ D CB) (hb : RadialRules.aux₃ D CB Cv C1 C2)
    (hR : HereditaryPositivity.Rest D Gm CB Co Cd Cs c C₁ Ks C₀ Cg) : HereditaryPositivity.admitted D Gm CB Co Cd Cv C1 C2 Cs c C₁ Ks C₀ Cg := by
  obtain ⟨r1, r2d, r3b, r4a, r8b, r9, r10a, r12c, r12d, r12e, r12f, r12g, r13, r14, r15, r16, r17, r18⟩ := hR
  exact ⟨r1, ⟨ChoiceOfModulusAndDiscriminant.gauge_of h, ChoiceOfModulusAndDiscriminant.herm_of h, ChoiceOfModulusAndDiscriminant.capelli_of h, r2d⟩, ⟨ChoiceOfModulusAndDiscriminant.top_of h, r3b, ChoiceOfModulusAndDiscriminant.signs_of h⟩,
    ⟨r4a, ChoiceOfModulusAndDiscriminant.rtt_of h⟩, ChoiceOfModulusAndDiscriminant.det_of h, HereditaryPositivity.restriction_dimension_of_division D CB h, HereditaryPositivity.level_tools_of_admitted D CB h, ⟨ChoiceOfModulusAndDiscriminant.dual_of h, r8b⟩, r9,
    ⟨r10a, ChoiceOfModulusAndDiscriminant.wave_of h⟩, HereditaryPositivity.killer_conditions_of_stable D CB Cv C1 C2 hC1 hb, ⟨ChoiceOfModulusAndDiscriminant.frame_of h, ChoiceOfModulusAndDiscriminant.pos_of h, r12c, r12d⟩, r12e, r12f,
    r12g, r13, r14, r15, r16, r17, r18⟩

def OnePlaceEstimates.Rest (D : Formalism.BasicNotions.D7) (Gm : HereditaryPositivity.GM) (CB Co Cd Cg₁ Cg₂ c C₁ Cs C₃ : ℝ) : Prop :=
  OnePlaceEstimates.adm1 D CB ∧ OnePlaceEstimates.ArithmeticRiemannRochThetaCond D ∧ OnePlaceEstimates.ConjugateSelfDualCharacter D CB Co Cd ∧ OnePlaceEstimates.DualityInequality D ∧ OnePlaceEstimates.adm11 D Cg₁ Cg₂ ∧ OnePlaceEstimates.adm12 D CB ∧
    OnePlaceEstimates.ShortGridGramBound D Gm CB Cs ∧ OnePlaceEstimates.LiftGridGramBound D Gm CB Cs ∧ OnePlaceEstimates.LargeBlockGridBound D Gm CB Cs C₃ ∧ OnePlaceEstimates.UniformGridGramBound D Gm CB Cs C₃ ∧ OnePlaceEstimates.adm18 D ∧
    OnePlaceEstimates.DualTranslationPrinciple D ∧ OnePlaceEstimates.adm19 D ∧ OnePlaceEstimates.adm20 D ∧ OnePlaceEstimates.adm21 D c C₁ ∧ OnePlaceEstimates.CapelliEigenvalueAlt D

theorem OnePlaceEstimates.Adm_of (D : Formalism.BasicNotions.D7) (Gm : HereditaryPositivity.GM) (CB Co Cd C0 CA Cg₁ Cg₂ c C₁ : ℝ) (Ks : ℕ)
    (E₀ Eg E₁ E₂ E₃ Cs C₃ Ch Cg Cq : ℝ) (h : ChoiceOfModulusAndDiscriminant.aux₃ D CB) (hE : RadialRuleConsequences.Conclusion2 D C0 CA)
    (hb : HereditaryPositivity.aux₃ D Gm Ks E₀ Eg E₁ E₂ E₃) (hR : OnePlaceEstimates.Rest D Gm CB Co Cd Cg₁ Cg₂ c C₁ Cs C₃)
    (h22 : OnePlaceEstimates.adm22 D Ch Cg Cq) :
    OnePlaceEstimates.admitted D Gm CB Co Cd C0 CA Cg₁ Cg₂ c C₁ Ks E₀ Eg E₁ E₂ E₃ Cs C₃ Ch Cg Cq := by
  obtain ⟨r1, r4a, r7b, r8a, r11, r12, r13s, r15s, r17s, r17u, r18, r18d, r19, r20, r21, r2d⟩ := hR
  exact ⟨r1, ChoiceOfModulusAndDiscriminant.gauge_of h, OnePlaceEstimates.integrality_of_commutation D CB h, ⟨r4a, ChoiceOfModulusAndDiscriminant.rtt_of h⟩, ChoiceOfModulusAndDiscriminant.det_of h, OnePlaceEstimates.restriction_dimension_of_division D CB h,
    ⟨ChoiceOfModulusAndDiscriminant.dual_of h, r7b⟩, ⟨r8a, ChoiceOfModulusAndDiscriminant.wave_of h⟩, OnePlaceEstimates.crystalline_lift_of_theorem_c D CB h, hE, r11, r12, hb.2.1, hb.2.2.1, hb.2.2.2, r13s, r15s,
    r17s, r17u, r18, r18d, r19, r20, r21, h22, r2d⟩

def BlockEstimateTheorem.Rest (D : Formalism.BasicNotions.D7) (Gm : BlockEstimateTheorem.GM) (Ks : ℕ) (CB Co Cd Cs c C₁ Cg₁ Cg₂ E₀ Eg : ℝ) : Prop :=
  BlockEstimateTheorem.adm1 D CB ∧ BlockEstimateTheorem.CapelliEigenvalueAlt D ∧ BlockEstimateTheorem.adm3b D ∧ BlockEstimateTheorem.ArithmeticRiemannRochThetaCond D ∧ BlockEstimateTheorem.DualityForLists D CB Co Cd ∧ BlockEstimateTheorem.adm9 D ∧
    BlockEstimateTheorem.PlaneWaveLetters D ∧ BlockEstimateTheorem.SliceBoundC D Cs ∧ BlockEstimateTheorem.SmoothnessTheoremP D CB ∧ BlockEstimateTheorem.SliceBoundE D Gm Ks E₀ Eg ∧ BlockEstimateTheorem.TopLevelPlaneWave D Gm Ks E₀ Eg ∧
    BlockEstimateTheorem.LowerLevelPositivity D Ks E₀ Eg ∧ BlockEstimateTheorem.adm23 D ∧
    BlockEstimateTheorem.adm13 D c C₁ ∧ BlockEstimateTheorem.adm14 D ∧ BlockEstimateTheorem.adm15 D ∧ BlockEstimateTheorem.adm16 D ∧ BlockEstimateTheorem.adm17 D Cg₁ Cg₂ ∧ BlockEstimateTheorem.adm18 D

theorem BlockEstimateTheorem.Adm_of (D : Formalism.BasicNotions.D7) (Gm : BlockEstimateTheorem.GM) (Ks : ℕ)
    (CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ E₀ Eg E₁ E₂ E₃ : ℝ) (hC1 : 0 < C1) (h : ChoiceOfModulusAndDiscriminant.aux₃ D CB)
    (hb : RadialRules.aux₃ D CB Cv C1 C2) (hE : HereditaryPositivity.aux₃ D Gm Ks E₀ Eg E₁ E₂ E₃)
    (hR : BlockEstimateTheorem.Rest D Gm Ks CB Co Cd Cs c C₁ Cg₁ Cg₂ E₀ Eg) :
    BlockEstimateTheorem.admitted D Gm Ks CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ E₀ Eg E₁ E₂ E₃ := by
  obtain ⟨r1, r2d, r3b, r4a, r8b, r9, r10a, r12c, r12d, r12e, r12f, r12g, r23, r13, r14, r15, r16, r17, r18⟩ := hR
  exact ⟨⟨r1, ⟨ChoiceOfModulusAndDiscriminant.gauge_of h, ChoiceOfModulusAndDiscriminant.herm_of h, ChoiceOfModulusAndDiscriminant.capelli_of h, r2d⟩, ⟨ChoiceOfModulusAndDiscriminant.top_of h, r3b, ChoiceOfModulusAndDiscriminant.signs_of h⟩,
    ⟨r4a, ChoiceOfModulusAndDiscriminant.rtt_of h⟩, ChoiceOfModulusAndDiscriminant.det_of h, BlockEstimateTheorem.restriction_dimension_of_division D CB h, BlockEstimateTheorem.level_tools_of_admitted D CB h, ⟨ChoiceOfModulusAndDiscriminant.dual_of h, r8b⟩, r9,
    ⟨r10a, ChoiceOfModulusAndDiscriminant.wave_of h⟩, BlockEstimateTheorem.killer_conditions_of_stable D CB Cv C1 C2 hC1 hb, ⟨ChoiceOfModulusAndDiscriminant.frame_of h, ChoiceOfModulusAndDiscriminant.pos_of h, r12c, r12d⟩, r13, r14,
    r15, r16, r17, r18⟩, r12e, r12f, hE.1, hE.2.1, hE.2.2.1, hE.2.2.2, r12g, r23⟩

section Same
variable (D : Formalism.BasicNotions.D7)

theorem RadialRuleConsequences.bessel_model_uniqueness_generic (h : RadialChainStatements.adm18 D) : RadialRuleConsequences.adm18 D := fun k r L B₁ B₂ hc =>
  h k r L B₁ B₂ (by rw [hc]; simp [Formalism.QuantumDeterminants.cStd])

end Same

theorem RadialRules.Adm_of (D : Formalism.BasicNotions.D7) (CB Ca : ℝ) (hA : ChoiceOfModulusAndDiscriminant.admitted D CB) (h : ChoiceOfModulusAndDiscriminant.aux₃ D Ca) : RadialRules.admitted D CB Ca := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hA
  exact ⟨a1, a2, a3, a4, a5, a6, h.1, h.2.1, h.2.2.1, a7⟩

def ChainHypothesesBlockEstimate (Gm : BlockEstimateTheorem.GM) (Ks : ℕ) : Prop :=
  ∃ CB₀ Co Cd Cs c C₁ Cg₁ Cg₂ E₀₀ Eg₀ : ℝ, ∀ CB ≥ CB₀, ∀ D : Formalism.BasicNotions.D7, ChoiceOfModulusAndDiscriminant.admitted D CB ∧
    ∀ E₀ ≥ E₀₀, ∀ Eg ≥ Eg₀, BlockEstimateTheorem.Rest D Gm Ks CB Co Cd Cs c C₁ Cg₁ Cg₂ E₀ Eg ∧ HereditaryPositivity.Rest D Gm CB Co Cd Cs c C₁ Ks E₀ Eg

def ChainHypothesesHereditaryPositivity (Gm : HereditaryPositivity.GM) (Ks : ℕ) : Prop :=
  (∃ CB₀ Co Cd Cs c C₁ Cg₁ Cg₂ Ss C₃ E₀₀ Eg₀ : ℝ, ∀ CB ≥ CB₀, ∀ D : Formalism.BasicNotions.D7, ChoiceOfModulusAndDiscriminant.admitted D CB ∧
    RadialRuleConsequences.Rest D CB Co Cd Cs c C₁ ∧ OnePlaceEstimates.Rest D Gm CB Co Cd Cg₁ Cg₂ c C₁ Ss C₃ ∧
    ∀ E₀ ≥ E₀₀, ∀ Eg ≥ Eg₀, HereditaryPositivity.Rest D Gm CB Co Cd Cs c C₁ Ks E₀ Eg) ∧
  ∀ Ch : ℝ, ∃ Gg₀ Gq₀ : ℝ, ∀ Cg ≥ Gg₀, ∀ Cq ≥ Gq₀, ∀ D : Formalism.BasicNotions.D7, OnePlaceEstimates.adm22 D Ch Cg Cq

section Assembly

variable {CB Co Cd Cs Cg₁ Cg₂ c C₁ : ℝ}

theorem RadialRuleConsequences.Rest_of (D : Formalism.BasicNotions.D7) (hCo : 0 < Co) (hX : PX.S1 CB Co Cd Cs Cg₁ Cg₂) (hd : PX.decay D c C₁)
    (hL : PX.ClassicalAnalysisAndRepresentationTheorems) : RadialRuleConsequences.Rest D CB Co Cd Cs c C₁ :=
  ⟨hX.lemmaB, hL.capEig, hX.t22, hX.LetterIdentitiesRTT, ⟨hCo, hX.dualList⟩, ⟨hX.PointwiseIntegrationByParts, hX.ConjugationIdentity⟩, hX.PlaneWaveLetterIdentities, hX.slices,
    hX.smooth, hX.slicesOrb, hd, hL.markov, hL.herglotz, hL.poisson, hL.statPhase, RadialRuleConsequences.bessel_model_uniqueness_generic D hL.besselModel_unique⟩

theorem RadialChainStatements.Rest_of (D : Formalism.BasicNotions.D7) (hCo : 0 < Co) (hX : PX.S1 CB Co Cd Cs Cg₁ Cg₂) (hd : PX.decay D c C₁)
    (hL : PX.ClassicalAnalysisAndRepresentationTheorems) : RadialChainStatements.Rest D CB Co Cd Cs c C₁ Cg₁ Cg₂ :=
  ⟨hX.lemmaB, hL.capEig, hX.t22, hX.LetterIdentitiesRTT, ⟨hCo, hX.dualList⟩, ⟨hX.PointwiseIntegrationByParts, hX.ConjugationIdentity⟩, hX.PlaneWaveLetterIdentities, hX.slices,
    hX.smooth, hX.slicesOrb, hd, hL.markov, hL.herglotz, hL.poisson, hX.germ, hL.besselModel_unique⟩

theorem HereditaryPositivity.Rest_of (D : Formalism.BasicNotions.D7) (Gm : HereditaryPositivity.GM) (Ks : ℕ) (E₀ Eg : ℝ) (hCo : 0 < Co)
    (hX : PX.S1 CB Co Cd Cs Cg₁ Cg₂) (hd : PX.decay D c C₁) (hp : PX.topPos D Gm Ks E₀ Eg)
    (hw : PX.topWave D Gm Ks E₀ Eg) (hl : PX.lowPos D Ks E₀ Eg) (hL : PX.ClassicalAnalysisAndRepresentationTheorems) :
    HereditaryPositivity.Rest D Gm CB Co Cd Cs c C₁ Ks E₀ Eg :=
  ⟨hX.lemmaB, hL.capEig, hX.t22, hX.LetterIdentitiesRTT, ⟨hCo, hX.dualList⟩, ⟨hX.PointwiseIntegrationByParts, hX.ConjugationIdentity⟩, hX.PlaneWaveLetterIdentities, hX.slicesOrb,
    hX.smooth, hp, hw, hl, hd, hL.markov, hL.herglotz, hL.poisson, hL.statPhase, RadialRuleConsequences.bessel_model_uniqueness_generic D hL.besselModel_unique⟩

theorem BlockEstimateTheorem.Rest_of (D : Formalism.BasicNotions.D7) (Gm : HereditaryPositivity.GM) (Ks : ℕ) (E₀ Eg : ℝ) (hCo : 0 < Co)
    (hX : PX.S1 CB Co Cd Cs Cg₁ Cg₂) (hd : PX.decay D c C₁) (hp : PX.topPos D Gm Ks E₀ Eg)
    (hw : PX.topWave D Gm Ks E₀ Eg) (hl : PX.lowPos D Ks E₀ Eg) (hL : PX.ClassicalAnalysisAndRepresentationTheorems) :
    BlockEstimateTheorem.Rest D Gm Ks CB Co Cd Cs c C₁ Cg₁ Cg₂ E₀ Eg :=
  ⟨hX.lemmaB, hL.capEig, hX.t22, hX.LetterIdentitiesRTT, ⟨hCo, hX.dualList⟩, ⟨hX.PointwiseIntegrationByParts, hX.ConjugationIdentity⟩, hX.PlaneWaveLetterIdentities,
    hX.slicesOrb, hX.smooth, hp, hw, hl, hX.lettersExist, hd, hL.markov, hL.herglotz, hL.poisson, hX.germ, hL.besselModel_unique⟩

theorem OnePlaceEstimates.Rest_of (D : Formalism.BasicNotions.D7) (Gm : HereditaryPositivity.GM) (Ss C₃ : ℝ) (hCo : 0 < Co) (hX : PX.S1 CB Co Cd Cs Cg₁ Cg₂)
    (hd : PX.decay D c C₁) (h71 : PX.LettersOnCells D CB) (hs : PX.shortGrids D Gm CB Ss C₃) (hL : PX.ClassicalAnalysisAndRepresentationTheorems) :
    OnePlaceEstimates.Rest D Gm CB Co Cd Cg₁ Cg₂ c C₁ Ss C₃ :=
  ⟨hX.lemmaB, hX.LetterIdentitiesRTT, ⟨hCo, hX.dualList⟩, hX.PlaneWaveLetterIdentities, hX.germ, h71, hs.e72, hs.e73, hs.e74, hs.sup, hL.tensorDS D,
    hL.tensorDSd D, hL.besselModel_unique, hL.kTypes D, hd, hL.capEig⟩

theorem ChoiceOfModulusAndDiscriminant.Adm_of (D : Formalism.BasicNotions.D7) (hB : PX.lemmaB CB) (hL : PX.ClassicalAnalysisAndRepresentationTheorems) : ChoiceOfModulusAndDiscriminant.admitted D CB :=
  ⟨hB.1, hB.2.1, ChoiceOfModulusAndDiscriminant.subgroup_admissible_holds D, hL.qAnti, hL.qBranch, hL.qWigner, hB.2.2.1⟩

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

theorem ChoiceOfModulusAndDiscriminant.AdmF_of (hB : PX.lemmaB CB) (hL : PX.ClassicalAnalysisAndRepresentationTheorems) : ChoiceOfModulusAndDiscriminant.AdmF Fm CB :=
  ⟨fun x i => (ChoiceOfModulusAndDiscriminant.Adm_of (Fm.D x i) hB hL).1,
    fun x i => (ChoiceOfModulusAndDiscriminant.Adm_of (Fm.D x i) hB hL).2.1,
    fun x i => (ChoiceOfModulusAndDiscriminant.Adm_of (Fm.D x i) hB hL).2.2.1,
    fun x i => (ChoiceOfModulusAndDiscriminant.Adm_of (Fm.D x i) hB hL).2.2.2.1,
    fun x i => (ChoiceOfModulusAndDiscriminant.Adm_of (Fm.D x i) hB hL).2.2.2.2.1,
    fun x i => (ChoiceOfModulusAndDiscriminant.Adm_of (Fm.D x i) hB hL).2.2.2.2.2.1,
    fun x i => (ChoiceOfModulusAndDiscriminant.Adm_of (Fm.D x i) hB hL).2.2.2.2.2.2⟩

theorem RadialRules.AdmF_of (Ca : ℝ) (h25 : ChoiceOfModulusAndDiscriminant.FamilyTargetsAtConstants Fm Ca) (hB : PX.lemmaB CB) (hL : PX.ClassicalAnalysisAndRepresentationTheorems) : RadialRules.AdmF Fm CB Ca :=
  ⟨fun x i => (RadialRules.Adm_of (Fm.D x i) CB Ca (ChoiceOfModulusAndDiscriminant.Adm_of (Fm.D x i) hB hL) (h25 x i)).1,
    fun x i => (RadialRules.Adm_of (Fm.D x i) CB Ca (ChoiceOfModulusAndDiscriminant.Adm_of (Fm.D x i) hB hL) (h25 x i)).2.1,
    fun x i => (RadialRules.Adm_of (Fm.D x i) CB Ca (ChoiceOfModulusAndDiscriminant.Adm_of (Fm.D x i) hB hL) (h25 x i)).2.2.1,
    fun x i => (RadialRules.Adm_of (Fm.D x i) CB Ca (ChoiceOfModulusAndDiscriminant.Adm_of (Fm.D x i) hB hL) (h25 x i)).2.2.2.1,
    fun x i => (RadialRules.Adm_of (Fm.D x i) CB Ca (ChoiceOfModulusAndDiscriminant.Adm_of (Fm.D x i) hB hL) (h25 x i)).2.2.2.2.1,
    fun x i => (RadialRules.Adm_of (Fm.D x i) CB Ca (ChoiceOfModulusAndDiscriminant.Adm_of (Fm.D x i) hB hL) (h25 x i)).2.2.2.2.2.1,
    fun x i => (RadialRules.Adm_of (Fm.D x i) CB Ca (ChoiceOfModulusAndDiscriminant.Adm_of (Fm.D x i) hB hL) (h25 x i)).2.2.2.2.2.2.1,
    fun x i => (RadialRules.Adm_of (Fm.D x i) CB Ca (ChoiceOfModulusAndDiscriminant.Adm_of (Fm.D x i) hB hL) (h25 x i)).2.2.2.2.2.2.2.1,
    fun x i => (RadialRules.Adm_of (Fm.D x i) CB Ca (ChoiceOfModulusAndDiscriminant.Adm_of (Fm.D x i) hB hL) (h25 x i)).2.2.2.2.2.2.2.2.1,
    fun x i => (RadialRules.Adm_of (Fm.D x i) CB Ca (ChoiceOfModulusAndDiscriminant.Adm_of (Fm.D x i) hB hL) (h25 x i)).2.2.2.2.2.2.2.2.2⟩

theorem RadialRuleConsequences.AdmF_of (Cv C1 C2 : ℝ) (hC1 : 0 < C1) (hCo : 0 < Co) (h25 : ChoiceOfModulusAndDiscriminant.FamilyTargetsAtConstants Fm CB)
    (h25b : RadialRules.FamilyTargetsAtConstants Fm CB Cv C1 C2) (hX : PX.S1 CB Co Cd Cs Cg₁ Cg₂)
    (hd : ∀ x (i : Fm.Ix x), PX.decay (Fm.D x i) c C₁) (hL : PX.ClassicalAnalysisAndRepresentationTheorems) :
    RadialRuleConsequences.AdmF Fm CB Co Cd Cv C1 C2 Cs c C₁ := by
  have hA : ∀ x (i : Fm.Ix x), RadialRuleConsequences.admitted (Fm.D x i) CB Co Cd Cv C1 C2 Cs c C₁ := fun x i =>
    RadialRuleConsequences.Adm_of _ CB Co Cd Cv C1 C2 Cs c C₁ hC1 (h25 x i) (h25b x i) (RadialRuleConsequences.Rest_of _ hCo hX (hd x i) hL)
  exact ⟨fun x i => (hA x i).1,
    fun x i => (hA x i).2.1,
    fun x i => (hA x i).2.2.1,
    fun x i => (hA x i).2.2.2.1,
    fun x i => (hA x i).2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

theorem RadialChainStatements.AdmF_of (Cv C1 C2 : ℝ) (hC1 : 0 < C1) (hCo : 0 < Co) (h25 : ChoiceOfModulusAndDiscriminant.FamilyTargetsAtConstants Fm CB)
    (h25b : RadialRules.FamilyTargetsAtConstants Fm CB Cv C1 C2) (hX : PX.S1 CB Co Cd Cs Cg₁ Cg₂)
    (hd : ∀ x (i : Fm.Ix x), PX.decay (Fm.D x i) c C₁) (hL : PX.ClassicalAnalysisAndRepresentationTheorems) :
    RadialChainStatements.AdmF Fm CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ := by
  have hA : ∀ x (i : Fm.Ix x), RadialChainStatements.admitted (Fm.D x i) CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ := fun x i =>
    RadialChainStatements.Adm_of _ CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ hC1 (h25 x i) (h25b x i) (RadialChainStatements.Rest_of _ hCo hX (hd x i) hL)
  exact ⟨fun x i => (hA x i).1,
    fun x i => (hA x i).2.1,
    fun x i => (hA x i).2.2.1,
    fun x i => (hA x i).2.2.2.1,
    fun x i => (hA x i).2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

theorem HereditaryPositivity.AdmF_of (Gm : HereditaryPositivity.GM) (Ks : ℕ) (E₀ Eg Cv C1 C2 : ℝ) (hC1 : 0 < C1) (hCo : 0 < Co) (h25 : ChoiceOfModulusAndDiscriminant.FamilyTargetsAtConstants Fm CB)
    (h25b : RadialRules.FamilyTargetsAtConstants Fm CB Cv C1 C2) (hX : PX.S1 CB Co Cd Cs Cg₁ Cg₂)
    (hd : ∀ x (i : Fm.Ix x), PX.decay (Fm.D x i) c C₁) (hp : ∀ x (i : Fm.Ix x), PX.topPos (Fm.D x i) Gm Ks E₀ Eg)
    (hw : ∀ x (i : Fm.Ix x), PX.topWave (Fm.D x i) Gm Ks E₀ Eg)
    (hl : ∀ x (i : Fm.Ix x), PX.lowPos (Fm.D x i) Ks E₀ Eg) (hL : PX.ClassicalAnalysisAndRepresentationTheorems) :
    HereditaryPositivity.AdmF Fm Gm CB Co Cd Cv C1 C2 Cs c C₁ Ks E₀ Eg := by
  have hA : ∀ x (i : Fm.Ix x), HereditaryPositivity.admitted (Fm.D x i) Gm CB Co Cd Cv C1 C2 Cs c C₁ Ks E₀ Eg := fun x i =>
    HereditaryPositivity.Adm_of _ Gm CB Co Cd Cv C1 C2 Cs c C₁ Ks E₀ Eg hC1 (h25 x i) (h25b x i)
      (HereditaryPositivity.Rest_of _ Gm Ks E₀ Eg hCo hX (hd x i) (hp x i) (hw x i) (hl x i) hL)
  exact ⟨fun x i => (hA x i).1,
    fun x i => (hA x i).2.1,
    fun x i => (hA x i).2.2.1,
    fun x i => (hA x i).2.2.2.1,
    fun x i => (hA x i).2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

theorem BlockEstimateTheorem.AdmF_of (Gm : HereditaryPositivity.GM) (Ks : ℕ) (E₀ Eg E₁ E₂ E₃ Cv C1 C2 : ℝ) (hC1 : 0 < C1) (hCo : 0 < Co)
    (h25 : ChoiceOfModulusAndDiscriminant.FamilyTargetsAtConstants Fm CB) (h25b : RadialRules.FamilyTargetsAtConstants Fm CB Cv C1 C2) (h07b : HereditaryPositivity.OrbitValuationBound Fm Gm Ks E₀ Eg E₁ E₂ E₃)
    (hX : PX.S1 CB Co Cd Cs Cg₁ Cg₂) (hd : ∀ x (i : Fm.Ix x), PX.decay (Fm.D x i) c C₁)
    (hp : ∀ x (i : Fm.Ix x), PX.topPos (Fm.D x i) Gm Ks E₀ Eg)
    (hw : ∀ x (i : Fm.Ix x), PX.topWave (Fm.D x i) Gm Ks E₀ Eg)
    (hl : ∀ x (i : Fm.Ix x), PX.lowPos (Fm.D x i) Ks E₀ Eg) (hL : PX.ClassicalAnalysisAndRepresentationTheorems) :
    BlockEstimateTheorem.AdmF Fm Gm Ks CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ E₀ Eg E₁ E₂ E₃ := by
  have hA : ∀ x (i : Fm.Ix x), BlockEstimateTheorem.admitted (Fm.D x i) Gm Ks CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ E₀ Eg E₁ E₂ E₃ :=
    fun x i => BlockEstimateTheorem.Adm_of _ Gm Ks CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ E₀ Eg E₁ E₂ E₃ hC1 (h25 x i) (h25b x i)
      ⟨h07b.1 x i, h07b.2.1 x i, h07b.2.2.1 x i, h07b.2.2.2 x i⟩
      (BlockEstimateTheorem.Rest_of _ Gm Ks E₀ Eg hCo hX (hd x i) (hp x i) (hw x i) (hl x i) hL)
  exact ⟨⟨fun x i => ((hA x i).1).1,
    fun x i => ((hA x i).1).2.1,
    fun x i => ((hA x i).1).2.2.1,
    fun x i => ((hA x i).1).2.2.2.1,
    fun x i => ((hA x i).1).2.2.2.2.1,
    fun x i => ((hA x i).1).2.2.2.2.2.1,
    fun x i => ((hA x i).1).2.2.2.2.2.2.1,
    fun x i => ((hA x i).1).2.2.2.2.2.2.2.1,
    fun x i => ((hA x i).1).2.2.2.2.2.2.2.2.1,
    fun x i => ((hA x i).1).2.2.2.2.2.2.2.2.2.1,
    fun x i => ((hA x i).1).2.2.2.2.2.2.2.2.2.2.1,
    fun x i => ((hA x i).1).2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => ((hA x i).1).2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => ((hA x i).1).2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => ((hA x i).1).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => ((hA x i).1).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => ((hA x i).1).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => ((hA x i).1).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩,
    ⟨fun x i => ((hA x i).2).1,
    fun x i => ((hA x i).2).2.1,
    fun x i => ((hA x i).2).2.2.1,
    fun x i => ((hA x i).2).2.2.2.1,
    fun x i => ((hA x i).2).2.2.2.2.1,
    fun x i => ((hA x i).2).2.2.2.2.2.1,
    fun x i => ((hA x i).2).2.2.2.2.2.2.1,
    fun x i => ((hA x i).2).2.2.2.2.2.2.2⟩⟩

theorem OnePlaceEstimates.AdmF_of (Gm : HereditaryPositivity.GM) (Ks : ℕ) (C0 CA E₀ Eg E₁ E₂ E₃ Ss C₃ Ch Cg Cq : ℝ) (hCo : 0 < Co)
    (h25 : ChoiceOfModulusAndDiscriminant.FamilyTargetsAtConstants Fm CB) (h07c : RadialRuleConsequences.ConclusionF2 Fm C0 CA) (h07b : HereditaryPositivity.OrbitValuationBound Fm Gm Ks E₀ Eg E₁ E₂ E₃)
    (hX : PX.S1 CB Co Cd Cs Cg₁ Cg₂) (hd : ∀ x (i : Fm.Ix x), PX.decay (Fm.D x i) c C₁)
    (h71 : ∀ x (i : Fm.Ix x), PX.LettersOnCells (Fm.D x i) CB)
    (hs : ∀ x (i : Fm.Ix x), PX.shortGrids (Fm.D x i) Gm CB Ss C₃)
    (h3d : ∀ x (i : Fm.Ix x), PX.s3d0 (Fm.D x i) Ch Cg Cq) (hL : PX.ClassicalAnalysisAndRepresentationTheorems) :
    OnePlaceEstimates.AdmF Fm Gm CB Co Cd C0 CA Cg₁ Cg₂ c C₁ Ks E₀ Eg E₁ E₂ E₃ Ss C₃ Ch Cg Cq := by
  have hA : ∀ x (i : Fm.Ix x),
      OnePlaceEstimates.admitted (Fm.D x i) Gm CB Co Cd C0 CA Cg₁ Cg₂ c C₁ Ks E₀ Eg E₁ E₂ E₃ Ss C₃ Ch Cg Cq := fun x i =>
    OnePlaceEstimates.Adm_of _ Gm CB Co Cd C0 CA Cg₁ Cg₂ c C₁ Ks E₀ Eg E₁ E₂ E₃ Ss C₃ Ch Cg Cq (h25 x i) (h07c x i)
      ⟨h07b.1 x i, h07b.2.1 x i, h07b.2.2.1 x i, h07b.2.2.2 x i⟩
      (OnePlaceEstimates.Rest_of _ Gm Ss C₃ hCo hX (hd x i) (h71 x i) (hs x i) hL) (h3d x i)
  exact ⟨fun x i => (hA x i).1,
    fun x i => (hA x i).2.1,
    fun x i => (hA x i).2.2.1,
    fun x i => (hA x i).2.2.2.1,
    fun x i => (hA x i).2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun x i => (hA x i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

end Assembly

theorem S1.family_statements_all {CB Co Cd Cs Cg₁ Cg₂ c C₁ eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Gm : HereditaryPositivity.GM) (Ks : ℕ)
    (CL Ca Cv C1 C2 E₀ Eg E₁ E₂ E₃ Gg GI C0 CA C C' Ch Aw Cu Bg Bq Bg' B1 B2 Bb BB2 Bgf Bf Ss C₃ : ℝ) (hC1 : 0 < C1) (hCo : 0 < Co)
    (s25a : ChoiceOfModulusAndDiscriminant.FamilyStatementAtConstants Fm CL Ca) (s25 : ChoiceOfModulusAndDiscriminant.FamilyStatementAtConstants Fm CL CB) (s25b : RadialRules.FamilyStatementAtConstants Fm CL Ca CB Cv C1 C2)
    (s07c : RadialRuleConsequences.KudlaFamilyStatement Fm CB Co Cd Cv C1 C2 Cs c C₁ Gg GI C0 CA)
    (s07b : HereditaryPositivity.KudlaFamilyStatement Fm Gm CB Co Cd Cv C1 C2 Cs c C₁ Ks E₀ Eg E₁ E₂ E₃)
    (s07a : BlockEstimateTheorem.KudlaFamilyStatement Fm Gm Ks CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ E₀ Eg E₁ E₂ E₃ C C')
    (s47 : OnePlaceEstimates.FamilyStatementAtConstants Fm Gm CB Co Cd C0 CA Cg₁ Cg₂ c C₁ Ks E₀ Eg E₁ E₂ E₃ Ss C₃ Ch Aw Cu Bg Bq Bg' B1 B2 Bb BB2 Bgf Bf)
    (hBL : PX.lemmaB CL) (hX : PX.S1 CB Co Cd Cs Cg₁ Cg₂) (hd : ∀ x (i : Fm.Ix x), PX.decay (Fm.D x i) c C₁)
    (hp : ∀ x (i : Fm.Ix x), PX.topPos (Fm.D x i) Gm Ks E₀ Eg)
    (hw : ∀ x (i : Fm.Ix x), PX.topWave (Fm.D x i) Gm Ks E₀ Eg)
    (hl : ∀ x (i : Fm.Ix x), PX.lowPos (Fm.D x i) Ks E₀ Eg) (h71 : ∀ x (i : Fm.Ix x), PX.LettersOnCells (Fm.D x i) CB)
    (hs : ∀ x (i : Fm.Ix x), PX.shortGrids (Fm.D x i) Gm CB Ss C₃)
    (h3d : ∀ x (i : Fm.Ix x), PX.s3d0 (Fm.D x i) Ch Bg Bq) (hL : PX.ClassicalAnalysisAndRepresentationTheorems) :
    ChoiceOfModulusAndDiscriminant.FamilyTargetsAtConstants Fm CB ∧ RadialRules.FamilyTargetsAtConstants Fm CB Cv C1 C2 ∧ (RadialRuleConsequences.ConclusionF1 Fm Gg GI ∧ RadialRuleConsequences.ConclusionF2 Fm C0 CA) ∧
      HereditaryPositivity.OrbitValuationBound Fm Gm Ks E₀ Eg E₁ E₂ E₃ ∧ BlockEstimateTheorem.OrbitValuationBound Fm Gm C C' Ks ∧
      OnePlaceEstimates.FamilyTargetsAtConstants Fm Ch Aw Cu Bg Bq Bg' B1 B2 Bb BB2 Bgf Bf := by
  have p25a : ChoiceOfModulusAndDiscriminant.FamilyTargetsAtConstants Fm Ca := s25a (ChoiceOfModulusAndDiscriminant.AdmF_of Fm hBL hL)
  have p25 : ChoiceOfModulusAndDiscriminant.FamilyTargetsAtConstants Fm CB := s25 (ChoiceOfModulusAndDiscriminant.AdmF_of Fm hBL hL)
  have p25b : RadialRules.FamilyTargetsAtConstants Fm CB Cv C1 C2 := s25b (RadialRules.AdmF_of Fm Ca p25a hBL hL)
  have p07c := s07c (RadialRuleConsequences.AdmF_of Fm Cv C1 C2 hC1 hCo p25 p25b hX hd hL)
  have p07b := s07b (HereditaryPositivity.AdmF_of Fm Gm Ks E₀ Eg Cv C1 C2 hC1 hCo p25 p25b hX hd hp hw hl hL)
  have p07a := s07a (BlockEstimateTheorem.AdmF_of Fm Gm Ks E₀ Eg E₁ E₂ E₃ Cv C1 C2 hC1 hCo p25 p25b p07b hX hd hp hw hl hL)
  have p47 := s47 (OnePlaceEstimates.AdmF_of Fm Gm Ks C0 CA E₀ Eg E₁ E₂ E₃ Ss C₃ Ch Bg Bq hCo p25 p07c.2 p07b hX hd h71 hs h3d hL)
  exact ⟨p25, p25b, p07c, p07b, p07a, p47⟩

section Family
variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C : ℝ)

variable (Gm : HereditaryPositivity.GM) (Ks : ℕ) (E₀ Eg E₁ E₂ E₃ : ℝ)

end Family

end Formalism.MainNotions
