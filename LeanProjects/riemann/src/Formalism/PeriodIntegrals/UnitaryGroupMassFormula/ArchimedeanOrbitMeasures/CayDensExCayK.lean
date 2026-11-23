import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensExCayS

noncomputable section

namespace HcInf

open HcS.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal

section Chart

variable (P Q : ℕ)

local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ

def cayCand (g : UpqT P Q) : Mat := (1 + 1) * (UpqT.mat g + 1)⁻¹ * (UpqT.mat g - 1)

open Classical in

def cayInv (g : UpqT P Q) : lieU P Q :=
  if h : cayCand P Q g ∈ lieU P Q then ⟨cayCand P Q g, h⟩ else 0

def CayInvMeas : Prop := ∀ P Q : ℕ, Measurable (cayInv P Q)

def CayInvIff : Prop := ∀ (P Q : ℕ) (g : UpqT P Q) (X : lieU P Q),
  UpqT.mat g * ((1 + 1) - ((X : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)) =
    (1 + 1) + ((X : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) → cayInv P Q g = X

def CaySUnivMeas : Prop := ∀ P Q : ℕ, MeasurableSet (cayS (Set.univ : Set (lieU P Q)))

end Chart

def CayleyDens : Prop :=
  ∀ (P Q : ℕ) (m : Measure (UpqT P Q)), m.IsHaarMeasure → ∀ c : ℝ≥0∞, c ≠ 0 → c ≠ ⊤ →
  ∀ lam : Measure (lieU P Q), IsOmegaLeb lam →
    Tendsto (fun r : ℝ => m {g | ∃ X ∈ ballU P Q r, UpqT.mat g =
      NormedSpace.exp (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)} /
      lam (ballU P Q r)) (𝓝[>] 0) (𝓝 c) →
  ∃ D ∈ 𝓝 (0 : lieU P Q), MeasurableSet D ∧ ∃ f : lieU P Q → ℝ≥0∞, Measurable f ∧
    Tendsto f (𝓝 0) (𝓝 c) ∧ (m.restrict (cayS D)).map (cayInv P Q) = (lam.restrict D).withDensity f

theorem cayS_eq (hI : CayInvIff) (P Q : ℕ) (V : Set (lieU P Q)) :
    cayS V = cayS Set.univ ∩ cayInv P Q ⁻¹' V := by
  ext g
  simp only [cayS, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_univ, true_and]
  constructor
  · rintro ⟨X, hX, hg⟩
    exact ⟨⟨X, hg⟩, by rw [hI P Q g X hg]; exact hX⟩
  · rintro ⟨⟨X, hg⟩, hV⟩
    exact ⟨X, by rw [← hI P Q g X hg]; exact hV, hg⟩

theorem cayleyLoc_of (hM : CayInvMeas) (hI : CayInvIff) (hU : CaySUnivMeas) (hD : CayleyDens) :
    CayleyLoc := by
  intro P Q m hm c hc0 hcT lam hlam hlim ε hε
  obtain ⟨D, hD0, hDm, f, hf, hft, hmap⟩ := hD P Q m hm c hc0 hcT lam hlam hlim
  have hε0 : ((ε : ℝ≥0∞)) ≠ 0 := by exact_mod_cast hε.ne'
  have h1ε : (1 + (ε : ℝ≥0∞)) ≠ ⊤ := by simp
  set N : Set ℝ≥0∞ := {y | y < (1 + (ε : ℝ≥0∞)) * c} ∩ {y | c < (1 + (ε : ℝ≥0∞)) * y} with hN
  have hNo : IsOpen N := by
    refine isOpen_lt continuous_id continuous_const |>.inter ?_
    exact isOpen_lt continuous_const (ENNReal.continuous_const_mul h1ε)
  have hlt : c < (1 + (ε : ℝ≥0∞)) * c := by
    rw [add_mul, one_mul]
    exact ENNReal.lt_add_right hcT (mul_ne_zero hε0 hc0)
  have hcN : c ∈ N := ⟨hlt, hlt⟩
  set V : Set (lieU P Q) := D ∩ f ⁻¹' N with hV
  have hVm : MeasurableSet V := hDm.inter (hf hNo.measurableSet)
  have hV0 : V ∈ 𝓝 (0 : lieU P Q) := Filter.inter_mem hD0 (hft (hNo.mem_nhds hcN))
  have hVD : V ⊆ D := Set.inter_subset_left
  refine ⟨V, hV0, hVm, ?_, cayInv P Q, hM P Q, ?_, f, hf, ?_, ?_⟩
  · rw [cayS_eq hI]
    exact (hU P Q).inter (hM P Q hVm)
  · intro g X hX
    constructor
    · intro h
      exact ⟨⟨X, hX, h⟩, hI P Q g X h⟩
    · rintro ⟨⟨X', hX', h'⟩, hg⟩
      rw [hI P Q g X' h'] at hg
      rw [← hg]
      exact h'
  · intro X hX
    exact ⟨hX.2.1.le, hX.2.2.le⟩
  · have e1 : cayS V = cayInv P Q ⁻¹' V ∩ cayS D := by
      rw [cayS_eq hI, cayS_eq hI P Q D, Set.inter_comm]
      ext g
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, h2, hVD h1⟩
      · rintro ⟨h1, h2, -⟩
        exact ⟨h1, h2⟩
    rw [e1, ← Measure.restrict_restrict (hM P Q hVm), ← Measure.restrict_map (hM P Q) hVm, hmap,
      restrict_withDensity hVm, Measure.restrict_restrict hVm, Set.inter_eq_left.2 hVD]

end HcInf
