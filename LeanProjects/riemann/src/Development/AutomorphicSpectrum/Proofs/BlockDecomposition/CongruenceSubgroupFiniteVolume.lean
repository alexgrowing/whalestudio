import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.KmVol

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isCompact_integralGL (N : ℕ) :
    IsCompact {g : GL (Fin N) k | (∀ i j, (g : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k]) ∧
      ∀ i j, ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k]} := by
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  have hO : IsCompact ((𝒪[k] : Subring k) : Set k) := IsNonarchimedeanLocalField.isCompact_closedBall k 1
  have hM : IsCompact {A : Matrix (Fin N) (Fin N) k | ∀ i j, A i j ∈ 𝒪[k]} := by
    have h := isCompact_univ_pi fun _ : Fin N => isCompact_univ_pi fun _ : Fin N => hO
    have e : {A : Matrix (Fin N) (Fin N) k | ∀ i j, A i j ∈ 𝒪[k]} =
        Set.univ.pi fun _ : Fin N => Set.univ.pi fun _ : Fin N => ((𝒪[k] : Subring k) : Set k) :=
      Set.ext fun A => ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    exact e ▸ h
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin N) (Fin N) k)).isCompact_preimage
    (hM.prod (hM.image MulOpposite.continuous_op))
  convert h using 1
  ext g
  exact ⟨fun h => ⟨h.1, _, h.2, rfl⟩, fun ⟨h1, A, hA, e⟩ => ⟨h1, fun i j => by
    have : A = ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) := MulOpposite.op_injective e
    exact this ▸ hA i j⟩⟩

theorem Km_subset_integralGL (N m : ℕ) :
    (Zls.Km k N m : Set (GL (Fin N) k)) ⊆
      {g : GL (Fin N) k | (∀ i j, (g : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k]) ∧
        ∀ i j, ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k]} := by
  have key : ∀ (h : GL (Fin N) 𝒪[k]) (i j : Fin N),
      ((Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k) h : GL (Fin N) k) :
        Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k] := fun h i j =>
    ((h : Matrix (Fin N) (Fin N) 𝒪[k]) i j).2
  rintro g ⟨h, -, rfl⟩
  refine ⟨key h, fun i j => ?_⟩
  rw [← map_inv]
  exact key h⁻¹ i j

theorem measure_image_Km_lt_top : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)] (μ : MeasureTheory.Measure (AdGL k N)), μ.IsHaarMeasure → ∀ m : ℕ, μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' (Zls.Km k N m : Set (GL (Fin N) k))) < ⊤ := by
  intro k _ _ _ _ N _ _ μ hμ m
  refine lt_of_le_of_lt (measure_mono (Set.image_mono (Km_subset_integralGL N m))) ?_
  exact ((isCompact_integralGL N).image QuotientGroup.continuous_mk).measure_lt_top

end GlobalTheory.CompanionTheory.KmVol
