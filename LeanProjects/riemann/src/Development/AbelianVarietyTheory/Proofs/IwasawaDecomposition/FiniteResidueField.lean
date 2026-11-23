import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodChi
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.CoefInt

open IsLocalRing Topology

variable {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
  [FiniteDimensional ℚ_[l] K]

omit [FiniteDimensional ℚ_[l] K] in

theorem dvd_iff_norm_le {a : integralClosure ℤ_[l] K} (ha : a ≠ 0) (x : integralClosure ℤ_[l] K) :
    a ∣ x ↔ ‖((x : K) : PadicAlgCl l)‖ ≤ ‖((a : K) : PadicAlgCl l)‖ := by
  constructor
  · rintro ⟨y, rfl⟩
    have hy := (GlobalTheory.mem_integralClosure_padicInt_iff K y).mp y.2
    push_cast
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hy
  · intro h
    have h0 : (a : K) ≠ 0 := fun h0 => ha (Subtype.ext h0)
    have h1 : ((a : K) : PadicAlgCl l) ≠ 0 := fun h1 => h0 (Subtype.ext h1)
    have hm : (x : K) / (a : K) ∈ integralClosure ℤ_[l] K := by
      rw [GlobalTheory.mem_integralClosure_padicInt_iff, IntermediateField.coe_div, norm_div]
      exact div_le_one_of_le₀ h (norm_nonneg _)
    exact ⟨⟨_, hm⟩, Subtype.ext (mul_div_cancel₀ _ h0).symm⟩

theorem isAdic_maximalIdeal : IsAdic (maximalIdeal (integralClosure ℤ_[l] K)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (integralClosure ℤ_[l] K)
  have hind : IsInducing (fun x : integralClosure ℤ_[l] K => ((x : K) : PadicAlgCl l)) :=
    IsInducing.subtypeVal.comp IsInducing.subtypeVal
  have hlt : ‖((π : K) : PadicAlgCl l)‖ < 1 :=
    (GlobalTheory.mem_maximalIdeal_integralClosure_iff K π).1 hπ.not_isUnit
  have hpos : 0 < ‖((π : K) : PadicAlgCl l)‖ :=
    norm_pos_iff.2 fun h => hπ.ne_zero (Subtype.ext (Subtype.ext h))
  have hmem : ∀ (n : ℕ) (x : integralClosure ℤ_[l] K),
      x ∈ maximalIdeal (integralClosure ℤ_[l] K) ^ n ↔
        ‖((x : K) : PadicAlgCl l)‖ ≤ ‖((π : K) : PadicAlgCl l)‖ ^ n := fun n x => by
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
      dvd_iff_norm_le K (pow_ne_zero n hπ.ne_zero)]
    push_cast
    rw [norm_pow]
  have hn : ∀ s : Set (integralClosure ℤ_[l] K), s ∈ 𝓝 (0 : integralClosure ℤ_[l] K) ↔
      ∃ ε > 0, ∀ x : integralClosure ℤ_[l] K, ‖((x : K) : PadicAlgCl l)‖ < ε → x ∈ s := fun s => by
    rw [hind.nhds_eq_comap, ((Metric.nhds_basis_ball).comap _).mem_iff]
    refine exists_congr fun ε => and_congr_right fun _ => ?_
    simp [Set.subset_def]
  rw [isAdic_iff]
  refine ⟨fun n => ?_, fun s hs => ?_⟩
  · refine AddSubgroup.isOpen_of_mem_nhds
      (maximalIdeal (integralClosure ℤ_[l] K) ^ n).toAddSubgroup (g := 0) ?_
    exact (hn _).2 ⟨_, pow_pos hpos n, fun x hx => (hmem n x).2 hx.le⟩
  · obtain ⟨ε, hε, h⟩ := (hn s).1 hs
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hlt
    exact ⟨n, fun x hx => h x (((hmem n x).1 hx).trans_lt hn)⟩

theorem finite_residueField : Finite (ResidueField (integralClosure ℤ_[l] K)) := by
  have := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful ℤ_[l] ℚ_[l] K
  have := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalHom ℤ_[l] K
  have : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField).symm.toEquiv
  exact Module.finite_of_finite (ResidueField ℤ_[l])

theorem integers_laws : ∀ (l : ℕ) [Fact l.Prime] (LL : Loc.FinExt l), ∃ (_ : IsDiscreteValuationRing ↥(Loc.OL LL)), Module.Finite ℤ_[l] ↥(Loc.OL LL) ∧ IsAdic (IsLocalRing.maximalIdeal ↥(Loc.OL LL)) ∧ IsAdicComplete (IsLocalRing.maximalIdeal ↥(Loc.OL LL)) ↥(Loc.OL LL) ∧ Finite (IsLocalRing.ResidueField ↥(Loc.OL LL)) ∧ IsFractionRing ↥(Loc.OL LL) ↥LL.1 := by
  intro l _ LL
  have := LL.2
  exact ⟨GlobalTheory.isDiscreteValuationRing_integralClosure_padicInt l LL.1,
    GlobalTheory.finite_integralClosure_padicInt l LL.1, isAdic_maximalIdeal LL.1,
    GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[l] (integralClosure ℤ_[l] LL.1),
    finite_residueField LL.1, GlobalTheory.isFractionRing_integralClosure_padicInt l LL.1⟩

end GlobalTheory.CoefInt
