import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckePrimeDetection
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KurValue

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie Polynomial

theorem exists_norm_eq_of_mem_closure {K : Type*} [NormedField K] [IsUltrametricDist K] {S : Set K} {x : K}
    (hx : x ∈ closure S) (h0 : x ≠ 0) : ∃ y ∈ S, ‖x‖ = ‖y‖ := by
  obtain ⟨y, hy, hd⟩ := Metric.mem_closure_iff.1 hx ‖x‖ (norm_pos_iff.2 h0)
  refine ⟨y, hy, ?_⟩
  rw [dist_comm, dist_eq_norm] at hd
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := y - x) (y := x) hd.ne
  rw [sub_add_cancel, max_eq_right hd.le] at this
  exact this.symm

variable {p : ℕ} [Fact p.Prime]

theorem mem_range_of_isIntegral {x : ℂ_[p]} (hx : IsIntegral (PadicAlgCl p) x) :
    x ∈ (algebraMap (PadicAlgCl p) ℂ_[p]).range :=
  minpoly.mem_range_of_degree_eq_one _ x (IsAlgClosed.degree_eq_one_of_irreducible _ (minpoly.irreducible hx))

theorem exists_lift {F : Type} [Field F] [NumberField F] (φ : F →+* ℂ_[p]) :
    ∃ ψ : F →+* PadicAlgCl p, ∀ a, algebraMap (PadicAlgCl p) ℂ_[p] (ψ a) = φ a := by
  have h : ∀ a : F, φ a ∈ (algebraMap (PadicAlgCl p) ℂ_[p]).range := fun a => by
    have h1 : IsIntegral ℚ (φ a) := (Algebra.IsIntegral.isIntegral (R := ℚ) a).map φ.toRatAlgHom
    exact mem_range_of_isIntegral h1.tower_top
  choose f hf using h
  have hi := (algebraMap (PadicAlgCl p) ℂ_[p]).injective
  refine ⟨⟨⟨⟨f, hi ?_⟩, fun a b => hi ?_⟩, hi ?_, fun a b => hi ?_⟩, hf⟩
  · rw [hf, map_one, map_one]
  · simp only [map_mul, hf]
  · simp only [map_zero, hf]
  · simp only [map_add, hf]

theorem exists_finite {F : Type} [Field F] [NumberField F] (ψ : F →+* PadicAlgCl p) :
    ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧ (∀ a, ψ a ∈ K) ∧
      ∀ x ∈ K, ∃ a, ‖x‖ = ‖ψ a‖ := by
  let b := Module.finBasis ℚ F
  refine ⟨IntermediateField.adjoin ℚ_[p] (Set.range fun i => ψ (b i)), ?_, fun a => ?_, fun x hx => ?_⟩
  · exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  · rw [← b.sum_repr a, map_sum]
    refine sum_mem fun i _ => ?_
    rw [Rat.smul_def, map_mul, map_ratCast]
    exact mul_mem (SubfieldClass.ratCast_mem _ _) (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  · let M : IntermediateField ℚ_[p] (PadicAlgCl p) :=
      ψ.fieldRange.topologicalClosure.toIntermediateField fun r => by
        have hc : IsClosed {r : ℚ_[p] | algebraMap ℚ_[p] (PadicAlgCl p) r ∈ ψ.fieldRange.topologicalClosure} :=
          (Subfield.isClosed_topologicalClosure _).preimage (continuous_algebraMap _ _)
        refine (Padic.denseRange_ratCast p).induction_on r hc fun q => ?_
        rw [map_ratCast]
        exact SubfieldClass.ratCast_mem _ _
    have hM : IntermediateField.adjoin ℚ_[p] (Set.range fun i => ψ (b i)) ≤ M := by
      refine IntermediateField.adjoin_le_iff.2 ?_
      rintro _ ⟨i, rfl⟩
      exact Subfield.le_topologicalClosure ψ.fieldRange ⟨b i, rfl⟩
    by_cases h0 : x = 0
    · exact ⟨0, by simp [h0]⟩
    obtain ⟨_, ⟨a, rfl⟩, h⟩ := exists_norm_eq_of_mem_closure (S := (ψ.fieldRange : Set (PadicAlgCl p))) (hM hx) h0
    exact ⟨a, h⟩

theorem exists_norm_eq {F : Type} [Field F] [NumberField F] (φ : F →+* ℂ_[p]) {x : ℂ_[p]} (hx : x ∈ kurC φ) :
    ∃ a : F, ‖x‖ = ‖φ a‖ := by
  obtain ⟨ψ, hψ⟩ := exists_lift φ
  obtain ⟨K, hK, hmem, hnorm⟩ := exists_finite ψ
  let M : Subfield ℂ_[p] := (ReciprocityTheory.DiscreteGroups.LocalClassField.MaximalUnramifiedExtension p K).toSubfield.map (algebraMap (PadicAlgCl p) ℂ_[p])
  have hle : kurC φ ≤ M.topologicalClosure := by
    refine Subfield.topologicalClosure_minimal _ (sup_le ?_ ?_) (Subfield.isClosed_topologicalClosure _)
    · rintro _ ⟨a, rfl⟩
      exact M.le_topologicalClosure ⟨ψ a, ReciprocityTheory.DiscreteGroups.LocalClassField.le_Kur (hmem a), hψ a⟩
    · refine Subfield.topologicalClosure_minimal _ (Subfield.closure_le.2 ?_) (Subfield.isClosed_topologicalClosure _)
      rintro ζ ⟨n, hn, hpn, hζ⟩
      obtain ⟨ξ, rfl⟩ := mem_range_of_isIntegral (IsIntegral.of_pow hn (by rw [hζ]; exact isIntegral_one))
      refine M.le_topologicalClosure ⟨ξ, ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Kur_of_pow hK hpn ?_, rfl⟩
      apply (algebraMap (PadicAlgCl p) ℂ_[p]).injective
      rw [map_pow, hζ, map_one]
  by_cases h0 : x = 0
  · exact ⟨0, by simp [h0]⟩
  obtain ⟨_, ⟨y, hy, rfl⟩, h⟩ := exists_norm_eq_of_mem_closure (S := (M : Set ℂ_[p])) (hle hx) h0
  obtain ⟨n, hn, hyn⟩ := (ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Kur_iff hK y).1 hy
  obtain ⟨z, hz, hyz⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.norm_Kn p K hK hn hyn
  obtain ⟨a, ha⟩ := hnorm z hz
  refine ⟨a, ?_⟩
  rw [h, ← hψ, norm_algebraMap', norm_algebraMap', ← ha, hyz]

theorem exists_near {F : Type} [Field F] (φ : F →+* ℂ_[p]) {x : ℂ_[p]} (hx : ‖x‖ ≤ 1) :
    ∃ y ∈ kurC φ, ‖x - y‖ < 1 := by
  rcases hx.lt_or_eq with hlt | heq
  · exact ⟨0, zero_mem _, by rwa [sub_zero]⟩
  obtain ⟨z, hz⟩ := (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl p)).exists_dist_lt x one_pos
  rw [dist_eq_norm, PadicComplex.coe_eq] at hz
  have hz1 : ‖z‖ = 1 := by
    have h1 : ‖algebraMap (PadicAlgCl p) ℂ_[p] z - x‖ < ‖x‖ := by rwa [norm_sub_rev, heq]
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1.ne
    rwa [sub_add_cancel, max_eq_right h1.le, heq, norm_algebraMap'] at this
  obtain ⟨ζ, m, hm, hζ, h⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_teichmuller_bar z hz1
  refine ⟨algebraMap (PadicAlgCl p) ℂ_[p] ζ, root_mem_kurC φ hm (by rw [← map_pow, hζ, map_one]), ?_⟩
  have e : x - algebraMap (PadicAlgCl p) ℂ_[p] ζ =
      (x - algebraMap (PadicAlgCl p) ℂ_[p] z) + algebraMap (PadicAlgCl p) ℂ_[p] (z - ζ) := by
    rw [map_sub]; ring
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hz (by rwa [norm_algebraMap']))

theorem kurC_value_residue : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]),
    (∀ x ∈ kurC φ, ∃ a : F, ‖x‖ = ‖φ a‖) ∧ ∀ x : ℂ_[p], ‖x‖ ≤ 1 → ∃ y ∈ kurC φ, ‖x - y‖ < 1 :=
  fun _ _ _ _ _ φ => ⟨fun _ hx => exists_norm_eq φ hx, fun _ hx => exists_near φ hx⟩

end GlobalTheory.KurValue

end
