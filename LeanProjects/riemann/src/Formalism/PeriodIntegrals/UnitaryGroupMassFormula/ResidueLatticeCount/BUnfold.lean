import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.UnitPreserving

open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace NumberField.Units MeasureTheory
open scoped nonZeroDivisors ENNReal Classical Pointwise

noncomputable section

namespace PI.Residue

variable {K : Type} [Field K] [NumberField K]

theorem mem_lat {J : (Ideal (𝓞 K))⁰} {x : mixedSpace K} :
    x ∈ lat K J ↔ ∃ a : 𝓞 K, a ∈ (J : Ideal (𝓞 K)) ∧ mixedEmbedding K (a : K) = x := by
  rw [lat, mem_idealLattice]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, FractionalIdeal.coe_mk0, FractionalIdeal.mem_coeIdeal] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a, ?_, rfl⟩
    rw [SetLike.mem_coe, FractionalIdeal.coe_mk0, FractionalIdeal.mem_coeIdeal]
    exact ⟨a, ha, rfl⟩

theorem smul_mem_lat {J : (Ideal (𝓞 K))⁰} {x : mixedSpace K} (u : (𝓞 K)ˣ) (hx : x ∈ lat K J) :
    u • x ∈ lat K J := by
  obtain ⟨a, ha, rfl⟩ := mem_lat.1 hx
  refine mem_lat.2 ⟨u * a, Ideal.mul_mem_left _ _ ha, ?_⟩
  rw [unitSMul_smul]
  simp [map_mul]

theorem measurableSet_shell' : MeasurableSet (shell K) := by
  have h1 : MeasurableSet {y : mixedSpace K | 1 / 2 < mixedEmbedding.norm y} :=
    (isOpen_lt continuous_const (mixedEmbedding.continuous_norm K)).measurableSet
  have h2 : MeasurableSet {y : mixedSpace K | mixedEmbedding.norm y ≤ 1} :=
    (isClosed_le (mixedEmbedding.continuous_norm K) continuous_const).measurableSet
  exact (measurableSet_fundamentalCone K).inter (h1.inter h2)

theorem measurableSet_hit' (ρ : ℝ) (x : mixedSpace K) : MeasurableSet (hit K ρ x) := by
  have : hit K ρ x = ⋂ w, {y | normAtPlace w y * normAtPlace w x < ρ} := by
    ext y; simp [hit]
  rw [this]
  exact MeasurableSet.iInter fun w =>
    (isOpen_lt ((continuous_normAtPlace w).mul continuous_const) continuous_const).measurableSet

theorem mem_hit_smul (ρ : ℝ) (u : (𝓞 K)ˣ) (x y : mixedSpace K) :
    y ∈ hit K ρ (u • x) ↔ u • y ∈ hit K ρ x := by
  simp only [hit, Set.mem_ofPred_eq, unitSMul_smul, map_mul]
  refine forall_congr' fun w => ?_
  rw [mul_left_comm, mul_assoc]

def urep (g : (𝓞 K)ˣ ⧸ torsion K) : (𝓞 K)ˣ := Quotient.out g

def Fv (ρ : ℝ) (x : mixedSpace K) : ℝ≥0∞ := volume (shell K ∩ hit K ρ x)

theorem exists_rep {J : (Ideal (𝓞 K))⁰} {x : mixedSpace K} (hx : x ∈ lat K J) (hx0 : x ≠ 0) :
    ∃ x1 ∈ idealSet K J, ∃ g : (𝓞 K)ˣ ⧸ torsion K, urep g • x1 = x := by
  have hnx : mixedEmbedding.norm x ≠ 0 := by
    obtain ⟨a, _, rfl⟩ := mem_lat.1 hx
    exact fun h => hx0 ((norm_eq_zero_iff' ⟨_, rfl⟩).1 h)
  obtain ⟨u, hu⟩ := exists_unit_smul_mem hnx
  obtain ⟨ζ, hζ⟩ := QuotientGroup.mk_out_eq_mul (torsion K) u⁻¹
  have hζ' : (ζ : (𝓞 K)ˣ)⁻¹ ∈ torsion K := inv_mem ζ.2
  refine ⟨(ζ : (𝓞 K)ˣ)⁻¹ • (u • x), ⟨torsion_smul_mem_of_mem hu hζ',
    smul_mem_lat _ (smul_mem_lat _ hx)⟩, QuotientGroup.mk u⁻¹, ?_⟩
  rw [urep, hζ, ← mul_smul, ← mul_smul]
  simp

theorem fib_le (hUP : UnitPreserving) (ρ : ℝ) (x1 : mixedSpace K) :
    ∑' g : (𝓞 K)ˣ ⧸ torsion K, Fv ρ (urep g • x1) ≤
      volume ({y | 1 / 2 < mixedEmbedding.norm y} ∩ hit K ρ x1) := by
  let A : (𝓞 K)ˣ ⧸ torsion K → Set (mixedSpace K) := fun g =>
    (fun z : mixedSpace K => (urep g)⁻¹ • z) ⁻¹' shell K ∩ hit K ρ x1
  have hAm : ∀ g, MeasurableSet (A g) := fun g =>
    ((hUP K (urep g)⁻¹).measurable measurableSet_shell').inter (measurableSet_hit' _ _)
  have hFA : ∀ g, Fv ρ (urep g • x1) = volume (A g) := by
    intro g
    have e : shell K ∩ hit K ρ (urep g • x1) = (fun y : mixedSpace K => urep g • y) ⁻¹' A g := by
      ext y
      simp only [A, Set.mem_inter_iff, Set.mem_preimage, mem_hit_smul, inv_smul_smul]
    rw [Fv, e, (hUP K (urep g)).measure_preimage (hAm g).nullMeasurableSet]
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro g g' hgg
    rw [Function.onFun, Set.disjoint_left]
    rintro z ⟨hz, _⟩ ⟨hz', _⟩
    apply hgg
    have h1 : (urep g)⁻¹ • z ∈ fundamentalCone K := hz.1
    have h2 : (urep g')⁻¹ • z ∈ fundamentalCone K := hz'.1
    have h3 : ((urep g')⁻¹ * urep g) • ((urep g)⁻¹ • z) ∈ fundamentalCone K := by
      rw [← mul_smul]; simpa using h2
    have h4 := (unit_smul_mem_iff_mem_torsion h1 _).1 h3
    have h5 : (QuotientGroup.mk (urep g') : (𝓞 K)ˣ ⧸ torsion K) = QuotientGroup.mk (urep g) :=
      QuotientGroup.eq.2 h4
    rw [urep, urep, QuotientGroup.out_eq', QuotientGroup.out_eq'] at h5
    exact h5.symm
  calc ∑' g, Fv ρ (urep g • x1) = ∑' g, volume (A g) := tsum_congr hFA
    _ ≤ volume (⋃ g, A g) := tsum_meas_le_meas_iUnion_of_disjoint volume hAm hdisj
    _ ≤ _ := by
        refine measure_mono (Set.iUnion_subset fun g => ?_)
        rintro z ⟨hz, hz'⟩
        refine ⟨?_, hz'⟩
        have : 1 / 2 < mixedEmbedding.norm ((urep g)⁻¹ • z) := hz.2.1
        rwa [norm_unit_smul] at this

theorem sum_ne_zero_le (J : (Ideal (𝓞 K))⁰) (F : mixedSpace K → ℝ≥0∞) :
    ∑' x : {x : lat K J // x ≠ 0}, F ((x : lat K J) : mixedSpace K) ≤
      ∑' p : idealSet K J × ((𝓞 K)ˣ ⧸ torsion K), F (urep p.2 • (p.1 : mixedSpace K)) := by
  have hex : ∀ x : {x : lat K J // x ≠ 0}, ∃ p : idealSet K J × ((𝓞 K)ˣ ⧸ torsion K),
      urep p.2 • (p.1 : mixedSpace K) = ((x : lat K J) : mixedSpace K) := by
    rintro ⟨⟨x, hx⟩, hx0⟩
    obtain ⟨x1, h1, g, hg⟩ := exists_rep hx (fun h => hx0 (Subtype.ext h))
    exact ⟨(⟨x1, h1⟩, g), hg⟩
  choose p hp using hex
  have hinj : Function.Injective p := by
    intro x y hxy
    apply Subtype.ext; apply Subtype.ext
    rw [← hp x, ← hp y, hxy]
  calc _ = ∑' x : {x : lat K J // x ≠ 0}, F (urep (p x).2 • ((p x).1 : mixedSpace K)) :=
        tsum_congr fun x => by rw [hp x]
    _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective hinj
        (fun p : idealSet K J × ((𝓞 K)ˣ ⧸ torsion K) => F (urep p.2 • (p.1 : mixedSpace K)))

theorem tsum_eq_zero_add_ne {α : Type*} [Zero α] (f : α → ℝ≥0∞) :
    ∑' x, f x = f 0 + ∑' x : {x : α // x ≠ 0}, f x := by
  rw [ENNReal.tsum_eq_add_tsum_ite 0]
  change _ = f 0 + ∑' x : ↑{x : α | x ≠ 0}, f x
  rw [tsum_subtype {x : α | x ≠ 0} f]
  congr 1
  refine tsum_congr fun x => ?_
  by_cases h : x = 0 <;> simp [h]

theorem Fv_le (ρ : ℝ) (x : mixedSpace K) : Fv ρ x ≤ volume (shell K) := by
  rw [Fv]; exact measure_mono Set.inter_subset_left

theorem lattice_sum_le_shell_volume (hUP : UnitPreserving) (J : (Ideal (𝓞 K))⁰) (ρ : ℝ) :
    ∑' x : lat K J, Fv ρ (x : mixedSpace K) ≤
      volume (shell K) +
        ∑' x : idealSet K J,
          volume ({y | 1 / 2 < mixedEmbedding.norm y} ∩ hit K ρ (x : mixedSpace K)) := by
  rw [tsum_eq_zero_add_ne (fun x : lat K J => Fv ρ (x : mixedSpace K))]
  refine add_le_add (Fv_le ρ _) ?_
  refine (sum_ne_zero_le J (Fv ρ)).trans ?_
  rw [ENNReal.tsum_prod']
  refine ENNReal.tsum_le_tsum fun x1 => ?_
  dsimp only
  exact fib_le hUP ρ (x1 : mixedSpace K)

theorem unfold_of (hUP : UnitPreserving) : Unfold :=
  fun _ _ _ J ρ _ => lattice_sum_le_shell_volume hUP J ρ

end PI.Residue
