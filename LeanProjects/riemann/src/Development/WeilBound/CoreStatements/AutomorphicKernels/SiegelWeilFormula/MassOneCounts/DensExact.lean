import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalQuadraticDensityNearOne
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalQuadraticDensityBoundNonzero
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneLocalDensityAlmostAll
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.PrimitiveVectorQuadraticLevelMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardLocalHaarPropertiesStatement

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.MOne

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology GlobalTheory.CompanionTheory.SW.LGPrim
open scoped TensorProduct ENNReal NNReal Matrix

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

local notation "𝒪" => HeightOneSpectrum.adicCompletionIntegers F v
local notation "𝓴" => IsLocalRing.ResidueField (HeightOneSpectrum.adicCompletionIntegers F v)
local notation "res" => IsLocalRing.residue (HeightOneSpectrum.adicCompletionIntegers F v)

theorem dens_exact (lam : Measure (Fv F v)) (hlam : IsStdV v lam) (h2 : Valued.v (2 : Fv F v) = 1)
    (ι : Type) [Fintype ι] [DecidableEq ι] (BO : Matrix ι ι 𝒪) (hBs : (BO.map phi).IsSymm)
    (hBdet : Valued.v (BO.map phi).det = 1) (s : 𝒪) (hsu : Valued.v (s : Fv F v) = 1)
    (A : Set (Fv F v)) (hA : MeasurableSet A) (hAs : A ⊆ {z | Valued.v (z - s) < Valued.v (s : Fv F v)}) :
    (Measure.pi fun _ : ι => lam) {x | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧
        (2 : Fv F v)⁻¹ * (x ⬝ᵥ ((BO.map phi) *ᵥ x)) ∈ A} =
      ((Nat.card {y : ι → 𝓴 // (2 : 𝓴)⁻¹ * (y ⬝ᵥ ((BO.map res) *ᵥ y)) = res s} : ℝ≥0∞) *
        (Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹ ^ (Fintype.card ι - 1)) * lam A := by
  classical
  have hLoc := GlobalTheory.T.completion_is_local_ring F v
  haveI : SecondCountableTopology (Fv F v) := hLoc.2.2.1
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨-, -, -, hcard⟩ := GlobalTheory.T.standard_local_haar_properties F v lam hlam
  have hq0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  haveI : Finite 𝓴 := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hq0)
  letI : Fintype 𝓴 := Fintype.ofFinite _
  have hBint : ∀ i j, (BO.map phi) i j ∈ v.adicCompletionIntegers F := fun i j => (BO i j).2
  have h20 : (2 : Fv F v) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h2
    exact zero_ne_one h2
  let c : 𝒪 := ⟨2⁻¹, by show Valued.v ((2 : Fv F v)⁻¹) ≤ 1; rw [map_inv₀, h2, inv_one]⟩
  have hc : (c : Fv F v) = 2⁻¹ := rfl
  have hc2 : c * 2 = 1 := by
    apply Subtype.ext
    have e : (phi : 𝒪 →+* Fv F v) (c * 2) = phi c * phi 2 := map_mul _ _ _
    have e2 : (phi : 𝒪 →+* Fv F v) 2 = 2 := map_ofNat _ 2
    have e3 : phi c = (2 : Fv F v)⁻¹ := hc
    rw [e2, e3, inv_mul_cancel₀ h20] at e
    exact e
  have hr1 : res c * 2 = 1 := by
    have := congrArg res hc2
    rwa [map_mul, map_one, map_ofNat] at this
  have hr : res c = 2⁻¹ := eq_inv_of_mul_eq_one_left hr1
  set sb : 𝓴 := res s with hsb
  have hsb0 : sb ≠ 0 := by
    intro h0
    have h' := (res_eq_zero_iff _).1 h0
    rw [hsu] at h'
    exact lt_irrefl _ h'
  let qk : (ι → 𝓴) → 𝓴 := fun y => (2 : 𝓴)⁻¹ * (y ⬝ᵥ ((BO.map res) *ᵥ y))
  let Fl : Finset (ι → 𝓴) := Finset.univ.filter fun y => qk y = sb
  have hN : Nat.card {y : ι → 𝓴 // (2 : 𝓴)⁻¹ * (y ⬝ᵥ ((BO.map res) *ᵥ y)) = sb} = Fl.card :=
    Nat.subtype_card Fl (fun x => by simp [Fl, qk])

  obtain ⟨π, hπ⟩ := GlobalTheory.CompanionTheory.SW.GBall.exists_unif v
  have hprimeq : {x : ι → Fv F v | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧
      (2 : Fv F v)⁻¹ * (x ⬝ᵥ ((BO.map phi) *ᵥ x)) ∈ A} =
      {x : ι → Fv F v | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧ (∃ i, Valued.v (x i) = 1) ∧
        (2 : Fv F v)⁻¹ * (x ⬝ᵥ ((BO.map phi) *ᵥ x)) ∈ A} := by
    ext x
    constructor
    · rintro ⟨hx, hQ⟩
      refine ⟨hx, ?_, hQ⟩
      by_contra hnp
      have h5 := GlobalTheory.CompanionTheory.SW.GBall.q_nonprim h2 hBint hπ hx hnp
      have hlt : Valued.v ((2 : Fv F v)⁻¹ * (x ⬝ᵥ ((BO.map phi) *ᵥ x)) - s) < Valued.v (s : Fv F v) := hAs hQ
      have hv := Valuation.map_eq_of_sub_lt Valued.v hlt
      rw [hv, hsu] at h5
      have hlt1 : WithZero.exp (-2 : ℤ) < 1 := by
        rw [← WithZero.exp_zero]
        exact WithZero.exp_lt_exp.2 (by norm_num)
      exact absurd h5 (not_le.2 hlt1)
    · rintro ⟨hx, -, hQ⟩
      exact ⟨hx, hQ⟩
  have hAs1 : A ⊆ {z | Valued.v (z - s) < 1} := fun z hz => by
    have := hAs hz
    rw [hsu] at this
    exact this
  rw [hprimeq, hN]
  set Qf : (ι → Fv F v) → Fv F v := fun x => (2 : Fv F v)⁻¹ * (x ⬝ᵥ ((BO.map phi) *ᵥ x)) with hQf
  have hQc : Continuous Qf := by
    refine continuous_const.mul ?_
    exact continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
  let P : (ι → 𝓴) → Set (ι → Fv F v) := fun y =>
    {x | (∀ i, Valued.v (x i - lf y i) < 1) ∧ Qf x ∈ A}
  let T0 : Finset (ι → 𝓴) := Finset.univ.filter fun y => y ≠ 0
  have hS : {x : ι → Fv F v | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧
      (∃ i, Valued.v (x i) = 1) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ ((BO.map phi) *ᵥ x)) ∈ A} =
      ⋃ y ∈ T0, P y := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨h1, h3, h4⟩
      obtain ⟨y, hy, h⟩ := (cover x).1 ⟨h1, h3⟩
      exact ⟨y, Finset.mem_filter.2 ⟨Finset.mem_univ _, hy⟩, h, h4⟩
    · rintro ⟨y, hy, h, h4⟩
      obtain ⟨h1, h3⟩ := (cover x).2 ⟨y, (Finset.mem_filter.1 hy).2, h⟩
      exact ⟨h1, h3, h4⟩
  have hball : MeasurableSet {a : Fv F v | Valued.v a < 1} := by
    have h := (Valued.isOpen_ball (Fv F v) 1).measurableSet
    simpa [Valuation.restrict_lt_iff_lt_embedding] using h
  have hmeas : ∀ y ∈ T0, MeasurableSet (P y) := by
    intro y _
    have e : P y = (⋂ i, (fun x : ι → Fv F v => x i - lf y i) ⁻¹' {a | Valued.v a < 1}) ∩ Qf ⁻¹' A := by
      ext x
      simp [P]
    rw [e]
    refine (MeasurableSet.iInter fun i => ?_).inter (hQc.measurable hA)
    exact ((continuous_apply i).sub continuous_const).measurable hball
  have hdisj : Set.PairwiseDisjoint (↑T0) P := by
    intro y _ y' _ hne
    exact Set.disjoint_left.2 fun x hx hx' => hne (eq_of_close x y y' hx.1 hx'.1)
  have hclass : ∀ y ∈ T0, (Measure.pi fun _ : ι => lam) (P y) =
      if qk y = sb then ((Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹ ^ (Fintype.card ι - 1)) * lam A else 0 := by
    intro y hy
    have hy0 : y ≠ 0 := (Finset.mem_filter.1 hy).2
    obtain ⟨hint, hprim⟩ := (cover (lf y)).2 ⟨y, hy0, fun i => by simp⟩
    obtain ⟨a, haQ, har⟩ := res_Q c hc hr BO y
    have key := GlobalTheory.T.primitive_vector_quadratic_level_measure F v lam hlam h2 ι (BO.map phi) hBs hBint hBdet (lf y) hint hprim A hA
    have hkey : (Measure.pi fun _ : ι => lam) (P y) = _ := key
    rw [hkey]
    have hcl : Valued.v ((s : Fv F v) - Qf (lf y)) < 1 ↔ qk y = sb := by
      have := res_eq_iff s a
      rw [har] at this
      rw [show Qf (lf y) = (a : Fv F v) from haQ.symm]
      exact ⟨fun h => (this.2 h).symm, fun h => this.1 h.symm⟩
    split_ifs with he
    · have hlt := hcl.2 he
      have : A ∩ {s' | Valued.v (s' - (2 : Fv F v)⁻¹ * (lf y ⬝ᵥ ((BO.map phi) *ᵥ lf y))) < 1} = A := by
        refine Set.inter_eq_left.2 fun z hz => ?_
        have h5 : Valued.v (z - s) < 1 := hAs1 hz
        have h6 := Valuation.map_add_lt _ h5 hlt
        have e : z - s + (s - Qf (lf y)) = z - Qf (lf y) := by ring
        rw [e] at h6
        exact h6
      rw [this]
    · have : A ∩ {s' | Valued.v (s' - (2 : Fv F v)⁻¹ * (lf y ⬝ᵥ ((BO.map phi) *ᵥ lf y))) < 1} = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.2 fun z hz => he (hcl.1 ?_)
        have h5 : Valued.v (z - s) < 1 := hAs1 hz.1
        have h6 : Valued.v (z - Qf (lf y)) < 1 := hz.2
        have h7 := Valuation.map_sub_lt _ h6 h5
        have e : z - Qf (lf y) - (z - s) = s - Qf (lf y) := by ring
        rw [e] at h7
        exact h7
      rw [this, measure_empty, mul_zero]
  rw [hS, measure_biUnion_finset hdisj hmeas, Finset.sum_congr rfl hclass, ← Finset.sum_filter,
    Finset.sum_const, nsmul_eq_mul]
  have hT : T0.filter (fun y => qk y = sb) = Fl := by
    ext y
    simp only [T0, Fl, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rintro rfl
      apply hsb0
      rw [← h]
      simp [qk]
  rw [hT, mul_assoc]

end PositivityTheory.SiegelWeilFormula.MOne

end
