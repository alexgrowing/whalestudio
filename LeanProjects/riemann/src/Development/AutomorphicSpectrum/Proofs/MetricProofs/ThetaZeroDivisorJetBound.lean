import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.KernelsMatrix
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.AssemblyAnalytic
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Assembly
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFundamentalDomainMeanNormSqThetaChar
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.CoordSiegel
import ReciprocityTheory.AnalyticForms.AnalyticCharts.NullZero
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.TorsOff

def proj {n : ℕ} (p : Fin n → ℝ) : Fin n → AddCircle (1 : ℝ) :=
  fun j => ((p j : ℝ) : AddCircle (1 : ℝ))

theorem proj_surjective {n : ℕ} : Function.Surjective (proj (n := n)) := by
  intro x
  choose p hp using fun j => QuotientAddGroup.mk_surjective (x j)
  exact ⟨p, funext hp⟩

theorem continuous_proj {n : ℕ} : Continuous (proj (n := n)) :=
  continuous_pi fun j => (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply j)

theorem proj_eq_iff {n : ℕ} {p q : Fin n → ℝ} :
    proj p = proj q ↔ ∃ k : Fin n → ℤ, p - q = fun α => (k α : ℝ) := by
  constructor
  · intro h
    have key : ∀ j, ∃ k : ℤ, p j - q j = k := by
      intro j
      have h1 := congrFun h j
      have h2 : ((p j - q j : ℝ) : AddCircle (1 : ℝ)) = 0 := by
        rw [AddCircle.coe_sub]
        exact sub_eq_zero.2 h1
      obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff 1).1 h2
      exact ⟨k, by simpa using hk.symm⟩
    choose k hk using key
    exact ⟨k, funext hk⟩
  · rintro ⟨k, hk⟩
    funext j
    have h1 := congrFun hk j
    simp only [Pi.sub_apply] at h1
    have h3 : p j = q j + k j := by linarith
    simp only [proj]
    rw [h3, AddCircle.coe_add, TorsionEquidistribution.coe_intCast_eq_zero, add_zero]

theorem proj_zero {n : ℕ} : proj (0 : Fin n → ℝ) = 0 := by
  funext j
  simp [proj]

theorem proj_eq_zero_iff {n : ℕ} {p : Fin n → ℝ} :
    proj p = 0 ↔ ∃ k : Fin n → ℤ, p = fun α => (k α : ℝ) := by
  rw [← proj_zero, proj_eq_iff, sub_zero]

theorem nsmul_proj {n : ℕ} (m : ℕ) (p : Fin n → ℝ) : m • proj p = proj ((m : ℝ) • p) := by
  funext j
  simp only [proj, Pi.smul_apply, smul_eq_mul]
  rw [← nsmul_eq_mul, AddCircle.coe_nsmul]

theorem norm_coe_eq_infDist (t : ℝ) :
    ‖((t : ℝ) : AddCircle (1 : ℝ))‖ = Metric.infDist t (Set.range ((↑) : ℤ → ℝ)) := by
  have h1 : ‖((t : ℝ) : AddCircle (1 : ℝ))‖ = |t - round t| := UnitAddCircle.norm_eq
  rw [h1]
  apply le_antisymm
  · rw [Metric.le_infDist (Set.range_nonempty _)]
    rintro _ ⟨k, rfl⟩
    rw [Real.dist_eq]
    exact round_le t k
  · have h2 := Metric.infDist_le_dist_of_mem (x := t) (s := Set.range ((↑) : ℤ → ℝ))
      (y := (round t : ℝ)) (Set.mem_range_self (round t))
    rwa [Real.dist_eq] at h2

theorem volume_eq_zero_of_proj {n : ℕ} {Z : Set (Fin n → AddCircle (1 : ℝ))}
    (hZ : MeasurableSet Z) (h : volume (proj ⁻¹' Z) = 0) : volume Z = 0 := by
  have hmp : ∀ _ : Fin n, MeasurePreserving ((↑) : ℝ → AddCircle (1 : ℝ))
      (volume.restrict (Set.Ioc (0 : ℝ) (0 + 1))) volume :=
    fun _ => AddCircle.measurePreserving_mk 1 0
  have hpi := measurePreserving_pi _ _ hmp
  rw [volume_pi, ← hpi.measure_preimage hZ.nullMeasurableSet, ← Measure.restrict_pi_pi]
  refine le_antisymm ?_ zero_le
  refine (Measure.restrict_apply_le _ _).trans ?_
  rw [← volume_pi]
  exact h.le

theorem volume_zero_set {n g : ℕ} {θ : (Fin g → ℂ) → ℂ} (L : (Fin n → ℝ) ≃ₗ[ℝ] (Fin g → ℂ))
    (hθ : Differentiable ℂ θ) {w : Fin g → ℂ} (hw : θ w ≠ 0) :
    volume {p : Fin n → ℝ | θ (L p) = 0} = 0 := by
  have han := ReciprocityTheory.AnForm.Osgood.osgood g Set.univ θ isOpen_univ hθ.differentiableOn
  have h0 := ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd isOpen_univ isPreconnected_univ han
    ⟨w, Set.mem_univ _, hw⟩
  have h0' : volume {z : Fin g → ℂ | θ z = 0} = 0 := by simpa using h0
  let Lc : (Fin n → ℝ) ≃L[ℝ] (Fin g → ℂ) := L.toContinuousLinearEquiv
  let e : (Fin n → ℝ) ≃ᵐ (Fin g → ℂ) := Lc.toHomeomorph.toMeasurableEquiv
  have he : (e : (Fin n → ℝ) → Fin g → ℂ) = Lc := rfl
  have hμ := Measure.isAddLeftInvariant_eq_smul (Measure.map Lc volume) (volume : Measure (Fin g → ℂ))
  have h1 : (Measure.map Lc volume) {z : Fin g → ℂ | θ z = 0} = 0 := by
    rw [hμ, Measure.smul_apply, h0', smul_zero]
  rw [← he, e.map_apply] at h1
  exact h1

section Lattice

variable {n g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)} {θ : (Fin g → ℂ) → ℂ}
  {L : (Fin n → ℝ) ≃ₗ[ℝ] (Fin g → ℂ)}

def zeroSet (θ : (Fin g → ℂ) → ℂ) (L : (Fin n → ℝ) ≃ₗ[ℝ] (Fin g → ℂ)) :
    Set (Fin n → AddCircle (1 : ℝ)) :=
  proj '' {p | θ (L p) = 0}

theorem zero_iff_of_proj_eq (hL : ∀ p, L p ∈ Λ ↔ ∃ k : Fin n → ℤ, p = fun α => (k α : ℝ))
    (hΛ : ∀ l ∈ Λ, ∀ w, θ (w + l) = 0 ↔ θ w = 0) {p q : Fin n → ℝ} (h : proj p = proj q) :
    θ (L p) = 0 ↔ θ (L q) = 0 := by
  obtain ⟨k, hk⟩ := proj_eq_iff.1 h
  have hmem : L (p - q) ∈ Λ := (hL _).2 ⟨k, hk⟩
  have h1 := hΛ _ hmem (L q)
  rwa [← map_add, add_comm, sub_add_cancel] at h1

theorem proj_mem_zeroSet (hL : ∀ p, L p ∈ Λ ↔ ∃ k : Fin n → ℤ, p = fun α => (k α : ℝ))
    (hΛ : ∀ l ∈ Λ, ∀ w, θ (w + l) = 0 ↔ θ w = 0) (p : Fin n → ℝ) :
    proj p ∈ zeroSet θ L ↔ θ (L p) = 0 := by
  constructor
  · rintro ⟨q, hq, hqp⟩
    exact (zero_iff_of_proj_eq hL hΛ hqp).1 hq
  · exact fun h => ⟨p, h, rfl⟩

theorem isClosed_zeroSet (hθ : Continuous θ)
    (hL : ∀ p, L p ∈ Λ ↔ ∃ k : Fin n → ℤ, p = fun α => (k α : ℝ))
    (hΛ : ∀ l ∈ Λ, ∀ w, θ (w + l) = 0 ↔ θ w = 0) : IsClosed (zeroSet θ L) := by
  have hLc : Continuous L := L.toLinearMap.continuous_of_finiteDimensional
  have hcl : IsClosed {p : Fin n → ℝ | θ (L p) = 0} :=
    isClosed_eq (hθ.comp hLc) continuous_const
  have hbox : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hcomp := (hbox.inter_left hcl).image (continuous_proj (n := n))
  have hEq : zeroSet θ L =
      proj '' ({p | θ (L p) = 0} ∩ Set.pi Set.univ fun _ : Fin n => Set.Icc (0 : ℝ) 1) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨p, hp, rfl⟩
      have hq : proj (fun j => Int.fract (p j)) = proj p :=
        proj_eq_iff.2 ⟨fun j => -⌊p j⌋, by
          funext j
          simp only [Pi.sub_apply, Int.cast_neg, Int.fract]
          ring⟩
      refine ⟨fun j => Int.fract (p j), ⟨?_, ?_⟩, hq⟩
      · exact (zero_iff_of_proj_eq hL hΛ hq).2 hp
      · intro j _
        exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
    · exact Set.image_mono Set.inter_subset_left
  rw [hEq]
  exact hcomp.isClosed

theorem volume_zeroSet (hθ : Differentiable ℂ θ) {w : Fin g → ℂ} (hw : θ w ≠ 0)
    (hL : ∀ p, L p ∈ Λ ↔ ∃ k : Fin n → ℤ, p = fun α => (k α : ℝ))
    (hΛ : ∀ l ∈ Λ, ∀ w, θ (w + l) = 0 ↔ θ w = 0) : volume (zeroSet θ L) = 0 := by
  refine volume_eq_zero_of_proj (isClosed_zeroSet hθ.continuous hL hΛ).measurableSet ?_
  have hpre : proj ⁻¹' zeroSet θ L = {p | θ (L p) = 0} := by
    ext p
    exact proj_mem_zeroSet hL hΛ p
  rw [hpre]
  exact volume_zero_set L hθ hw

theorem natCast_smul_map (m : ℕ) (p : Fin n → ℝ) : (m : ℂ) • L p = L ((m : ℝ) • p) := by
  rw [map_smul]
  funext j
  simp

theorem proj_mem_torsion_iff (hL : ∀ p, L p ∈ Λ ↔ ∃ k : Fin n → ℤ, p = fun α => (k α : ℝ))
    (m : ℕ) (p : Fin n → ℝ) : proj p ∈ torusTorsion n m ↔ (m : ℂ) • L p ∈ Λ := by
  change m • proj p = 0 ↔ _
  rw [nsmul_proj, natCast_smul_map, hL, proj_eq_zero_iff]

theorem eventually_exists_off (hθ : Continuous θ) {w : Fin g → ℂ} (hw : θ w ≠ 0) :
    ∀ᶠ m : ℕ in Filter.atTop, ∃ p : Fin n → ℝ,
      (∃ k : Fin n → ℤ, (m : ℝ) • p = fun α => (k α : ℝ)) ∧ θ (L p) ≠ 0 := by
  have hLc : Continuous L := L.toLinearMap.continuous_of_finiteDimensional
  have hopen : IsOpen {p : Fin n → ℝ | θ (L p) ≠ 0} :=
    isOpen_ne_fun (hθ.comp hLc) continuous_const
  have hmem : L.symm w ∈ {p : Fin n → ℝ | θ (L p) ≠ 0} := by simpa using hw
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen _ hmem
  have hev : ∀ᶠ m : ℕ in Filter.atTop, 1 / (m : ℝ) < ε :=
    tendsto_one_div_atTop_nhds_zero_nat.eventually (gt_mem_nhds hε)
  filter_upwards [hev, Filter.eventually_gt_atTop 0] with m hm hm0
  have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm0
  refine ⟨fun j => (⌊(m : ℝ) * L.symm w j⌋ : ℝ) / m, ⟨fun j => ⌊(m : ℝ) * L.symm w j⌋, ?_⟩, ?_⟩
  · funext j
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  · apply hball
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro j
    rw [Real.dist_eq]
    set x := L.symm w j
    have h1 := Int.floor_le ((m : ℝ) * x)
    have h2 := Int.lt_floor_add_one ((m : ℝ) * x)
    have h3 : (⌊(m : ℝ) * x⌋ : ℝ) / m - x = ((⌊(m : ℝ) * x⌋ : ℝ) - m * x) / m := by
      field_simp
    rw [h3, abs_div, abs_of_pos hmR]
    refine lt_of_le_of_lt ?_ hm
    apply div_le_div_of_nonneg_right _ hmR.le
    rw [abs_le]
    constructor <;> linarith

theorem core (hn : 0 < n) (c₀ : ℝ) (hθ : Differentiable ℂ θ) (hw : ∃ w, θ w ≠ 0)
    (hL : ∀ p, L p ∈ Λ ↔ ∃ k : Fin n → ℤ, p = fun α => (k α : ℝ))
    (hΛ : ∀ l ∈ Λ, ∀ w, θ (w + l) = 0 ↔ θ w = 0) (hc : ∃ k : ℤ, c₀ = k / 2) :
    ∀ᶠ m : ℕ in Filter.atTop, ∀ (Ix : Type) [Fintype Ix] (r : Ix → Fin g → ℂ),
      (∀ i, (m : ℂ) • r i ∈ Λ ∧ θ (r i) ≠ 0) →
      (∀ w : Fin g → ℂ, (m : ℂ) • w ∈ Λ → θ w ≠ 0 → ∃! i, w - r i ∈ Λ) →
      Nonempty Ix ∧ Fintype.card Ix ≤
        3 * {i | (1 / 4 : ℝ) ≤
          Metric.infDist (L.symm (r i) ⟨0, hn⟩ + c₀) (Set.range ((↑) : ℤ → ℝ))}.ncard := by
  obtain ⟨w, hw⟩ := hw
  have hfull := TorsionEquidistribution.full n hn (zeroSet θ L) c₀
    (isClosed_zeroSet hθ.continuous hL hΛ) (volume_zeroSet hθ hw hL hΛ) hc
  filter_upwards [hfull, eventually_exists_off (L := L) hθ.continuous hw]
  rintro m h1 ⟨p, hp1, hp2⟩ Ix _ r hr hu
  have hmp : (m : ℂ) • L p ∈ Λ := by
    rw [natCast_smul_map]
    exact (hL _).2 hp1
  refine ⟨?_, ?_⟩
  · obtain ⟨i, -, -⟩ := hu (L p) hmp hp2
    exact ⟨i⟩
  let f : Ix → Fin n → AddCircle (1 : ℝ) := fun i => proj (L.symm (r i))
  have hinj : Function.Injective f := by
    intro i j hij
    obtain ⟨k, hk⟩ := proj_eq_iff.1 hij
    have hmem : r i - r j ∈ Λ := by
      have h2 := (hL _).2 ⟨k, hk⟩
      simpa using h2
    obtain ⟨i', -, huniq⟩ := hu (r i) (hr i).1 (hr i).2
    rw [huniq i (by simp), huniq j hmem]
  have hrange : Set.range f = torusTorsion n m \ zeroSet θ L := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [proj_mem_torsion_iff hL]
        simpa using (hr i).1
      · rw [proj_mem_zeroSet hL hΛ]
        simpa using (hr i).2
    · rintro ⟨hx1, hx2⟩
      obtain ⟨q, rfl⟩ := proj_surjective x
      rw [proj_mem_torsion_iff hL] at hx1
      rw [proj_mem_zeroSet hL hΛ] at hx2
      obtain ⟨i, hi, -⟩ := hu (L q) hx1 hx2
      refine ⟨i, (proj_eq_iff (p := q) (q := L.symm (r i))).2 ((hL _).1 ?_) |>.symm⟩
      simpa using hi
  have hcard : Fintype.card Ix = (torusTorsion n m \ zeroSet θ L).ncard := by
    rw [← hrange, ← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ,
      Nat.card_eq_fintype_card]
  have hnorm : ∀ i, ‖f i ⟨0, hn⟩ + (c₀ : AddCircle (1 : ℝ))‖ =
      Metric.infDist (L.symm (r i) ⟨0, hn⟩ + c₀) (Set.range ((↑) : ℤ → ℝ)) := by
    intro i
    rw [← norm_coe_eq_infDist, AddCircle.coe_add]
    rfl
  have hgood : {x ∈ torusTorsion n m \ zeroSet θ L |
        (1 / 4 : ℝ) ≤ ‖x ⟨0, hn⟩ + (c₀ : AddCircle (1 : ℝ))‖} =
      f '' {i | (1 / 4 : ℝ) ≤
        Metric.infDist (L.symm (r i) ⟨0, hn⟩ + c₀) (Set.range ((↑) : ℤ → ℝ))} := by
    ext x
    constructor
    · rintro ⟨hx, hx2⟩
      rw [← hrange] at hx
      obtain ⟨i, rfl⟩ := hx
      exact ⟨i, by simpa only [Set.mem_setOf_eq, ← hnorm] using hx2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      refine ⟨hrange ▸ Set.mem_range_self i, ?_⟩
      rw [hnorm]
      exact hi
  rw [hgood, Set.ncard_image_of_injective _ hinj] at h1
  rw [hcard]
  exact h1

end Lattice

theorem torsion_off_zeros : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (θ : (Fin g → ℂ) → ℂ)
    (L : (Fin g ⊕ Fin g → ℝ) ≃ₗ[ℝ] (Fin g → ℂ)) (i₀ : Fin g ⊕ Fin g) (c₀ : ℝ),
    Differentiable ℂ θ → (∃ w, θ w ≠ 0) →
    (∀ p, L p ∈ Λ ↔ ∃ k : Fin g ⊕ Fin g → ℤ, p = fun α => (k α : ℝ)) →
    (∀ l ∈ Λ, ∀ w, θ (w + l) = 0 ↔ θ w = 0) →
    (∃ k : ℤ, c₀ = k / 2) →
    ∀ᶠ m : ℕ in Filter.atTop, ∀ (Ix : Type) [Fintype Ix] (r : Ix → Fin g → ℂ),
      (∀ i, (m : ℂ) • r i ∈ Λ ∧ θ (r i) ≠ 0) →
      (∀ w : Fin g → ℂ, (m : ℂ) • w ∈ Λ → θ w ≠ 0 → ∃! i, w - r i ∈ Λ) →
      Nonempty Ix ∧ Fintype.card Ix ≤
        3 * {i | (1 / 4 : ℝ) ≤ Metric.infDist (L.symm (r i) i₀ + c₀) (Set.range ((↑) : ℤ → ℝ))}.ncard := by
  intro g Λ θ L i₀ c₀ hθ hw hL hΛ hc
  have hn : 0 < Fintype.card (Fin g ⊕ Fin g) := Fintype.card_pos_iff.2 ⟨i₀⟩
  let e0 := Fintype.equivFin (Fin g ⊕ Fin g)
  let e : (Fin g ⊕ Fin g) ≃ Fin (Fintype.card (Fin g ⊕ Fin g)) :=
    e0.trans (Equiv.swap (e0 i₀) ⟨0, hn⟩)
  have hi0 : e i₀ = ⟨0, hn⟩ := by simp [e]
  let L' : (Fin (Fintype.card (Fin g ⊕ Fin g)) → ℝ) ≃ₗ[ℝ] (Fin g → ℂ) :=
    (LinearEquiv.funCongrLeft ℝ ℝ e).trans L
  have hL'a : ∀ q, L' q = L (q ∘ e) := fun _ => rfl
  have hsymm : ∀ w, L'.symm w ⟨0, hn⟩ = L.symm w i₀ := by
    intro w
    have h1 : (L'.symm w) ∘ e = L.symm w := by
      rw [LinearEquiv.eq_symm_apply, ← hL'a]
      exact L'.apply_symm_apply w
    rw [← h1, Function.comp_apply, hi0]
  have hL' : ∀ q, L' q ∈ Λ ↔ ∃ k : Fin (Fintype.card (Fin g ⊕ Fin g)) → ℤ,
      q = fun α => (k α : ℝ) := by
    intro q
    rw [hL'a, hL]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k ∘ e.symm, ?_⟩
      funext j
      simpa using congrFun hk (e.symm j)
    · rintro ⟨k, rfl⟩
      exact ⟨k ∘ e, rfl⟩
  filter_upwards [core (L := L') hn c₀ hθ hw hL' hΛ hc] with m hm Ix _ r h1 h2
  simpa only [hsymm] using hm Ix r h1 h2

end GlobalTheory.CompanionTheory.TorsOff
