import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteFieldQuadraticFormPointCountStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.PrimitiveVectorQuadraticLevelMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardLocalHaarPropertiesStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.SW.LGPrim

theorem real_bound (q N Nf : ℝ) (hq : 0 < q) (M : ℕ) (hM : 1 ≤ M)
    (h : |Nf - q ^ (2 * M - 1)| ≤ q ^ M) (h1 : N ≤ Nf) (h2 : Nf ≤ N + 1) :
    |N * (q⁻¹) ^ (2 * M - 1) - 1| ≤ 1 / q ^ (M - 1) + 1 / q ^ (2 * M - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  have e1 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  have e2 : m + 1 - 1 = m := by omega
  rw [e1] at h ⊢
  rw [e2]
  have hQ : q ^ (2 * m + 1) = q ^ (m + 1) * q ^ m := by rw [← pow_add]; congr 1; omega
  have hQpos : 0 < q ^ (2 * m + 1) := by positivity
  have habs : |N - q ^ (2 * m + 1)| ≤ q ^ (m + 1) + 1 := by
    obtain ⟨h3, h4⟩ := abs_le.1 h
    have hp : 0 ≤ q ^ (m + 1) := by positivity
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have e3 : N * (q⁻¹) ^ (2 * m + 1) - 1 = (N - q ^ (2 * m + 1)) / q ^ (2 * m + 1) := by
    rw [inv_pow]; field_simp
  rw [e3, abs_div, abs_of_pos hQpos, div_le_iff₀ hQpos]
  have e4 : (1 / q ^ m + 1 / q ^ (2 * m + 1)) * q ^ (2 * m + 1) = q ^ (m + 1) + 1 := by
    rw [add_mul, one_div, one_div, inv_mul_cancel₀ hQpos.ne', hQ]
    have : q ^ m ≠ 0 := by positivity
    field_simp
  rw [e4]
  exact habs

theorem map_quad {R S ι : Type} [CommRing R] [CommRing S] [Fintype ι] (f : R →+* S)
    (B : Matrix ι ι R) (x : ι → R) :
    f (x ⬝ᵥ (B *ᵥ x)) = (f ∘ x) ⬝ᵥ ((B.map f) *ᵥ (f ∘ x)) := by
  rw [RingHom.map_dotProduct]
  congr 1
  funext i
  exact RingHom.map_mulVec f B x i

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

local notation "𝒪" => HeightOneSpectrum.adicCompletionIntegers F v
local notation "𝓴" => IsLocalRing.ResidueField (HeightOneSpectrum.adicCompletionIntegers F v)
local notation "res" => IsLocalRing.residue (HeightOneSpectrum.adicCompletionIntegers F v)

theorem res_eq_zero_iff (a : 𝒪) : res a = 0 ↔ Valued.v (a : Fv F v) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro h
    have h1 : Valued.v (a : Fv F v) ≤ 1 := a.2
    refine lt_of_le_of_ne h1 fun h2 => h ?_
    have ha0 : (a : Fv F v) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at h2
      exact zero_ne_one h2
    have hinv : (a : Fv F v)⁻¹ ∈ v.adicCompletionIntegers F := by
      show Valued.v ((a : Fv F v)⁻¹) ≤ 1
      rw [map_inv₀, h2, inv_one]
    refine IsUnit.of_mul_eq_one (⟨(a : Fv F v)⁻¹, hinv⟩ : v.adicCompletionIntegers F) ?_
    apply Subtype.ext
    show (a : Fv F v) * (a : Fv F v)⁻¹ = 1
    exact mul_inv_cancel₀ ha0
  · intro h hu
    obtain ⟨b, hb⟩ := hu.exists_right_inv
    have h3 : Valued.v ((a : Fv F v) * (b : Fv F v)) = 1 := by
      have : (a : Fv F v) * (b : Fv F v) = 1 := congrArg Subtype.val hb
      rw [this, map_one]
    rw [map_mul] at h3
    have hb1 : Valued.v (b : Fv F v) ≤ 1 := b.2
    have h4 : Valued.v (a : Fv F v) * Valued.v (b : Fv F v) < 1 := by
      calc _ ≤ Valued.v (a : Fv F v) * 1 := by gcongr
        _ < 1 := by simpa using h
    exact absurd h3 (ne_of_lt h4)

theorem res_eq_iff (a b : 𝒪) : res a = res b ↔ Valued.v ((a : Fv F v) - b) < 1 := by
  rw [← sub_eq_zero, ← map_sub, res_eq_zero_iff]
  rfl

def lift (y : 𝓴) : 𝒪 := Function.surjInv IsLocalRing.residue_surjective y

theorem res_lift (y : 𝓴) : res (lift y) = y := Function.surjInv_eq _ y

def lf {ι : Type} (y : ι → 𝓴) : ι → Fv F v := fun i => (lift (y i) : 𝒪)

theorem cover {ι : Type} (x : ι → Fv F v) :
    ((∀ i, x i ∈ 𝒪) ∧ ∃ i, Valued.v (x i) = 1) ↔
      ∃ y : ι → 𝓴, y ≠ 0 ∧ ∀ i, Valued.v (x i - lf y i) < 1 := by
  constructor
  · rintro ⟨hx, i₀, hi₀⟩
    refine ⟨fun i => res ⟨x i, hx i⟩, ?_, fun i => ?_⟩
    · intro h0
      have h1 := (res_eq_zero_iff (⟨x i₀, hx i₀⟩ : 𝒪)).1 (congrFun h0 i₀)
      exact absurd hi₀ (ne_of_lt h1)
    · exact (res_eq_iff (⟨x i, hx i⟩ : 𝒪) (lift _)).1 (res_lift _).symm
  · rintro ⟨y, hy, h⟩
    have hx : ∀ i, x i ∈ 𝒪 := by
      intro i
      have e : x i = (x i - lf y i) + lf y i := by ring
      show Valued.v (x i) ≤ 1
      rw [e]
      exact Valuation.map_add_le _ (h i).le (lift (y i)).2
    refine ⟨hx, ?_⟩
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hy
    refine ⟨i, le_antisymm (hx i) (not_lt.1 fun hlt => hi ?_)⟩
    have e : res (⟨x i, hx i⟩ : 𝒪) = y i := by
      rw [(res_eq_iff (⟨x i, hx i⟩ : 𝒪) (lift (y i))).2 (h i), res_lift]
    rw [← e]
    exact (res_eq_zero_iff _).2 hlt

theorem eq_of_close {ι : Type} (x : ι → Fv F v) (y y' : ι → 𝓴)
    (h : ∀ i, Valued.v (x i - lf y i) < 1) (h' : ∀ i, Valued.v (x i - lf y' i) < 1) : y = y' := by
  funext i
  have h1 := Valuation.map_sub_lt _ (h' i) (h i)
  have e : (x i - lf y' i) - (x i - lf y i) = lf y i - lf y' i := by ring
  rw [e] at h1
  have h2 := (res_eq_iff (lift (y i)) (lift (y' i))).2 h1
  rwa [res_lift, res_lift] at h2

abbrev phi : 𝒪 →+* Fv F v := ValuationSubring.subtype _

theorem res_Q {ι : Type} [Fintype ι] (c : 𝒪) (hc : (c : Fv F v) = 2⁻¹) (hr : res c = 2⁻¹)
    (BO : Matrix ι ι 𝒪) (y : ι → 𝓴) :
    ∃ a : 𝒪, (a : Fv F v) = (2 : Fv F v)⁻¹ * (lf y ⬝ᵥ ((BO.map phi) *ᵥ lf y)) ∧
      res a = (2 : 𝓴)⁻¹ * (y ⬝ᵥ ((BO.map res) *ᵥ y)) := by
  refine ⟨c * ((lift ∘ y) ⬝ᵥ (BO *ᵥ (lift ∘ y))), ?_, ?_⟩
  · have h1 := map_quad phi BO (lift ∘ y)
    have h2 : (phi : 𝒪 →+* Fv F v) (c * ((lift ∘ y) ⬝ᵥ (BO *ᵥ (lift ∘ y)))) = phi c * phi ((lift ∘ y) ⬝ᵥ (BO *ᵥ (lift ∘ y))) := map_mul _ _ _
    rw [h1] at h2
    have h3 : phi c = (2 : Fv F v)⁻¹ := hc
    rw [h3] at h2
    exact h2
  · rw [map_mul, hr, map_quad]
    have : (⇑res ∘ lift ∘ y) = y := by
      funext i
      exact res_lift _
    rw [this]

theorem core (lam : Measure (Fv F v)) (hlam : IsStdV v lam) (h2 : Valued.v (2 : Fv F v) = 1)
    (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι (Fv F v)) (hBs : B.IsSymm)
    (hBint : ∀ i j, B i j ∈ v.adicCompletionIntegers F) (hBdet : Valued.v B.det = 1)
    (M : ℕ) (hM : Fintype.card ι = 2 * M) (hM1 : 1 ≤ M) (s : Fv F v)
    (hs : s ∈ v.adicCompletionIntegers F) :
    ∃ D : ℝ≥0, |(D : ℝ) - 1| ≤ 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ (M - 1) +
        1 / (Ideal.absNorm v.asIdeal : ℝ) ^ (2 * M - 1) ∧
      ∀ A : Set (Fv F v), MeasurableSet A → A ⊆ {z | Valued.v (z - s) < 1} →
        (Measure.pi fun _ : ι => lam) {x | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧
          (∃ i, Valued.v (x i) = 1) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} = (D : ℝ≥0∞) * lam A := by
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
  have hcardk : Fintype.card 𝓴 = Ideal.absNorm v.asIdeal := by
    rw [← Nat.card_eq_fintype_card]; exact hcard
  obtain ⟨BO, rfl⟩ : ∃ BO : Matrix ι ι 𝒪, BO.map phi = B :=
    ⟨Matrix.of fun i j => ⟨B i j, hBint i j⟩, by ext i j; rfl⟩
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
  have hchar : ringChar 𝓴 ≠ 2 := by
    intro h
    have h0 : (2 : 𝓴) = 0 := by
      have := ringChar.Nat.cast_ringChar (R := 𝓴)
      rw [h] at this
      exact_mod_cast this
    rw [h0, mul_zero] at hr1
    exact zero_ne_one hr1
  have hBO : BO.IsSymm := by
    exact Matrix.IsSymm.ext fun i j => Subtype.ext (congrFun (congrFun hBs i) j)
  have hBks : (BO.map res).IsSymm := hBO.map _
  have hBkdet : (BO.map res).det ≠ 0 := by
    intro h0
    have e : res BO.det = (BO.map res).det := RingHom.map_det res BO
    rw [← e] at h0
    have h3 := (res_eq_zero_iff _).1 h0
    have e2 : ((BO.det : 𝒪) : Fv F v) = (BO.map phi).det := RingHom.map_det phi BO
    rw [e2, hBdet] at h3
    exact lt_irrefl _ h3
  set sb : 𝓴 := res (⟨s, hs⟩ : 𝒪) with hsb
  have hcount := GlobalTheory.T.finite_field_quadratic_form_point_count 𝓴 hchar ι M hM hM1 (BO.map res) hBks hBkdet sb
  let qk : (ι → 𝓴) → 𝓴 := fun y => (2 : 𝓴)⁻¹ * (y ⬝ᵥ ((BO.map res) *ᵥ y))
  let Fl : Finset (ι → 𝓴) := Finset.univ.filter fun y => qk y = sb
  let T : Finset (ι → 𝓴) := Fl.filter fun y => y ≠ 0
  have hN : Nat.card {x : ι → 𝓴 // (2 : 𝓴)⁻¹ * (x ⬝ᵥ ((BO.map res) *ᵥ x)) = sb} = Fl.card :=
    Nat.subtype_card Fl (fun x => by simp [Fl, qk])
  rw [hN, hcardk] at hcount
  have hle1 : T.card ≤ Fl.card := Finset.card_filter_le _ _
  have hle2 : Fl.card ≤ T.card + 1 := by
    have hsub : Fl ⊆ insert 0 T := by
      intro y hy
      by_cases h0 : y = 0
      · simp [h0]
      · exact Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hy, h0⟩)
    exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  have hqpos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq0
  refine ⟨(T.card : ℝ≥0) * ((Ideal.absNorm v.asIdeal : ℝ≥0)⁻¹) ^ (2 * M - 1), ?_, fun A hA hAs => ?_⟩
  · push_cast
    exact real_bound _ _ (Fl.card : ℝ) hqpos M hM1 hcount (by exact_mod_cast hle1)
      (by exact_mod_cast hle2)
  · set Qf : (ι → Fv F v) → Fv F v := fun x => (2 : Fv F v)⁻¹ * (x ⬝ᵥ ((BO.map phi) *ᵥ x)) with hQf
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
    have hball : MeasurableSet {a : Fv F v | Valued.v a < 1} :=
      by
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
        if qk y = sb then ((Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹ ^ (2 * M - 1)) * lam A else 0 := by
      intro y hy
      have hy0 : y ≠ 0 := (Finset.mem_filter.1 hy).2
      obtain ⟨hint, hprim⟩ := (cover (lf y)).2 ⟨y, hy0, fun i => by simp⟩
      obtain ⟨a, haQ, har⟩ := res_Q c hc hr BO y
      have key := GlobalTheory.T.primitive_vector_quadratic_level_measure F v lam hlam h2 ι (BO.map phi) hBs hBint hBdet (lf y) hint hprim A hA
      have hkey : (Measure.pi fun _ : ι => lam) (P y) = _ := key
      rw [hkey, hM]
      have hcl : Valued.v (s - Qf (lf y)) < 1 ↔ qk y = sb := by
        have := res_eq_iff (⟨s, hs⟩ : 𝒪) a
        rw [har] at this
        rw [show Qf (lf y) = (a : Fv F v) from haQ.symm]
        exact ⟨fun h => (this.2 h).symm, fun h => this.1 h.symm⟩
      split_ifs with he
      · have hlt := hcl.2 he
        have : A ∩ {s' | Valued.v (s' - (2 : Fv F v)⁻¹ * (lf y ⬝ᵥ ((BO.map phi) *ᵥ lf y))) < 1} = A := by
          refine Set.inter_eq_left.2 fun z hz => ?_
          have h5 : Valued.v (z - s) < 1 := hAs hz
          have h6 := Valuation.map_add_lt _ h5 hlt
          have e : z - s + (s - Qf (lf y)) = z - Qf (lf y) := by ring
          rw [e] at h6
          exact h6
        rw [this]
      · have : A ∩ {s' | Valued.v (s' - (2 : Fv F v)⁻¹ * (lf y ⬝ᵥ ((BO.map phi) *ᵥ lf y))) < 1} = ∅ := by
          refine Set.eq_empty_iff_forall_notMem.2 fun z hz => he (hcl.1 ?_)
          have h5 : Valued.v (z - s) < 1 := hAs hz.1
          have h6 : Valued.v (z - Qf (lf y)) < 1 := hz.2
          have h7 := Valuation.map_sub_lt _ h6 h5
          have e : z - Qf (lf y) - (z - s) = s - Qf (lf y) := by ring
          rw [e] at h7
          exact h7
        rw [this, measure_empty, mul_zero]
    rw [hS, measure_biUnion_finset hdisj hmeas, Finset.sum_congr rfl hclass, ← Finset.sum_filter,
      Finset.sum_const, nsmul_eq_mul]
    have hT : T0.filter (fun y => qk y = sb) = T := by
      ext y
      simp [T0, T, Fl, and_comm]
    rw [hT]
    have hq0' : (Ideal.absNorm v.asIdeal : ℝ≥0) ≠ 0 := by exact_mod_cast hq0
    push_cast [ENNReal.coe_inv hq0']
    rw [mul_assoc]

theorem density_primitive : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → Valued.v (2 : Fv F v) = 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι (Fv F v)), B.IsSymm → (∀ i j, B i j ∈ v.adicCompletionIntegers F) → Valued.v B.det = 1 → ∀ M : ℕ, Fintype.card ι = 2 * M → 1 ≤ M → ∀ s : Fv F v, s ∈ v.adicCompletionIntegers F → ∃ D : ℝ≥0, |(D : ℝ) - 1| ≤ 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ (M - 1) + 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ (2 * M - 1) ∧ ∀ A : Set (Fv F v), MeasurableSet A → A ⊆ {z | Valued.v (z - s) < 1} → (Measure.pi fun _ : ι => lam) {x | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧ (∃ i, Valued.v (x i) = 1) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} = (D : ℝ≥0∞) * lam A := by
  intro F _ _ v lam hlam h2 ι _ _ B hBs hBint hBdet M hM hM1 s hs
  exact core lam hlam h2 ι B hBs hBint hBdet M hM hM1 s hs

end GlobalTheory.CompanionTheory.SW.LGPrim
