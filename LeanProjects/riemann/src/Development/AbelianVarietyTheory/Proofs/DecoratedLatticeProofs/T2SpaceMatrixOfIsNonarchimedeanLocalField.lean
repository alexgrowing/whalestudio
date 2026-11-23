import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IndicatorFunctionIdentity
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearChangeOfVariablesLocalFieldMatrix
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist

noncomputable section

open MeasureTheory ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (InDual)
open scoped Pointwise Topology

namespace GlobalTheory.FinPl.Comm

section General

variable {X A B : Type} [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B] [T2Space X]

theorem comp_mem_SB {f : A → ℂ} (hf : f ∈ SB A) {p : X → A} {s : A → X} (hp : Continuous p) (hs : Continuous s)
    (h : ∀ x, s (p x) = x) : (fun x => f (p x)) ∈ SB X := by
  have hf' : IsLocallyConstant f ∧ HasCompactSupport f := hf
  change IsLocallyConstant _ ∧ HasCompactSupport _
  refine ⟨hf'.1.comp_continuous hp, ?_⟩
  refine HasCompactSupport.intro (hf'.2.isCompact.image hs) fun x hx => ?_
  by_contra hne
  exact hx ⟨p x, subset_tsupport f hne, h x⟩

theorem prod_mem_SB {f : A → ℂ} {g : B → ℂ} (hf : f ∈ SB A) (hg : g ∈ SB B) {p : X → A} {r : X → B} {s : A × B → X}
    (hp : Continuous p) (hr : Continuous r) (hs : Continuous s) (h : ∀ x, s (p x, r x) = x) :
    (fun x => f (p x) * g (r x)) ∈ SB X := by
  have hf' : IsLocallyConstant f ∧ HasCompactSupport f := hf
  have hg' : IsLocallyConstant g ∧ HasCompactSupport g := hg
  change IsLocallyConstant _ ∧ HasCompactSupport _
  refine ⟨(hf'.1.comp_continuous hp).mul (hg'.1.comp_continuous hr), ?_⟩
  refine HasCompactSupport.intro ((hf'.2.isCompact.prod hg'.2.isCompact).image hs) fun x hx => ?_
  by_contra hne
  have h1 : f (p x) ≠ 0 := fun h0 => hne (by simp [h0])
  have h2 : g (r x) ≠ 0 := fun h0 => hne (by simp [h0])
  exact hx ⟨(p x, r x), ⟨subset_tsupport f h1, subset_tsupport g h2⟩, h x⟩

open Classical in
theorem ite_mem_SB {P : X → Prop} (hK : IsCompact {x | P x}) (ho : IsOpen {x | P x}) :
    (fun x => if P x then (1 : ℂ) else 0) ∈ SB X := by
  have hc : IsClosed {x | P x} := hK.isClosed
  change IsLocallyConstant _ ∧ HasCompactSupport _
  refine ⟨fun t => ?_, HasCompactSupport.intro hK fun x hx => if_neg hx⟩
  have ht : (fun x => if P x then (1 : ℂ) else 0) ⁻¹' t =
      ({x | P x} ∩ {_x | (1 : ℂ) ∈ t}) ∪ ({x | P x}ᶜ ∩ {_x | (0 : ℂ) ∈ t}) := by
    ext x
    by_cases hx : P x <;> simp [hx]
  rw [ht]
  exact (ho.inter isOpen_const).union (hc.isOpen_compl.inter isOpen_const)

private theorem t2Space_of_isNonarchimedeanLocalField_decorated_lattice (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : T2Space K := by
  refine IsTopologicalAddGroup.t2Space_of_zero_sep fun x hx => ⟨{y | valuation K y < valuation K x}, ?_, by simp⟩
  exact (IsValuativeTopology.hasBasis_nhds_zero' K).mem_of_mem (by simpa using hx)

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem t2Space_matrix_of_isNonarchimedeanLocalField : T2Space (Matrix n n' k) := by
  haveI := t2Space_of_isNonarchimedeanLocalField_decorated_lattice k
  infer_instance

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem tensCol_mem {Ψ : Matrix n n' k → ℂ} {a : (n → k) → ℂ} (hΨ : Ψ ∈ SB (Matrix n n' k)) (ha : a ∈ SB (n → k)) :
    tensCol Ψ a ∈ SB (Matrix n (n' ⊕ Fin 1) k) := by
  haveI : T2Space (Matrix n (n' ⊕ Fin 1) k) := t2Space_matrix_of_isNonarchimedeanLocalField
  refine prod_mem_SB hΨ ha (p := fun x : Matrix n (n' ⊕ Fin 1) k => x.submatrix id Sum.inl)
    (r := fun (x : Matrix n (n' ⊕ Fin 1) k) i => x i (Sum.inr 0))
    (s := fun z => (Matrix.of fun i j => Sum.elim (z.1 i) (fun _ => z.2 i) j : Matrix n (n' ⊕ Fin 1) k))
    (continuous_id.matrix_submatrix _ _) (continuous_pi fun i => continuous_id.matrix_elem i _)
    (continuous_matrix fun i j => ?_) fun x => ?_
  · rcases j with j | j
    · simp only [Matrix.of_apply, Sum.elim_inl]
      exact continuous_fst.matrix_elem i j
    · simp only [Matrix.of_apply, Sum.elim_inr]
      exact (continuous_apply i).comp continuous_snd
  · ext i j
    rcases j with j | j
    · simp
    · simp [Subsingleton.elim j 0]

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem tensRow_mem {Ψ : Matrix n n' k → ℂ} {b : (n' → k) → ℂ} (hΨ : Ψ ∈ SB (Matrix n n' k)) (hb : b ∈ SB (n' → k)) :
    tensRow Ψ b ∈ SB (Matrix (n ⊕ Fin 1) n' k) := by
  haveI : T2Space (Matrix (n ⊕ Fin 1) n' k) := t2Space_matrix_of_isNonarchimedeanLocalField
  refine prod_mem_SB hΨ hb (p := fun x : Matrix (n ⊕ Fin 1) n' k => x.submatrix Sum.inl id)
    (r := fun x : Matrix (n ⊕ Fin 1) n' k => x (Sum.inr 0))
    (s := fun z => (Matrix.of fun i j => Sum.elim (fun i => z.1 i j) (fun _ => z.2 j) i : Matrix (n ⊕ Fin 1) n' k))
    (continuous_id.matrix_submatrix _ _) (continuous_pi fun j => continuous_id.matrix_elem _ j)
    (continuous_matrix fun i j => ?_) fun x => ?_
  · rcases i with i | i
    · simp only [Matrix.of_apply, Sum.elim_inl]
      exact continuous_fst.matrix_elem i j
    · simp only [Matrix.of_apply, Sum.elim_inr]
      exact (continuous_apply j).comp continuous_snd
  · ext i j
    rcases i with i | i
    · simp
    · simp [Subsingleton.elim i 0]

theorem isCompact_lat (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] : IsCompact (L : Set (n → k)) := by
  obtain ⟨m, v, hv⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (inferInstance : L.IsLattice k).fg
  have hset : (L : Set (n → k)) = Set.range fun c : Fin m → 𝒪[k] => ∑ i, c i • v i := by
    ext x
    rw [SetLike.mem_coe, ← hv, Submodule.mem_span_range_iff_exists_fun, Set.mem_range]
  rw [hset]
  refine isCompact_range (continuous_finset_sum _ fun i _ => continuous_pi fun j => ?_)
  change Continuous fun c : Fin m → 𝒪[k] => (c i : k) * v i j
  exact (continuous_subtype_val.comp (continuous_apply i)).mul continuous_const

theorem dual_compact_open (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] :
    IsCompact {η | InDual L η} ∧ IsOpen {η | InDual L η} := by
  obtain ⟨m, v, hv⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (inferInstance : L.IsLattice k).fg
  have hvL : ∀ i, v i ∈ L := fun i => by
    rw [← hv]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hiff : ∀ η : n → k, InDual L η ↔ ∀ i, η ⬝ᵥ v i ∈ 𝒪[k] := by
    intro η
    constructor
    · intro h i
      exact h (v i) (hvL i)
    · intro h y hy
      rw [← hv, Submodule.mem_span_range_iff_exists_fun] at hy
      obtain ⟨c, rfl⟩ := hy
      rw [dotProduct_sum]
      refine Subring.sum_mem _ fun i _ => ?_
      rw [dotProduct_smul]
      exact mul_mem (c i).2 (h i)
  have hcont : ∀ i, Continuous fun η : n → k => η ⬝ᵥ v i := fun i =>
    continuous_id.dotProduct continuous_const
  have hO : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer
  have hC : IsClosed (𝒪[k] : Set k) := Valuation.isClosed_integer
  have hset : {η | InDual L η} = ⋂ i, (fun η : n → k => η ⬝ᵥ v i) ⁻¹' (𝒪[k] : Set k) := by
    ext η
    simp only [Set.mem_setOf_eq, hiff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
  have hopen : IsOpen {η | InDual L η} := by
    rw [hset]
    exact isOpen_iInter_of_finite fun i => hO.preimage (hcont i)
  have hclosed : IsClosed {η | InDual L η} := by
    rw [hset]
    exact isClosed_iInter fun i => hC.preimage (hcont i)
  refine ⟨?_, hopen⟩
  have htop : Submodule.span k (Set.range v) = ⊤ := by
    rw [← Submodule.span_span_of_tower 𝒪[k] k (Set.range v), hv]
    exact (inferInstance : L.IsLattice k).span_eq_top
  have hcoef : ∀ j : n, ∃ a : Fin m → k, ∑ i, a i • v i = Pi.single j 1 := fun j =>
    (Submodule.mem_span_range_iff_exists_fun k).mp (by rw [htop]; exact Submodule.mem_top)
  choose a ha using hcoef
  have hsub : {η | InDual L η} ⊆
      Set.pi Set.univ fun j => Set.range fun c : Fin m → 𝒪[k] => ∑ i, a j i * (c i : k) := by
    intro η hη j _
    refine ⟨fun i => ⟨η ⬝ᵥ v i, (hiff η).mp hη i⟩, ?_⟩
    have := congrArg (fun w => η ⬝ᵥ w) (ha j)
    simp only [dotProduct_sum, dotProduct_smul, smul_eq_mul, dotProduct_single, mul_one] at this
    simpa using this
  refine IsCompact.of_isClosed_subset (isCompact_univ_pi fun j => isCompact_range ?_) hclosed hsub
  exact continuous_finset_sum _ fun i _ =>
    continuous_const.mul (continuous_subtype_val.comp (continuous_apply i))

theorem vecInd_mem (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] : vecInd L ∈ SB (n → k) := by
  haveI := t2Space_of_isNonarchimedeanLocalField_decorated_lattice k
  exact ite_mem_SB (P := fun y => y ∈ L) (isCompact_lat L) (isOpen_lat L)

theorem dualInd_mem (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] : dualInd L ∈ SB (n → k) := by
  haveI := t2Space_of_isNonarchimedeanLocalField_decorated_lattice k
  exact ite_mem_SB (P := fun η => InDual L η) (dual_compact_open L).1 (dual_compact_open L).2

variable [MeasurableSpace k] [BorelSpace k]

def fpair (χ : AddChar k Circle) (ε : k) (μ : Measure (n → k)) (a b : (n → k) → ℂ) : ℂ :=
  ∫ η, (∫ y, a y * (χ (ε * (η ⬝ᵥ y)) : ℂ) ∂μ) * b η ∂μ

private theorem exists_valuation_lt_subset_of_mem_nhds_zero (G : Set (n → k)) (hG : G ∈ 𝓝 (0 : n → k)) :
    ∃ γ : ValueGroupWithZero k, γ ≠ 0 ∧ ∀ z : n → k, (∀ i, valuation k (z i) < γ) → z ∈ G := by
  rw [nhds_pi, Filter.mem_pi'] at hG
  obtain ⟨I, t, ht, hsub⟩ := hG
  have hV : (⋂ i, t i) ∈ 𝓝 (0 : k) := Filter.iInter_mem.mpr ht
  obtain ⟨γ, hγ, hγV⟩ := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mp hV
  refine ⟨γ, hγ, fun z hz => hsub fun i _ => ?_⟩
  exact Set.mem_iInter.mp (hγV (hz i)) i

private theorem measurableSet_of_isCompact_of_mem_nhds_of_add_mem (G : Set (n → k)) (hK : IsCompact G) (hG : G ∈ 𝓝 (0 : n → k))
    (hadd : ∀ x ∈ G, ∀ y ∈ G, x + y ∈ G) : MeasurableSet G := by
  obtain ⟨γ, hγ, hbox⟩ := exists_valuation_lt_subset_of_mem_nhds_zero G hG
  have hball : ∀ a : k, IsOpen {x : k | valuation k (x - a) < γ} := by
    intro a
    refine isOpen_iff_mem_nhds.mpr fun x hx => ?_
    rw [IsValuativeTopology.mem_nhds_iff']
    refine ⟨Units.mk0 γ hγ, fun z hz => ?_⟩
    have := Valuation.map_add_lt (valuation k) hz hx
    simpa [sub_add_sub_cancel] using this
  have hcopen : ∀ g : n → k, IsOpen (Set.univ.pi fun i => {x : k | valuation k (x - g i) < γ}) :=
    fun g => isOpen_set_pi Set.finite_univ fun i _ => hball (g i)
  have hcmeas : ∀ g : n → k, MeasurableSet (Set.univ.pi fun i => {x : k | valuation k (x - g i) < γ}) :=
    fun g => MeasurableSet.univ_pi fun i => (hball (g i)).measurableSet
  have hcov : G ⊆ ⋃ g ∈ G, Set.univ.pi fun i => {x : k | valuation k (x - g i) < γ} := by
    intro g hg
    refine Set.mem_biUnion hg (Set.mem_univ_pi.mpr fun i => ?_)
    simpa [zero_lt_iff] using hγ
  obtain ⟨b, hbG, hbfin, hbcov⟩ := hK.elim_finite_subcover_image (fun g _ => hcopen g) hcov
  have heq : G = ⋃ g ∈ b, Set.univ.pi fun i => {x : k | valuation k (x - g i) < γ} := by
    refine Set.Subset.antisymm hbcov ?_
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨g, hg, hzg⟩ := hz
    have hzg' := Set.mem_univ_pi.mp hzg
    have hd : z - g ∈ G := hbox _ fun i => by simpa using hzg' i
    simpa using hadd _ hd g (hbG hg)
  rw [heq]
  exact MeasurableSet.biUnion hbfin.countable fun g _ => hcmeas g

open Classical in

theorem fpair_ne_zero (χ : AddChar k Circle) (hχ : Continuous χ) (ε : k) (hε : ε = 1 ∨ ε = -1) (μ : Measure (n → k))
    [μ.IsAddHaarMeasure] (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] : fpair χ ε μ (vecInd L) (dualInd L) ≠ 0 := by
  obtain ⟨s, hs⟩ := exists_cball_addChar_eq_one χ hχ
  have hcb : ∀ y : k, valuation k y ≤ valuation k (s : k) → y ∈ cball s := by
    intro y hy
    simp only [cball, Set.mem_setOf_eq]
    exact hy
  have hv1 : ∀ x : k, valuation k (ε * x) = valuation k x := by
    intro x
    rcases hε with rfl | rfl <;> simp
  obtain ⟨T, hT⟩ : ∃ T : Set (n → k), T = {η | ∀ y ∈ L, χ (ε * (η ⬝ᵥ y)) = 1} := ⟨_, rfl⟩
  have hmT : ∀ η, η ∈ T ↔ ∀ y ∈ L, χ (ε * (η ⬝ᵥ y)) = 1 := fun η => by rw [hT]; rfl
  have hLm : MeasurableSet (L : Set (n → k)) :=
    measurableSet_of_isCompact_of_mem_nhds_of_add_mem _ (isCompact_lat L) ((isOpen_lat L).mem_nhds L.zero_mem) fun x hx y hy => L.add_mem hx hy
  have hTc : IsClosed T := by
    have : T = ⋂ y ∈ (L : Set (n → k)), {η | χ (ε * (η ⬝ᵥ y)) = 1} := by
      ext η
      simp only [hmT, Set.mem_iInter, Set.mem_setOf_eq, SetLike.mem_coe]
    rw [this]
    exact isClosed_biInter fun y _ =>
      isClosed_eq (hχ.comp (continuous_const.mul (continuous_id.dotProduct continuous_const))) continuous_const
  have hs0 : (s : k) ≠ 0 := s.ne_zero
  have hD0 : InDual L 0 := by
    intro y _
    simp
  have hS'o : IsOpen ({η : n → k | InDual L ((s : k)⁻¹ • η)} ∩ {η | InDual L η}) :=
    ((dual_compact_open L).2.preimage (continuous_const_smul _)).inter (dual_compact_open L).2
  have h0S' : (0 : n → k) ∈ {η : n → k | InDual L ((s : k)⁻¹ • η)} ∩ {η | InDual L η} :=
    ⟨by simpa using hD0, hD0⟩
  have hS'sub : {η : n → k | InDual L ((s : k)⁻¹ • η)} ∩ {η | InDual L η} ⊆ T ∩ {η | InDual L η} := by
    rintro η ⟨h1, h2⟩
    refine ⟨(hmT η).mpr fun y hy => hs _ ?_, h2⟩
    have h3 := (show InDual L ((s : k)⁻¹ • η) from h1) y hy
    rw [smul_dotProduct, smul_eq_mul, Valuation.mem_integer_iff] at h3
    apply hcb
    rw [hv1]
    calc valuation k (η ⬝ᵥ y) = valuation k ((s : k) * ((s : k)⁻¹ * (η ⬝ᵥ y))) := by
          rw [mul_inv_cancel_left₀ hs0]
      _ = valuation k (s : k) * valuation k ((s : k)⁻¹ * (η ⬝ᵥ y)) := map_mul _ _ _
      _ ≤ valuation k (s : k) * 1 := mul_le_mul' le_rfl h3
      _ = valuation k (s : k) := mul_one _
  have hTDm : MeasurableSet (T ∩ {η | InDual L η}) := by
    refine measurableSet_of_isCompact_of_mem_nhds_of_add_mem _ ((dual_compact_open L).1.inter_left hTc)
      (Filter.mem_of_superset (hS'o.mem_nhds h0S') hS'sub) ?_
    rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩
    refine ⟨(hmT _).mpr fun z hz => ?_, show InDual L (x + y) from fun z hz => ?_⟩
    · rw [add_dotProduct, mul_add, AddChar.map_add_eq_mul, (hmT x).mp hx1 z hz, (hmT y).mp hy1 z hz, one_mul]
    · rw [add_dotProduct]
      exact add_mem ((show InDual L x from hx2) z hz) ((show InDual L y from hy2) z hz)
  have hin : ∀ η : n → k, ∫ y, vecInd L y * (χ (ε * (η ⬝ᵥ y)) : ℂ) ∂μ =
      T.indicator (fun _ => ((μ.real (L : Set (n → k)) : ℝ) : ℂ)) η := by
    intro η
    by_cases hη : η ∈ T
    · rw [Set.indicator_apply, if_pos hη]
      have hη' := (hmT η).mp hη
      have : (fun y => vecInd L y * (χ (ε * (η ⬝ᵥ y)) : ℂ)) = (L : Set (n → k)).indicator fun _ => (1 : ℂ) := by
        funext y
        by_cases hy : y ∈ L
        · simp [vecInd, hy, hη' y hy]
        · simp [vecInd, hy]
      rw [this, integral_indicator_const _ hLm]
      simp
    · rw [Set.indicator_apply, if_neg hη]
      have hex : ∃ y ∈ L, χ (ε * (η ⬝ᵥ y)) ≠ 1 := by
        by_contra hcon
        push_neg at hcon
        exact hη ((hmT η).mpr hcon)
      obtain ⟨y₀, hy₀, hne⟩ := hex
      have hc : (χ (ε * (η ⬝ᵥ y₀)) : ℂ) ≠ 1 := fun h => hne (Circle.coe_injective (h.trans Circle.coe_one.symm))
      have hf : ∀ y, vecInd L (y + y₀) * (χ (ε * (η ⬝ᵥ (y + y₀))) : ℂ) =
          (χ (ε * (η ⬝ᵥ y₀)) : ℂ) * (vecInd L y * (χ (ε * (η ⬝ᵥ y)) : ℂ)) := by
        intro y
        simp only [vecInd, L.add_mem_iff_left hy₀, dotProduct_add, mul_add, AddChar.map_add_eq_mul,
          Circle.coe_mul]
        ring
      have h1 := integral_add_right_eq_self (μ := μ) (fun y => vecInd L y * (χ (ε * (η ⬝ᵥ y)) : ℂ)) y₀
      simp only [hf, integral_const_mul] at h1
      have h2 : (1 - (χ (ε * (η ⬝ᵥ y₀)) : ℂ)) * ∫ y, vecInd L y * (χ (ε * (η ⬝ᵥ y)) : ℂ) ∂μ = 0 := by
        linear_combination -h1
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd (sub_eq_zero.mp h).symm hc
      · exact h
  have hout : ∀ η, T.indicator (fun _ => ((μ.real (L : Set (n → k)) : ℝ) : ℂ)) η * dualInd L η =
      (T ∩ {η | InDual L η}).indicator (fun _ => ((μ.real (L : Set (n → k)) : ℝ) : ℂ)) η := by
    intro η
    by_cases h1 : η ∈ T <;> by_cases h2 : InDual L η <;> simp [Set.indicator, dualInd, h1, h2]
  simp only [fpair, hin, hout]
  rw [integral_indicator_const _ hTDm]
  have hL0 : μ (L : Set (n → k)) ≠ 0 := (isOpen_lat L).measure_ne_zero μ ⟨0, L.zero_mem⟩
  have hLt : μ (L : Set (n → k)) ≠ ⊤ := (isCompact_lat L).measure_lt_top.ne
  have hI0 : μ (T ∩ {η | InDual L η}) ≠ 0 := fun h =>
    hS'o.measure_ne_zero μ ⟨0, h0S'⟩ (measure_mono_null hS'sub h)
  have hIt : μ (T ∩ {η | InDual L η}) ≠ ⊤ :=
    ((measure_mono Set.inter_subset_right).trans_lt (dual_compact_open L).1.measure_lt_top).ne
  exact smul_ne_zero (ENNReal.toReal_pos hI0 hIt).ne'
    (Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos hL0 hLt).ne')

end GlobalTheory.FinPl.Comm

end
