import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSNCAtlasOfIsEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential

open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt GlobalTheory.SNCComp
open scoped ENNReal

namespace GlobalTheory.SNCComp.CompAtlas

open Set Topology Filter

noncomputable section

open scoped Classical

abbrev ins {n : ℕ} (a : Fin (n + 1)) (z : Fin n → ℂ) : Fin (n + 1) → ℂ := Fin.insertNth a 0 z

def insZero {n : ℕ} (a : Fin (n + 1)) : (Fin n → ℂ) →L[ℂ] (Fin (n + 1) → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => ins a z
      map_add' := by
        intro z w; ext i
        induction i using Fin.succAboveCases a <;> simp
      map_smul' := by
        intro c z; ext i
        induction i using Fin.succAboveCases a <;> simp }

theorem coe_insZero {n : ℕ} (a : Fin (n + 1)) :
    (insZero a : (Fin n → ℂ) → (Fin (n + 1) → ℂ)) = fun z => ins a z := by
  ext z i; simp [insZero]

def dropC {n : ℕ} (a : Fin (n + 1)) : (Fin (n + 1) → ℂ) →L[ℂ] (Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p b => p (a.succAbove b)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem coe_dropC {n : ℕ} (a : Fin (n + 1)) :
    (dropC a : (Fin (n + 1) → ℂ) → (Fin n → ℂ)) = fun p b => p (a.succAbove b) := by
  ext p b; simp [dropC]

theorem insertNth_drop {n : ℕ} (a : Fin (n + 1)) (p : Fin (n + 1) → ℂ) (h : p a = 0) :
    ins a (fun b => p (a.succAbove b)) = p := by
  ext i
  induction i using Fin.succAboveCases a <;> simp [h]

theorem drop_insertNth {n : ℕ} (a : Fin (n + 1)) (z : Fin n → ℂ) :
    (fun b => ins a z (a.succAbove b)) = z := by
  ext b; simp

theorem continuous_insertNth_zero {n : ℕ} (a : Fin (n + 1)) :
    Continuous fun z : Fin n → ℂ => ins a z := by
  rw [← coe_insZero]; exact (insZero a).continuous

section restr

variable {Y : Type} [TopologicalSpace Y] {n : ℕ}

def restrChart (χ : OpenPartialHomeomorph Y (Fin (n + 1) → ℂ)) (a : Fin (n + 1)) (S : Set Y)
    (hS : ∀ w ∈ χ.source, w ∈ S ↔ χ w a = 0) (y₀ : S) : OpenPartialHomeomorph S (Fin n → ℂ) where
  toFun v := fun b => χ v.1 (a.succAbove b)
  invFun z := if h : ins a z ∈ χ.target then
      ⟨χ.symm (ins a z), (hS _ (χ.map_target h)).2 (by rw [χ.right_inv h]; simp)⟩
    else y₀
  source := Subtype.val ⁻¹' χ.source
  target := {z | ins a z ∈ χ.target}
  map_source' := by
    intro v hv
    have h0 : χ v.1 a = 0 := (hS _ hv).1 v.2
    show ins a (fun b => χ v.1 (a.succAbove b)) ∈ χ.target
    rw [insertNth_drop a _ h0]; exact χ.map_source hv
  map_target' := by
    intro z hz
    have hz' : ins a z ∈ χ.target := hz
    show (if h : ins a z ∈ χ.target then _ else y₀).1 ∈ χ.source
    rw [dif_pos hz']
    exact χ.map_target hz'
  left_inv' := by
    intro v hv
    have h0 : χ v.1 a = 0 := (hS _ hv).1 v.2
    have hm : ins a (fun b => χ v.1 (a.succAbove b)) ∈ χ.target := by
      rw [insertNth_drop a _ h0]; exact χ.map_source hv
    show (if h : ins a (fun b => χ v.1 (a.succAbove b)) ∈ χ.target then _ else y₀) = v
    rw [dif_pos hm]
    apply Subtype.ext
    show χ.symm (ins a (fun b => χ v.1 (a.succAbove b))) = v.1
    rw [insertNth_drop a _ h0, χ.left_inv hv]
  right_inv' := by
    intro z hz
    have hz' : ins a z ∈ χ.target := hz
    show (fun b => χ (if h : ins a z ∈ χ.target then _ else y₀).1 (a.succAbove b)) = z
    rw [dif_pos hz']
    show (fun b => χ (χ.symm (ins a z)) (a.succAbove b)) = z
    rw [χ.right_inv hz']
    exact drop_insertNth a z
  open_source := χ.open_source.preimage continuous_subtype_val
  open_target := χ.open_target.preimage (continuous_insertNth_zero a)
  continuousOn_toFun :=
    (continuous_pi fun b => continuous_apply (a.succAbove b)).comp_continuousOn
      (χ.continuousOn.comp continuous_subtype_val.continuousOn fun _ hv => hv)
  continuousOn_invFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine (χ.continuousOn_symm.comp (continuous_insertNth_zero a).continuousOn
      fun z hz => hz).congr ?_
    intro z hz
    have hz' : ins a z ∈ χ.target := hz
    simp only [Function.comp_apply]
    rw [dif_pos hz']

end restr

section restrLemmas

variable {Y : Type} [TopologicalSpace Y] {n : ℕ}

theorem restrChart_symm_val (χ : OpenPartialHomeomorph Y (Fin (n + 1) → ℂ)) (a : Fin (n + 1))
    (S : Set Y) (hS : ∀ w ∈ χ.source, w ∈ S ↔ χ w a = 0) (y₀ : S) {z : Fin n → ℂ}
    (hz : z ∈ (restrChart χ a S hS y₀).target) :
    ((restrChart χ a S hS y₀).symm z).1 = χ.symm (ins a z) := by
  have hz' : ins a z ∈ χ.target := hz
  show (if h : ins a z ∈ χ.target then _ else y₀).1 = _
  rw [dif_pos hz']

end restrLemmas

theorem analyticAt_trans {m : ℕ} {Y : Type} [TopologicalSpace Y] (B : FinHolAtlas m Y)
    {χ χ' : OpenPartialHomeomorph Y (Fin m → ℂ)} (h : IsCompatChart B χ) (h' : IsCompatChart B χ')
    {p : Fin m → ℂ} (hp : p ∈ χ.target) (hp' : χ.symm p ∈ χ'.source) :
    AnalyticAt ℂ (χ' ∘ χ.symm) p := by
  obtain ⟨j, hj⟩ := B.cover (χ.symm p)
  have h1 : AnalyticAt ℂ (B.chart j ∘ χ.symm) p := (h j).2 p ⟨hp, hj⟩
  have h2 : AnalyticAt ℂ (χ' ∘ (B.chart j).symm) (B.chart j (χ.symm p)) :=
    (h' j).1 _ ⟨(B.chart j).map_source hj, by
      show (B.chart j).symm (B.chart j (χ.symm p)) ∈ χ'.source
      rw [(B.chart j).left_inv hj]; exact hp'⟩
  refine (h2.comp_of_eq h1 rfl).congr ?_
  filter_upwards [(χ.continuousAt_symm hp).preimage_mem_nhds
    ((B.chart j).open_source.mem_nhds hj)] with p' hp'
  simp only [Function.comp_apply]
  rw [(B.chart j).left_inv hp']

theorem exists_isSNCAtlas : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (B : FinHolAtlas (n + 1) Y) (X : Type) [TopologicalSpace X] (μ : Y → X) (q r : ℕ)
    (L : Fin q → LocPot X) (t : Fin q → X → X → ℂ) (W : Fin r → Set Y) (e : Fin q → Fin r → ℕ),
    IsJointSNC B μ L t W e → ∀ k, ∃ C : FinHolAtlas n (W k), HoloMap C B Subtype.val ∧
      GlobalTheory.SNCComp.IsSNCAtlas B μ L t W e k C := by
  intro n Y _ _ _ B X _ μ q r L t W e hJ k
  choose χ hχB hyχ κ hκinj hκW hκt using hJ
  have hmem : ∀ y, ∀ w ∈ (χ y).source, w ∈ W k ↔ ∃ a, κ y k = some a ∧ χ y w a = 0 := by
    intro y w hw
    constructor
    · intro hwk
      have h : w ∈ W k ∩ (χ y).source := ⟨hwk, hw⟩
      rw [hκW y k] at h
      exact h.2
    · intro hex
      have h : w ∈ {w ∈ (χ y).source | ∃ a, κ y k = some a ∧ χ y w a = 0} := ⟨hw, hex⟩
      rw [← hκW y k] at h
      exact h.1
  have hclosed : IsClosed (W k) := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro y hy
    cases hk : κ y k with
    | none =>
      refine ⟨(χ y).source, ?_, (χ y).open_source, hyχ y⟩
      intro w hw hwk
      obtain ⟨a, ha, -⟩ := (hmem y w hw).1 hwk
      rw [hk] at ha
      cases ha
    | some a =>
      refine ⟨(χ y).source ∩ χ y ⁻¹' {p | p a ≠ 0}, ?_,
        (χ y).continuousOn.isOpen_inter_preimage (χ y).open_source
          (isOpen_ne_fun (continuous_apply a) continuous_const), hyχ y, ?_⟩
      · rintro w ⟨hw, hwa⟩ hwk
        obtain ⟨a', ha', h0⟩ := (hmem y w hw).1 hwk
        rw [hk] at ha'
        cases Option.some_injective _ ha'
        exact hwa h0
      · intro h0
        exact hy ((hmem y y (hyχ y)).2 ⟨a, hk, h0⟩)
  obtain ⟨T, hTW, hcov⟩ := hclosed.isCompact.elim_nhds_subcover (fun y => (χ y).source)
    fun y _ => (χ y).open_source.mem_nhds (hyχ y)
  let y : Fin T.card → Y := fun j => (T.equivFin.symm j).1
  have hyW : ∀ j, y j ∈ W k := fun j => hTW _ (T.equivFin.symm j).2
  have hA : ∀ j, ∃ a, κ (y j) k = some a := fun j => by
    obtain ⟨a, ha, -⟩ := (hmem (y j) (y j) (hyχ _)).1 (hyW j)
    exact ⟨a, ha⟩
  choose a ha using hA
  have hS : ∀ j, ∀ w ∈ (χ (y j)).source, w ∈ W k ↔ χ (y j) w (a j) = 0 := by
    intro j w hw
    rw [hmem _ w hw]
    constructor
    · rintro ⟨a', ha', h0⟩
      rw [ha j] at ha'
      cases Option.some_injective _ ha'
      exact h0
    · intro h0
      exact ⟨a j, ha j, h0⟩
  let c : Fin T.card → OpenPartialHomeomorph (W k) (Fin n → ℂ) := fun j =>
    restrChart (χ (y j)) (a j) (W k) (hS j) ⟨y j, hyW j⟩
  have hc_symm : ∀ j, ∀ z ∈ (c j).target, ((c j).symm z).1 = (χ (y j)).symm (ins (a j) z) :=
    fun j z hz => restrChart_symm_val _ _ _ _ _ hz
  have hc_nhds : ∀ j, ∀ z ∈ (c j).target,
      ∀ᶠ z' in 𝓝 z, ((c j).symm z').1 = (χ (y j)).symm (ins (a j) z') := fun j z hz => by
    filter_upwards [(c j).open_target.mem_nhds hz] with z' hz'
    exact hc_symm j z' hz'
  let C : FinHolAtlas n (W k) :=
    { n := T.card
      chart := c
      cover := by
        intro v
        have hv := hcov v.2
        simp only [mem_iUnion, exists_prop] at hv
        obtain ⟨x, hx, hvx⟩ := hv
        refine ⟨T.equivFin ⟨x, hx⟩, ?_⟩
        show v.1 ∈ (χ (y (T.equivFin ⟨x, hx⟩))).source
        simpa [y] using hvx
      holo := by
        rintro j j' z ⟨hz, hz'⟩
        have hzt : ins (a j) z ∈ (χ (y j)).target := hz
        have hz's : (χ (y j)).symm (ins (a j) z) ∈ (χ (y j')).source := by
          have : ((c j).symm z).1 ∈ (χ (y j')).source := hz'
          rwa [hc_symm j z hz] at this
        have han := (dropC (a j')).analyticAt _ |>.comp
          ((analyticAt_trans B (hχB _) (hχB _) hzt hz's).comp ((insZero (a j)).analyticAt z))
        refine han.congr ?_
        filter_upwards [hc_nhds j z hz] with z' hz'
        simp only [Function.comp_apply, coe_dropC, coe_insZero]
        show _ = fun b => χ (y j') ((c j).symm z').1 ((a j').succAbove b)
        rw [hz'] }
  refine ⟨C, ⟨continuous_subtype_val, ?_⟩, ?_⟩
  · rintro j j' z ⟨hz, hz'⟩
    have hzt : ins (a j) z ∈ (χ (y j)).target := hz
    have hz's : (χ (y j)).symm (ins (a j) z) ∈ (B.chart j').source := by
      have : ((c j).symm z).1 ∈ (B.chart j').source := hz'
      rwa [hc_symm j z hz] at this
    have han := ((hχB (y j) j').2 _ ⟨hzt, hz's⟩).comp ((insZero (a j)).analyticAt z)
    refine han.congr ?_
    filter_upwards [hc_nhds j z hz] with z' hz'
    simp only [Function.comp_apply, coe_insZero]
    show _ = B.chart j' ((c j).symm z').1
    rw [hz']
  · intro j
    refine ⟨y j, χ (y j), κ (y j), a j, hχB _, hyχ _, ha j, hκinj _, hκW _, ?_, rfl,
      fun w _ => rfl, rfl, fun z hz => hc_symm j z hz⟩
    intro i
    obtain ⟨h1, u, hu, hu0, hut⟩ := hκt (y j) i
    refine ⟨h1, u, hu, hu0, fun w hw => ?_⟩
    rw [hut w hw]
    congr 1
    refine Finset.prod_congr rfl fun k' _ => ?_
    cases κ (y j) k' <;> rfl

end

end GlobalTheory.SNCComp.CompAtlas
