import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.LConvCut
import GroundTheory.AutomorphicForms.GLnLocal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth

set_option linter.unusedSectionVars false

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Topology
open GroundTheory.Automorphic.GLnLocal (congruenceSubgroup isOpen_congruenceSubgroup isCompact_congruenceSubgroup)

namespace DiscreteGroups.sglob.LConv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}

theorem superDiag_mul {u v : GL (Fin m) k} (hu : u ∈ unipB k (Fin m)) (hv : v ∈ unipB k (Fin m)) :
    superDiag (u * v) = superDiag u + superDiag v := by
  simp only [superDiag, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj =>
    GlobalTheory.LocGL.unipB_mul_apply ⟨u, hu⟩ ⟨v, hv⟩ (Finset.mem_filter.1 hj).2

theorem superDiag_one : superDiag (1 : GL (Fin m) k) = 0 := by
  have := superDiag_mul (one_mem (unipB k (Fin m))) (one_mem (unipB k (Fin m)))
  rw [mul_one] at this
  exact left_eq_add.1 this

theorem continuous_superDiag : Continuous (superDiag : GL (Fin m) k → k) := by
  unfold superDiag
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    Units.continuous_val.matrix_elem i j

variable (ψ : AddChar k Circle)

def WT : Submodule ℂ (GL (Fin m) k → ℂ) where
  carrier := {f | IsWhitTest ψ f}
  zero_mem' := ⟨fun _ _ _ => by simp, IsLocallyConstant.const 0, ∅, isCompact_empty, fun _ h => (h rfl).elim⟩
  add_mem' := by
    rintro f f' ⟨h1, h2, C, hC, h3⟩ ⟨h1', h2', C', hC', h3'⟩
    refine ⟨fun u hu g => ?_, h2.add h2', C ∪ C', hC.union hC', fun g hg => ?_⟩
    · simp only [Pi.add_apply, h1 u hu g, h1' u hu g]
      ring
    · by_cases hf : f g = 0
      · have hf' : f' g ≠ 0 := fun e => hg (by simp [hf, e])
        obtain ⟨u, hu, c, hc, e⟩ := h3' g hf'
        exact ⟨u, hu, c, Or.inr hc, e⟩
      · obtain ⟨u, hu, c, hc, e⟩ := h3 g hf
        exact ⟨u, hu, c, Or.inl hc, e⟩
  smul_mem' := by
    rintro a f ⟨h1, h2, C, hC, h3⟩
    refine ⟨fun u hu g => ?_, h2.comp (a * ·), C, hC, fun g hg => h3 g fun e => hg (by simp [e])⟩
    simp only [Pi.smul_apply, smul_eq_mul, h1 u hu g]
    ring

theorem mem_WT {f : GL (Fin m) k → ℂ} : f ∈ WT ψ ↔ IsWhitTest ψ f := Iff.rfl

def rhoW : Representation ℂ (GL (Fin m) k) (WT (m := m) ψ) where
  toFun x :=
    { toFun := fun f => ⟨fun g => (f : GL (Fin m) k → ℂ) (g * x), by
        obtain ⟨h1, h2, C, hC, h3⟩ := f.2
        refine ⟨fun u hu g => by beta_reduce; rw [mul_assoc, h1 u hu],
          h2.comp_continuous (continuous_id.mul continuous_const), (· * x⁻¹) '' C,
          hC.image (continuous_id.mul continuous_const), fun g hg => ?_⟩
        obtain ⟨u, hu, c, hc, e⟩ := h3 _ hg
        exact ⟨u, hu, _, ⟨c, hc, rfl⟩, by rw [← mul_assoc, ← e, mul_inv_cancel_right]⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext f g
    simp
  map_mul' x y := by
    ext f g
    simp [mul_assoc]

@[simp] theorem rhoW_apply (x : GL (Fin m) k) (f : WT (m := m) ψ) (g : GL (Fin m) k) :
    (rhoW ψ x f : GL (Fin m) k → ℂ) g = (f : GL (Fin m) k → ℂ) (g * x) := rfl

variable {ψ}

theorem WT.left (x : WT (m := m) ψ) {u : GL (Fin m) k} (hu : u ∈ unipB k (Fin m)) (g : GL (Fin m) k) :
    (x : GL (Fin m) k → ℂ) (u * g) = (ψ (superDiag u) : ℂ) * (x : GL (Fin m) k → ℂ) g := x.2.1 u hu g

theorem exists_congruence_subset {U : Set (GL (Fin m) k)} (hU : U ∈ 𝓝 (1 : GL (Fin m) k)) :
    ∃ r : ℕ, (congruenceSubgroup k m r : Set (GL (Fin m) k)) ⊆ U := by
  obtain ⟨r, -, hr⟩ := (GroundTheory.Automorphic.GLnLocal.hasBasis_nhds_one k m).mem_iff.1 hU
  exact ⟨r, hr⟩

theorem exists_fix_congruence (x : WT (m := m) ψ) :
    ∃ r : ℕ, ∀ κ ∈ congruenceSubgroup k m r, rhoW ψ κ x = x := by
  obtain ⟨h1, h2, C, hC, h3⟩ := x.2
  have hlc : IsLocallyConstant fun p : GL (Fin m) k × GL (Fin m) k =>
      (x : GL (Fin m) k → ℂ) (p.1 * p.2) - (x : GL (Fin m) k → ℂ) p.1 :=
    (h2.comp_continuous (continuous_fst.mul continuous_snd)).sub (h2.comp_continuous continuous_fst)
  obtain ⟨U, V, -, hV, hCU, h1V, hUV⟩ := generalized_tube_lemma hC (isCompact_singleton (x := (1 : GL (Fin m) k)))
    (hlc.isOpen_fiber 0) (by
      rintro ⟨c, y⟩ ⟨-, hy⟩
      have : y = 1 := hy
      simp [this])
  obtain ⟨r, hr⟩ := exists_congruence_subset (hV.mem_nhds (h1V rfl))
  have key : ∀ κ ∈ congruenceSubgroup k m r, ∀ g, (x : GL (Fin m) k → ℂ) g ≠ 0 →
      (x : GL (Fin m) k → ℂ) (g * κ) = (x : GL (Fin m) k → ℂ) g := by
    intro κ hκ g hg
    obtain ⟨u, hu, c, hc, rfl⟩ := h3 g hg
    have h4 : (x : GL (Fin m) k → ℂ) (c * κ) - (x : GL (Fin m) k → ℂ) c = 0 :=
      hUV (Set.mk_mem_prod (hCU hc) (hr hκ))
    rw [mul_assoc, h1 u hu, h1 u hu, sub_eq_zero.1 h4]
  refine ⟨r, fun κ hκ => Subtype.ext (funext fun g => ?_)⟩
  rw [rhoW_apply]
  by_cases hg : (x : GL (Fin m) k → ℂ) g = 0
  · by_contra hne
    have := key κ⁻¹ (inv_mem hκ) (g * κ) (by rw [← hg]; exact hne)
    rw [mul_inv_cancel_right] at this
    exact hne this.symm
  · exact key κ hκ g hg

theorem exists_fix (x : WT (m := m) ψ) : ∃ K : Subgroup (GL (Fin m) k), IsOpen (K : Set (GL (Fin m) k)) ∧
    IsCompact (K : Set (GL (Fin m) k)) ∧ ∀ κ ∈ K, rhoW ψ κ x = x := by
  obtain ⟨r, hr⟩ := exists_fix_congruence x
  exact ⟨_, isOpen_congruenceSubgroup k m r, isCompact_congruenceSubgroup k m r, hr⟩

theorem isSmooth_rhoW : IsSmooth (rhoW (m := m) ψ) := fun x => by
  obtain ⟨K, hK, -, h⟩ := exists_fix x
  refine isOpen_iff_mem_nhds.2 fun g hg => ?_
  have hg' : rhoW ψ g x = x := hg
  refine Filter.mem_of_superset
    ((hK.preimage (continuous_const.mul continuous_id : Continuous fun y => g⁻¹ * y)).mem_nhds (by simp)) ?_
  intro y hy
  show rhoW ψ y x = x
  have : y = g * (g⁻¹ * y) := by simp
  rw [this, map_mul, Module.End.mul_apply, h (g⁻¹ * y) hy, hg']

variable (ψ) in

def Good (K : Subgroup (GL (Fin m) k)) : Prop :=
  IsOpen (K : Set (GL (Fin m) k)) ∧ IsCompact (K : Set (GL (Fin m) k)) ∧
    ∀ u ∈ unipB k (Fin m), u ∈ K → ψ (superDiag u) = 1

theorem Good.mono {K K' : Subgroup (GL (Fin m) k)} (hK : Good ψ K) (h : K' ≤ K)
    (ho : IsOpen (K' : Set (GL (Fin m) k))) : Good ψ K' :=
  ⟨ho, hK.2.1.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho) h, fun u hu hu' => hK.2.2 u hu (h hu')⟩

theorem circle_eq_one {z : Circle} (h : ∀ n : ℕ, 0 < ((z ^ n : Circle) : ℂ).re) : z = 1 := by
  by_contra hz
  have h1 : (z : ℂ) ≠ 1 := fun e => hz (Subtype.ext e)
  have hb : ∀ n : ℕ, ‖∑ i ∈ Finset.range n, (z : ℂ) ^ i‖ ≤ 2 / ‖(z : ℂ) - 1‖ := fun n => by
    rw [geom_sum_eq h1, norm_div]
    refine div_le_div_of_nonneg_right ((norm_sub_le _ _).trans ?_) (norm_nonneg _)
    rw [norm_pow, Circle.norm_coe, one_pow, norm_one]
    norm_num
  have hq : ∀ n : ℕ, (1 / 2 : ℝ) ≤ ((z : ℂ) ^ n).re := fun n => by
    have h2 := h (2 * n)
    have h0 := h n
    have hn : ((z : ℂ) ^ n).re ^ 2 + ((z : ℂ) ^ n).im ^ 2 = 1 := by
      have : Complex.normSq ((z : ℂ) ^ n) = 1 := by
        rw [map_pow, Circle.normSq_coe, one_pow]
      rw [Complex.normSq_apply] at this
      nlinarith
    rw [Circle.coe_pow] at h0
    rw [Circle.coe_pow, mul_comm, pow_mul, sq, Complex.mul_re] at h2
    nlinarith
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * (2 / ‖(z : ℂ) - 1‖))
  have h3 : (n : ℝ) * (1 / 2) ≤ (∑ i ∈ Finset.range n, (z : ℂ) ^ i).re := by
    rw [Complex.re_sum]
    calc (n : ℝ) * (1 / 2) = ∑ _i ∈ Finset.range n, (1 / 2 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => hq i
  have h4 := (Complex.re_le_norm _).trans (hb n)
  linarith

theorem exists_good (hψ : Continuous ψ) {U : Set (GL (Fin m) k)} (hU : U ∈ 𝓝 (1 : GL (Fin m) k)) :
    ∃ K : Subgroup (GL (Fin m) k), Good ψ K ∧ (K : Set (GL (Fin m) k)) ⊆ U := by
  have hc : Continuous fun g : GL (Fin m) k => ((ψ (superDiag g) : Circle) : ℂ).re :=
    Complex.continuous_re.comp (continuous_subtype_val.comp (hψ.comp continuous_superDiag))
  have hV : {g : GL (Fin m) k | 0 < ((ψ (superDiag g) : Circle) : ℂ).re} ∈ 𝓝 (1 : GL (Fin m) k) :=
    (isOpen_lt continuous_const hc).mem_nhds (by simp [superDiag_one])
  obtain ⟨r, hr⟩ := exists_congruence_subset (Filter.inter_mem hU hV)
  refine ⟨congruenceSubgroup k m r, ⟨isOpen_congruenceSubgroup k m r, isCompact_congruenceSubgroup k m r,
    fun u hu huK => circle_eq_one fun n => ?_⟩, fun g hg => (hr hg).1⟩
  have hp : ∀ n : ℕ, ψ (superDiag (u ^ n)) = ψ (superDiag u) ^ n := fun n => by
    induction n with
    | zero => simp [superDiag_one]
    | succ n ih => rw [pow_succ, superDiag_mul (pow_mem hu n) hu, AddChar.map_add_eq_mul, ih, pow_succ]
  rw [← hp]
  exact (hr (pow_mem huK n)).2

open Classical in
variable (ψ) in

def deltaFun (K : Subgroup (GL (Fin m) k)) (g : GL (Fin m) k) : ℂ :=
  if h : ∃ u ∈ unipB k (Fin m), ∃ κ ∈ K, g = u * κ then (ψ (superDiag h.choose) : ℂ) else 0

theorem deltaFun_mul {K : Subgroup (GL (Fin m) k)} (hK : Good ψ K) {u κ : GL (Fin m) k}
    (hu : u ∈ unipB k (Fin m)) (hκ : κ ∈ K) : deltaFun ψ K (u * κ) = (ψ (superDiag u) : ℂ) := by
  have h : ∃ u' ∈ unipB k (Fin m), ∃ κ' ∈ K, u * κ = u' * κ' := ⟨u, hu, κ, hκ, rfl⟩
  rw [deltaFun, dif_pos h]
  obtain ⟨hu', κ', hκ', e⟩ := h.choose_spec
  set u' := h.choose
  have e2 : u'⁻¹ * u = κ' * κ⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, mul_assoc, e, inv_mul_cancel_left]
  have h1 := hK.2.2 _ (mul_mem (inv_mem hu') hu) (e2 ▸ mul_mem hκ' (inv_mem hκ))
  have h2 := superDiag_mul hu' (mul_mem (inv_mem hu') hu)
  rw [mul_inv_cancel_left] at h2
  rw [h2, AddChar.map_add_eq_mul, h1, mul_one]

theorem deltaFun_eq_zero {K : Subgroup (GL (Fin m) k)} {g : GL (Fin m) k}
    (h : ¬ ∃ u ∈ unipB k (Fin m), ∃ κ ∈ K, g = u * κ) : deltaFun ψ K g = 0 := by
  rw [deltaFun, dif_neg h]

theorem deltaFun_right {K : Subgroup (GL (Fin m) k)} (hK : Good ψ K) (g : GL (Fin m) k) {κ : GL (Fin m) k}
    (hκ : κ ∈ K) : deltaFun ψ K (g * κ) = deltaFun ψ K g := by
  by_cases h : ∃ u ∈ unipB k (Fin m), ∃ κ ∈ K, g = u * κ
  · obtain ⟨u, hu, κ', hκ', rfl⟩ := h
    rw [mul_assoc, deltaFun_mul hK hu (mul_mem hκ' hκ), deltaFun_mul hK hu hκ']
  · rw [deltaFun_eq_zero h, deltaFun_eq_zero]
    rintro ⟨u, hu, κ', hκ', e⟩
    exact h ⟨u, hu, κ' * κ⁻¹, mul_mem hκ' (inv_mem hκ), by rw [← mul_assoc, ← e, mul_inv_cancel_right]⟩

theorem isWhitTest_deltaFun {K : Subgroup (GL (Fin m) k)} (hK : Good ψ K) : IsWhitTest ψ (deltaFun ψ K) := by
  refine ⟨fun v hv g => ?_, ?_, K, hK.2.1, fun g hg => ?_⟩
  · by_cases h : ∃ u ∈ unipB k (Fin m), ∃ κ ∈ K, g = u * κ
    · obtain ⟨u, hu, κ, hκ, rfl⟩ := h
      rw [← mul_assoc, deltaFun_mul hK (mul_mem hv hu) hκ, deltaFun_mul hK hu hκ, superDiag_mul hv hu,
        AddChar.map_add_eq_mul, Circle.coe_mul]
    · rw [deltaFun_eq_zero h, deltaFun_eq_zero, mul_zero]
      rintro ⟨u, hu, κ, hκ, e⟩
      exact h ⟨v⁻¹ * u, mul_mem (inv_mem hv) hu, κ, hκ, by rw [mul_assoc, ← e, inv_mul_cancel_left]⟩
  · refine (IsLocallyConstant.iff_exists_open _).2 fun g => ⟨(fun y => g⁻¹ * y) ⁻¹' K,
      hK.1.preimage (continuous_const.mul continuous_id), by simp, fun y hy => ?_⟩
    rw [← deltaFun_right hK g hy, mul_inv_cancel_left]
  · by_contra h
    exact hg (deltaFun_eq_zero h)

open Classical in
variable (ψ) in

def delta (K : Subgroup (GL (Fin m) k)) : WT (m := m) ψ :=
  if h : Good ψ K then ⟨deltaFun ψ K, isWhitTest_deltaFun h⟩ else 0

theorem coe_delta {K : Subgroup (GL (Fin m) k)} (hK : Good ψ K) :
    (delta ψ K : GL (Fin m) k → ℂ) = deltaFun ψ K := by
  rw [delta, dif_pos hK]

theorem delta_mul {K : Subgroup (GL (Fin m) k)} (hK : Good ψ K) {u κ : GL (Fin m) k}
    (hu : u ∈ unipB k (Fin m)) (hκ : κ ∈ K) : (delta ψ K : GL (Fin m) k → ℂ) (u * κ) = (ψ (superDiag u) : ℂ) := by
  rw [coe_delta hK, deltaFun_mul hK hu hκ]

theorem delta_eq_zero {K : Subgroup (GL (Fin m) k)} {g : GL (Fin m) k}
    (h : ¬ ∃ u ∈ unipB k (Fin m), ∃ κ ∈ K, g = u * κ) : (delta ψ K : GL (Fin m) k → ℂ) g = 0 := by
  by_cases hK : Good ψ K
  · rw [coe_delta hK, deltaFun_eq_zero h]
  · rw [delta, dif_neg hK]
    rfl

theorem rhoW_delta {K : Subgroup (GL (Fin m) k)} {κ : GL (Fin m) k} (hκ : κ ∈ K) :
    rhoW ψ κ (delta ψ K) = delta ψ K := by
  by_cases hK : Good ψ K
  · refine Subtype.ext (funext fun g => ?_)
    rw [rhoW_apply, coe_delta hK, deltaFun_right hK g hκ]
  · rw [delta, dif_neg hK, map_zero]

theorem apply_mul_of_fixed {x : WT (m := m) ψ} {κ : GL (Fin m) k} (h : rhoW ψ κ x = x) (g : GL (Fin m) k) :
    (x : GL (Fin m) k → ℂ) (g * κ) = (x : GL (Fin m) k → ℂ) g := by
  rw [← rhoW_apply, h]

theorem eq_smul_delta {K : Subgroup (GL (Fin m) k)} (hK : Good ψ K) (x : WT (m := m) ψ)
    (hx : ∀ κ ∈ K, rhoW ψ κ x = x)
    (hs : ∀ g, (x : GL (Fin m) k → ℂ) g ≠ 0 → ∃ u ∈ unipB k (Fin m), ∃ κ ∈ K, g = u * κ) :
    x = (x : GL (Fin m) k → ℂ) 1 • delta ψ K := by
  refine Subtype.ext (funext fun g => ?_)
  show _ = (x : GL (Fin m) k → ℂ) 1 * (delta ψ K : GL (Fin m) k → ℂ) g
  by_cases h : ∃ u ∈ unipB k (Fin m), ∃ κ ∈ K, g = u * κ
  · obtain ⟨u, hu, κ, hκ, rfl⟩ := h
    rw [delta_mul hK hu hκ, apply_mul_of_fixed (hx κ hκ), mul_comm, ← WT.left x hu, mul_one]
  · rw [delta_eq_zero h, mul_zero]
    by_contra h0
    exact h (hs g h0)

theorem mem_conj {K : Subgroup (GL (Fin m) k)} {g y : GL (Fin m) k} :
    y ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ K := by
  constructor
  · rintro ⟨κ, hκ, rfl⟩
    simpa [mul_assoc] using hκ
  · intro h
    exact ⟨_, h, by simp [mul_assoc]⟩

theorem mem_span_delta_of_cover {K : Subgroup (GL (Fin m) k)} (hKo : IsOpen (K : Set (GL (Fin m) k)))
    (hKc : IsCompact (K : Set (GL (Fin m) k))) (D : Set (GL (Fin m) k)) (s : Finset (GL (Fin m) k)) :
    (∀ g ∈ s, g ∈ D) → ∀ x : WT (m := m) ψ, (∀ κ ∈ K, rhoW ψ κ x = x) →
      (∀ y, (x : GL (Fin m) k → ℂ) y ≠ 0 → ∃ g ∈ s, ∃ u ∈ unipB k (Fin m), ∃ κ ∈ K, y = u * g * κ) →
      x ∈ Submodule.span ℂ {y | ∃ g ∈ D, Good ψ (K.map (MulAut.conj g).toMonoidHom) ∧
        y = rhoW ψ g⁻¹ (delta ψ (K.map (MulAut.conj g).toMonoidHom))} := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _ x _ hs
    have : x = 0 := Subtype.ext (funext fun y => by
      by_contra h
      obtain ⟨g, hg, -⟩ := hs y h
      simp at hg)
    rw [this]
    exact zero_mem _
  | insert g s _ ih =>
    intro hD x hx hs
    have hD' : ∀ g ∈ s, g ∈ D := fun a ha => hD a (Finset.mem_insert_of_mem ha)
    have hval : ∀ u ∈ unipB k (Fin m), ∀ κ ∈ K, (x : GL (Fin m) k → ℂ) (u * g * κ) =
        (ψ (superDiag u) : ℂ) * (x : GL (Fin m) k → ℂ) g := fun u hu κ hκ => by
      rw [apply_mul_of_fixed (hx κ hκ), WT.left x hu]
    by_cases hg : (x : GL (Fin m) k → ℂ) g = 0
    · refine ih hD' x hx fun y hy => ?_
      obtain ⟨a, ha, u, hu, κ, hκ, e⟩ := hs y hy
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact absurd (by rw [e, hval u hu κ hκ, hg, mul_zero]) hy
      · exact ⟨a, ha, u, hu, κ, hκ, e⟩
    · have hgood : Good ψ (K.map (MulAut.conj g).toMonoidHom) := by
        refine ⟨?_, ?_, fun u hu huK => ?_⟩
        · have : ((K.map (MulAut.conj g).toMonoidHom : Subgroup _) : Set (GL (Fin m) k)) =
              (fun y => g⁻¹ * y * g) ⁻¹' K := Set.ext fun y => mem_conj
          rw [this]
          exact hKo.preimage ((continuous_const.mul continuous_id).mul continuous_const)
        · rw [Subgroup.coe_map]
          exact hKc.image ((continuous_const.mul continuous_id).mul continuous_const :
            Continuous fun y => g * y * g⁻¹)
        · have h1 := apply_mul_of_fixed (hx _ (mem_conj.1 huK)) g
          rw [← mul_assoc, mul_inv_cancel_left, WT.left x hu] at h1
          exact Subtype.ext ((mul_eq_right₀ hg).1 h1)
      set d := rhoW ψ g⁻¹ (delta ψ (K.map (MulAut.conj g).toMonoidHom)) with hd
      have hdK : ∀ κ ∈ K, rhoW ψ κ d = d := fun κ hκ => by
        have e : κ * g⁻¹ = g⁻¹ * (g * κ * g⁻¹) := by simp [mul_assoc]
        rw [hd, ← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply,
          rhoW_delta (mem_conj.2 (by simpa [mul_assoc] using hκ))]
      have h2 := ih hD' (x - (x : GL (Fin m) k → ℂ) g • d)
        (fun κ hκ => by rw [map_sub, map_smul, hx κ hκ, hdK κ hκ]) fun y hy => by
          have hy' : (x : GL (Fin m) k → ℂ) y - (x : GL (Fin m) k → ℂ) g *
              (delta ψ (K.map (MulAut.conj g).toMonoidHom) : GL (Fin m) k → ℂ) (y * g⁻¹) ≠ 0 := hy
          by_cases h : ∃ u ∈ unipB k (Fin m), ∃ κ ∈ K, y = u * g * κ
          · obtain ⟨u, hu, κ, hκ, rfl⟩ := h
            have e : u * g * κ * g⁻¹ = u * (g * κ * g⁻¹) := by simp [mul_assoc]
            rw [e, delta_mul hgood hu (mem_conj.2 (by simpa [mul_assoc] using hκ)), hval u hu κ hκ] at hy'
            exact absurd (by ring) hy'
          · rw [delta_eq_zero, mul_zero, sub_zero] at hy'
            · obtain ⟨a, ha, hrest⟩ := hs y hy'
              rcases Finset.mem_insert.1 ha with rfl | ha
              · exact absurd hrest h
              · exact ⟨a, ha, hrest⟩
            · rintro ⟨u, hu, κ, hκ, e⟩
              refine h ⟨u, hu, _, mem_conj.1 hκ, ?_⟩
              rw [mul_inv_eq_iff_eq_mul.1 e]
              simp [mul_assoc]
      have h3 : d ∈ Submodule.span ℂ {y | ∃ g ∈ D, Good ψ (K.map (MulAut.conj g).toMonoidHom) ∧
          y = rhoW ψ g⁻¹ (delta ψ (K.map (MulAut.conj g).toMonoidHom))} :=
        Submodule.subset_span ⟨g, hD g (Finset.mem_insert_self _ _), hgood, rfl⟩
      have h4 := add_mem h2 (Submodule.smul_mem _ ((x : GL (Fin m) k → ℂ) g) h3)
      rwa [sub_add_cancel] at h4

theorem mem_span_delta_of_dense {K : Subgroup (GL (Fin m) k)} (hKo : IsOpen (K : Set (GL (Fin m) k)))
    (hKc : IsCompact (K : Set (GL (Fin m) k))) {D : Set (GL (Fin m) k)} (hD : Dense D) (x : WT (m := m) ψ)
    (hx : ∀ κ ∈ K, rhoW ψ κ x = x) :
    x ∈ Submodule.span ℂ {y | ∃ g ∈ D, Good ψ (K.map (MulAut.conj g).toMonoidHom) ∧
      y = rhoW ψ g⁻¹ (delta ψ (K.map (MulAut.conj g).toMonoidHom))} := by
  classical
  obtain ⟨-, -, C, hC, h3⟩ := x.2
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun d : D => (fun y => (d : GL (Fin m) k)⁻¹ * y) ⁻¹' K)
    (fun d => hKo.preimage (continuous_const.mul continuous_id)) fun c _ => by
      obtain ⟨d, hd, hdD⟩ := hD.inter_open_nonempty ((fun y => y⁻¹ * c) ⁻¹' K)
        (hKo.preimage (continuous_inv.mul continuous_const)) ⟨c, by simp⟩
      exact Set.mem_iUnion.2 ⟨⟨d, hdD⟩, hd⟩
  refine mem_span_delta_of_cover hKo hKc D (t.image Subtype.val) (fun g hg => ?_) x hx fun y hy => ?_
  · obtain ⟨d, -, rfl⟩ := Finset.mem_image.1 hg
    exact d.2
  · obtain ⟨u, hu, c, hc, rfl⟩ := h3 y hy
    obtain ⟨d, hd, hcd⟩ := Set.mem_iUnion₂.1 (ht hc)
    exact ⟨d, Finset.mem_image_of_mem _ hd, u, hu, _, hcd, by simp [mul_assoc]⟩

theorem mem_span_delta {K : Subgroup (GL (Fin m) k)} (hKo : IsOpen (K : Set (GL (Fin m) k)))
    (hKc : IsCompact (K : Set (GL (Fin m) k))) (x : WT (m := m) ψ) (hx : ∀ κ ∈ K, rhoW ψ κ x = x) :
    x ∈ Submodule.span ℂ {y | ∃ g, Good ψ (K.map (MulAut.conj g).toMonoidHom) ∧
      y = rhoW ψ g⁻¹ (delta ψ (K.map (MulAut.conj g).toMonoidHom))} :=
  Submodule.span_mono (by rintro _ ⟨g, -, h⟩; exact ⟨g, h⟩) (mem_span_delta_of_dense hKo hKc dense_univ x hx)

theorem exists_countable_span : ∃ s : Set (WT (m := m) ψ), s.Countable ∧ Submodule.span ℂ s = ⊤ := by
  have : SecondCountableTopology (GL (Fin m) k) := GlobalTheory.LocGL.secondCountableTopology_GL k _
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (GL (Fin m) k)
  refine ⟨⋃ r : ℕ, (fun g => rhoW ψ g⁻¹ (delta ψ ((congruenceSubgroup k m r).map (MulAut.conj g).toMonoidHom))) '' D,
    Set.countable_iUnion fun r => hDc.image _, eq_top_iff.2 fun x _ => ?_⟩
  obtain ⟨r, hr⟩ := exists_fix_congruence x
  refine Submodule.span_mono ?_ (mem_span_delta_of_dense (isOpen_congruenceSubgroup k m r)
    (isCompact_congruenceSubgroup k m r) hDd x hr)
  rintro _ ⟨g, hg, -, rfl⟩
  exact Set.mem_iUnion.2 ⟨r, g, hg, rfl⟩

theorem isTestFun_mul (x : WT (m := m) ψ) (W : GL (Fin m) k → ℂ)
    (hW : ∀ u ∈ unipB k (Fin m), ∀ g, W (u * g) = (ψ⁻¹ (superDiag u) : ℂ) * W g) (hlc : IsLocallyConstant W) :
    IsTestFun fun g => (x : GL (Fin m) k → ℂ) g * W g := by
  obtain ⟨h1, h2, C, hC, h3⟩ := x.2
  refine ⟨fun u hu g => ?_, h2.mul hlc, C, hC, fun g hg => h3 g (left_ne_zero_of_mul hg)⟩
  have hpp : (ψ (superDiag u) : ℂ) * ((ψ⁻¹ : AddChar k Circle) (superDiag u) : ℂ) = 1 := by
    rw [AddChar.inv_apply', Circle.coe_inv]
    exact mul_inv_cancel₀ (Circle.coe_ne_zero _)
  beta_reduce
  rw [h1 u hu, hW u hu]
  linear_combination ((x : GL (Fin m) k → ℂ) g * W g) * hpp

end DiscreteGroups.sglob.LConv

end
