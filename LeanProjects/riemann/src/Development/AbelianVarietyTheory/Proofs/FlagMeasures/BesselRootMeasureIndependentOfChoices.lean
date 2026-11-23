import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RootMeasureTransportDoubleCoset
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction

noncomputable section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp.RootMove
open scoped ENNReal

namespace GlobalTheory.SnMass.RootUniq

theorem blockIdx_mono : ∀ (bs : List (ℂ × ℕ)) (i j : ℕ), i ≤ j → blockIdx bs i ≤ blockIdx bs j
  | [], _, _, _ => le_rfl
  | (_, s) :: bs, i, j, h => by
    have := blockIdx_mono bs (i - s) (j - s) (by omega)
    simp only [blockIdx]
    split_ifs <;> omega

theorem ptEntry_symm : ∀ (bs : List (ℂ × ℕ)) (i j : ℕ), ptEntry bs i j = ptEntry bs j i
  | [], _, _ => rfl
  | (t, s) :: bs, i, j => by
    simp only [ptEntry]
    rw [ptEntry_symm bs (i - s) (j - s), add_comm i j]
    simp only [and_comm]

theorem ptEntry_row : ∀ (bs : List (ℂ × ℕ)), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) → ∀ i, i < (bs.map Prod.snd).sum →
    ∃ j, j < (bs.map Prod.snd).sum ∧ blockIdx bs j = blockIdx bs i ∧ ptEntry bs i j ≠ 0 ∧
      ∀ j', j' ≠ j → ptEntry bs i j' = 0
  | [], _, i, hi => by simp at hi
  | (t, s) :: bs, h, i, hi => by
    have ht : t ≠ 0 := (h (t, s) (by simp)).1
    simp only [List.map_cons, List.sum_cons] at hi ⊢
    by_cases his : i < s
    · refine ⟨s - 1 - i, by omega, ?_, ?_, ?_⟩
      · simp only [blockIdx]
        rw [if_pos (by omega), if_pos his]
      · simp only [ptEntry]
        rw [if_pos (by omega), if_pos (by omega)]
        exact ht
      · intro j' hj'
        simp only [ptEntry]
        split_ifs <;> first | rfl | omega
    · obtain ⟨j, h1, h2, h3, h4⟩ := ptEntry_row bs (fun b hb => h b (by simp [hb])) (i - s) (by omega)
      refine ⟨j + s, by omega, ?_, ?_, ?_⟩
      · simp only [blockIdx]
        rw [if_neg (by omega), if_neg his, Nat.add_sub_cancel, h2]
      · simp only [ptEntry]
        rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel]
        exact h3
      · intro j' hj'
        simp only [ptEntry]
        rw [if_neg (by omega)]
        split_ifs with hh
        · exact h4 _ (by omega)
        · rfl

theorem ptEntry_inj : ∀ (bs bs' : List (ℂ × ℕ)), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) → (∀ b ∈ bs', b.1 ≠ 0 ∧ 1 ≤ b.2) →
    (bs.map Prod.snd).sum = (bs'.map Prod.snd).sum →
    (∀ i j, i < (bs.map Prod.snd).sum → j < (bs.map Prod.snd).sum → ptEntry bs i j = ptEntry bs' i j) → bs = bs'
  | [], [], _, _, _, _ => rfl
  | [], (t, s) :: _, _, h', e, _ => by
    have := (h' (t, s) (by simp)).2
    simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil] at e
    omega
  | (t, s) :: _, [], h, _, e, _ => by
    have := (h (t, s) (by simp)).2
    simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil] at e
    omega
  | (t, s) :: bs, (t', s') :: bs', h, h', e, H => by
    obtain ⟨ht, hs⟩ : t ≠ 0 ∧ 1 ≤ s := h (t, s) (by simp)
    obtain ⟨ht', hs'⟩ : t' ≠ 0 ∧ 1 ≤ s' := h' (t', s') (by simp)
    simp only [List.map_cons, List.sum_cons] at e H
    have h0 := H 0 (s - 1) (by omega) (by omega)
    simp only [ptEntry] at h0
    rw [if_pos (by omega), if_pos (by omega)] at h0
    have hss : s = s' := by
      by_contra hne
      apply ht
      rw [h0]
      split_ifs <;> first | rfl | omega
    subst hss
    rw [if_pos (by omega), if_pos (by omega)] at h0
    subst h0
    congr 1
    refine ptEntry_inj bs bs' (fun b hb => h b (by simp [hb])) (fun b hb => h' b (by simp [hb])) (by omega) ?_
    intro i j hi hj
    have h1 := H (i + s) (j + s) (by omega) (by omega)
    simp only [ptEntry] at h1
    rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega)] at h1
    simpa using h1

theorem ptMat_inj {m : ℕ} {p p' : Point ℂ m} (h : ptMat p = ptMat p') : p = p' := by
  refine Subtype.ext (ptEntry_inj _ _ p.2.1 p'.2.1 (p.2.2.trans p'.2.2.symm) fun i j hi hj => ?_)
  rw [p.2.2] at hi hj
  exact congrFun (congrFun h ⟨i, hi⟩) ⟨j, hj⟩

theorem pt_perm {m : ℕ} (p : Point ℂ m) : ∃ σ : Fin m → Fin m, (∀ a, σ (σ a) = a) ∧
    (∀ a, blockIdx p.1 (σ a).val = blockIdx p.1 a.val) ∧ (∀ a, ptMat p a (σ a) ≠ 0) ∧
    (∀ a b, b ≠ σ a → ptMat p a b = 0) ∧
    (∀ (U : Matrix (Fin m) (Fin m) ℂ) a d, (ptMat p * U) a d = ptMat p a (σ a) * U (σ a) d) ∧
    (∀ (L : Matrix (Fin m) (Fin m) ℂ) a d, (L * ptMat p) a d = L a (σ d) * ptMat p d (σ d)) := by
  have := fun a : Fin m => ptEntry_row p.1 p.2.1 a.val (by rw [p.2.2]; exact a.2)
  choose f h1 h2 h3 h4 using this
  let σ : Fin m → Fin m := fun a => ⟨f a, by have := h1 a; rwa [p.2.2] at this⟩
  have h0 : ∀ a b, b ≠ σ a → ptMat p a b = 0 := fun a b hb => h4 a b.val fun e => hb (Fin.ext e)
  have hs : ∀ a b, ptMat p a b = ptMat p b a := fun a b => ptEntry_symm _ _ _
  refine ⟨σ, fun a => ?_, h2, h3, h0, fun U a d => ?_, fun L a d => ?_⟩
  · by_contra hne
    exact h3 a ((hs a (σ a)).trans (h0 _ _ (Ne.symm hne)))
  · rw [Matrix.mul_apply, Finset.sum_eq_single (σ a) (fun b _ hb => by rw [h0 a b hb, zero_mul]) (by simp)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (σ d) (fun b _ hb => by rw [hs, h0 d b hb, mul_zero]) (by simp), hs]

theorem ptMat_cancel {m : ℕ} (p : Point ℂ m) {L L' : Matrix (Fin m) (Fin m) ℂ} (h : L * ptMat p = L' * ptMat p) :
    L = L' := by
  obtain ⟨σ, h1, -, h3, -, -, h6⟩ := pt_perm p
  ext a b
  have := congrFun (congrFun h a) (σ b)
  rw [h6, h6, h1] at this
  exact mul_right_cancel₀ (by have := h3 (σ b); rwa [h1] at this) this

theorem bruhat {m : ℕ} (p p' : Point ℂ m) (L U : Matrix (Fin m) (Fin m) ℂ) (hU : ∀ a, U a a = 1)
    (hL0 : ∀ a b, a < b → L a b = 0) (hL1 : ∀ a, L a a = 1) (h : ptMat p * U = L * ptMat p') :
    p = p' ∧ ∀ c d : Fin m, blockIdx p.1 c.val < blockIdx p.1 d.val → U c d = 0 := by
  obtain ⟨σ, h1, h2, h3, h4, h5, -⟩ := pt_perm p
  obtain ⟨τ, k1, -, k3, k4, -, k6⟩ := pt_perm p'
  have e : ∀ a d, ptMat p a (σ a) * U (σ a) d = L a (τ d) * ptMat p' d (τ d) := fun a d => by
    rw [← h5, ← k6, h]
  have hle : ∀ a, (τ (σ a)).val ≤ a.val := fun a => by
    by_contra hlt
    have := e a (σ a)
    rw [hU, mul_one, hL0 _ _ (Fin.lt_def.2 (by omega)), zero_mul] at this
    exact h3 a this
  have hb : Function.Bijective fun a => τ (σ a) :=
    (Function.Involutive.bijective k1).comp (Function.Involutive.bijective h1)
  have hs : ∑ a, (τ (σ a)).val = ∑ a : Fin m, a.val := hb.sum_comp fun a => a.val
  have heq := (Finset.sum_eq_sum_iff_of_le (fun a _ => hle a)).1 hs
  have hτ : ∀ a, τ (σ a) = a := fun a => Fin.ext (heq a (Finset.mem_univ a))
  have hστ : ∀ a, τ a = σ a := fun a => by rw [← hτ (σ a), h1]
  refine ⟨ptMat_inj ?_, fun c d hcd => ?_⟩
  · ext a b
    by_cases hb : b = σ a
    · have := e a (σ a)
      rw [hU, mul_one, hτ, hL1, one_mul] at this
      rw [hb, this]
      exact ptEntry_symm _ _ _
    · rw [h4 a b hb, k4 a b (by rwa [hστ])]
  · have := e (σ c) d
    have hlt : σ c < τ d := by
      rw [hστ, Fin.lt_def]
      by_contra hh
      have := blockIdx_mono p.1 (σ d).val (σ c).val (by omega)
      rw [h2, h2] at this
      omega
    rw [hL0 _ _ hlt, zero_mul, h1] at this
    exact (mul_eq_zero.1 this).resolve_left (by have := h3 (σ c); rwa [h1] at this)

def Up {m : ℕ} (U : Matrix (Fin m) (Fin m) ℂ) : Prop := (∀ c a, a < c → U c a = 0) ∧ ∀ c, U c c = 1

theorem mem_rootPat {r : ℕ} (p : Point ℂ (r + 1)) (q : Fin (r + 1) × Fin (r + 1)) :
    q ∈ rootPat p ↔ q.1 < q.2 ∧ blockIdx p.1 q.1.val = blockIdx p.1 q.2.val := by
  simp [rootPat]

theorem exists_mp {r : ℕ} (p : Point ℂ (r + 1)) {u v : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hu : Up u) (hv : Up v) :
    ∃ T : (rootPat p → ℂ) → (rootPat p → ℂ), MeasurePreserving T volume volume ∧
      ∀ X, Up X → (fun q : rootPat p => (u * X * v) q.1.1 q.1.2) = T fun q => X q.1.1 q.1.2 := by
  let M : Matrix (rootPat p) (rootPat p) ℂ := fun q q' => u q.1.1 q'.1.1 * v q'.1.2 q.1.2
  have hdet : M.det = 1 := by
    let key : rootPat p → ℕ ×ₗ ℕ := fun q => toLex (q.1.1.val, r + 1 - q.1.2.val)
    have hk : Function.Injective key := by
      intro a b hab
      have := toLex.injective hab
      simp only [Prod.mk.injEq] at this
      have h1 := a.1.2.2
      have h2 := b.1.2.2
      exact Subtype.ext (Prod.ext (Fin.ext this.1) (Fin.ext (by omega)))
    rw [@Matrix.det_of_isUpperTriangular _ _ M _ _ _ (LinearOrder.lift' key hk) ?_]
    · exact Finset.prod_eq_one fun q _ => by simp only [M, hu.2, hv.2, mul_one]
    · intro i j hij
      have hij' : key j < key i := hij
      rcases Prod.Lex.toLex_lt_toLex.1 hij' with h | h
      · simp only [M]
        rw [hu.1 _ _ (Fin.lt_def.2 h), zero_mul]
      · simp only [M]
        rw [hv.1 _ _ (Fin.lt_def.2 (by have := h.2; simp only at this; omega)), mul_zero]
  have hlin : MeasurePreserving (fun y : rootPat p → ℂ => M *ᵥ y) volume volume := by
    let f : (rootPat p → ℂ) →ₗ[ℝ] (rootPat p → ℂ) := (Matrix.toLin' M).restrictScalars ℝ
    have hf : LinearMap.det f = 1 := by
      rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', hdet, map_one]
    refine ⟨f.continuous_of_finiteDimensional.measurable, ?_⟩
    have := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (rootPat p → ℂ)) (f := f) (by rw [hf]; simp)
    rw [hf] at this
    have h3 : Measure.map (fun y : rootPat p → ℂ => M *ᵥ y) volume = ENNReal.ofReal |(1 : ℝ)⁻¹| • volume := this
    simpa using h3
  refine ⟨fun y => (fun q : rootPat p => (u * v) q.1.1 q.1.2) + M *ᵥ y,
    (measurePreserving_add_left volume _).comp hlin, fun X hX => ?_⟩
  funext q
  have e : u * X * v = u * v + u * (X - 1) * v := by noncomm_ring
  rw [e, Matrix.add_apply]
  change _ = (u * v) q.1.1 q.1.2 + ∑ c : rootPat p, M q c * X c.1.1 c.1.2
  congr 1
  have hq := (mem_rootPat p q.1).1 q.2
  have e2 : (u * (X - 1) * v) q.1.1 q.1.2 =
      ∑ c : Fin (r + 1) × Fin (r + 1), u q.1.1 c.1 * v c.2 q.1.2 * (X - 1) c.1 c.2 := by
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e2, ← Finset.sum_subset (Finset.subset_univ (rootPat p)), ← Finset.sum_coe_sort]
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.sub_apply, Matrix.one_apply_ne ((mem_rootPat p c.1).1 c.2).1.ne, sub_zero]
  · intro c _ hc
    rw [mem_rootPat] at hc
    by_cases h1 : c.1 < q.1.1
    · rw [hu.1 _ _ h1]; ring
    by_cases h2 : q.1.2 < c.2
    · rw [hv.1 _ _ h2]; ring
    rcases lt_trichotomy c.1 c.2 with h | h | h
    · exfalso
      refine hc ⟨h, ?_⟩
      have a1 := blockIdx_mono p.1 _ _ (Fin.le_def.1 (not_lt.1 h1))
      have a2 := blockIdx_mono p.1 _ _ (Fin.le_def.1 (not_lt.1 h2))
      have a3 := blockIdx_mono p.1 _ _ (Fin.le_def.1 h.le)
      omega
    · rw [h, Matrix.sub_apply, hX.2, Matrix.one_apply_eq]; ring
    · rw [Matrix.sub_apply, hX.1 _ _ h, Matrix.one_apply_ne h.ne']; ring

theorem eq_of_map_eq {α β : Type} [TopologicalSpace α] [PolishSpace α] [MeasurableSpace α] [BorelSpace α]
    [TopologicalSpace β] [T2Space β] [MeasurableSpace β] [BorelSpace β] {S : Set α} (hS : MeasurableSet S)
    {f : α → β} (hf : Continuous f) (hi : Set.InjOn f S) {μ ν : Measure α} (hμ : μ Sᶜ = 0) (hν : ν Sᶜ = 0)
    (h : μ.map f = ν.map f) : μ = ν := by
  have hE := hf.continuousOn.measurableEmbedding hS hi
  have key : ∀ μ : Measure α, μ Sᶜ = 0 → (μ.comap (Subtype.val : S → α)).map Subtype.val = μ := fun μ hμ => by
    rw [map_comap_subtype_coe hS, Measure.restrict_eq_self_of_ae_mem hμ]
  rw [← key μ hμ, ← key ν hν] at h ⊢
  rw [Measure.map_map hf.measurable measurable_subtype_coe, Measure.map_map hf.measurable measurable_subtype_coe] at h
  rw [hE.map_injective h]

variable {k r : ℕ}

theorem up_Uof (z : Fin (2 * r + k + 1) → ℂ) {m : Mat k r} (hm : m ∈ Nset k r) : Up (Uof k r z m) :=
  ⟨Uof_lower_zero hm, Uof_diag hm⟩

theorem F_row {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {ι : Type} (U : Matrix (Fin (r + 1)) ι ℂ)
    (i : Fin (2 * r + k + 1)) (hi : i.val < r) (j : ι) : (Fm k r z * U) i j = U ⟨i.val, by omega⟩ j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨i.val, by omega⟩ : Fin (r + 1))]
  · simp only [Fm, Matrix.of_apply]
    rw [fvec_apply_lt z hz _ i hi, if_pos rfl, one_mul]
  · intro c _ hc
    simp only [Fm, Matrix.of_apply]
    rw [fvec_apply_lt z hz _ i hi, if_neg (fun h => hc (Fin.ext h)), zero_mul]
  · simp

theorem besselUnipotent_matrix_mul_three {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {a x b : Mat k r} (ha : a ∈ Nset k r)
    (hx : x ∈ Nset k r) (hb : b ∈ Nset k r) (c d : Fin (r + 1)) (hc : c < d) :
    Uof k r z (a * x * b) c d = (Uof k r z a * Uof k r z x * Uof k r z b) c d := by
  have hc' : c.val < r := by have := d.2; have := Fin.lt_def.1 hc; omega
  have e : a * x * b * Fm k r z = Fm k r z * (Uof k r z a * Uof k r z x * Uof k r z b) := by
    rw [Matrix.mul_assoc, N_F hz hb, ← Matrix.mul_assoc, Matrix.mul_assoc a, N_F hz hx, ← Matrix.mul_assoc,
      N_F hz ha]
    simp only [Matrix.mul_assoc]
  conv_lhs => unfold Uof
  rw [dif_pos hc', e, F_row hz _ _ hc']
  rfl

theorem continuous_rootCoords (z : Fin (2 * r + k + 1) → ℂ) (p : Point ℂ (r + 1)) :
    Continuous (rootCoords k r z p) := by
  refine continuous_pi fun q => ?_
  unfold rootCoords flagMat
  split_ifs
  · unfold Matrix.mulVec dotProduct
    simp only [Matrix.of_apply]
    fun_prop
  all_goals exact continuous_const

theorem map_lr {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (p : Point ℂ (r + 1)) {g a b : Mat k r}
    (ha : a ∈ Nset k r) (hb : b ∈ Nset k r) {μ : Measure (Mt k r)} {c : ℝ≥0∞}
    (h0 : μ {x | Matrix.of x ∉ Rset k r g} = 0) (h1 : μ.map (rootCoords k r z p) = c • volume) :
    (μ.map (lr a b)).map (rootCoords k r z p) = c • volume := by
  obtain ⟨T, hT, hX⟩ := exists_mp p (up_Uof z ha) (up_Uof z hb)
  have hae : rootCoords k r z p ∘ lr a b =ᵐ[μ] T ∘ rootCoords k r z p := by
    refine measure_mono_null (fun x hx => show Matrix.of x ∉ Rset k r g from fun hx' => hx ?_) h0
    refine Eq.trans ?_ (hX _ (up_Uof z hx'.1))
    funext q
    exact besselUnipotent_matrix_mul_three hz ha hx'.1 hb _ _ ((mem_rootPat p q.1).1 q.2).1
  rw [Measure.map_map (measurable_rootCoords z p) (continuous_lr a b).measurable, Measure.map_congr hae,
    ← Measure.map_map hT.measurable (measurable_rootCoords z p), h1, Measure.map_smul, hT.map_eq]

def Sg (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.diagonal fun b => (-1 : ℂ) ^ (r - b.val)

theorem sign_sq (n : ℕ) : (-1 : ℂ) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; simp

theorem Sg_sq : Sg r * Sg r = 1 := by
  rw [Sg, Matrix.diagonal_mul_diagonal]
  simp only [sign_sq, Matrix.diagonal_one]

theorem zhatO_eq (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) : ZhatO k r z z' g = Zhat k r z z' g * Sg r := by
  ext a b
  rw [Sg, Matrix.mul_diagonal, mul_comm]
  rfl

theorem zhat_move {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') {a b : Mat k r}
    (ha : a ∈ Nset k r) (hb : b ∈ Nset k r) (g : Mat k r) :
    (Uof k r z a)ᴴ * Zhat k r z z' (a * g * b) = Zhat k r z z' g * Uof k r z' b := by
  have hU : aᴴ * Hpk k r * a = Hpk k r := ha.1
  rw [Zhat_eq, Zhat_eq]
  calc (Uof k r z a)ᴴ * ((Fm k r z)ᴴ * Hpk k r * (a * g * b) * Fm k r z')
      = (Fm k r z * Uof k r z a)ᴴ * Hpk k r * a * g * (b * Fm k r z') := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = (a * Fm k r z)ᴴ * Hpk k r * a * g * (Fm k r z' * Uof k r z' b) := by rw [N_F hz ha, N_F hz' hb]
    _ = (Fm k r z)ᴴ * (aᴴ * Hpk k r * a) * g * Fm k r z' * Uof k r z' b := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = (Fm k r z)ᴴ * Hpk k r * g * Fm k r z' * Uof k r z' b := by rw [hU]

theorem pt_move {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') {a b g : Mat k r}
    (ha : a ∈ Nset k r) (hb : b ∈ Nset k r) {p p' : Point ℂ (r + 1)} (hp : ZhatO k r z z' g = ptMat p)
    (hp' : ZhatO k r z z' (a * g * b) = ptMat p') :
    p = p' ∧ ∀ c d : Fin (r + 1), blockIdx p.1 c.val < blockIdx p.1 d.val → Uof k r z' b c d = 0 := by
  have e : ∀ c d, (Sg r * Uof k r z' b * Sg r) c d = (-1) ^ (r - c.val) * Uof k r z' b c d * (-1) ^ (r - d.val) :=
    fun c d => by rw [Sg, Matrix.mul_diagonal, Matrix.diagonal_mul]
  obtain ⟨h1, h2⟩ := bruhat p p' (Uof k r z a)ᴴ (Sg r * Uof k r z' b * Sg r)
    (fun c => by rw [e, Uof_diag hb, mul_one, sign_sq])
    (fun c d h => by rw [conjTranspose_apply, Uof_lower_zero ha _ _ h, star_zero])
    (fun c => by rw [conjTranspose_apply, Uof_diag ha, star_one])
    (by
      rw [← hp, ← hp', zhatO_eq, zhatO_eq, ← Matrix.mul_assoc (Uof k r z a)ᴴ, zhat_move hz hz' ha hb]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (Sg r) (Sg r), Sg_sq, Matrix.one_mul])
  refine ⟨h1, fun c d h => ?_⟩
  have := h2 c d h
  rw [e] at this
  simpa using this

theorem FH_row (z : Fin (2 * r + k + 1) → ℂ) (Q : Mat k r) (a : Fin r) (j : Fin (2 * r + k + 1)) :
    ((Fm k r z)ᴴ * Hpk k r * Q) a.castSucc j = Q (esI k r a) j := by
  have ha := a.2
  have e : ∀ i, ((Fm k r z)ᴴ * Hpk k r) a.castSucc i = if i = esI k r a then 1 else 0 := fun i => by
    have : ((Fm k r z)ᴴ * Hpk k r) a.castSucc i = Hpk k r (eI k r a) i := by
      simp [Matrix.mul_apply, Fm, fvec, bvec, Pi.single_apply]
    rw [this]
    unfold Hpk eI esI
    simp only [Fin.ext_iff]
    split_ifs <;> first | rfl | omega
  rw [Matrix.mul_apply]
  simp [e]

theorem eq_one_of_fix {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') {g c : Mat k r}
    (hg : g ∈ GG k r) (hG : Gf k r z z' g ≠ 0) (hc : c ∈ Nset k r) (h1 : c * Fm k r z = Fm k r z)
    (h2 : c * (g * Fm k r z') = g * Fm k r z') : c = 1 := by
  set A := Matrix.fromCols (Fm k r z) (g * Fm k r z') with hA
  have hgram : gramM k r z z' g = Aᴴ * Hpk k r * A := by
    have hv : ∀ j, gramVec k r z z' g j = fun i => A i j := by
      rintro (j | j) <;> rfl
    ext i j
    unfold gramM herm
    rw [hv, hv, Matrix.mul_assoc]
    rfl
  have hdet : IsUnit (Aᴴ * Hpk k r * A).det := by
    rw [← hgram]
    refine Ne.isUnit fun h => hG ?_
    have := gGram k r z z' hz hz' g hg
    rw [h, mul_zero] at this
    exact_mod_cast this
  have hcA : c * A = A := by rw [hA, Matrix.mul_fromCols, h1, h2]
  have hcU : cᴴ * Hpk k r * c = Hpk k r := hc.1
  have h3 : Aᴴ * Hpk k r * (c - 1) = 0 := by
    have : Aᴴ * Hpk k r * c = Aᴴ * Hpk k r := by
      calc Aᴴ * Hpk k r * c = (c * A)ᴴ * Hpk k r * c := by rw [hcA]
        _ = Aᴴ * (cᴴ * Hpk k r * c) := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [hcU]
    rw [Matrix.mul_sub, this, Matrix.mul_one, sub_self]
  set Q : Mat k r := 1 - A * ((Aᴴ * Hpk k r * A)⁻¹ * (Aᴴ * Hpk k r)) with hQ
  have h4 : Aᴴ * Hpk k r * Q = 0 := by
    rw [hQ, Matrix.mul_sub, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hdet, Matrix.mul_one, sub_self]
  have h5 : (c - 1) * Q = c - 1 := by
    rw [hQ, Matrix.mul_sub, ← Matrix.mul_assoc, Matrix.sub_mul c 1 A, hcA]
    simp
  have h6 : ∀ i j, r + k < i.val → Q i j = 0 := fun i j hi => by
    have hi2 := i.2
    have := congrFun (congrFun h4 (Sum.inl (Fin.castSucc ⟨2 * r + k - i.val, by omega⟩))) j
    rw [hA, conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul, Matrix.fromRows_mul,
      Matrix.fromRows_apply_inl, FH_row] at this
    rw [← show esI k r ⟨2 * r + k - i.val, by omega⟩ = i from Fin.ext (by simp only [esI]; omega)]
    exact this
  have h7 : ∀ i j, r ≤ i.val → (c - 1) i j = 0 := fun i j hi => by
    rw [← h5, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : r + k < l.val
    · rw [h6 l j hl, mul_zero]
    · have : (c - 1) i l = 0 := by
        rw [Matrix.sub_apply, Matrix.one_apply, sub_eq_zero]
        by_cases hl2 : l.val < r
        · exact hc.2.1 ⟨l.val, hl2⟩ i (by simp only; omega)
        · exact hc.2.2 i l (by omega) (by omega) hi
      rw [this, zero_mul]
  let T : Matrix (Fin (r + 1)) (Fin (2 * r + k + 1)) ℂ := Matrix.of fun a j =>
    if h : a.val < r then (c - 1) (eI k r ⟨a.val, h⟩) j else 0
  have h8 : c - 1 = A * Matrix.fromRows T (0 : Matrix (Fin (r + 1)) (Fin (2 * r + k + 1)) ℂ) := by
    rw [hA, Matrix.fromCols_mul_fromRows, Matrix.mul_zero, add_zero]
    ext i j
    by_cases hi : i.val < r
    · rw [F_row hz _ _ hi]
      simp only [T, Matrix.of_apply, dif_pos hi]
      rfl
    · rw [h7 i j (by omega), Matrix.mul_apply]
      refine (Finset.sum_eq_zero fun l _ => ?_).symm
      simp only [Fm, Matrix.of_apply]
      rw [fvec_apply_ge z _ i (by omega)]
      split_ifs with hl
      · simp only [T, Matrix.of_apply]
        rw [dif_neg (by omega), mul_zero]
      · rw [zero_mul]
  rw [h8, ← Matrix.mul_assoc] at h3
  have h9 : Matrix.fromRows T (0 : Matrix (Fin (r + 1)) (Fin (2 * r + k + 1)) ℂ) = 0 := by
    rw [← Matrix.nonsing_inv_mul_cancel_left _ (Matrix.fromRows T 0) hdet, h3, Matrix.mul_zero]
  rw [h9, Matrix.mul_zero, sub_eq_zero] at h8
  exact h8

theorem injOn_rootCoords {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') {g : Mat k r}
    (hg : g ∈ GG k r) (hG : Gf k r z z' g ≠ 0) {p : Point ℂ (r + 1)} (hp : ZhatO k r z z' g = ptMat p) :
    Set.InjOn (rootCoords k r z' p) {x : Mt k r | Matrix.of x ∈ Rset k r g} := by
  have N := nSubgroup k r
  have hu := unit_det hg
  have blk : ∀ x ∈ Rset k r g, ∀ c d : Fin (r + 1), blockIdx p.1 c.val < blockIdx p.1 d.val → Uof k r z' x c d = 0 := by
    intro x hx
    refine (pt_move hz hz' (N.2.2 _ hx.2) hx.1 hp (p' := p) ?_).2
    have : (g * x * g⁻¹)⁻¹ * g * x = g := by
      simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.mul_assoc,
        Matrix.nonsing_inv_mul_cancel_left _ _ hu, Matrix.nonsing_inv_mul _ (unit_det hx.1.1), Matrix.mul_one]
    rw [this, hp]
  intro x hx y hy hxy
  change Matrix.of x ∈ Rset k r g at hx
  change Matrix.of y ∈ Rset k r g at hy
  have hU : Uof k r z' (Matrix.of x) = Uof k r z' (Matrix.of y) := by
    ext c d
    rcases lt_trichotomy c d with h | h | h
    · by_cases hb : blockIdx p.1 c.val = blockIdx p.1 d.val
      · exact congrFun hxy ⟨(c, d), (mem_rootPat p _).2 ⟨h, hb⟩⟩
      · have := lt_of_le_of_ne (blockIdx_mono p.1 _ _ (Fin.le_def.1 h.le)) hb
        rw [blk _ hx _ _ this, blk _ hy _ _ this]
    · rw [h, Uof_diag hx.1, Uof_diag hy.1]
    · rw [Uof_lower_zero hx.1 _ _ h, Uof_lower_zero hy.1 _ _ h]
  suffices h : Matrix.of x = Matrix.of y from h
  generalize Matrix.of x = X at *
  generalize Matrix.of y = Y at *
  have huy := unit_det hy.1.1
  have hc : (g * Y * g⁻¹)⁻¹ * (g * X * g⁻¹) ∈ Nset k r := N.2.1 _ (N.2.2 _ hy.2) _ hx.2
  have e : (g * Y * g⁻¹)⁻¹ * (g * X * g⁻¹) = g * (Y⁻¹ * X) * g⁻¹ := by
    simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul_cancel_left _ _ hu]
  rw [e] at hc
  have h2 : g * (Y⁻¹ * X) * g⁻¹ * (g * Fm k r z') = g * Fm k r z' := by
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu]
    rw [N_F hz' hx.1, hU, ← N_F hz' hy.1, Matrix.nonsing_inv_mul_cancel_left _ _ huy]
  have h3 := zhat_move hz hz' hc N.1 g
  have h4 : Zhat k r z z' (g * (Y⁻¹ * X) * g⁻¹ * g * 1) = Zhat k r z z' g := by
    rw [Zhat_eq, Zhat_eq, Matrix.mul_one, Matrix.mul_assoc _ _ (Fm k r z'), Matrix.mul_assoc _ g (Fm k r z'), h2,
      Matrix.mul_assoc _ g (Fm k r z')]
  have h5 : Zhat k r z z' g * Uof k r z' 1 = Zhat k r z z' g := by
    rw [Zhat_eq, Matrix.mul_assoc _ (Fm k r z'), ← N_F hz' N.1, Matrix.one_mul]
  rw [h4, h5] at h3
  have h6 : (Uof k r z (g * (Y⁻¹ * X) * g⁻¹))ᴴ = 1 := by
    refine ptMat_cancel p ?_
    rw [← hp, zhatO_eq, ← Matrix.mul_assoc, h3, Matrix.one_mul]
  have h7 := eq_one_of_fix hz hz' hg hG hc
    (by rw [N_F hz hc, conjTranspose_eq_one.1 h6, Matrix.mul_one]) h2
  have h8 : X = Y * (g⁻¹ * (g * (Y⁻¹ * X) * g⁻¹) * g) := by
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu, Matrix.nonsing_inv_mul _ hu,
      Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ huy]
  rw [h8, h7, Matrix.mul_one, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

theorem conj_mem' {P Q g x : Mat k r} (hP : P ∈ Nset k r) (hQ : Q ∈ Nset k r) (hx : x ∈ Rset k r g) :
    P⁻¹ * x * P ∈ Rset k r (Q * g * P) := by
  have N := nSubgroup k r
  refine ⟨N.2.1 _ (N.2.1 _ (N.2.2 _ hP) _ hx.1) _ hP, ?_⟩
  have e : Q * g * P * (P⁻¹ * x * P) * (Q * g * P)⁻¹ = Q * (g * x * g⁻¹) * Q⁻¹ := by
    have hu := unit_det hP.1
    simp only [Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  rw [e]
  exact N.2.1 _ (N.2.1 _ hQ _ hx.2) _ (N.2.2 _ hQ)

theorem conc_conj {P Q g : Mat k r} (hP : P ∈ Nset k r) (hQ : Q ∈ Nset k r) {μ : Measure (Mt k r)}
    (h0 : μ {x | Matrix.of x ∉ Rset k r g} = 0) :
    (μ.map (lr P⁻¹ P)) {x | Matrix.of x ∉ Rset k r (Q * g * P)} = 0 := by
  rw [Measure.map_apply (continuous_lr _ _).measurable (measurableSet_notR _)]
  exact measure_mono_null (fun x hx hx' => hx (conj_mem' hP hQ hx')) h0

theorem conc_lmul {g t : Mat k r} (hg : g ∈ GG k r) (ht : t ∈ Rset k r g) {μ : Measure (Mt k r)}
    (h0 : μ {x | Matrix.of x ∉ Rset k r g} = 0) : (μ.map (lr t 1)) {x | Matrix.of x ∉ Rset k r g} = 0 := by
  have N := nSubgroup k r
  have key : ∀ x ∈ Rset k r g, t * x * 1 ∈ Rset k r g := fun x hx => by
    rw [Matrix.mul_one]
    refine ⟨N.2.1 _ ht.1 _ hx.1, ?_⟩
    have := N.2.1 _ ht.2 _ hx.2
    simpa only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (unit_det hg)] using this
  rw [Measure.map_apply (continuous_lr _ _).measurable (measurableSet_notR _)]
  exact measure_mono_null (fun x hx hx' => hx (key _ hx')) h0

theorem map_lr_lr (μ : Measure (Mt k r)) (a b c d : Mat k r) :
    (μ.map (lr a b)).map (lr c d) = μ.map (lr (c * a) (b * d)) := by
  rw [Measure.map_map (continuous_lr _ _).measurable (continuous_lr _ _).measurable]
  congr 1
  funext x
  change c * (a * Matrix.of x * b) * d = c * a * Matrix.of x * (b * d)
  simp only [Matrix.mul_assoc]

theorem lmul_eq (s : Mat k r) : lmulM s = lr s 1 := by
  funext x
  change s * Matrix.of x = s * Matrix.of x * 1
  rw [Matrix.mul_one]

theorem lr_one : lr (1 : Mat k r) 1 = id := by
  funext x
  change 1 * Matrix.of x * 1 = Matrix.of x
  rw [Matrix.mul_one, Matrix.one_mul]

theorem uniq {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') {g : Mat k r}
    (hg : g ∈ GG k r) (hG : Gf k r z z' g ≠ 0) {p : Point ℂ (r + 1)} (hp : ZhatO k r z z' g = ptMat p)
    {μ ν : Measure (Mt k r)} (hμ : μ {x | Matrix.of x ∉ Rset k r g} = 0) (hν : ν {x | Matrix.of x ∉ Rset k r g} = 0)
    (h : μ.map (rootCoords k r z' p) = ν.map (rootCoords k r z' p)) : μ = ν :=
  eq_of_map_eq (S := {x : Mt k r | Matrix.of x ∈ Rset k r g}) (measurableSet_notR g).of_compl
    (continuous_rootCoords z' p) (injOn_rootCoords hz hz' hg hG hp) hμ hν h

theorem mem_S (z : Fin (2 * r + k + 1) → ℂ) {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, ⟨(uHGroup _ _ det_Hpk).1, fun a => by simp, by simp⟩, n, hn, by simp⟩

theorem good_of {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') {n n' g : Mat k r}
    (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) (hg : n * g * n' ∈ GG k r) (hG : Gf k r z z' (n * g * n') ≠ 0) :
    g ∈ GG k r ∧ Gf k r z z' g ≠ 0 := by
  refine ⟨?_, by rwa [gInv k r z z' hz hz' _ (mem_S z hn) _ (mem_S z' hn')] at hG⟩
  have G := uHGroup _ _ (det_Hpk (k := k) (r := r))
  have e : g = n⁻¹ * (n * g * n') * n'⁻¹ := by
    rw [Matrix.mul_assoc n, Matrix.nonsing_inv_mul_cancel_left _ _ (unit_det hn.1),
      Matrix.mul_nonsing_inv_cancel_right _ _ (unit_det hn'.1)]
  rw [e]
  exact G.2.1 _ (G.2.1 _ (G.2.2 _ hn.1).2 _ hg) _ (G.2.2 _ hn'.1).2

theorem rootMeas_unique : ∀ (D : Formalism.BasicNotions.D7) (z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (γ : Mat D.R.k D.R.rS) (p p' : Point ℂ (D.R.rS + 1)) (μ μ' : Measure (Mt D.R.k D.R.rS)), inWb D.R.k D.R.rS z → inWb D.R.k D.R.rS z' → 0 < Tz D.R.k D.R.rS z → 0 < Tz D.R.k D.R.rS z' → γ ∈ GG D.R.k D.R.rS → Gf D.R.k D.R.rS z z' γ ≠ 0 → 0 < D.host.ka → Formalism.MainNotions.S.IsRootMeasR D z z' p γ μ → Formalism.MainNotions.S.IsRootMeasR D z z' p' γ μ' → p = p' ∧ μ = μ' ∧ IsHaarOn (Rset D.R.k D.R.rS γ) μ := by
  intro D z z' γ p p' μ μ' hz hz' _ _ hγ hG hka hR hR'
  obtain ⟨m, hm, m', hm', g₁, e₁, hZ₁, μ₁, k0, k1, rfl⟩ := hR'
  obtain ⟨n, hn, n', hn', g₀, e₀, hZ₀, μ₀, h0, h1, rfl⟩ := hR
  have N := nSubgroup D.R.k D.R.rS
  obtain ⟨hg₁, hG₁⟩ := good_of hz hz' hm hm' (e₁ ▸ hγ) (e₁ ▸ hG)
  subst e₀
  obtain ⟨hg₀, hG₀⟩ := good_of hz hz' hn hn' hγ hG
  have um := unit_det hm.1
  have um' := unit_det hm'.1
  have un := unit_det hn.1
  have un' := unit_det hn'.1
  have ha := N.2.1 _ (N.2.2 _ hm) _ hn
  have hb := N.2.1 _ hn' _ (N.2.2 _ hm')
  have e : m⁻¹ * n * g₀ * (n' * m'⁻¹) = g₁ := by
    have : m⁻¹ * n * g₀ * (n' * m'⁻¹) = m⁻¹ * (n * g₀ * n') * m'⁻¹ := by simp only [Matrix.mul_assoc]
    rw [this, e₁, Matrix.mul_assoc m, Matrix.nonsing_inv_mul_cancel_left _ _ um,
      Matrix.mul_nonsing_inv_cancel_right _ _ um']
  obtain rfl : p = p' := (pt_move hz hz' ha hb hZ₀ (e.symm ▸ hZ₁)).1
  change _ ∧ μ₀.map (lr n'⁻¹ n') = μ₁.map (lr m'⁻¹ m') ∧ IsHaarOn _ (μ₀.map (lr n'⁻¹ n'))
  have back : (μ₀.map (lr n'⁻¹ n')).map (lr n' n'⁻¹) = μ₀ := by
    rw [map_lr_lr, Matrix.mul_nonsing_inv _ un', lr_one, Measure.map_id]
  refine ⟨rfl, ?_, ?_, ?_, conc_conj hn' hn h0, fun s hs => ?_⟩
  · have := uniq hz hz' hg₁ hG₁ hZ₁ (e ▸ conc_conj hb ha h0) k0
      ((map_lr hz' p (N.2.2 _ hb) hb h0 h1).trans k1.symm)
    rw [← this, map_lr_lr, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ um',
      Matrix.nonsing_inv_mul_cancel_left _ _ um', Matrix.nonsing_inv_mul_cancel_right _ _ um']
  · refine SigmaFinite.of_map _ (continuous_lr n' n'⁻¹).measurable.aemeasurable ?_
    rw [back]
    refine SigmaFinite.of_map _ (measurable_rootCoords z' p).aemeasurable ?_
    rw [h1]
    exact inferInstanceAs (SigmaFinite (Real.toNNReal _ • volume))
  · intro h
    rw [h, Measure.map_zero] at back
    rw [← back, Measure.map_zero] at h1
    have hg : 0 < gg D := mul_pos (by exact_mod_cast (D.host.g_prime 0).pos) (by exact_mod_cast (D.host.g_prime 1).pos)
    have := Real.pi_pos
    have h2 := congrArg (fun ν : Measure (rootPat p → ℂ) => ν Set.univ) h1
    simp only [Measure.smul_apply, smul_eq_mul, Measure.coe_zero, Pi.zero_apply] at h2
    rcases mul_eq_zero.1 h2.symm with h2 | h2
    · exact absurd h2 (ENNReal.ofReal_pos.2 (by positivity)).ne'
    · exact NeZero.ne _ (Measure.measure_univ_eq_zero.1 h2)
  · have hs' : n' * s * n'⁻¹ ∈ Rset _ _ g₀ := by
      have := conj_mem' (N.2.2 _ hn') (N.2.2 _ hn) hs
      rwa [Matrix.nonsing_inv_nonsing_inv _ un', Matrix.mul_assoc n, Matrix.nonsing_inv_mul_cancel_left _ _ un,
        Matrix.mul_nonsing_inv_cancel_right _ _ un'] at this
    have hinv : μ₀.map (lr (n' * s * n'⁻¹) 1) = μ₀ := by
      refine uniq hz hz' hg₀ hG₀ hZ₀ ?_ h0 ((map_lr hz' p hs'.1 N.1 h0 h1).trans h1.symm)
      exact conc_lmul hg₀ hs' h0
    conv_rhs => rw [← hinv]
    rw [lmul_eq, map_lr_lr, map_lr_lr, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc n',
      Matrix.nonsing_inv_mul_cancel_left _ _ un']

end GlobalTheory.SnMass.RootUniq
