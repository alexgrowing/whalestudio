import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeOfPerpEqBot

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.QRefl

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

theorem hf_add_left (x y z : Fin n → E) : hf L Hm (x + y) z = hf L Hm x z + hf L Hm y z := by
  simp [hf, add_mul, Finset.sum_add_distrib]

theorem hf_add_right (x y z : Fin n → E) : hf L Hm x (y + z) = hf L Hm x y + hf L Hm x z := by
  simp [hf, mul_add, Finset.sum_add_distrib]

theorem hf_smul_left (t : E) (x y : Fin n → E) : hf L Hm (t • x) y = t * hf L Hm x y := by
  simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_smul_right (t : E) (x y : Fin n → E) : hf L Hm x (t • y) = L.cj t * hf L Hm x y := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_zero_left (y : Fin n → E) : hf L Hm 0 y = 0 := by simp [hf]

theorem hf_zero_right (y : Fin n → E) : hf L Hm y 0 = 0 := by simp [hf]

theorem hf_sum_left {ι : Type} (s : Finset ι) (f : ι → Fin n → E) (y : Fin n → E) :
    hf L Hm (∑ i ∈ s, f i) y = ∑ i ∈ s, hf L Hm (f i) y := by
  induction s using Finset.induction_on with
  | empty => simp [hf_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hf_add_left, ih]

theorem hf_sum_right {ι : Type} (s : Finset ι) (f : ι → Fin n → E) (y : Fin n → E) :
    hf L Hm y (∑ i ∈ s, f i) = ∑ i ∈ s, hf L Hm y (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [hf_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hf_add_right, ih]

theorem cj_hf (hH : IsHerm L Hm) (x y : Fin n → E) : L.cj (hf L Hm x y) = hf L Hm y x := by
  have h : ∀ i j, L.cj (Hm i j) = Hm j i := fun i j => congrFun (congrFun hH j) i
  simp only [hf, map_sum, map_mul, L.cj_cj, h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem cj_mem_O {t : E} (ht : t ∈ L.O) : L.cj t ∈ L.O := by
  rw [L.O_def] at ht ⊢
  exact ht.map (L.cj.toAlgHom.restrictScalars 𝒪[F])

def conjLin (c : (Fin n → E) →+ (Fin n → E)) (hs : ∀ t v, c (t • v) = L.cj t • c v)
    (hc : ∀ v, c (c v) = v) (h : (Fin n → E) ≃ₗ[E] (Fin n → E)) :
    (Fin n → E) ≃ₗ[E] (Fin n → E) where
  toFun v := c (h (c v))
  invFun v := c (h.symm (c v))
  map_add' u v := by simp only [map_add]
  map_smul' t v := by simp only [hs, map_smul, L.cj_cj, RingHom.id_apply]
  left_inv v := by simp only [hc, LinearEquiv.symm_apply_apply]
  right_inv v := by simp only [hc, LinearEquiv.apply_symm_apply]

def conjAut (c : (Fin n → E) →+ (Fin n → E)) (hs : ∀ t v, c (t • v) = L.cj t • c v)
    (hc : ∀ v, c (c v) = v) :
    ((Fin n → E) ≃ₗ[E] (Fin n → E)) ≃* ((Fin n → E) ≃ₗ[E] (Fin n → E)) where
  toFun := conjLin L c hs hc
  invFun := conjLin L c hs hc
  left_inv h := by
    ext1 v
    show c (c (h (c (c v)))) = h v
    rw [hc, hc]
  right_inv h := by
    ext1 v
    show c (c (h (c (c v)))) = h v
    rw [hc, hc]
  map_mul' h k := by
    ext1 v
    show c (h (k (c v))) = c (h (c (c (k (c v)))))
    rw [hc]

theorem mem_stabL (Λ : Submodule L.O (Fin n → E)) (h : (Fin n → E) ≃ₗ[E] (Fin n → E)) :
    h ∈ stabL L Λ ↔ ∀ v, h v ∈ Λ ↔ v ∈ Λ := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro e v
    constructor
    · intro hv
      rw [← e, Submodule.mem_smul_pointwise_iff_exists] at hv
      obtain ⟨w, hw, hwv⟩ := hv
      have : w = v := h.injective hwv
      exact this ▸ hw
    · intro hv
      rw [← e, Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨v, hv, rfl⟩
  · intro e
    ext v
    rw [Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (e w).2 hw
    · intro hv
      refine ⟨h.symm v, (e _).1 (by simpa using hv), ?_⟩
      show h (h.symm v) = v
      simp

theorem of_involution (hH : IsHerm L Hm) (c : (Fin n → E) →+ (Fin n → E))
    (hs : ∀ t v, c (t • v) = L.cj t • c v) (hc : ∀ v, c (c v) = v)
    (hf' : ∀ v w, hf L Hm (c v) (c w) = L.cj (hf L Hm v w))
    (Y : Submodule E (Fin n → E)) (hY : ∀ v ∈ Y, c v ∈ Y)
    (Λ : Submodule L.O (Fin n → E)) (hΛ : ∀ v ∈ Λ, c v ∈ Λ)
    (a : Fin n → E) (ha : c a = a) (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (hg : IsQRefl L Hm a g) :
    ∃ α : ((Fin n → E) ≃ₗ[E] (Fin n → E)) ≃* ((Fin n → E) ≃ₗ[E] (Fin n → E)),
      (fixG L Hm Y ⊓ stabL L Λ).map α.toMonoidHom = fixG L Hm Y ⊓ stabL L Λ ∧ α g = g⁻¹ := by
  have hY' : ∀ v, c v ∈ Y ↔ v ∈ Y := fun v => ⟨fun h => hc v ▸ hY _ h, hY v⟩
  have hΛ' : ∀ v, c v ∈ Λ ↔ v ∈ Λ := fun v => ⟨fun h => hc v ▸ hΛ _ h, hΛ v⟩
  have key : ∀ h ∈ fixG L Hm Y ⊓ stabL L Λ, conjAut L c hs hc h ∈ fixG L Hm Y ⊓ stabL L Λ := by
    rintro h ⟨⟨h1, h2, h3⟩, h4⟩
    refine ⟨⟨fun v w => ?_, fun v => ?_, fun v hv => ?_⟩, ?_⟩
    · show hf L Hm (c (h (c v))) (c (h (c w))) = _
      rw [hf', h1, hf', L.cj_cj]
    · show c (h (c v)) ∈ Y ↔ _
      rw [hY', h2, hY']
    · show c (h (c v)) - v ∈ (⊥ : Submodule E (Fin n → E))
      have := h3 _ (hY v hv)
      rw [Submodule.mem_bot, sub_eq_zero] at this ⊢
      rw [this, hc]
    · refine (mem_stabL L Λ _).2 fun v => ?_
      show c (h (c v)) ∈ Λ ↔ _
      rw [hΛ', (mem_stabL L Λ _).1 h4, hΛ']
  refine ⟨conjAut L c hs hc, le_antisymm ?_ fun h hh => ?_, ?_⟩
  · rintro _ ⟨h, hh, rfl⟩
    exact key h hh
  · exact ⟨_, key h hh, (conjAut L c hs hc).left_inv h⟩
  · obtain ⟨hN, hi, s, hsv⟩ := hg
    have hN' : L.cj (hf L Hm a a) = hf L Hm a a := cj_hf L Hm hH a a
    have e1 : hf L Hm (g a) (g a) = hf L Hm a a := hi a a
    rw [hsv a] at e1
    simp only [hf_add_left, hf_add_right, hf_smul_left, hf_smul_right, map_mul, hN'] at e1
    have e2 : L.cj s + s + s * L.cj s * hf L Hm a a = 0 := by
      refine (hN.mul hN).mul_left_cancel ?_
      linear_combination e1
    rw [eq_inv_iff_mul_eq_one]
    ext1 v
    show c (g (c (g v))) = v
    have e3 : ∀ w, c (g (c w)) = w + (L.cj s * hf L Hm w a) • a := fun w => by
      rw [hsv, map_add, hc, hs, ha, map_mul]
      congr 3
      rw [← hf', hc, ha]
    rw [e3, hsv v, hf_add_left, hf_smul_left, add_assoc, ← add_smul]
    have : s * hf L Hm v a + L.cj s * (hf L Hm v a + s * hf L Hm v a * hf L Hm a a) = 0 := by
      linear_combination hf L Hm v a * e2
    rw [this, zero_smul, add_zero]

theorem exists_involution (hH : IsHerm L Hm) {ι : Type} [Fintype ι] (b : ι → Fin n → E)
    (hb : Submodule.span E (Set.range b) = ⊤) (hu : ∀ i, IsUnit (hf L Hm (b i) (b i)))
    (ho : ∀ i j, i ≠ j → hf L Hm (b i) (b j) = 0) :
    ∃ c : (Fin n → E) →+ (Fin n → E), (∀ t v, c (t • v) = L.cj t • c v) ∧ (∀ v, c (c v) = v) ∧
      (∀ v w, hf L Hm (c v) (c w) = L.cj (hf L Hm v w)) ∧ ∀ i, c (b i) = b i := by
  let c : (Fin n → E) →+ (Fin n → E) := AddMonoidHom.mk'
    (fun v => ∑ i, (hf L Hm (b i) v * ↑(hu i).unit⁻¹) • b i) (fun u v => by
      simp only [hf_add_right, add_mul, add_smul, Finset.sum_add_distrib])
  have hcv : ∀ v, c v = ∑ i, (hf L Hm (b i) v * ↑(hu i).unit⁻¹) • b i := fun v => rfl
  have hs : ∀ t v, c (t • v) = L.cj t • c v := fun t v => by
    simp only [hcv, hf_smul_right, Finset.smul_sum, smul_smul, mul_assoc]
  have hbi : ∀ i, c (b i) = b i := fun i => by
    rw [hcv, Finset.sum_eq_single i]
    · rw [IsUnit.mul_val_inv, one_smul]
    · intro j _ hj
      rw [ho j i hj, zero_mul, zero_smul]
    · simp
  have hmem : ∀ v, v ∈ Submodule.span E (Set.range b) := fun v => hb ▸ Submodule.mem_top
  refine ⟨c, hs, fun v => ?_, fun v w => ?_, hbi⟩
  · induction hmem v using Submodule.span_induction with
    | mem _ h => obtain ⟨i, rfl⟩ := h; rw [hbi, hbi]
    | zero => simp
    | add x y _ _ h1 h2 => rw [map_add, map_add, h1, h2]
    | smul t x _ h => rw [hs, hs, L.cj_cj, h]
  · induction hmem v using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨i, rfl⟩ := h
      induction hmem w using Submodule.span_induction with
      | mem _ h =>
        obtain ⟨j, rfl⟩ := h
        rw [hbi, hbi, cj_hf L Hm hH]
        by_cases hij : i = j
        · rw [hij]
        · rw [ho i j hij, ho j i (Ne.symm hij)]
      | zero => simp [hf_zero_right]
      | add x y _ _ h1 h2 => rw [map_add, hf_add_right, hf_add_right, h1, h2, map_add]
      | smul t x _ h => rw [hs, hf_smul_right, hf_smul_right, h, map_mul]
    | zero => simp [hf_zero_left]
    | add x y _ _ h1 h2 => rw [map_add, hf_add_left, hf_add_left, h1, h2, map_add]
    | smul t x _ h => rw [hs, hf_smul_left, hf_smul_left, h, map_mul]

end

theorem qrefl_inverted : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ (m : ℕ) (x : Fin m → Fin n → E), IsUnit (gramT L Hm x).det → ∀ a ∈ perp L Hm (Submodule.span E (Set.range x)), ∀ g, IsQRefl L Hm a g → ∃ Λ : Submodule L.O (Fin n → E), IsLat L Λ ∧ ∃ α : ((Fin n → E) ≃ₗ[E] (Fin n → E)) ≃* ((Fin n → E) ≃ₗ[E] (Fin n → E)), (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ).map α.toMonoidHom = fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ ∧ α g = g⁻¹ := by
  intro F _ _ _ _ _ E _ _ _ L n Hm hH m x hx a ha g hg
  let Γ : Matrix (Fin m) (Fin m) E := (gramT L Hm x).transpose
  have hΓ : IsHermND L Γ := by
    refine ⟨?_, by rwa [Matrix.det_transpose]⟩
    funext i j
    exact cj_hf L Hm hH.1 _ _
  let φ : (Fin m → E) →ₗ[E] (Fin n → E) := Fintype.linearCombination E x
  have hφ : ∀ s t, hf L Hm (φ s) (φ t) = hf L Γ s t := fun s t => by
    simp only [φ, Fintype.linearCombination_apply, hf_sum_left, hf_sum_right, hf_smul_left,
      hf_smul_right, Finset.mul_sum]
    conv_rhs => unfold hf
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Γ, gramT, Matrix.transpose_apply, Matrix.of_apply]
    ring
  obtain ⟨-, -, w, hw1, hw2, hw3⟩ := GlobalTheory.HermOrthBasis.orth_basis_perp L Γ hΓ 0 Fin.elim0 (by simp)
  have hw : Submodule.span E (Set.range w) = ⊤ := by
    rw [hw1, eq_top_iff]
    intro v _ y hy
    rw [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at hy
    rw [hy, hf_zero_right]
  let u : Fin (m - 0) → Fin n → E := fun i => φ (w i)
  have hu : Submodule.span E (Set.range u) = Submodule.span E (Set.range x) := by
    rw [show u = φ ∘ w from rfl, Set.range_comp, ← Submodule.map_span, hw, Submodule.map_top,
      Fintype.range_linearCombination]
  have hau : ∀ i, hf L Hm a (u i) = 0 := fun i =>
    ha _ (hu ▸ Submodule.subset_span ⟨i, rfl⟩)
  let z : Fin (m - 0 + 1) → Fin n → E := Fin.cons a u
  have hz1 : ∀ i, IsUnit (hf L Hm (z i) (z i)) := fun i => by
    refine Fin.cases hg.1 (fun k => ?_) i
    show IsUnit (hf L Hm (φ _) (φ _))
    rw [hφ]; exact hw2 k
  have hz2 : ∀ i j, i ≠ j → hf L Hm (z i) (z j) = 0 := fun i j => by
    refine Fin.cases ?_ (fun k => ?_) i <;> refine Fin.cases ?_ (fun l => ?_) j <;> intro hij
    · exact absurd rfl hij
    · exact hau l
    · show hf L Hm (u k) a = 0
      rw [← cj_hf L Hm hH.1, hau, map_zero]
    · show hf L Hm (φ _) (φ _) = 0
      rw [hφ]; exact hw3 k l fun e => hij (by rw [e])
  have hz : IsUnit (gramT L Hm z).det := by
    have : gramT L Hm z = Matrix.diagonal fun i => hf L Hm (z i) (z i) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp [gramT]
      · rw [Matrix.diagonal_apply_ne _ hij]; exact hz2 j i (Ne.symm hij)
    rw [this, Matrix.det_diagonal]
    exact IsUnit.prod_univ_iff.2 hz1
  obtain ⟨-, hcompl, r, hr1, hr2, hr3⟩ := GlobalTheory.HermOrthBasis.orth_basis_perp L Hm hH _ z hz
  have hrz : ∀ i j, hf L Hm (r i) (z j) = 0 := fun i j => by
    have : r i ∈ perp L Hm (Submodule.span E (Set.range z)) :=
      hr1 ▸ Submodule.subset_span ⟨i, rfl⟩
    exact this _ (Submodule.subset_span ⟨j, rfl⟩)
  have hb : Submodule.span E (Set.range (Sum.elim z r)) = ⊤ := by
    rw [Set.Sum.elim_range, Submodule.span_union, hr1]
    exact hcompl.sup_eq_top
  obtain ⟨c, hs, hc, hf', hbi⟩ := exists_involution L Hm hH.1 (Sum.elim z r) hb
    (by rintro (i | i); exacts [hz1 i, hr2 i])
    (by
      rintro (i | i) (j | j) hij
      · exact hz2 i j fun e => hij (by rw [e])
      · show hf L Hm (z i) (r j) = 0
        rw [← cj_hf L Hm hH.1, hrz, map_zero]
      · exact hrz i j
      · exact hr3 i j fun e => hij (by rw [e]))
  refine ⟨Submodule.span L.O (Set.range (Sum.elim z r)),
    ⟨Submodule.fg_span (Set.finite_range _), ?_⟩, ?_⟩
  · rw [eq_top_iff, ← hb]
    exact Submodule.span_mono Submodule.subset_span
  refine of_involution L Hm hH.1 c hs hc hf' _ ?_ _ ?_ a (hbi (Sum.inl 0)) g hg
  · rw [← hu]
    intro v hv
    induction hv using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨i, rfl⟩ := h
      have : c (u i) = u i := hbi (Sum.inl i.succ)
      rw [this]; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add x y _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
    | smul t x _ h => rw [hs]; exact Submodule.smul_mem _ _ h
  · intro v hv
    induction hv using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨i, rfl⟩ := h
      rw [hbi]; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add x y _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
    | smul t x _ h =>
      have : c (t • x) = (⟨L.cj t, cj_mem_O L t.2⟩ : L.O) • c x := hs t x
      rw [this]; exact Submodule.smul_mem _ _ h

end GlobalTheory.QRefl
