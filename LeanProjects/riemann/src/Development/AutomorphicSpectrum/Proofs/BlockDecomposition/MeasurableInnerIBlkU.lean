import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.RS.ColN
open PositivityTheory.AdelicQuotientData

section Ring

variable {R : Type} [CommRing R] {a : ℕ}

theorem posM_blk_apply (m : ℕ) (c : UnipotentBlockColumnIndex a m m → R) (i j : Fin a) :
    posM (Subtype.val : UnipotentBlockColumnIndex a m m → Fin a × Fin a) c i j =
      if h : (i : ℕ) < m ∧ (j : ℕ) = m then c ⟨(i, j), h.1, h.2.ge, h.2.le⟩ else 0 := by
  simp only [posM, Matrix.sum_apply, Matrix.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨(i, j), h.1, h.2.ge, h.2.le⟩]
    · simp
    · intro t _ ht
      rw [if_neg]
      rintro ⟨e1, e2⟩
      exact ht (Subtype.ext (Prod.ext e1 e2))
    · simp
  · refine Finset.sum_eq_zero fun t _ => ?_
    rw [if_neg]
    rintro ⟨e1, e2⟩
    apply h
    have h1 := t.2
    rw [← e1, ← e2]
    omega

theorem posM_mul_of_row (m : ℕ) (c : UnipotentBlockColumnIndex a m m → R) (M : Matrix (Fin a) (Fin a) R)
    (hM : ∀ r j : Fin a, (r : ℕ) = m → M r j = (1 : Matrix (Fin a) (Fin a) R) r j) :
    posM (Subtype.val : UnipotentBlockColumnIndex a m m → Fin a × Fin a) c * M = posM Subtype.val c := by
  simp only [posM, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 := t.2
  calc Matrix.single t.1.1 t.1.2 (c t) * M = Matrix.single t.1.1 t.1.2 (c t) * 1 := by
        ext p q
        simp only [Matrix.mul_apply, Matrix.single_apply]
        refine Finset.sum_congr rfl fun l _ => ?_
        by_cases h : t.1.1 = p ∧ t.1.2 = l
        · rw [if_pos h, hM l q (by rw [← h.2]; omega)]
        · rw [if_neg h, zero_mul, zero_mul]
    _ = _ := mul_one _

theorem blkU_mul_val (m : ℕ) (c : UnipotentBlockColumnIndex a m m → R) (γ : GL (Fin a) R)
    (hM : ∀ r j : Fin a, (r : ℕ) = m → γ.val r j = (1 : Matrix (Fin a) (Fin a) R) r j) :
    (blkU c * γ).val = γ.val + posM Subtype.val c := by
  change (1 + posM Subtype.val c) * γ.val = _
  rw [add_mul, one_mul, posM_mul_of_row m c _ hM]

theorem blkU_inv_mul_val (m : ℕ) (c : UnipotentBlockColumnIndex a m m → R) (γ : GL (Fin a) R)
    (hM : ∀ r j : Fin a, (r : ℕ) = m → γ.val r j = (1 : Matrix (Fin a) (Fin a) R) r j) :
    ((blkU c)⁻¹ * γ).val = γ.val - posM Subtype.val c := by
  change (1 - posM Subtype.val c) * γ.val = _
  rw [sub_mul, one_mul, posM_mul_of_row m c _ hM]

theorem blkU_add (m : ℕ) (x y : UnipotentBlockColumnIndex a m m → R) : blkU (x + y) = blkU x * blkU y :=
  posU_add _ x y

theorem blkU_neg (m : ℕ) (x : UnipotentBlockColumnIndex a m m → R) : blkU (-x) = (blkU x)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← blkU_add, neg_add_cancel]
  exact posU_zero _

end Ring

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem row_of_blk {m : ℕ} {γ : GL (Fin k) E} (h : GlobalTheory m γ) (r j : Fin k) (hr : (r : ℕ) = m) :
    γ.val r j = (1 : Matrix (Fin k) (Fin k) E) r j := h r j (Or.inl hr.ge)

theorem isMir_blkU_mul {m : ℕ} (c : UnipotentBlockColumnIndex k m m → E) {γ : GL (Fin k) E} (h : GlobalTheory m γ) :
    IsMir m (blkU c * γ) := by
  intro i j hij
  rw [blkU_mul_val m c γ (row_of_blk h), Matrix.add_apply, posM_blk_apply, dif_neg (by omega), add_zero]
  exact h i j (by omega)

def colEquiv (m : ℕ) :
    (UnipotentBlockColumnIndex k m m → E) × ({γ | GlobalTheory m γ} : Set (GL (Fin k) E)) ≃ ({γ | IsMir m γ} : Set (GL (Fin k) E)) :=
  Equiv.ofBijective (fun p => ⟨blkU p.1 * p.2.1, isMir_blkU_mul p.1 p.2.2⟩) (by
    constructor
    · rintro ⟨c, γ, hγ⟩ ⟨c', γ', hγ'⟩ h
      have h0 : blkU c * γ = blkU c' * γ' := congrArg Subtype.val h
      have hv := congrArg Units.val h0
      rw [blkU_mul_val m c γ (row_of_blk hγ), blkU_mul_val m c' γ' (row_of_blk hγ')] at hv
      have hc : c = c' := by
        funext t
        have h1 := t.2
        have h2 := congrFun (congrFun hv t.1.1) t.1.2
        simp only [Matrix.add_apply] at h2
        rw [hγ t.1.1 t.1.2 (Or.inr h1.2.1), hγ' t.1.1 t.1.2 (Or.inr h1.2.1), posM_blk_apply, posM_blk_apply,
          dif_pos ⟨h1.1, by omega⟩, dif_pos ⟨h1.1, by omega⟩] at h2
        exact add_left_cancel h2
      subst hc
      have : γ = γ' := mul_left_cancel h0
      subst this
      rfl
    · rintro ⟨p, hp⟩
      have hrow : ∀ r j : Fin k, (r : ℕ) = m → p.val r j = (1 : Matrix (Fin k) (Fin k) E) r j :=
        fun r j hr => hp r j (Or.inl hr.ge)
      let c : UnipotentBlockColumnIndex k m m → E := fun t => p.val t.1.1 t.1.2
      have hγ : GlobalTheory m ((blkU c)⁻¹ * p) := by
        intro i j hij
        rw [blkU_inv_mul_val m c p hrow, Matrix.sub_apply, posM_blk_apply]
        split_ifs with h
        · have hne : i ≠ j := fun e => by rw [e] at h; omega
          rw [Matrix.one_apply_ne hne]
          exact sub_self _
        · rw [sub_zero]
          exact hp i j (by omega)
      exact ⟨(c, ⟨_, hγ⟩), Subtype.ext (mul_inv_cancel_left _ _)⟩)

theorem colEquiv_val (m : ℕ) (c : UnipotentBlockColumnIndex k m m → E) (γ : ({γ | GlobalTheory m γ} : Set (GL (Fin k) E))) :
    (colEquiv m (c, γ)).1 = blkU c * γ.1 := rfl

theorem blk_ratGL {m : ℕ} {γ : GL (Fin k) E} (h : GlobalTheory m γ) : GlobalTheory m (ratGL E k γ) := by
  intro i j hij
  change algebraMap E (Ad E) (γ.val i j) = _
  rw [h i j hij, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem lintegral_nuG (Γ : Set (GL (Fin k) E)) (d : ℕ) {Φ : GA E k → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ h, Φ h ∂nuG Γ d = ∑' γ : Γ, ∫⁻ h, Φ (ratGL E k γ * h) ∂nuD E k d := by
  rw [nuG, lintegral_sum_measure]
  refine tsum_congr fun γ => ?_
  rw [lintegral_map hΦ (measurable_const_mul _)]

theorem measurable_blkU_mul (m : ℕ) :
    Measurable fun p : (UnipotentBlockColumnIndex k m m → Ad E) × GA E k => (blkU p.1 * p.2 : GA E k) :=
  (((continuous_posU (isNil_blk k m m)).comp continuous_fst).mul continuous_snd).measurable

theorem lintegral_nuD_succ (m d : ℕ) (hm : m = k - (d + 1)) [SFinite (nuD E k d)] {Φ : GA E k → ℝ≥0∞}
    (hΦ : Measurable Φ) :
    ∫⁻ h, Φ h ∂nuD E k (d + 1) =
      ∫⁻ x : UnipotentBlockColumnIndex k m m → Ad E, ∫⁻ n, Φ (blkU x * n) ∂nuD E k d ∂vecMeasure E (UnipotentBlockColumnIndex k m m) := by
  subst hm
  rw [nuD, lintegral_map hΦ (measurable_blkU_mul _)]
  exact lintegral_prod (fun p : (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E) × GA E k => Φ (blkU p.1 * p.2))
    (hΦ.comp (measurable_blkU_mul _)).aemeasurable

theorem unfold_vec (ι : Type) [Fintype ι] (G : (ι → Ad E) → ℝ≥0∞) :
    ∫⁻ y, G y ∂vecMeasure E ι =
      ∑' c : ι → E, ∫⁻ x in vecDomain E ι, G (-x + fun t => algebraMap E (Ad E) (c t)) ∂vecMeasure E ι := by
  haveI : (vecMeasure E ι).IsNegInvariant := Measure.pi.isNegInvariant _
  haveI := GroundTheory.Global.countable_numberField E
  rw [← lintegral_neg_eq_self, (isAddFundamentalDomain_vecDomain (K := E) (ι := ι)).lintegral_eq_tsum']
  let e : (ι → E) ≃ vecLattice E ι := Equiv.ofBijective
    (fun c => ⟨fun t => algebraMap E (Ad E) (c t), c, rfl⟩) (by
      constructor
      · intro c c' h
        funext t
        exact NumberField.AdeleRing.algebraMap_injective (𝓞 E) E (congrFun (congrArg Subtype.val h) t)
      · rintro ⟨_, c, rfl⟩
        exact ⟨c, rfl⟩)
  rw [← e.tsum_eq]
  refine tsum_congr fun c => lintegral_congr fun x => ?_
  congr 1
  change -(-(fun t => algebraMap E (Ad E) (c t)) + x) = _
  rw [neg_add, neg_neg, add_comm]

theorem countable_GL : Countable (GL (Fin k) E) := by
  haveI := GroundTheory.Global.countable_numberField E
  haveI : Countable (Matrix (Fin k) (Fin k) E) := inferInstanceAs (Countable (Fin k → Fin k → E))
  exact Function.Injective.countable (f := fun g : GL (Fin k) E => g.val) Units.val_injective

def innerI (d : ℕ) (F : GA E k → ℝ≥0∞) (g u : GA E k) : ℝ≥0∞ := ∫⁻ n, F (u * (g * n)) ∂nuD E k d

theorem measurable_innerI (d : ℕ) [SFinite (nuD E k d)] {F : GA E k → ℝ≥0∞} (hF : Measurable F) (g : GA E k) :
    Measurable (innerI d F g) :=
  Measurable.lintegral_prod_right' (f := fun p : GA E k × GA E k => F (p.1 * (g * p.2)))
    (hF.comp (measurable_fst.mul (measurable_snd.const_mul g)))

theorem measurable_innerI_blkU (m d : ℕ) [SFinite (nuD E k d)] {F : GA E k → ℝ≥0∞} (hF : Measurable F)
    (g : GA E k) : Measurable fun y : UnipotentBlockColumnIndex k m m → Ad E => innerI d F g (blkU y) :=
  (measurable_innerI d hF g).comp (continuous_posU (isNil_blk k m m)).measurable

theorem left_side (m d : ℕ) (hm : m = k - (d + 1)) (hd : d + 1 ≤ k) (sf : SFinite (nuD E k d))
    (dt1 : ∀ γ : GL (Fin k) E, Dt (ratGL E k γ) = 1)
    (mod : ∀ g : GA E k, GlobalTheory m g → ∀ F : GA E k → ℝ≥0∞, Measurable F →
      ∫⁻ x : UnipotentBlockColumnIndex k m m → Ad E, F (g * blkU x * g⁻¹) ∂vecMeasure E _ =
        ENNReal.ofReal (Dt g)⁻¹ * ∫⁻ x : UnipotentBlockColumnIndex k m m → Ad E, F (blkU x) ∂vecMeasure E _)
    {F : GA E k → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ h, F h ∂nuB E k m =
      ∑' γ : ({γ | GlobalTheory m γ} : Set (GL (Fin k) E)),
        ∫⁻ y : UnipotentBlockColumnIndex k m m → Ad E, innerI d F (ratGL E k γ.1) (blkU y) ∂vecMeasure E (UnipotentBlockColumnIndex k m m) := by
  have hkm : k - m = d + 1 := by omega
  rw [nuB, hkm, lintegral_nuG _ _ hF]
  refine tsum_congr fun γ => ?_
  have h1 := lintegral_nuD_succ m d hm (Φ := fun h => F (ratGL E k γ.1 * h)) (hF.comp (measurable_const_mul _))
  have key := mod (ratGL E k γ.1) (blk_ratGL γ.2) (innerI d F (ratGL E k γ.1)) (measurable_innerI d hF _)
  rw [dt1, inv_one, ENNReal.ofReal_one, one_mul] at key
  rw [h1, ← key]
  refine lintegral_congr fun x => lintegral_congr fun n => ?_
  simp only [mul_assoc, inv_mul_cancel_left]

theorem right_inner (m d : ℕ) (hm : m = k - (d + 1)) (hd : d + 1 ≤ k) {F : GA E k → ℝ≥0∞} (hF : Measurable F)
    (x : UnipotentBlockColumnIndex k m m → Ad E) :
    ∫⁻ h, F ((blkU x)⁻¹ * h) ∂nuP E k m =
      ∑' γ : ({γ | GlobalTheory m γ} : Set (GL (Fin k) E)), ∑' c : UnipotentBlockColumnIndex k m m → E,
        innerI d F (ratGL E k γ.1) (blkU (-x + fun t => algebraMap E (Ad E) (c t))) := by
  have hkm' : k - (m + 1) = d := by omega
  rw [nuP, hkm', lintegral_nuG _ _ (Φ := fun h => F ((blkU x)⁻¹ * h)) (hF.comp (measurable_const_mul _)),
    ← (colEquiv m).tsum_eq, ENNReal.tsum_prod', ENNReal.tsum_comm]
  refine tsum_congr fun γ => tsum_congr fun c => lintegral_congr fun n => ?_
  rw [colEquiv_val, map_mul, ratGL_blkU, blkU_add, blkU_neg]
  simp only [mul_assoc]

theorem main (m d : ℕ) (hm : m = k - (d + 1)) (hd : d + 1 ≤ k) (sf : SFinite (nuD E k d))
    (dt1 : ∀ γ : GL (Fin k) E, Dt (ratGL E k γ) = 1)
    (mod : ∀ g : GA E k, GlobalTheory m g → ∀ F : GA E k → ℝ≥0∞, Measurable F →
      ∫⁻ x : UnipotentBlockColumnIndex k m m → Ad E, F (g * blkU x * g⁻¹) ∂vecMeasure E _ =
        ENNReal.ofReal (Dt g)⁻¹ * ∫⁻ x : UnipotentBlockColumnIndex k m m → Ad E, F (blkU x) ∂vecMeasure E _)
    {F : GA E k → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ h, F h ∂nuB E k m =
      ∫⁻ x in vecDomain E (UnipotentBlockColumnIndex k m m), ∫⁻ h, F ((blkU x)⁻¹ * h) ∂nuP E k m ∂vecMeasure E (UnipotentBlockColumnIndex k m m) := by
  haveI := GroundTheory.Global.countable_numberField E
  haveI : Countable (GL (Fin k) E) := countable_GL
  have hmeas : ∀ (γ : ({γ | GlobalTheory m γ} : Set (GL (Fin k) E))) (c : UnipotentBlockColumnIndex k m m → E),
      Measurable fun x : UnipotentBlockColumnIndex k m m → Ad E =>
        innerI d F (ratGL E k γ.1) (blkU (-x + fun t => algebraMap E (Ad E) (c t))) := fun γ c =>
    (measurable_innerI_blkU m d hF _).comp (measurable_neg.add_const _)
  rw [left_side m d hm hd sf dt1 mod hF, lintegral_congr (right_inner m d hm hd hF),
    lintegral_tsum fun γ => (Measurable.ennreal_tsum fun c => hmeas γ c).aemeasurable]
  refine tsum_congr fun γ => ?_
  rw [lintegral_tsum fun c => (hmeas γ c).aemeasurable]
  exact unfold_vec _ _

theorem one_more_column : D0 → N0 → N1 → N3 → ColumnConjugationMeasure → OneMoreAdelicColumn := by
  intro hD _ hN1 _ hM E _ _ _ k m hm F hF
  obtain ⟨d, hd, hmd⟩ : ∃ d, d + 1 ≤ k ∧ m = k - (d + 1) := ⟨k - (m + 1), by omega, by omega⟩
  exact main m d hmd hd (hN1 E k d (by omega)).1 (hD E k).2.2.2.1 (hM E k m hm) hF

end GlobalTheory.CompanionTheory.RS.ColN

end
