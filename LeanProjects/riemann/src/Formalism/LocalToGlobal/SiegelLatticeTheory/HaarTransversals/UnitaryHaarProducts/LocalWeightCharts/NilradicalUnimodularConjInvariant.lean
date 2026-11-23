import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.StarOfInv
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.ProductDecompositionHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.DDMulApply

noncomputable section

open MeasureTheory Matrix Topology Filter
open scoped ENNReal NNReal Pointwise

namespace WlocSk.HM

open Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

abbrev GN (k r : ℕ) := Grp (Nset k r : Set (Mx k r)) n_clsub

def conjE (a : Mx k r) (ha : IsUnit a.det) (h1 : ∀ g ∈ Nset k r, a⁻¹ * g * a ∈ Nset k r)
    (h2 : ∀ g ∈ Nset k r, a * g * a⁻¹ ∈ Nset k r) : GN k r ≃* GN k r where
  toFun g := Grp.mk (a⁻¹ * g.val * a) (h1 _ g.mem)
  invFun g := Grp.mk (a * g.val * a⁻¹) (h2 _ g.mem)
  left_inv g := Grp.ext' (by
    show a * (a⁻¹ * g.val * a) * a⁻¹ = g.val
    calc a * (a⁻¹ * g.val * a) * a⁻¹ = (a * a⁻¹) * g.val * (a * a⁻¹) := by simp only [Matrix.mul_assoc]
      _ = g.val := by rw [Matrix.mul_nonsing_inv a ha, Matrix.one_mul, Matrix.mul_one])
  right_inv g := Grp.ext' (by
    show a⁻¹ * (a * g.val * a⁻¹) * a = g.val
    calc a⁻¹ * (a * g.val * a⁻¹) * a = (a⁻¹ * a) * g.val * (a⁻¹ * a) := by simp only [Matrix.mul_assoc]
      _ = g.val := by rw [Matrix.nonsing_inv_mul a ha, Matrix.one_mul, Matrix.mul_one])
  map_mul' g g' := Grp.ext' (by
    show a⁻¹ * (g.val * g'.val) * a = (a⁻¹ * g.val * a) * (a⁻¹ * g'.val * a)
    calc a⁻¹ * (g.val * g'.val) * a = a⁻¹ * g.val * (a * a⁻¹) * g'.val * a := by
          rw [Matrix.mul_nonsing_inv a ha, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = (a⁻¹ * g.val * a) * (a⁻¹ * g'.val * a) := by simp only [Matrix.mul_assoc])

lemma conjE_val (a : Mx k r) (ha : IsUnit a.det) (h1 : ∀ g ∈ Nset k r, a⁻¹ * g * a ∈ Nset k r)
    (h2 : ∀ g ∈ Nset k r, a * g * a⁻¹ ∈ Nset k r) (g : GN k r) :
    (conjE a ha h1 h2 g).val = a⁻¹ * g.val * a := rfl

lemma conjE_cont (a : Mx k r) (ha : IsUnit a.det) (h1 : ∀ g ∈ Nset k r, a⁻¹ * g * a ∈ Nset k r)
    (h2 : ∀ g ∈ Nset k r, a * g * a⁻¹ ∈ Nset k r) : Continuous (conjE a ha h1 h2) := by
  rw [Grp.emb.isInducing.continuous_iff]
  show Continuous fun g : GN k r => a⁻¹ * g.val * a
  exact (continuous_const.matrix_mul Grp.emb.continuous).matrix_mul continuous_const

lemma conjE_symm_cont (a : Mx k r) (ha : IsUnit a.det) (h1 : ∀ g ∈ Nset k r, a⁻¹ * g * a ∈ Nset k r)
    (h2 : ∀ g ∈ Nset k r, a * g * a⁻¹ ∈ Nset k r) : Continuous (conjE a ha h1 h2).symm := by
  rw [Grp.emb.isInducing.continuous_iff]
  show Continuous fun g : GN k r => a * g.val * a⁻¹
  exact (continuous_const.matrix_mul Grp.emb.continuous).matrix_mul continuous_const

lemma smul_cancel {a b : ℝ≥0} (h : a • (Measure.haar : Measure (GN k r)) = b • Measure.haar) : a = b := by
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (1 : GN k r)
  have hK0 : (Measure.haar : Measure (GN k r)) K ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hKn).ne'
  have hKt : (Measure.haar : Measure (GN k r)) K ≠ ∞ := hK.measure_lt_top.ne
  have e := congrArg (fun ν : Measure (GN k r) => ν K) h
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at e
  exact ENNReal.coe_injective ((ENNReal.mul_left_inj hK0 hKt).mp e)

lemma map_rmul (g : GN k r) :
    Measure.map (· * g) (Measure.haar : Measure (GN k r)) =
      Measure.modularCharacter g • (Measure.haar : Measure (GN k r)) := by
  have e := Measure.modularCharacterFun_eq_haarScalarFactor (Measure.haar : Measure (GN k r)) g
  change _ = Measure.modularCharacterFun g • _
  rw [e]
  exact Measure.isMulLeftInvariant_eq_smul _ _

lemma auto_scalar (e : GN k r ≃* GN k r) (he : Continuous e) (hs : Continuous e.symm) :
    ∃ s : ℝ≥0, 0 < s ∧ Measure.map e (Measure.haar : Measure (GN k r)) = s • (Measure.haar : Measure (GN k r)) := by
  have : (Measure.map e (Measure.haar : Measure (GN k r))).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map _ e he hs
  exact ⟨_, Measure.haarScalarFactor_pos_of_isHaarMeasure _ _, Measure.isMulLeftInvariant_eq_smul _ _⟩

lemma mod_auto (e : GN k r ≃* GN k r) (he : Continuous e) (hs : Continuous e.symm) (g : GN k r) :
    Measure.modularCharacter (e g) = Measure.modularCharacter g := by
  obtain ⟨s, hsp, hE⟩ := auto_scalar e he hs
  have hs0 : s ≠ 0 := hsp.ne'
  have key : Measure.map (· * e g) (Measure.map e (Measure.haar : Measure (GN k r))) =
      Measure.map e (Measure.map (· * g) (Measure.haar : Measure (GN k r))) := by
    rw [Measure.map_map (measurable_mul_const _) he.measurable,
      Measure.map_map he.measurable (measurable_mul_const _)]
    congr 1
    funext x
    simp only [Function.comp_apply, map_mul]
  rw [hE, Measure.map_smul, map_rmul, map_rmul, Measure.map_smul, hE, smul_smul, smul_smul] at key
  have := smul_cancel key
  rw [mul_comm] at this
  exact mul_right_cancel₀ hs0 this

lemma mod_bound : ∃ K : Set (GN k r), K ∈ 𝓝 (1 : GN k r) ∧ ∃ B : ℝ≥0, ∀ g ∈ K, Measure.modularCharacter g ≤ B := by
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (1 : GN k r)
  have hK0 : (Measure.haar : Measure (GN k r)) K ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hKn).ne'
  have hKt : (Measure.haar : Measure (GN k r)) K ≠ ∞ := hK.measure_lt_top.ne
  have hC : IsCompact (K * K⁻¹) := hK.mul hK.inv
  have hCt : (Measure.haar : Measure (GN k r)) (K * K⁻¹) ≠ ∞ := hC.measure_lt_top.ne
  refine ⟨K, hKn, ((Measure.haar : Measure (GN k r)) (K * K⁻¹)).toNNReal /
    ((Measure.haar : Measure (GN k r)) K).toNNReal, fun g hg => ?_⟩
  have e := congrArg (fun ν : Measure (GN k r) => ν K) (map_rmul g)
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at e
  rw [Measure.map_apply (measurable_mul_const g) hK.isClosed.measurableSet] at e
  have hsub : (· * g) ⁻¹' K ⊆ K * K⁻¹ := by
    intro x hx
    exact ⟨x * g, hx, g⁻¹, Set.inv_mem_inv.mpr hg, by simp⟩
  have hle : (Measure.modularCharacter g : ℝ≥0∞) * (Measure.haar : Measure (GN k r)) K ≤
      (Measure.haar : Measure (GN k r)) (K * K⁻¹) := e ▸ measure_mono hsub
  rw [← ENNReal.coe_toNNReal hKt, ← ENNReal.coe_toNNReal hCt, ← ENNReal.coe_mul, ENNReal.coe_le_coe] at hle
  have hpos : 0 < ((Measure.haar : Measure (GN k r)) K).toNNReal := ENNReal.toNNReal_pos hK0 hKt
  rw [le_div_iff₀ hpos]
  exact hle

def wt (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℤ :=
  if i.val < r then (r : ℤ) - i.val else if i.val ≤ r + k then 0 else (r : ℤ) + k - i.val

def NWtUpper : Prop :=
  ∀ (k r : ℕ) (m : Mx k r), m ∈ Nset k r → ∀ i j : Fin (2 * r + k + 1),
    wt k r i ≤ wt k r j → m i j = if i = j then 1 else 0

lemma wt_tau (i : Fin (2 * r + k + 1)) : wt k r (tau k r i) = - wt k r i := by
  unfold wt tau
  simp only
  split_ifs <;> omega

lemma diag_uh (a : Fin (2 * r + k + 1) → ℂ) (ha : ∀ i, star (a i) * a (tau k r i) = 1) :
    (diagonal a)ᴴ * Hpk k r * diagonal a = Hpk k r := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul, hpk_row]
  by_cases hj : j = tau k r i
  · subst hj
    simp only [Pi.star_apply, ite_true]
    linear_combination (sgn k r i) * ha i
  · simp [hj]

lemma diag_conj_n (a b : Fin (2 * r + k + 1) → ℂ) (hab : ∀ i, a i * b i = 1)
    (ha : ∀ i, star (a i) * a (tau k r i) = 1) (hb : ∀ i, star (b i) * b (tau k r i) = 1)
    {g : Mx k r} (hg : g ∈ Nset k r) : diagonal a * g * diagonal b ∈ Nset k r := by
  rw [nset_iff] at hg ⊢
  obtain ⟨hU, hc⟩ := hg
  have hU' : gᴴ * Hpk k r * g = Hpk k r := hU
  refine ⟨?_, fun i j hj hi => ?_⟩
  · show (diagonal a * g * diagonal b)ᴴ * Hpk k r * (diagonal a * g * diagonal b) = Hpk k r
    calc (diagonal a * g * diagonal b)ᴴ * Hpk k r * (diagonal a * g * diagonal b)
        = (diagonal b)ᴴ * (gᴴ * ((diagonal a)ᴴ * Hpk k r * diagonal a) * g) * diagonal b := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Hpk k r := by rw [diag_uh a ha, hU', diag_uh b hb]
  · rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hc i j hj hi]
    by_cases h : i = j
    · subst h; simp [hab]
    · simp [h]

def dv (k r : ℕ) (t : ℝ) (i : Fin (2 * r + k + 1)) : ℂ := ((t ^ wt k r i : ℝ) : ℂ)

def dvi (k r : ℕ) (t : ℝ) (i : Fin (2 * r + k + 1)) : ℂ := ((t ^ (- wt k r i) : ℝ) : ℂ)

lemma dvi_dv {t : ℝ} (ht : t ≠ 0) (i : Fin (2 * r + k + 1)) : dvi k r t i * dv k r t i = 1 := by
  unfold dv dvi
  rw [← Complex.ofReal_mul, ← zpow_add₀ ht, neg_add_cancel, zpow_zero, Complex.ofReal_one]

lemma dv_dvi {t : ℝ} (ht : t ≠ 0) (i : Fin (2 * r + k + 1)) : dv k r t i * dvi k r t i = 1 := by
  rw [mul_comm]; exact dvi_dv ht i

lemma star_ofReal' (x : ℝ) : star (x : ℂ) = x := Complex.conj_ofReal x

lemma dv_form {t : ℝ} (ht : t ≠ 0) (i : Fin (2 * r + k + 1)) :
    star (dv k r t i) * dv k r t (tau k r i) = 1 := by
  unfold dv
  rw [star_ofReal', wt_tau, ← Complex.ofReal_mul, ← zpow_add₀ ht, add_neg_cancel, zpow_zero, Complex.ofReal_one]

lemma dvi_form {t : ℝ} (ht : t ≠ 0) (i : Fin (2 * r + k + 1)) :
    star (dvi k r t i) * dvi k r t (tau k r i) = 1 := by
  unfold dvi
  rw [star_ofReal', wt_tau, neg_neg, ← Complex.ofReal_mul, ← zpow_add₀ ht, neg_add_cancel, zpow_zero,
    Complex.ofReal_one]

lemma dg_left_inv {t : ℝ} (ht : t ≠ 0) : diagonal (dvi k r t) * diagonal (dv k r t) = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact dvi_dv ht i

lemma dg_inv {t : ℝ} (ht : t ≠ 0) : (diagonal (dv k r t))⁻¹ = diagonal (dvi k r t) :=
  Matrix.inv_eq_left_inv (dg_left_inv ht)

lemma dg_unit {t : ℝ} (ht : t ≠ 0) : IsUnit (diagonal (dv k r t)).det :=
  Matrix.isUnit_det_of_left_inverse (dg_left_inv ht)

def tn (n : ℕ) : ℝ := (n : ℝ) + 1

lemma tn_ne (n : ℕ) : tn n ≠ 0 := by unfold tn; positivity

lemma tn_top : Tendsto tn atTop atTop :=
  tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop

def dE (k r : ℕ) (n : ℕ) : GN k r ≃* GN k r :=
  conjE (diagonal (dv k r (tn n))) (dg_unit (tn_ne n))
    (fun g hg => by
      rw [dg_inv (tn_ne n)]
      exact diag_conj_n _ _ (dvi_dv (tn_ne n)) (dvi_form (tn_ne n)) (dv_form (tn_ne n)) hg)
    (fun g hg => by
      rw [dg_inv (tn_ne n)]
      exact diag_conj_n _ _ (dv_dvi (tn_ne n)) (dv_form (tn_ne n)) (dvi_form (tn_ne n)) hg)

lemma dE_val (n : ℕ) (g : GN k r) :
    (dE k r n g).val = diagonal (dvi k r (tn n)) * g.val * diagonal (dv k r (tn n)) := by
  rw [dE, conjE_val, dg_inv (tn_ne n)]

lemma dE_cont (n : ℕ) : Continuous (dE k r n) := conjE_cont _ _ _ _

lemma dE_symm_cont (n : ℕ) : Continuous (dE k r n).symm := conjE_symm_cont _ _ _ _

lemma dE_tendsto (hB : NWtUpper) (g : GN k r) : Tendsto (fun n => dE k r n g) atTop (𝓝 1) := by
  rw [Grp.emb.isInducing.tendsto_nhds_iff]
  have hv : (Grp.val ∘ fun n => dE k r n g) =
      fun n => diagonal (dvi k r (tn n)) * g.val * diagonal (dv k r (tn n)) := by
    funext n
    exact dE_val n g
  rw [hv, Grp.val_one]
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have hent : ∀ n, (diagonal (dvi k r (tn n)) * g.val * diagonal (dv k r (tn n))) i j =
      g.val i j * ((tn n ^ (wt k r j - wt k r i) : ℝ) : ℂ) := by
    intro n
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    unfold dv dvi
    rw [← neg_add_eq_sub, zpow_add₀ (tn_ne n)]
    push_cast
    ring
  simp only [hent]
  by_cases hw : wt k r i ≤ wt k r j
  · rw [hB k r g.val g.mem i j hw]
    by_cases h : i = j
    · subst h
      simp only [sub_self, zpow_zero, Complex.ofReal_one, mul_one, Matrix.one_apply_eq]
      exact tendsto_const_nhds
    · simp only [if_neg h, zero_mul, Matrix.one_apply_ne h]
      exact tendsto_const_nhds
  · have h : i ≠ j := by
      intro e; subst e; exact hw le_rfl
    rw [Matrix.one_apply_ne h]
    have hlim : Tendsto (fun n => ((tn n ^ (wt k r j - wt k r i) : ℝ) : ℂ)) atTop (𝓝 0) := by
      have h1 := (tendsto_zpow_atTop_zero (by omega : wt k r j - wt k r i < 0)).comp tn_top
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
      rw [Complex.ofReal_zero] at h2
      exact h2
    have h3 := hlim.const_mul (g.val i j)
    rw [mul_zero] at h3
    exact h3

theorem mod_one (hB : NWtUpper) (g : GN k r) : Measure.modularCharacter g = 1 := by
  obtain ⟨K, hK, B, hBd⟩ := mod_bound (k := k) (r := r)
  have hpow : ∀ x : GN k r, ∀ p : ℕ, Measure.modularCharacter x ^ p ≤ B := by
    intro x p
    obtain ⟨n, hn⟩ := ((dE_tendsto hB (x ^ p)).eventually hK).exists
    have h1 := hBd _ hn
    rw [mod_auto (dE k r n) (dE_cont n) (dE_symm_cont n), map_pow] at h1
    exact h1
  have hle : ∀ x : GN k r, Measure.modularCharacter x ≤ 1 := by
    intro x
    by_contra hx
    push Not at hx
    obtain ⟨p, hp⟩ := pow_unbounded_of_one_lt B hx
    exact absurd (hpow x p) (not_le.mpr hp)
  have hprod : Measure.modularCharacter g * Measure.modularCharacter g⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  apply le_antisymm (hle g)
  calc (1 : ℝ≥0) = Measure.modularCharacter g * Measure.modularCharacter g⁻¹ := hprod.symm
    _ ≤ Measure.modularCharacter g * 1 := mul_le_mul_of_nonneg_left (hle g⁻¹) zero_le
    _ = Measure.modularCharacter g := mul_one _

theorem haar_right (hB : NWtUpper) (g : GN k r) :
    Measure.map (· * g) (Measure.haar : Measure (GN k r)) = Measure.haar := by
  rw [map_rmul, mod_one hB, one_smul]

def conjW (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hT : 0 < Tz k r z) (h : Mx k r)
    (hh : h ∈ UWset k r z) : GN k r ≃* GN k r :=
  conjE h (isUnit_of_uh hh.1) (fun g hg => ((subgroup_hypothesis_holds k r z 0 hz hT).2.2.2.2 h hh g hg).1)
    (fun g hg => by
      have := ((subgroup_hypothesis_holds k r z 0 hz hT).2.2.2.2 h⁻¹ ((uw_clsub z).inv_mem h hh) g hg).1
      rwa [Matrix.nonsing_inv_nonsing_inv h (isUnit_of_uh hh.1)] at this)

lemma conjW_cont (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hT : 0 < Tz k r z) (h : Mx k r)
    (hh : h ∈ UWset k r z) : Continuous (conjW z hz hT h hh) := conjE_cont _ _ _ _

lemma conjW_symm_cont (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hT : 0 < Tz k r z) (h : Mx k r)
    (hh : h ∈ UWset k r z) : Continuous (conjW z hz hT h hh).symm := conjE_symm_cont _ _ _ _

theorem haar_conj (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hT : 0 < Tz k r z) (h : Mx k r)
    (hh : h ∈ UWset k r z) :
    Measure.map (conjW z hz hT h hh) (Measure.haar : Measure (GN k r)) = Measure.haar := by
  have he := conjW_cont z hz hT h hh
  have hs := conjW_symm_cont z hz hT h hh
  obtain ⟨s, -, hEq⟩ := auto_scalar (conjW z hz hT h hh) he hs
  have hu := isUnit_of_uh hh.1
  have hW := uw_clsub (k := k) (r := r) z
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (1 : GN k r)
  let F : Mx k r × Mx k r → Mx k r := fun p => p.1 * p.2 * jinv p.1
  have hF : Continuous F := (continuous_fst.matrix_mul continuous_snd).matrix_mul (jinv_cont.comp continuous_fst)
  let K' : Set (GN k r) := Grp.val ⁻¹' (F '' ((UWset k r z : Set (Mx k r)) ×ˢ (Grp.val '' K)))
  have hK' : IsCompact K' :=
    Grp.emb.isCompact_preimage (((compactW z hz hT).prod (hK.image Grp.emb.continuous)).image hF)
  have memK' : ∀ y : GN k r, y ∈ K' ↔ ∃ h' ∈ UWset k r z, ∃ x ∈ K, y.val = h' * x.val * h'⁻¹ := by
    intro y
    constructor
    · rintro ⟨⟨h', v⟩, ⟨hh', x, hx, rfl⟩, hy⟩
      refine ⟨h', hh', x, hx, ?_⟩
      rw [jinv_eq hh'.1]
      exact hy.symm
    · rintro ⟨h', hh', x, hx, hy⟩
      refine ⟨(h', x.val), ⟨hh', x, hx, rfl⟩, ?_⟩
      show h' * x.val * jinv h' = y.val
      rw [← jinv_eq hh'.1, hy]
  have hKK : K ⊆ K' := by
    intro x hx
    rw [memK']
    refine ⟨1, hW.one_mem, x, hx, ?_⟩
    rw [inv_one, Matrix.one_mul, Matrix.mul_one]
  have hpre : (conjW z hz hT h hh) ⁻¹' K' = K' := by
    ext g
    rw [Set.mem_preimage, memK', memK']
    have e1 : h * h⁻¹ = 1 := Matrix.mul_nonsing_inv h hu
    constructor
    · rintro ⟨h', hh', x, hx, hy⟩
      have hy' : h⁻¹ * g.val * h = h' * x.val * h'⁻¹ := hy
      refine ⟨h * h', hW.mul_mem _ hh _ hh', x, hx, ?_⟩
      rw [Matrix.mul_inv_rev]
      calc g.val = (h * h⁻¹) * g.val * (h * h⁻¹) := by rw [e1, Matrix.one_mul, Matrix.mul_one]
        _ = h * (h⁻¹ * g.val * h) * h⁻¹ := by simp only [Matrix.mul_assoc]
        _ = h * (h' * x.val * h'⁻¹) * h⁻¹ := by rw [hy']
        _ = h * h' * x.val * (h'⁻¹ * h⁻¹) := by simp only [Matrix.mul_assoc]
    · rintro ⟨h', hh', x, hx, hy⟩
      refine ⟨h⁻¹ * h', hW.mul_mem _ (hW.inv_mem h hh) _ hh', x, hx, ?_⟩
      show h⁻¹ * g.val * h = h⁻¹ * h' * x.val * (h⁻¹ * h')⁻¹
      rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv h hu, hy]
      simp only [Matrix.mul_assoc]
  have hK0 : (Measure.haar : Measure (GN k r)) K' ≠ 0 :=
    (lt_of_lt_of_le (Measure.measure_pos_of_mem_nhds _ hKn) (measure_mono hKK)).ne'
  have hKt : (Measure.haar : Measure (GN k r)) K' ≠ ∞ := hK'.measure_lt_top.ne
  have ev := congrArg (fun ν : Measure (GN k r) => ν K') hEq
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at ev
  rw [Measure.map_apply he.measurable hK'.isClosed.measurableSet, hpre] at ev
  have hs1 : s = 1 := by
    have h2 : (s : ℝ≥0∞) * (Measure.haar : Measure (GN k r)) K' = 1 * (Measure.haar : Measure (GN k r)) K' := by
      rw [one_mul]; exact ev.symm
    exact ENNReal.coe_eq_one.mp ((ENNReal.mul_left_inj hK0 hKt).mp h2)
  rw [hEq, hs1, one_smul]

theorem nUnimod_core (hB : NWtUpper) (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μN : Measure (Mt k r))
    (hz : inWb k r z) (hT : 0 < Tz k r z) (hN : IsHaarOn (Nset k r) μN)
    (_hNc : ∀ K : Set (Mt k r), IsCompact K → μN K < ⊤) (h : Mx k r) (hh : h ∈ UWset k r z)
    (m₀ : Mx k r) (hm₀ : m₀ ∈ Nset k r) :
    μN.map (fun x : Mt k r => fun i j => (h⁻¹ * Matrix.of x * h * m₀) i j) = μN := by
  obtain ⟨c, -, -, hμ⟩ := n_unique μN hN
  have hΦ : Measurable (fun x : Mt k r => fun i j => (h⁻¹ * Matrix.of x * h * m₀) i j) := by
    have : Continuous (fun x : Mt k r => fun i j => (h⁻¹ * Matrix.of x * h * m₀) i j) := by
      show Continuous fun x : Mt k r => (h⁻¹ * Matrix.of x * h * m₀ : Mx k r)
      exact ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_mul continuous_const
    exact this.measurable
  have he := conjW_cont z hz hT h hh
  have hcomp : (fun x : Mt k r => fun i j => (h⁻¹ * Matrix.of x * h * m₀) i j) ∘ Grp.vt =
      Grp.vt ∘ (fun g : GN k r => conjW z hz hT h hh g * Grp.mk m₀ hm₀) := by
    funext g
    rfl
  have hψ : Measurable (fun g : GN k r => conjW z hz hT h hh g * Grp.mk m₀ hm₀) :=
    he.measurable.mul_const _
  have hsplit : (fun g : GN k r => conjW z hz hT h hh g * Grp.mk m₀ hm₀) =
      (· * Grp.mk m₀ hm₀) ∘ conjW z hz hT h hh := rfl
  rw [hμ, haarNm_eq, Measure.map_smul, Measure.map_map hΦ Grp.embt.continuous.measurable, hcomp,
    ← Measure.map_map Grp.embt.continuous.measurable hψ, hsplit,
    ← Measure.map_map (measurable_mul_const _) he.measurable, haar_conj z hz hT h hh, haar_right hB]

lemma wt_eq (i : Fin (2 * r + k + 1)) : wt k r i = NB.wt k r i := by
  unfold wt NB.wt
  split_ifs <;> push_cast <;> ring

theorem nilradical_weight_upper_block : NWtUpper := by
  intro k r m hm i j hw
  have h := NB.nset_upper hm i j (by rw [← wt_eq, ← wt_eq]; omega)
  rw [Matrix.sub_apply, Matrix.one_apply, sub_eq_zero] at h
  exact h

end WlocSk.HM

namespace WlocSk

theorem nilradical_unimodular_conj_invariant : NUnimod := fun k r z μN hz hT hN hNc h hh m₀ hm₀ =>
  HM.nUnimod_core HM.nilradical_weight_upper_block k r z μN hz hT hN hNc h hh m₀ hm₀

end WlocSk
