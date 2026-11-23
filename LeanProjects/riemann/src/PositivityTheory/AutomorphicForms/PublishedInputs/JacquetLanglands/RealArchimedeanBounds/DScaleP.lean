import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.ATrans
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.FinSupp

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.CentralScalingLemmas

def cb (K P1 P2 : ℝ) (n : ℕ) : ℝ := max (max 1 (K ^ n * P2)) (min 1 (P1 / K ^ n))⁻¹

theorem cb_pos (K P1 P2 : ℝ) (n : ℕ) : 0 < cb K P1 P2 n :=
  lt_of_lt_of_le one_pos (le_trans (le_max_left _ _) (le_max_left _ _))

theorem bal {ι : Type} [Fintype ι] [Nonempty ι] (a : ι → ℝ) {K P1 P2 : ℝ} (hK : 0 < K) (hP1 : 0 < P1)
    (ha : ∀ v, 0 < a v) (hb : ∀ v v', a v ≤ K * a v') (h1 : P1 ≤ ∏ v, a v) (h2 : ∏ v, a v ≤ P2) (v : ι) :
    (cb K P1 P2 (Fintype.card ι))⁻¹ ≤ a v ∧ a v ≤ cb K P1 P2 (Fintype.card ι) := by
  have hn : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
  have hKn : 0 < K ^ Fintype.card ι := pow_pos hK _
  have hup : a v ^ Fintype.card ι ≤ K ^ Fintype.card ι * P2 := by
    calc a v ^ Fintype.card ι = ∏ _v' : ι, a v := by rw [Finset.prod_const, Finset.card_univ]
      _ ≤ ∏ v' : ι, K * a v' := Finset.prod_le_prod (fun _ _ => (ha v).le) fun v' _ => hb v v'
      _ = K ^ Fintype.card ι * ∏ v', a v' := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      _ ≤ K ^ Fintype.card ι * P2 := mul_le_mul_of_nonneg_left h2 hKn.le
  have hlo : P1 / K ^ Fintype.card ι ≤ a v ^ Fintype.card ι := by
    rw [div_le_iff₀ hKn]
    calc P1 ≤ ∏ v', a v' := h1
      _ ≤ ∏ _v' : ι, K * a v := Finset.prod_le_prod (fun v' _ => (ha v').le) fun v' _ => hb v' v
      _ = a v ^ Fintype.card ι * K ^ Fintype.card ι := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const, Finset.card_univ, mul_comm]
  have hm : 0 < min 1 (P1 / K ^ Fintype.card ι) := lt_min one_pos (div_pos hP1 hKn)
  have hmv : min 1 (P1 / K ^ Fintype.card ι) ≤ a v := by
    rcases le_total (a v) 1 with h | h
    · exact le_trans (min_le_right _ _) (le_trans hlo (pow_le_of_le_one (ha v).le h hn))
    · exact le_trans (min_le_left _ _) h
  refine ⟨le_trans (inv_le_of_inv_le₀ hm (le_max_right _ _)) hmv, ?_⟩
  refine le_trans ?_ (le_max_left _ _)
  rcases le_total (a v) 1 with h | h
  · exact le_trans h (le_max_left _ _)
  · exact le_trans (le_self_pow₀ h hn) (le_trans hup (le_max_right _ _))

variable {F : Type} [Field F] [NumberField F]

def good (N : ℕ) (A : GF F) : Prop := ∀ i j, (N : Af F) * A.val i j ∈ Ohat F

theorem good_mul {a b : ℕ} {A B : GF F} (hA : good a A) (hB : good b B) : good (a * b) (A * B) := by
  intro i j
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Nat.cast_mul]
  have e : (a : Af F) * b * (A.val i 0 * B.val 0 j + A.val i 1 * B.val 1 j) =
      (a * A.val i 0) * (b * B.val 0 j) + (a * A.val i 1) * (b * B.val 1 j) := by ring
  rw [e]
  exact add_mem (mul_mem (hA i 0) (hB 0 j)) (mul_mem (hA i 1) (hB 1 j))

theorem good_dvd {a b : ℕ} {A : GF F} (hA : good a A) (h : a ∣ b) : good b A := by
  obtain ⟨c, rfl⟩ := h
  intro i j
  rw [Nat.cast_mul, mul_comm (a : Af F), mul_assoc]
  exact mul_mem (natCast_mem _ c) (hA i j)

omit [NumberField F] in
theorem scal_center (s : Fˣ) : Matrix.GeneralLinearGroup.scalar (Fin 2) s ∈ Subgroup.center (GL (Fin 2) F) :=
  Subgroup.mem_center_iff.2 fun g => Units.ext (Matrix.scalar_commute (n := Fin 2) (s : F) (fun _ => Commute.all _ _) g.val).symm.eq

theorem jF_scalar (s : Fˣ) : jF F (Matrix.GeneralLinearGroup.scalar (Fin 2) s) = zc F (ratU F s) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jF, zc, ratU]

theorem det_jF (g : GL (Fin 2) F) :
    Matrix.GeneralLinearGroup.det (jF F g) = ratU F (Matrix.GeneralLinearGroup.det g) := by
  ext
  simp [jF, ratU, Matrix.det_fin_two]

theorem zc_val (a : (Af F)ˣ) (i j : Fin 2) : (zc F a).val i j = if i = j then (a : Af F) else 0 := by
  fin_cases i <;> fin_cases j <;> simp [zc]

theorem reAt_eq [IsTotallyReal F] (v : InfinitePlace F) (t : F) : reAt v t = sg v t := by
  rw [reAt, ← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v), Complex.ofReal_re]

end UpperTheory.Esk.CentralScalingLemmas

namespace UpperTheory.Esk

open CentralScalingLemmas in
theorem dScale : AMem → ACls → AUnit → DScale := by
  intro hM hC hU F _ _ _ c hc χ ω
  obtain ⟨hK0, -, hKc, hHc, hdet, hint, hN, hunit⟩ := hM F
  obtain ⟨T, hT⟩ := hC F
  obtain ⟨C0, hC0, hU'⟩ := hU F
  obtain ⟨x, rfl⟩ : ∃ x : GF F, (x : GF F ⧸ Hc c) = ω := QuotientGroup.mk_surjective ω
  obtain ⟨N1, hN1, hx1⟩ := hN x
  obtain ⟨N2, hN2, hx2⟩ := hN x⁻¹
  choose Nf hNf0 hNf using hN
  have hzK : ∀ a : (Af F)ˣ, (a : Af F) ∈ Ohat F → ((a⁻¹ : (Af F)ˣ) : Af F) ∈ Ohat F → zc F a ∈ K0 F := by
    intro a h1 h2
    refine (hK0 _).2 ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [zc_val]; split_ifs
      · exact h1
      · exact zero_mem _
    · rw [← map_inv, zc_val]; split_ifs
      · exact h2
      · exact zero_mem _
  refine ⟨N1 * (∏ r ∈ T, Nf (zc F r)) * N2,
    cb (C0 ^ 2) (∑ r ∈ T, absF (Matrix.GeneralLinearGroup.det (zc F r)))⁻¹
      (∑ r ∈ T, (absF (Matrix.GeneralLinearGroup.det (zc F r)))⁻¹) (Fintype.card (InfinitePlace F)), ?_, cb_pos _ _ _ _, ?_⟩
  · exact Nat.mul_ne_zero (Nat.mul_ne_zero hN1 (Finset.prod_ne_zero_iff.2 fun r _ => hNf0 _)) hN2
  intro γ hγ
  induction γ using QuotientGroup.induction_on with
  | H γ₀ =>
  have h1 : x⁻¹ * (jF F γ₀ * x) ∈ Hc c := by
    have e : ((jF F γ₀ * x : GF F) : GF F ⧸ Hc c) = (x : GF F ⧸ Hc c) := hγ
    have := inv_mem (QuotientGroup.eq.1 e)
    convert this using 1
    group
  obtain ⟨k, hk, z, hkz⟩ := (hHc c _).1 h1
  obtain ⟨y, u, r, hr, hu, hz⟩ := hT z
  set d : F := γ₀.val.det * ((y⁻¹ : Fˣ) : F) ^ 2 with hd
  have hd0 : d ≠ 0 := mul_ne_zero γ₀.det_ne_zero (pow_ne_zero _ (Units.ne_zero _))
  obtain ⟨ε, hε0, hεi, hεi', hεb⟩ := hU' (fun v => Real.sqrt (abs (sg v d)))
    (fun v => (Real.sqrt_pos.2 (abs_pos.2 ((map_ne_zero (sg v)).2 hd0))).ne')
  obtain ⟨g, hg⟩ : ∃ g : GL (Fin 2) F, g = γ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (y⁻¹ * Units.mk0 ε hε0) := ⟨_, rfl⟩
  have hK' : k * zc F (u * ratU F (Units.mk0 ε hε0)) ∈ K0 F := by
    refine mul_mem (hKc c hk) ?_
    rw [map_mul]
    refine mul_mem (hunit u hu).1 (hzK _ ?_ ?_)
    · exact (hint ε).1 hεi
    · rw [← map_inv]
      simpa [ratU] using (hint ε⁻¹).1 hεi'
  have hconj : x⁻¹ * (jF F g * x) = (k * zc F (u * ratU F (Units.mk0 ε hε0))) * zc F r := by
    have hjγ : jF F γ₀ = x * (k * zc F z) * x⁻¹ := by rw [← hkz]; group
    have hcomm := Subgroup.mem_center_iff.1 (zc_center (ratU F (y⁻¹ * Units.mk0 ε hε0))) x
    have hzS : z * ratU F (y⁻¹ * Units.mk0 ε hε0) = r * (u * ratU F (Units.mk0 ε hε0)) := by
      rw [hz, map_mul, map_inv]
      rw [show ratU F y * r * u * ((ratU F y)⁻¹ * ratU F (Units.mk0 ε hε0)) =
        (ratU F y * (ratU F y)⁻¹) * (r * (u * ratU F (Units.mk0 ε hε0))) by ac_rfl, mul_inv_cancel, one_mul]
    calc x⁻¹ * (jF F g * x)
        = x⁻¹ * (x * (k * zc F z) * x⁻¹ * zc F (ratU F (y⁻¹ * Units.mk0 ε hε0)) * x) := by
          rw [hg, map_mul, jF_scalar, hjγ]
      _ = x⁻¹ * (x * (k * zc F z) * x⁻¹ * (x * zc F (ratU F (y⁻¹ * Units.mk0 ε hε0)))) := by
          rw [mul_assoc _ (zc F _) x, ← hcomm]
      _ = k * (zc F z * zc F (ratU F (y⁻¹ * Units.mk0 ε hε0))) := by group
      _ = k * zc F (r * (u * ratU F (Units.mk0 ε hε0))) := by rw [← map_mul, hzS]
      _ = k * zc F (u * ratU F (Units.mk0 ε hε0)) * zc F r := by rw [mul_comm r, map_mul, mul_assoc]
  have hjg : jF F g = x * ((k * zc F (u * ratU F (Units.mk0 ε hε0))) * zc F r) * x⁻¹ := by
    rw [← hconj]; group
  refine ⟨g, ?_, fun i j => ?_, ?_⟩
  · rw [hg, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 (scal_center _), mul_one]
  ·
    have hgood : good (N1 * 1 * Nf (zc F r) * N2) (jF F g) := by
      rw [hjg, ← mul_assoc x]
      refine good_mul (good_mul (good_mul hx1 ?_) (hNf _)) hx2
      intro i j
      rw [Nat.cast_one, one_mul]
      exact ((hK0 _).1 hK').1 i j
    have hg2 := good_dvd (b := N1 * (∏ r ∈ T, Nf (zc F r)) * N2) hgood (by
      rw [mul_one]
      exact Nat.mul_dvd_mul (Nat.mul_dvd_mul_left _ (Finset.dvd_prod_of_mem _ hr)) dvd_rfl) i j
    refine (hint _).2 ?_
    rw [map_mul, map_natCast]
    exact hg2
  ·
    have hV : ∀ r' : (Af F)ˣ, 0 < absF (Matrix.GeneralLinearGroup.det (zc F r')) := fun r' => (Hm.absf F).1 _
    have habs : absF (ratU F (Matrix.GeneralLinearGroup.det g)) = absF (Matrix.GeneralLinearGroup.det (zc F r)) := by
      rw [← det_jF, hjg, map_mul, map_mul, map_inv, mul_comm (Matrix.GeneralLinearGroup.det x), mul_assoc,
        mul_inv_cancel, mul_one, map_mul, (Hm.absf F).2.1, (Hm.absf F).2.2.1 _ fun w => (hdet _ hK' w).1, one_mul]
    have hprod : ∏ v, |sg v g.val.det| = (absF (Matrix.GeneralLinearGroup.det (zc F r)))⁻¹ := by
      have := (Hm.absf F).2.2.2 (Matrix.GeneralLinearGroup.det g)
      have e : ∀ v, |reAt v ((Matrix.GeneralLinearGroup.det g : Fˣ) : F)| = |sg v g.val.det| := fun v => by
        rw [reAt_eq, Matrix.GeneralLinearGroup.val_det_apply]
      simp only [e] at this
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← habs]
      exact this
    have hdg : g.val.det = d * ε ^ 2 := by
      rw [hg, Units.val_mul, Matrix.det_mul, hd]
      simp [Matrix.det_fin_two]
      ring
    have ha : ∀ v, |sg v g.val.det| = |sg v ε * Real.sqrt (abs (sg v d))| ^ 2 := by
      intro v
      rw [hdg, map_mul, map_pow, abs_mul, sq_abs, mul_pow, Real.sq_sqrt (abs_nonneg _), abs_pow, sq_abs, mul_comm]
    intro v
    refine bal (fun v => |sg v g.val.det|) (pow_pos hC0 2) ?_ ?_ ?_ ?_ ?_ v
    · exact inv_pos.2 (lt_of_lt_of_le (hV r) (Finset.single_le_sum (fun r' _ => (hV r').le) hr))
    · intro v
      exact abs_pos.2 ((map_ne_zero (sg v)).2 g.det_ne_zero)
    · intro v v'
      rw [ha, ha, ← mul_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hεb v v') 2
    · rw [hprod]
      exact inv_anti₀ (hV r) (Finset.single_le_sum (fun r' _ => (hV r').le) hr)
    · rw [hprod]
      exact Finset.single_le_sum (fun r' _ => (inv_pos.2 (hV r')).le) hr

end UpperTheory.Esk
