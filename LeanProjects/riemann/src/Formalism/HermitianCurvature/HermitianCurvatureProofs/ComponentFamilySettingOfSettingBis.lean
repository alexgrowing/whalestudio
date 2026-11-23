import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings

namespace Formalism.FourierDecayAlt.P.PBD

open Formalism.FourierDecayAlt NumberField MeasureTheory Formalism.QuantumDeterminants
open scoped Matrix

section pts

theorem toStd_append' (r : ℕ) (g : ℝ) (c : ℂ) : ∀ (h : C.LPt) (b : ℕ),
    D.toStd r g b (h ++ [(1, c)]) = D.toStd r g b h ++
      [(1, (((g / (2 * Real.pi)) ^ S6.nuBlock r ((b + D.ptSize h : ℕ) : ℤ) ((1 : ℕ) : ℤ) : ℝ) : ℂ) * c)]
  | [], b => by simp [D.toStd, D.ptSize]
  | (s, t) :: rest, b => by
    have ih := toStd_append' r g c rest (b + s)
    simp only [List.cons_append, D.toStd, ih, D.ptSize, List.map_cons, List.sum_cons, add_assoc]

theorem toStd_size' (r : ℕ) (g : ℝ) : ∀ (p : C.LPt) (b : ℕ), D.ptSize (D.toStd r g b p) = D.ptSize p
  | [], _ => rfl
  | (s, t) :: rest, b => by
    have ih := toStd_size' r g rest (b + s)
    simp only [D.ptSize, D.toStd, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]

theorem toStd_ok_iff (r : ℕ) (g : ℝ) (hg : 0 < g) : ∀ (p : C.LPt) (b : ℕ),
    (∀ x ∈ D.toStd r g b p, 1 ≤ x.1 ∧ x.2 ≠ 0) ↔ ∀ x ∈ p, 1 ≤ x.1 ∧ x.2 ≠ 0
  | [], _ => by simp [D.toStd]
  | (s, t) :: rest, b => by
    have ih := toStd_ok_iff r g hg rest (b + s)
    have hne : ((((g / (2 * Real.pi)) ^ S6.nuBlock r b s : ℝ) : ℂ) * Complex.I ^ (s - 1)) ≠ 0 := by
      refine mul_ne_zero ?_ (pow_ne_zero _ Complex.I_ne_zero)
      have : 0 < (g / (2 * Real.pi)) ^ S6.nuBlock r b s := zpow_pos (by positivity) _
      exact_mod_cast this.ne'
    simp only [D.toStd, List.mem_cons, forall_eq_or_imp]
    rw [ih]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, fun ht => h2 (by rw [ht, mul_zero])⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, mul_ne_zero hne h2⟩, h3⟩

theorem isLocPt_toStd_iff (r : ℕ) (g : ℝ) (hg : 0 < g) (p : C.LPt) (b i : ℕ) :
    D.IsLocPt (D.toStd r g b p) i ↔ D.IsLocPt p i := by
  unfold D.IsLocPt
  rw [toStd_ok_iff r g hg p b, toStd_size']

theorem bSt_append_one (κ : ℝ) (h : C.LPt) (c : ℂ) : D.bSt κ (h ++ [(1, c)]) = D.bSt κ h := by
  simp [D.bSt]

theorem bSt_pos' (κ : ℝ) (hκ : 0 < κ) (p : C.LPt) : 0 < D.bSt κ p := by
  unfold D.bSt
  refine List.prod_pos fun x hx => ?_
  obtain ⟨a, _, rfl⟩ := List.mem_map.1 hx
  exact Finset.prod_pos fun m _ => zpow_pos (div_pos (zpow_pos hκ _) Real.pi_pos) _

theorem rd_pos' (E : Type) [Field E] [NumberField E] : 0 < S6.rd E := by
  unfold S6.rd
  refine Real.rpow_pos_of_pos ?_ _
  exact_mod_cast abs_pos.2 (discr_ne_zero E)

end pts

section weights

theorem weight_product_append (k r : ℕ) (GG : ℝ) (fr : ℕ → ℕ → ℝ) (x : ℕ × ℂ) : ∀ (h : C.LPt) (b : ℕ),
    C.nAux k r GG fr b (h ++ [x]) = C.nAux k r GG fr b h * C.nAux k r GG fr (b + D.ptSize h) [x]
  | [], b => by simp [C.nAux, D.ptSize]
  | (s, t) :: rest, b => by
    have ih := weight_product_append k r GG fr x rest (b + s)
    simp only [List.cons_append, C.nAux, ih, D.ptSize, List.map_cons, List.sum_cons, add_assoc, mul_assoc]

theorem weight_product_indep_of_real_parameter (k r : ℕ) (GG GG' : ℝ) (fr : ℕ → ℕ → ℝ) : ∀ (h : C.LPt) (b : ℕ), 1 ≤ b →
    b + D.ptSize h ≤ r + 1 → C.nAux k r GG fr b h = C.nAux k r GG' fr b h
  | [], _, _, _ => by simp [C.nAux]
  | (s, t) :: rest, b, hb, hs => by
    simp only [D.ptSize, List.map_cons, List.sum_cons] at hs
    have ih := weight_product_indep_of_real_parameter k r GG GG' fr rest (b + s) (by omega) (by simp only [D.ptSize] at *; omega)
    simp only [C.nAux, ih]
    congr 1
    have : ¬ (b + s - 1 = r + 1 ∧ s = 1) := by
      rintro ⟨h1, h2⟩
      have : 0 ≤ (rest.map Prod.fst).sum := Nat.zero_le _
      omega
    rw [if_neg this, if_neg this]

theorem weight_product_pos_of_nonzero (k r : ℕ) (GG : ℝ) (fr : ℕ → ℕ → ℝ) (hfr : ∀ b s, 0 < fr b s) :
    ∀ (p : C.LPt) (b : ℕ), 1 ≤ b → b + D.ptSize p ≤ r + 1 → (∀ x ∈ p, 1 ≤ x.1 ∧ x.2 ≠ 0) →
      0 < C.nAux k r GG fr b p
  | [], _, _, _, _ => by simp [C.nAux]
  | (s, t) :: rest, b, hb, hs, h => by
    have h1 := h (s, t) (by simp)
    have ht : 0 < ‖t‖ := norm_pos_iff.2 h1.2
    simp only [D.ptSize, List.map_cons, List.sum_cons] at hs
    have ih := weight_product_pos_of_nonzero k r GG fr hfr rest (b + s) (by omega) (by simp only [D.ptSize]; omega)
      (fun y hy => h y (by simp [hy]))
    simp only [C.nAux]
    refine mul_pos ?_ ih
    have : ¬ (b + s - 1 = r + 1 ∧ s = 1) := by
      rintro ⟨h1, h2⟩
      have : 0 ≤ (rest.map Prod.fst).sum := Nat.zero_le _
      omega
    rw [if_neg this]
    exact zpow_pos (mul_pos (hfr b s) ht) _

end weights

section det

theorem ptEntry_app_lt (c : ℂ) : ∀ (H : C.LPt) (a b : ℕ), a < D.ptSize H → b < D.ptSize H →
    D.ptEntry (H ++ [(1, c)]) a b = D.ptEntry H a b
  | [], a, b, ha, _ => by simp [D.ptSize] at ha
  | (s, t) :: rest, a, b, ha, hb => by
    simp only [D.ptSize, List.map_cons, List.sum_cons] at ha hb
    simp only [List.cons_append, D.ptEntry]
    by_cases h1 : a < s ∧ b < s
    · rw [if_pos h1, if_pos h1]
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : s ≤ a ∧ s ≤ b
      · rw [if_pos h2, if_pos h2]
        exact ptEntry_app_lt c rest (a - s) (b - s) (by simp only [D.ptSize]; omega) (by simp only [D.ptSize]; omega)
      · rw [if_neg h2, if_neg h2]

theorem ptEntry_app_last (c : ℂ) : ∀ (H : C.LPt), D.ptEntry (H ++ [(1, c)]) (D.ptSize H) (D.ptSize H) = c
  | [] => by simp [D.ptSize, D.ptEntry]
  | (s, t) :: rest => by
    simp only [List.cons_append, D.ptEntry, D.ptSize, List.map_cons, List.sum_cons]
    have h0 : 0 ≤ (rest.map Prod.fst).sum := Nat.zero_le _
    by_cases hs : s = 0
    · subst hs
      simp only [lt_self_iff_false, false_and, if_false, zero_le, and_self, if_true, zero_add, Nat.sub_zero]
      have := ptEntry_app_last c rest
      simpa [D.ptSize] using this
    · rw [if_neg (by omega), if_pos (by omega)]
      have := ptEntry_app_last c rest
      simp only [D.ptSize] at this
      rwa [show s + (rest.map Prod.fst).sum - s = (rest.map Prod.fst).sum by omega]

theorem ptEntry_app_row (c : ℂ) : ∀ (H : C.LPt) (b : ℕ), b < D.ptSize H →
    D.ptEntry (H ++ [(1, c)]) (D.ptSize H) b = 0
  | [], b, hb => by simp [D.ptSize] at hb
  | (s, t) :: rest, b, hb => by
    simp only [D.ptSize, List.map_cons, List.sum_cons] at hb
    simp only [List.cons_append, D.ptEntry, D.ptSize, List.map_cons, List.sum_cons]
    by_cases h1 : s + (rest.map Prod.fst).sum < s ∧ b < s
    · omega
    · rw [if_neg h1]
      by_cases h2 : s ≤ s + (rest.map Prod.fst).sum ∧ s ≤ b
      · rw [if_pos h2]
        have := ptEntry_app_row c rest (b - s) (by simp only [D.ptSize]; omega)
        simp only [D.ptSize] at this
        rwa [show s + (rest.map Prod.fst).sum - s = (rest.map Prod.fst).sum by omega]
      · rw [if_neg h2]

theorem det_ptMatN_app (c : ℂ) (H : C.LPt) (n : ℕ) (hn : D.ptSize H = n) :
    (D.ptMatN (H ++ [(1, c)]) (n + 1)).det = c * (D.ptMatN H n).det ∧
      D.ptMatN (H ++ [(1, c)]) n = D.ptMatN H n := by
  subst hn
  have hsub : (D.ptMatN (H ++ [(1, c)]) (D.ptSize H + 1)).submatrix Fin.castSucc Fin.castSucc =
      D.ptMatN H (D.ptSize H) := by
    ext a b
    simp only [Matrix.submatrix_apply, D.ptMatN, Fin.coe_castSucc]
    exact ptEntry_app_lt c H a b a.isLt b.isLt
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_succ_row _ (Fin.last _), Finset.sum_eq_single (Fin.last _)]
    · simp only [Fin.val_last, Fin.succAbove_last]
      rw [hsub]
      simp only [D.ptMatN, Fin.val_last, ptEntry_app_last]
      simp
    · intro j _ hj
      have hj' : (j : ℕ) < D.ptSize H := by
        have := j.isLt
        have : (j : ℕ) ≠ D.ptSize H := fun h => hj (Fin.ext (by simp [h]))
        omega
      simp [D.ptMatN, ptEntry_app_row c H j hj']
    · simp
  · ext a b
    simp only [D.ptMatN]
    exact ptEntry_app_lt c H a b a.isLt b.isLt

theorem ptG_app (TT : ℝ) (c : ℂ) (H : C.LPt) (n : ℕ) (hn : D.ptSize H = n) :
    D.ptG TT n (H ++ [(1, c)]) = Complex.normSq (D.ptMatN H n).det * (Complex.normSq c - TT) := by
  obtain ⟨h1, h2⟩ := det_ptMatN_app c H n hn
  unfold D.ptG
  rw [h1, h2, Complex.normSq_mul]
  ring

end det

section main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem lpt_value_nonneg_of_pos_of_size_le (k r : ℕ) (GG : ℝ) (fr : ℕ → ℕ → ℝ) (hfr : ∀ b s, 0 < fr b s) :
    ∀ (p : C.LPt) (b : ℕ), 1 ≤ b → b + D.ptSize p ≤ r + 1 → 0 ≤ C.nAux k r GG fr b p
  | [], _, _, _ => by simp [C.nAux]
  | (s, t) :: rest, b, hb, hs => by
    simp only [D.ptSize, List.map_cons, List.sum_cons] at hs
    have ih := lpt_value_nonneg_of_pos_of_size_le k r GG fr hfr rest (b + s) (by omega) (by simp only [D.ptSize]; omega)
    simp only [C.nAux]
    refine mul_nonneg ?_ ih
    have : ¬ (b + s - 1 = r + 1 ∧ s = 1) := by
      rintro ⟨h1, h2⟩
      have : 0 ≤ (rest.map Prod.fst).sum := Nat.zero_le _
      omega
    rw [if_neg this]
    exact zpow_nonneg (mul_nonneg (hfr b s).le (norm_nonneg _)) _

theorem cutWord_of_adm (S : C.HidaSetting E Wp Wq) (hG : C.GridsOK S) (hC : KB.CutInside S) (w : S.W) (v : Fin S.f) :
    KB.CutWord (D.parOf S v) (S.l + 1) (w.1 v) := by
  have hA := w.2.1
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · have h1 := hA.1 v a a.isLt
    have hnode := (hG v).2.2.2.2.2
    apply hC v
    set x := (w.1 v)[(a : ℕ)]'a.isLt with hx
    have hget : (w.1 v).get a = x := by simp [hx]
    rw [hget]
    have hcut : ∀ Y ∈ (S.G.place (S.pl v)).cutI S.l, Y ∈ Set.Icc (S.cutLo v) (S.cutHi v) := by
      intro Y hY
      simp only [Sz.Cfg.cutI, Set.mem_setOf_eq] at hY
      simp only [C.HidaSetting.cutLo, C.HidaSetting.cutHi, Set.mem_Icc]
      constructor <;> linarith [hY.1, hY.2]
    by_cases hp : x.1
    · rw [if_pos hp] at h1
      have hy : (∃ a, x.2 ∈ S.grid v a) ∨ x.2 ∈ S.grid1 v := by
        rcases Finset.mem_union.1 h1 with h | h
        · exact Or.inl ⟨_, h⟩
        · exact Or.inr h
      exact hcut _ (hnode _ hy).1
    · rw [if_neg hp] at h1
      have hy : (∃ a, x.2 - 1 ∈ S.grid v a) ∨ x.2 - 1 ∈ S.grid1 v := by
        rcases Finset.mem_union.1 h1 with h | h
        · exact Or.inl ⟨_, h⟩
        · exact Or.inr h
      have := hcut _ (hnode _ hy).2.1
      simpa using this
  · have h2 := hA.2 v a b a.isLt b.isLt (fun h => hab (Fin.ext h)) 0 (by norm_num) (by norm_num)
    simpa using h2

theorem scal_id (A B : ℝ) (hA : 0 < A) (hB : 0 < B) (ν e : ℤ) :
    (B ^ (-ν) / ((A * B)⁻¹ ^ ν)) ^ (2 * e) / ((A * B)⁻¹ ^ ν) ^ 2 = B ^ (2 * ν) * A ^ (2 * ν * (e + 1)) := by
  have h1 : B ^ (-ν) / ((A * B)⁻¹ ^ ν) = A ^ ν := by
    rw [inv_zpow, div_inv_eq_mul, mul_zpow, zpow_neg]
    field_simp
  have h2 : ((A * B)⁻¹ ^ ν) ^ 2 = A ^ (-(2 * ν)) * B ^ (-(2 * ν)) := by
    rw [← zpow_natCast, ← zpow_mul, mul_inv, mul_zpow, ← zpow_neg_one, ← zpow_neg_one B, ← zpow_mul, ← zpow_mul]
    congr 2 <;> push_cast <;> ring
  rw [h1, h2, ← zpow_mul]
  rw [div_eq_mul_inv, mul_inv, ← zpow_neg, ← zpow_neg]
  simp only [neg_neg]
  rw [show 2 * ν * (e + 1) = ν * (2 * e) + 2 * ν by ring, zpow_add₀ hA.ne']
  ring

theorem gamLev_succ (k r : ℕ) (κ de : ℝ) (j : ℕ) (hj : j ≤ r) :
    D.GamLev k r κ de j =
      κ ^ (-(4 * ((r : ℤ) + 1 - ((j + 1 : ℕ) : ℤ)) * (C.Mlev k r (j + 1) - 1))) / de * D.GamLev k r κ de (j + 1) := by
  unfold D.GamLev
  have : Finset.Ioc j (r + 1) = insert (j + 1) (Finset.Ioc (j + 1) (r + 1)) := by
    ext x; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
  rw [this, Finset.prod_insert (by simp)]

theorem gamLev_pos (k r : ℕ) (κ de : ℝ) (hκ : 0 < κ) (hde : 0 < de) (i : ℕ) : 0 < D.GamLev k r κ de i := by
  unfold D.GamLev
  exact Finset.prod_pos fun l _ => div_pos (zpow_pos hκ _) hde

theorem hsInner_zero_left {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) : B.hsInner (0 : Wq →L[ℂ] Wp) A = 0 := by
  unfold B.hsInner B.hsVec
  have : (WithLp.toLp 2 fun i : Fin (Module.finrank ℂ Wq) => (0 : Wq →L[ℂ] Wp) (stdOrthonormalBasis ℂ Wq i)) = 0 := by
    simp; rfl
  rw [this, inner_zero_right]

theorem rrTop_zero {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (l0 : ℕ)
    (T : D.LevTower P.k P.r Wp Wq) (ν' : Fin (2 * P.r + P.k + 1) → ℂ) (m₀ : B.Mat P.k P.r)
    (Θ : Top.TopLift P.k P.r Wp Wq) (TP : Top.TypeProj P T.base.π T.base.z (m₀ *ᵥ ν')) (s : ℂ)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (H H' : C.LPt) (c : ℂ) (hH : D.ptSize H = P.r)
    (hc : Complex.normSq c ≤ Tz P.k P.r T.base.z * Tz P.k P.r T.base.z') :
    D.RRplace T s ν' m₀ (Top.topOf P l0 T ν' m₀ Θ TP) F (P.r + 1) w (H ++ [(1, c)]) H' = 0 := by
  have hv : ∀ F' : B.Mat P.k P.r → (Wq →L[ℂ] Wp), D.vecV T.base ν' m₀ F' (H ++ [(1, c)]) = 0 := by
    intro F'
    unfold D.vecV
    rw [dif_neg]
    rintro ⟨-, hG⟩
    rw [ptG_app _ c H P.r hH] at hG
    have : Complex.normSq (D.ptMatN H P.r).det * (Complex.normSq c - Tz P.k P.r T.base.z * Tz P.k P.r T.base.z') ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) (by linarith)
    linarith
  unfold D.RRplace
  split_ifs with h1 h2 h3 h4
  · omega
  · rw [hv, hsInner_zero_left]
  · unfold Top.topOf
    refine Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun ρ _ => ?_
    rw [hv, ContinuousLinearMap.comp_zero, hsInner_zero_left, mul_zero]
  · rfl
  · rfl

def StdInt {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ j, j ≤ P.r → ∀ w, KB.CutWord P p.l0 w → ∀ h h' : C.LPt, D.IsLocPt h j → D.IsLocPt h' j →
    ∃ φ : ℂ → ℂ, Continuous φ ∧ (∃ Cφ : ℝ, ∀ c, ‖φ c‖ ≤ Cφ * ((1 + ‖c‖) ^ 3)⁻¹) ∧
      (∀ c : ℂ, c ≠ 0 → φ c = (KB.levW P (j + 1) c : ℂ) * p.RR F (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)])) ∧
      ∫ c, φ c = p.RR F j w h h'

def FrameInt : Prop :=
  ∀ (Cb Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    KB.IsLeadingFormSetting Cb Cc S p f χ A₀ → KB.CutInside S →
    (∀ v ε, 0 < ε → StdInt (p v) (D.cutF (p v).T.base χ (f v) ε)) →
    KB.IntAll S

theorem frameInt : FrameInt := by
  intro Cb Cc E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB hC hstd v
  obtain ⟨hg1, hg2, -, -, -, -, -, -, -, -, hGr, -, -, -, -, hv⟩ := hB
  obtain ⟨hl0, -, hpd, -, -⟩ := hv v
  intro ε hε i hi1 hir w h h' hsz hsz'
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hjr : j ≤ S.G.r := by omega
  simp only [Nat.add_sub_cancel] at hsz hsz' ⊢
  have hgpos : (0 : ℝ) < (S.g : ℝ) := by unfold C.HidaSetting.g; exact_mod_cast Nat.mul_pos hg1 hg2
  have hrd := rd_pos' E
  have hκ : 0 < D.kapG (S.g : ℝ) (S6.rd E) := by unfold D.kapG; positivity
  have hδ : 0 < D.deG (S.g : ℝ) (S6.rd E) := by unfold D.deG; positivity
  have hfr : ∀ b s, 0 < S.fr b s := fun b s => Real.rpow_pos_of_pos hrd _

  have hTT : Tz S.G.k S.G.r (p v).T.base.z * Tz S.G.k S.G.r (p v).T.base.z' = S.T * S.T' := by
    have h := S.hT v
    rw [hpd] at h
    rw [← h.1, ← h.2]
    rfl

  set RRs : ℕ → C.LPt → C.LPt → ℂ := fun i P Q => D.RRplace (p v).T (M.sgn (D.parOf S v) (S.l + 1)) (p v).ν'
      (p v).m₀ (Top.topOf (D.parOf S v) (S.l + 1) (p v).T (p v).ν' (p v).m₀ (p v).Θ (p v).TP)
      (D.cutF (p v).T.base χ (f v) ε) i (w.1 v) P Q with hRRs
  have hRR : ∀ i P Q, (p v).RR (D.cutF (p v).T.base χ (f v) ε) i (w.1 v) P Q = RRs i P Q := by
    intro i P Q
    simp only [KB.Pl.RR, hRRs, hl0]
  set nn : C.LPt → ℝ := fun P => C.nLoc S.G.k S.G.r S.fr
      (D.ptGG (Tz S.G.k S.G.r (p v).T.base.z * Tz S.G.k S.G.r (p v).T.base.z')) P with hnn
  set Γ : ℕ → ℝ := fun i => D.GamLev S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) i with hΓ
  set bS : C.LPt → ℝ := fun P => D.bSt (D.kapG (S.g : ℝ) (S6.rd E)) P with hbS
  have hgram : ∀ i P Q, S.gramLoc v ε i (w.1 v) P Q =
      ((√(nn P) * √(nn Q) : ℝ) : ℂ) * (((1 / (bS P * bS Q * Γ i)) : ℝ) : ℂ) *
        RRs i (D.toStd S.G.r (S.g : ℝ) 1 P) (D.toStd S.G.r (S.g : ℝ) 1 Q) := by
    intro i P Q
    unfold C.HidaSetting.gramLoc
    rw [hpd]
    simp only [D.componentFamilySetting_ofSetting, one_pow, mul_assoc, hnn, hΓ, hbS, hRRs]

  have hstd_app : ∀ (H : C.LPt) (c : ℂ), D.ptSize H = j → D.toStd S.G.r (S.g : ℝ) 1 (H ++ [(1, c)]) =
      D.toStd S.G.r (S.g : ℝ) 1 H ++
        [(1, ((((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock (S.G.r : ℤ) ((j + 1 : ℕ) : ℤ) ((1 : ℕ) : ℤ) : ℝ) : ℂ) * c)] := by
    intro H c hH
    rw [toStd_append', hH, show 1 + j = j + 1 by omega]
  set lam : ℝ := ((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock (S.G.r : ℤ) ((j + 1 : ℕ) : ℤ) ((1 : ℕ) : ℤ) with hlam
  have hlam_pos : 0 < lam := zpow_pos (by positivity) _
  set TT0 := Tz S.G.k S.G.r (p v).T.base.z * Tz S.G.k S.G.r (p v).T.base.z' with hTT0
  set xw : ℂ → ℝ := fun c => C.nAux S.G.k S.G.r (Complex.normSq c - TT0) S.fr (j + 1) [(1, c)] with hxw
  have hn_app : ∀ (H : C.LPt) (c : ℂ), D.ptSize H = j → nn (H ++ [(1, c)]) = nn H * xw c := by
    intro H c hH
    simp only [hnn, hxw, C.nLoc]
    rw [weight_product_append, hH, show 1 + j = j + 1 by omega]
    have hG : D.ptGG TT0 (H ++ [(1, c)]) = Complex.normSq c - TT0 := by simp [D.ptGG, D.ptLast]
    rw [hG, weight_product_indep_of_real_parameter _ _ _ (D.ptGG TT0 H) _ H 1 le_rfl (by omega)]
  have hn_nonneg : ∀ H, D.ptSize H = j → 0 ≤ nn H := fun H hH =>
    lpt_value_nonneg_of_pos_of_size_le _ _ _ _ hfr H 1 le_rfl (by omega)
  have hsq : ∀ c, √(nn (h ++ [(1, c)])) * √(nn (h' ++ [(1, c)])) = √(nn h) * √(nn h') * (√(xw c) * √(xw c)) := by
    intro c
    rw [hn_app h c hsz, hn_app h' c hsz', Real.sqrt_mul (hn_nonneg h hsz), Real.sqrt_mul (hn_nonneg h' hsz')]
    ring
  set Mj : ℤ := C.Mlev S.G.k S.G.r (j + 1) with hMj
  set ρ : ℝ := (S.fr (j + 1) 1 / lam) ^ (2 * (Mj - 2)) with hρ
  have hW : ∀ (H H' : C.LPt) (c : ℂ), D.ptSize H = j → c ≠ 0 →
      ((√(xw c) * √(xw c) : ℝ) : ℂ) * RRs (j + 1) (H ++ [(1, (lam : ℂ) * c)]) (H' ++ [(1, (lam : ℂ) * c)]) =
        ((ρ * KB.levW (D.parOf S v) (j + 1) ((lam : ℂ) * c) : ℝ) : ℂ) *
          RRs (j + 1) (H ++ [(1, (lam : ℂ) * c)]) (H' ++ [(1, (lam : ℂ) * c)]) := by
    intro H H' c hH hc
    by_cases hjt : j = S.G.r
    · have hnu : S6.nuBlock (S.G.r : ℤ) ((j + 1 : ℕ) : ℤ) ((1 : ℕ) : ℤ) = 0 := by
        unfold S6.nuBlock; rw [hjt]; push_cast; ring
      have hlam1 : lam = 1 := by rw [hlam, hnu, zpow_zero]
      have hfr1 : S.fr (j + 1) 1 = 1 := by
        unfold C.HidaSetting.fr
        have : ((S6.nuBlock (S.G.r : ℤ) (Nat.cast (j + 1)) (Nat.cast 1) : ℤ) : ℝ) = 0 := by
          unfold S6.nuBlock; rw [hjt]; push_cast; ring
        rw [this]; simp
      have hρ1 : ρ = 1 := by rw [hρ, hlam1, hfr1]; simp
      have hx : xw c = (Complex.normSq c - TT0) ^ (S.G.k - 1) := by
        simp only [hxw, C.nAux]
        rw [if_pos (by constructor <;> first | trivial | omega), mul_one]
      have hlev : KB.levW (D.parOf S v) (j + 1) ((lam : ℂ) * c) = B2.zWeight S.G.k S.T S.T' c := by
        rw [hlam1, Complex.ofReal_one, one_mul]
        unfold KB.levW
        rw [if_pos (by simp [hjt])]
      rw [hρ1, hlev, one_mul, hx]
      by_cases hc2 : S.T * S.T' ≤ Complex.normSq c
      · rw [Real.mul_self_sqrt (pow_nonneg (by rw [hTT]; linarith) _)]
        unfold B2.zWeight
        rw [if_pos hc2, hTT]
      · have h0 : RRs (j + 1) (H ++ [(1, (lam : ℂ) * c)]) (H' ++ [(1, (lam : ℂ) * c)]) = 0 := by
          have := rrTop_zero (D.parOf S v) (S.l + 1) (p v).T (p v).ν' (p v).m₀ (p v).Θ (p v).TP
            (M.sgn (D.parOf S v) (S.l + 1)) (D.cutF (p v).T.base χ (f v) ε) (w.1 v) H (H' ++ [(1, (lam : ℂ) * c)])
            ((lam : ℂ) * c) (by rw [hH, hjt]) (by
              rw [hlam1, Complex.ofReal_one, one_mul]
              show Complex.normSq c ≤ TT0
              rw [hTT]; linarith)
          simp only [hRRs]
          rw [show j + 1 = (D.parOf S v).r + 1 by rw [hjt]]
          exact this
        rw [h0, mul_zero, mul_zero]
    · have hx : xw c = (S.fr (j + 1) 1 * ‖c‖) ^ (2 * (Mj - 2)) := by
        simp only [hxw, C.nAux]
        rw [if_neg (by omega), mul_one, hMj]
        congr 1
        simp only [Nat.add_sub_cancel, Nat.cast_one]
        ring
      have hxpos : 0 < xw c := by rw [hx]; exact zpow_pos (mul_pos (hfr _ _) (norm_pos_iff.2 hc)) _
      rw [Real.mul_self_sqrt hxpos.le]
      congr 2
      rw [hx, hρ]
      unfold KB.levW
      rw [if_neg (by simp only [D.parOf]; omega)]
      have hnorm : ‖(lam : ℂ) * c‖ = lam * ‖c‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hlam_pos.le]
      rw [hnorm, ← mul_zpow]
      congr 1
      field_simp

  have hloc_app : ∀ (H : C.LPt) (c : ℂ), D.ptSize H = j → D.IsLocPt (H ++ [(1, c)]) (j + 1) → D.IsLocPt H j :=
    fun H c hH h1 => ⟨fun b hb => h1.1 b (List.mem_append_left _ hb), hH⟩
  have hRRnl : ∀ i P Q, ¬ (D.IsLocPt P i ∧ D.IsLocPt Q i) →
      RRs i (D.toStd S.G.r (S.g : ℝ) 1 P) (D.toStd S.G.r (S.g : ℝ) 1 Q) = 0 := by
    intro i P Q hPQ
    simp only [hRRs]
    unfold D.RRplace
    rw [dif_neg]
    rwa [isLocPt_toStd_iff _ _ hgpos, isLocPt_toStd_iff _ _ hgpos]
  by_cases hloc : D.IsLocPt h j ∧ D.IsLocPt h' j
  · obtain ⟨hh, hh'⟩ := hloc
    have hH : D.IsLocPt (D.toStd S.G.r (S.g : ℝ) 1 h) j := (isLocPt_toStd_iff _ _ hgpos h 1 j).2 hh
    have hH' : D.IsLocPt (D.toStd S.G.r (S.g : ℝ) 1 h') j := (isLocPt_toStd_iff _ _ hgpos h' 1 j).2 hh'
    obtain ⟨φ, hφc, ⟨Cφ, hCφ⟩, hφ, hφint⟩ := hstd v ε hε j hjr (w.1 v)
      (by rw [hl0]; exact cutWord_of_adm S hGr hC w v) _ _ hH hH'
    set K : ℝ := √(nn h) * √(nn h') * (1 / (bS h * bS h' * Γ (j + 1))) * ρ with hK
    refine ⟨fun c => (K : ℂ) * φ ((lam : ℂ) * c), ?_, ?_, ?_, ?_⟩
    · exact continuous_const.mul (hφc.comp (continuous_const.mul continuous_id))
    · intro c hc
      have hlc : (lam : ℂ) * c ≠ 0 := mul_ne_zero (by exact_mod_cast hlam_pos.ne') hc
      have hWc := hW (D.toStd S.G.r (S.g : ℝ) 1 h) (D.toStd S.G.r (S.g : ℝ) 1 h') c
        (by rw [toStd_size']; exact hsz) hc
      simp only
      rw [hgram, hstd_app h c hsz, hstd_app h' c hsz', hsq, hφ _ hlc, hRR]
      simp only [hbS, bSt_append_one]
      simp only [← hbS]
      push_cast at hWc ⊢
      rw [hK]
      push_cast
      linear_combination (-((√(nn h) : ℂ) * (√(nn h') : ℂ) * (1 / ((bS h : ℂ) * (bS h' : ℂ) * (Γ (j + 1) : ℂ))))) * hWc
    · refine ⟨|K| * |Cφ| * (min 1 lam ^ 3)⁻¹, fun c => ?_⟩
      have hm : 0 < min 1 lam := lt_min one_pos hlam_pos
      have hnorm : ‖(lam : ℂ) * c‖ = lam * ‖c‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hlam_pos.le]
      have h1 : min 1 lam * (1 + ‖c‖) ≤ 1 + ‖(lam : ℂ) * c‖ := by
        rw [hnorm]
        have := min_le_left 1 lam; have := min_le_right 1 lam
        nlinarith [norm_nonneg c]
      have h2 : ((1 + ‖(lam : ℂ) * c‖) ^ 3)⁻¹ ≤ (min 1 lam ^ 3)⁻¹ * ((1 + ‖c‖) ^ 3)⁻¹ := by
        rw [← mul_inv, ← mul_pow]
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h1 3)
      have h3 := hCφ ((lam : ℂ) * c)
      have h4 : 0 ≤ ((1 + ‖(lam : ℂ) * c‖) ^ 3)⁻¹ := by positivity
      simp only
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |K| * ‖φ ((lam : ℂ) * c)‖ ≤ |K| * (|Cφ| * ((1 + ‖(lam : ℂ) * c‖) ^ 3)⁻¹) :=
            mul_le_mul_of_nonneg_left (h3.trans (mul_le_mul_of_nonneg_right (le_abs_self _) h4)) (abs_nonneg _)
        _ ≤ |K| * (|Cφ| * ((min 1 lam ^ 3)⁻¹ * ((1 + ‖c‖) ^ 3)⁻¹)) := by gcongr
        _ = |K| * |Cφ| * (min 1 lam ^ 3)⁻¹ * ((1 + ‖c‖) ^ 3)⁻¹ := by ring
    · have e1 : (fun c : ℂ => (K : ℂ) * φ ((lam : ℂ) * c)) = fun c => (K : ℂ) * φ (lam • c) := by
        funext c; rw [Complex.real_smul]
      rw [e1, integral_const_mul, Measure.integral_comp_smul, Complex.finrank_real_complex, hφint, hRR, hgram]

      have hfac := gamLev_succ S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) j hjr
      have hΓpos : 0 < Γ (j + 1) := gamLev_pos _ _ _ _ hκ hδ _
      have hbh : 0 < bS h := bSt_pos' _ hκ h
      have hbh' : 0 < bS h' := bSt_pos' _ hκ h'
      have hgl : (S.g : ℝ) / (2 * Real.pi) = (D.kapG (S.g : ℝ) (S6.rd E) * S6.rd E)⁻¹ := by
        unfold D.kapG; field_simp
      have hfrj : S.fr (j + 1) 1 = S6.rd E ^ (-(S6.nuBlock (S.G.r : ℤ) ((j + 1 : ℕ) : ℤ) ((1 : ℕ) : ℤ))) := by
        unfold C.HidaSetting.fr
        rw [← Real.rpow_intCast]
        push_cast
        ring_nf
      have hkey : ρ * (lam ^ 2)⁻¹ = S6.rd E ^ (2 * S6.nuBlock (S.G.r : ℤ) ((j + 1 : ℕ) : ℤ) ((1 : ℕ) : ℤ)) *
          D.kapG (S.g : ℝ) (S6.rd E) ^ (4 * ((S.G.r : ℤ) + 1 - ((j + 1 : ℕ) : ℤ)) * (C.Mlev S.G.k S.G.r (j + 1) - 1)) := by
        rw [hρ, hfrj, hlam, hgl, ← div_eq_mul_inv, scal_id _ _ hκ hrd]
        congr 1
        congr 1
        unfold S6.nuBlock
        rw [hMj]
        push_cast
        ring
      have hscal : K * |(lam ^ 2)⁻¹| = KB.dlB S (j + 1) 1 * (√(nn h) * √(nn h') * (1 / (bS h * bS h' * Γ j))) := by
        rw [abs_of_pos (by positivity)]
        have hΓj : Γ j = _ := hfac
        rw [hΓj]
        have e2 : K * (lam ^ 2)⁻¹ = √(nn h) * √(nn h') * (1 / (bS h * bS h' * Γ (j + 1))) * (ρ * (lam ^ 2)⁻¹) := by
          rw [hK]; ring
        rw [e2, hkey]
        unfold KB.dlB
        have hΓ1 : Γ (j + 1) = D.GamLev S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) (j + 1) :=
          rfl
        rw [← hΓ1, zpow_neg]
        have hκX := zpow_pos hκ (4 * ((S.G.r : ℤ) + 1 - ((j + 1 : ℕ) : ℤ)) * (C.Mlev S.G.k S.G.r (j + 1) - 1))
        field_simp
      rw [Complex.real_smul]
      push_cast
      have hs := congrArg (fun x : ℝ => (x : ℂ)) hscal
      push_cast at hs
      linear_combination (RRs j (D.toStd S.G.r (S.g : ℝ) 1 h) (D.toStd S.G.r (S.g : ℝ) 1 h')) * hs
  · refine ⟨fun _ => 0, continuous_const, fun c hc => ?_, ⟨0, fun c => by simp⟩, ?_⟩
    · rw [hgram, hRRnl]
      · simp
      · rintro ⟨h1, h2⟩
        exact hloc ⟨hloc_app h c hsz h1, hloc_app h' c hsz' h2⟩
    · rw [hgram, hRRnl _ _ _ hloc]
      simp

end main

end Formalism.FourierDecayAlt.P.PBD

theorem Formalism.FourierDecayAlt.P.frame_integrability : Formalism.FourierDecayAlt.P.PBD.FrameInt := Formalism.FourierDecayAlt.P.PBD.frameInt
