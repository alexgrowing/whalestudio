import Formalism.HermitianCurvature.HermitianCurvatureProofs.PtSizeToStd

namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt MeasureTheory NumberField

noncomputable section

theorem isLocalPoint_to_standard (r : ℕ) (g : ℝ) (hg : 0 < g) :
    ∀ (b : ℕ) (P : C.LPt), (∀ x ∈ P, 1 ≤ x.1 ∧ x.2 ≠ 0) → ∀ x ∈ D.toStd r g b P, 1 ≤ x.1 ∧ x.2 ≠ 0
  | _, [] => by simp [D.toStd]
  | b, (s, t) :: rest => by
    intro h x hx
    simp only [D.toStd, List.mem_cons] at hx
    rcases hx with rfl | hx
    · have h1 := h (s, t) (by simp)
      refine ⟨h1.1, ?_⟩
      have hq : (0 : ℝ) < g / (2 * Real.pi) := div_pos hg (by positivity)
      refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ Complex.I_ne_zero)) h1.2
      exact Complex.ofReal_ne_zero.mpr (zpow_pos hq _).ne'
    · exact isLocalPoint_to_standard r g hg (b + s) rest (fun y hy => h y (by simp [hy])) x hx

theorem isLocPt_toStd (r : ℕ) (g : ℝ) (hg : 0 < g) (P : C.LPt) (i : ℕ) (hP : D.IsLocPt P i) :
    D.IsLocPt (D.toStd r g 1 P) i :=
  ⟨isLocalPoint_to_standard r g hg 1 P hP.1, by rw [ptSize_toStd]; exact hP.2⟩

theorem weight_product_append (k r : ℕ) (GG : ℝ) (fr : ℕ → ℕ → ℝ) :
    ∀ (b : ℕ) (P Q : C.LPt), C.nAux k r GG fr b (P ++ Q) = C.nAux k r GG fr b P * C.nAux k r GG fr (b + D.ptSize P) Q
  | b, [], Q => by simp [C.nAux, D.ptSize]
  | b, (s, t) :: rest, Q => by
    simp only [List.cons_append, C.nAux]
    rw [weight_product_append k r GG fr (b + s) rest Q, ← mul_assoc]
    have e : b + D.ptSize ((s, t) :: rest) = b + s + D.ptSize rest := by
      simp only [D.ptSize, List.map_cons, List.sum_cons]; ring
    rw [e]

theorem weight_product_germ_indep (k r : ℕ) (GG GG' : ℝ) (fr : ℕ → ℕ → ℝ) :
    ∀ (b : ℕ) (P : C.LPt), b + D.ptSize P ≤ r + 1 → C.nAux k r GG fr b P = C.nAux k r GG' fr b P
  | b, [], _ => by simp [C.nAux]
  | b, (s, t) :: rest, h => by
    simp only [C.nAux]
    have hs : D.ptSize ((s, t) :: rest) = s + D.ptSize rest := by simp [D.ptSize]
    rw [hs] at h
    have hc : ¬ (b + s - 1 = r + 1 ∧ s = 1) := by omega
    rw [if_neg hc, if_neg hc, weight_product_germ_indep k r GG GG' fr (b + s) rest (by omega)]

theorem bSt_append (κ : ℝ) (P Q : C.LPt) : D.bSt κ (P ++ Q) = D.bSt κ P * D.bSt κ Q := by
  simp [D.bSt, List.map_append, List.prod_append]

theorem norm_fs (r : ℕ) (g : ℝ) (hg : 0 < g) (b s : ℕ) (t : ℂ) :
    ‖GermFibreKernels.fs r g b s t‖ = (g / (2 * Real.pi)) ^ S6.nuBlock (r : ℤ) (b : ℤ) (s : ℤ) * ‖t‖ := by
  unfold GermFibreKernels.fs
  have hq : (0 : ℝ) < g / (2 * Real.pi) := div_pos hg (by positivity)
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (zpow_pos hq _)]

section loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem sizeAt_nonneg (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (a : List C.Letter) : 0 ≤ S.sizeAt v a := by
  unfold C.HidaSetting.sizeAt
  exact List.prod_nonneg fun x hx => by
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    exact abs_nonneg _

theorem rd_pos' : 0 < S6.rd E := GermRealisation.rd_pos E

theorem gamLev_nonneg (S : C.HidaSetting E Wp Wq) (i : ℕ) :
    0 ≤ D.GamLev S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) i := by
  have hrd := (rd_pos' (E := E)).le
  have hg : (0 : ℝ) ≤ (S.g : ℝ) := Nat.cast_nonneg _
  unfold D.GamLev
  refine Finset.prod_nonneg fun l _ => div_nonneg (zpow_nonneg ?_ _) ?_
  · unfold D.kapG; positivity
  · unfold D.deG; positivity

theorem gamLev_zero (S : C.HidaSetting E Wp Wq) (i : ℕ) (hi : i ≤ S.G.r) (hg : (S.g : ℝ) = 0) :
    D.GamLev S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) i = 0 := by
  unfold D.GamLev
  refine Finset.prod_eq_zero (i := S.G.r + 1) (by simp; omega) ?_
  simp [D.deG, hg]

theorem gNSetC_main (S : C.HidaSetting E Wp Wq) [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (i : ℕ)
    (hi : i ≤ S.G.r) (a : List C.Letter) (P Q : C.LPt) (hP : D.IsLocPt P i) (hQ : D.IsLocPt Q i) :
    KB.gN (PBL.setC S p F) v ε i a P Q =
      ((lamP S v a i P * lamP S v a i Q : ℝ) : ℂ) *
        D.formLev (p v).T (M.sgn (D.parOf S v) (p v).l0) ⟨i, by have e : (D.parOf S v).r = S.G.r := rfl; omega⟩ a
          (KB.slv (p v).T (F v ε) i hi a (D.toStd S.G.r (S.g : ℝ) 1 P) (by
            rw [← hP.2]; exact FormNormSumIdentities.ptSize_toStd S.G.r (S.g : ℝ) 1 P))
          (KB.slv (p v).T (F v ε) i hi a (D.toStd S.G.r (S.g : ℝ) 1 Q) (by
            rw [← hQ.2]; exact FormNormSumIdentities.ptSize_toStd S.G.r (S.g : ℝ) 1 Q)) := by
  have hsz : 0 ≤ S.sizeAt v a := sizeAt_nonneg S v a
  have hΓ := gamLev_nonneg S i
  have e1 : KB.gN (PBL.setC S p F) v ε i a P Q =
      ((√(C.nLoc S.G.k S.G.r S.fr (S.pd v).G P) * √(C.nLoc S.G.k S.G.r S.fr (S.pd v).G Q) : ℝ) : ℂ) *
        PBL.rrC S p F v ε i a P Q / (S.sizeAt v a : ℂ) := rfl
  rw [e1]
  unfold PBL.rrC KB.Pl.RR lamP
  set Γ := D.GamLev S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) i with hΓdef
  set bP := D.bSt (D.kapG (S.g : ℝ) (S6.rd E)) P
  set bQ := D.bSt (D.kapG (S.g : ℝ) (S6.rd E)) Q
  set nP := C.nLoc S.G.k S.G.r S.fr (S.pd v).G P
  set nQ := C.nLoc S.G.k S.G.r S.fr (S.pd v).G Q
  set sz := S.sizeAt v a
  have hsq : √(Γ * sz) * √(Γ * sz) = Γ * sz := Real.mul_self_sqrt (mul_nonneg hΓ hsz)
  have hcoef : √nP / (bP * √(Γ * sz)) * (√nQ / (bQ * √(Γ * sz))) = √nP * √nQ * (1 / (bP * bQ * Γ)) / sz := by
    rw [div_mul_div_comm, show bP * √(Γ * sz) * (bQ * √(Γ * sz)) = bP * bQ * (√(Γ * sz) * √(Γ * sz)) by ring, hsq]
    field_simp
  rcases eq_or_lt_of_le (Nat.cast_nonneg (S.g) : (0 : ℝ) ≤ (S.g : ℝ)) with hg | hg
  · have h0 : Γ = 0 := gamLev_zero S i hi hg.symm
    simp [h0]
  · have hP' := isLocPt_toStd S.G.r (S.g : ℝ) hg P i hP
    have hQ' := isLocPt_toStd S.G.r (S.g : ℝ) hg Q i hQ
    unfold D.RRplace
    rw [dif_pos ⟨hP', hQ'⟩, dif_pos hi, hcoef]
    unfold KB.slv
    push_cast
    ring

theorem gNSetC : GNSetC := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p F v ε i hi a P Q hP hQ
  exact gNSetC_main S p F v ε i hi a P Q hP hQ

end loc

def betaZ (κ : ℝ) (N : ℤ) : ℝ := ∏ x ∈ Finset.Ico 1 N, (κ ^ (1 - 2 * x) / Real.pi) ^ (N - x)

theorem bSt_cons (κ : ℝ) (n : ℕ) (t : ℂ) (P : C.LPt) : D.bSt κ ((n, t) :: P) = betaZ κ n * D.bSt κ P := by
  simp [D.bSt, betaZ]

theorem bSt_nil (κ : ℝ) : D.bSt κ [] = 1 := by simp [D.bSt]

theorem betaZ_one (κ : ℝ) : betaZ κ 1 = 1 := by simp [betaZ]

theorem prod_Ico_int_succ (f : ℤ → ℝ) (a b : ℤ) (h : a ≤ b) :
    ∏ x ∈ Finset.Ico a (b + 1), f x = (∏ x ∈ Finset.Ico a b, f x) * f b := by
  rw [Finset.Ico_add_one_right_eq_Icc, ← Finset.Ico_insert_right h, Finset.prod_insert (by simp), mul_comm]

theorem betaZ_succ (κ : ℝ) (hκ : κ ≠ 0) (n : ℕ) :
    betaZ κ ((n : ℤ) + 1) = betaZ κ n * ∏ x ∈ Finset.Ico 1 ((n : ℤ) + 1), (κ ^ (1 - 2 * x) / Real.pi) := by
  unfold betaZ
  have hc : ∀ x : ℤ, κ ^ (1 - 2 * x) / Real.pi ≠ 0 := fun x => div_ne_zero (zpow_ne_zero _ hκ) Real.pi_ne_zero
  have e : ∏ x ∈ Finset.Ico 1 ((n : ℤ) + 1), (κ ^ (1 - 2 * x) / Real.pi) ^ ((n : ℤ) + 1 - x) =
      ∏ x ∈ Finset.Ico 1 ((n : ℤ) + 1), ((κ ^ (1 - 2 * x) / Real.pi) ^ ((n : ℤ) - x) * (κ ^ (1 - 2 * x) / Real.pi)) := by
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [← zpow_add_one₀ (hc x)]; congr 1; ring
  rw [e, Finset.prod_mul_distrib]
  congr 1
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [prod_Ico_int_succ _ _ _ (by omega), sub_self, zpow_zero, mul_one]

theorem prod_c (κ : ℝ) (hκ : κ ≠ 0) : ∀ n : ℕ,
    ∏ x ∈ Finset.Ico 1 ((n : ℤ) + 1), (κ ^ (1 - 2 * x) / Real.pi) = κ ^ (-((n : ℤ) ^ 2)) / Real.pi ^ n
  | 0 => by simp
  | n + 1 => by
    rw [show ((n + 1 : ℕ) : ℤ) + 1 = ((n : ℤ) + 1) + 1 by push_cast; ring, prod_Ico_int_succ _ _ _ (by omega),
      prod_c κ hκ n, div_mul_div_comm, ← zpow_add₀ hκ, pow_succ]
    congr 2
    push_cast; ring

theorem betaZ_succ' (κ : ℝ) (hκ : κ ≠ 0) (n : ℕ) :
    betaZ κ ((n : ℤ) + 1) = betaZ κ n * (κ ^ (-((n : ℤ) ^ 2)) / Real.pi ^ n) := by
  rw [betaZ_succ κ hκ, prod_c κ hκ]

theorem sqrt_zpow_two_mul (y : ℝ) (hy : 0 ≤ y) (a b : ℤ) : √(y ^ (2 * a * b)) = y ^ (a * b) := by
  rw [show 2 * a * b = (a * b) * 2 by ring, zpow_mul, zpow_two, Real.sqrt_mul_self (zpow_nonneg hy _)]

theorem bSt_pos_loc (κ : ℝ) (hκ : 0 < κ) (p : C.LPt) : 0 < D.bSt κ p := by
  unfold D.bSt
  refine List.prod_pos fun x hx => ?_
  obtain ⟨a, _, rfl⟩ := List.mem_map.1 hx
  exact Finset.prod_pos fun m _ => zpow_pos (div_pos (zpow_pos hκ _) Real.pi_pos) _

theorem weight_product_nonneg (k r : ℕ) (fr : ℕ → ℕ → ℝ) (hfr : ∀ b s, 0 ≤ fr b s) :
    ∀ (b : ℕ) (P : C.LPt), 0 ≤ C.nAux k r 0 fr b P
  | _, [] => by simp [C.nAux]
  | b, (s, t) :: rest => by
    simp only [C.nAux]
    refine mul_nonneg ?_ (weight_product_nonneg k r fr hfr (b + s) rest)
    split_ifs
    · rcases Nat.eq_zero_or_pos (k - 1) with h | h
      · rw [h]; simp
      · rw [zero_pow h.ne']
    · exact zpow_nonneg (mul_nonneg (hfr _ _) (norm_nonneg _)) _

theorem betaZ_pos (κ : ℝ) (hκ : 0 < κ) (N : ℤ) : 0 < betaZ κ N :=
  Finset.prod_pos fun _ _ => zpow_pos (div_pos (zpow_pos hκ _) Real.pi_pos) _

section loc2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem lambdaValue_append_two (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (a : List C.Letter) (b0 m : ℕ) (hi : b0 + m + 2 ≤ S.G.r)
    (h : C.LPt) (hh : D.ptSize h = b0) (t c : ℂ) :
    lamP S v a (b0 + m + 2) (h ++ [(m + 1, t), (1, c)]) =
      √(C.nAux S.G.k S.G.r 0 S.fr 1 h) /
          (D.bSt (D.kapG (S.g : ℝ) (S6.rd E)) h *
            √(D.GamLev S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) (b0 + m + 2) *
              S.sizeAt v a)) *
        ((S.fr (1 + b0) (m + 1) * ‖t‖) ^ (((m + 1 : ℕ) : ℤ) * (C.Mlev S.G.k S.G.r (1 + b0 + (m + 1) - 1) + ((m + 1 : ℕ) : ℤ) - 3)) *
          (S.fr (1 + b0 + (m + 1)) 1 * ‖c‖) ^ (((1 : ℕ) : ℤ) * (C.Mlev S.G.k S.G.r (1 + b0 + (m + 1) + 1 - 1) + ((1 : ℕ) : ℤ) - 3)) /
          (betaZ (D.kapG (S.g : ℝ) (S6.rd E)) ((m + 1 : ℕ) : ℤ) * betaZ (D.kapG (S.g : ℝ) (S6.rd E)) ((1 : ℕ) : ℤ))) := by
  have hfr : ∀ b s, 0 ≤ S.fr b s := fun b s => by unfold C.HidaSetting.fr; exact Real.rpow_nonneg (rd_pos' (E := E)).le _
  unfold lamP C.nLoc
  have hsz : D.ptSize (h ++ [(m + 1, t), (1, c)]) = b0 + m + 2 := by
    simp [D.ptSize, List.map_append, List.sum_append] at hh ⊢; omega
  rw [weight_product_germ_indep S.G.k S.G.r _ 0 S.fr 1 _ (by omega), weight_product_append, hh]
  simp only [C.nAux, mul_one]
  rw [bSt_append, bSt_cons, bSt_cons, bSt_nil, mul_one]
  split_ifs with H1 H2 <;> first | (exfalso; omega) | (exfalso; simp only [and_true] at *; omega) | skip
  rw [Real.sqrt_mul (weight_product_nonneg _ _ _ hfr _ _), Real.sqrt_mul (zpow_nonneg (mul_nonneg (hfr _ _) (norm_nonneg t)) _),
    sqrt_zpow_two_mul _ (mul_nonneg (hfr _ _) (norm_nonneg t)), sqrt_zpow_two_mul _ (mul_nonneg (hfr _ _) (norm_nonneg c))]
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem lambdaMap_one_eq_zero (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (a : List C.Letter) (b0 m : ℕ) (hi : b0 + m + 2 ≤ S.G.r)
    (h : C.LPt) (hh : D.ptSize h = b0) (z : ℂ) :
    lamP S v a (b0 + m + 2) (h ++ [(m + 2, z)]) =
      √(C.nAux S.G.k S.G.r 0 S.fr 1 h) /
          (D.bSt (D.kapG (S.g : ℝ) (S6.rd E)) h *
            √(D.GamLev S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) (b0 + m + 2) *
              S.sizeAt v a)) *
        ((S.fr (1 + b0) (m + 2) * ‖z‖) ^ (((m + 2 : ℕ) : ℤ) * (C.Mlev S.G.k S.G.r (1 + b0 + (m + 2) - 1) + ((m + 2 : ℕ) : ℤ) - 3)) /
          betaZ (D.kapG (S.g : ℝ) (S6.rd E)) ((m + 2 : ℕ) : ℤ)) := by
  have hfr : ∀ b s, 0 ≤ S.fr b s := fun b s => by unfold C.HidaSetting.fr; exact Real.rpow_nonneg (rd_pos' (E := E)).le _
  unfold lamP C.nLoc
  have hsz : D.ptSize (h ++ [(m + 2, z)]) = b0 + m + 2 := by
    simp [D.ptSize, List.map_append, List.sum_append] at hh ⊢; omega
  rw [weight_product_germ_indep S.G.k S.G.r _ 0 S.fr 1 _ (by omega), weight_product_append, hh]
  simp only [C.nAux, mul_one]
  rw [bSt_append, bSt_cons, bSt_nil, mul_one]
  split_ifs with H1 <;> first | (exfalso; omega) | (exfalso; simp only [and_true] at *; omega) | skip
  rw [Real.sqrt_mul (weight_product_nonneg _ _ _ hfr _ _), sqrt_zpow_two_mul _ (mul_nonneg (hfr _ _) (norm_nonneg z))]
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem germConst : GermConst := by
  intro E _ _ _ Wp Wq _ _ _ _ S v a b s hg1 hg2 hb hs hi h hh
  obtain ⟨b0, rfl⟩ : ∃ b0, b = b0 + 1 := ⟨b - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 2 := ⟨s - 2, by omega⟩
  have ei : b0 + 1 + (m + 2) - 1 = b0 + m + 2 := by omega
  have es1 : m + 2 - 1 = m + 1 := by omega
  have es2 : m + 2 - 2 = m := by omega
  have eh : b0 + 1 - 1 = b0 := by omega
  rw [eh] at hh
  rw [ei] at hi ⊢
  simp only [es1, es2]
  obtain ⟨ρ, hρ⟩ : ∃ ρ, S.G.r = b0 + m + 2 + ρ := ⟨S.G.r - (b0 + m + 2), by omega⟩
  have eρ : S.G.r - (b0 + m + 2) = ρ := by omega
  rw [eρ]
  have hgpos : (0 : ℝ) < (S.g : ℝ) := by unfold C.HidaSetting.g; exact_mod_cast Nat.mul_pos hg1 hg2
  simp only [lambdaValue_append_two S v a b0 m hi h hh, lambdaMap_one_eq_zero S v a b0 m hi h hh, norm_fs _ _ hgpos, norm_mul, norm_pow,
    norm_inv, KB.dlB]
  have n1 : 1 + b0 + (m + 1) - 1 = b0 + m + 1 := by omega
  have n2 : 1 + b0 + (m + 1) + 1 - 1 = b0 + m + 2 := by omega
  have n3 : 1 + b0 + (m + 2) - 1 = b0 + m + 2 := by omega
  have n4 : 1 + b0 + (m + 1) = b0 + m + 2 := by omega
  have n5 : U.Mlev S.G.k ρ - 2 = S.G.k + 2 * ρ + 1 := by simp only [U.Mlev]; omega
  have hκ : D.kapG (S.g : ℝ) (S6.rd E) = ((S.g : ℝ) / (2 * Real.pi) * S6.rd E)⁻¹ := by
    unfold D.kapG; field_simp
  have hrd : 0 < S6.rd E := rd_pos' (E := E)
  have hκ0 : D.kapG (S.g : ℝ) (S6.rd E) ≠ 0 := by rw [hκ]; positivity
  rw [show ((m + 2 : ℕ) : ℤ) = ((m + 1 : ℕ) : ℤ) + 1 by push_cast; ring, betaZ_succ' _ hκ0 (m + 1)]
  simp only [n1, n2, n3, n4, n5, Nat.cast_one, betaZ_one, mul_one, C.HidaSetting.fr]
  set Hf := √(C.nAux S.G.k S.G.r 0 S.fr 1 h) /
      (D.bSt (D.kapG (S.g : ℝ) (S6.rd E)) h *
        √(D.GamLev S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) (b0 + m + 2) * S.sizeAt v a))
    with hHf
  clear_value Hf
  have hB1 := betaZ_pos _ (show 0 < D.kapG (S.g : ℝ) (S6.rd E) by rw [hκ]; positivity) ((m + 1 : ℕ) : ℤ)
  set B1 := betaZ (D.kapG (S.g : ℝ) (S6.rd E)) ((m + 1 : ℕ) : ℤ) with hB1d
  clear_value B1
  rw [hκ]
  have hδ : 0 < D.deG (S.g : ℝ) (S6.rd E) := by unfold D.deG; positivity
  set δ := D.deG (S.g : ℝ) (S6.rd E) with hδd
  clear_value δ
  have hq : 0 < (S.g : ℝ) / (2 * Real.pi) := by positivity
  set q := (S.g : ℝ) / (2 * Real.pi) with hqd
  clear_value q
  set R := S6.rd E with hRd
  clear_value R
  rw [hρ]
  have n6 : b0 + m + 2 - 1 = b0 + m + 1 := by omega
  have n7 : b0 + m + 2 + 1 - 1 = b0 + m + 2 := by omega
  simp only [n6, n7]
  have hHf0 : 0 ≤ Hf := by
    rw [hHf]
    refine div_nonneg (Real.sqrt_nonneg _) (mul_nonneg (bSt_pos_loc _ (by rw [hκ]; positivity) h).le (Real.sqrt_nonneg _))
  unfold kapB
  have c1 : (((m + 1) * (m + 4) / 2 : ℕ) : ℝ) = ((m : ℝ) + 1) * ((m : ℝ) + 4) / 2 := by
    have : 2 ∣ (m + 1) * (m + 4) := by
      have h2 : (m + 1) * (m + 4) = (m + 1) * (m + 2) + 2 * (m + 1) := by ring
      rw [h2]; exact (Nat.even_mul_succ_self (m + 1)).two_dvd.add (dvd_mul_right 2 _)
    rw [Nat.cast_div this (by norm_num)]; push_cast; ring
  have c2 : (((m + 2) * (m + 1) / 2 : ℕ) : ℝ) = ((m : ℝ) + 2) * ((m : ℝ) + 1) / 2 := by
    have : 2 ∣ (m + 2) * (m + 1) := by
      rw [mul_comm]; exact (Nat.even_mul_succ_self (m + 1)).two_dvd
    rw [Nat.cast_div this (by norm_num)]; push_cast; ring
  set ν1 : ℤ := S6.nuBlock ((b0 + m + 2 + ρ : ℕ) : ℤ) ((b0 + 1 : ℕ) : ℤ) ((m + 1 : ℕ) : ℤ) with hν1
  set ν2 : ℤ := S6.nuBlock ((b0 + m + 2 + ρ : ℕ) : ℤ) ((b0 + m + 2 : ℕ) : ℤ) 1 with hν2
  set e1 : ℤ := ((m + 1 : ℕ) : ℤ) * ((S.G.k : ℤ) + 2 * ρ + m + 3) with he1
  set e2 : ℤ := (S.G.k : ℤ) + 2 * ρ + 1 with he2
  refine ⟨Hf * (R ^ (-ν2 - ν1 * e1 - ν2 * e2) * √δ * Real.pi ^ ((m + 1) * (m + 4) / 2) / B1 /
    q ^ (ν1 * ((m + 1 : ℕ) : ℤ) * ((S.G.k : ℤ) + 2 * ρ + m + 2) + ν2 * e2)), fun x D z hx hD hz => ?_⟩
  have hX : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hDn : 0 < ‖D‖ := norm_pos_iff.mpr hD
  have hz0 : z ≠ 0 := by rintro rfl; apply hD; rw [← hz]; simp
  have hZ : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hZl : ((m : ℝ) + 2) * Real.log ‖z‖ = Real.log ‖D‖ := by
    rw [← hz, norm_pow, Real.log_pow]; push_cast; ring
  rcases hHf0.eq_or_lt with h0 | hHp
  · rw [← h0]; simp
  have lg : ∀ {A B : ℝ}, 0 < A → 0 < B → Real.log A = Real.log B → A = B :=
    fun hA hB hAB => Real.log_injOn_pos (Set.mem_Ioi.2 hA) (Set.mem_Ioi.2 hB) hAB
  refine ⟨lg (by positivity) (by positivity) ?_, lg (by positivity) (by positivity) ?_⟩
  · simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_inv, Real.log_pow, Real.log_zpow,
      Real.log_rpow, Real.log_sqrt, c1, c2]
    simp only [hν1, hν2, he1, he2, S6.nuBlock, C.Mlev, U.Mlev]
    push_cast
    ring
  · simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_inv, Real.log_pow, Real.log_zpow,
      Real.log_rpow, Real.log_sqrt, c1, c2]
    simp only [hν1, hν2, he1, he2, S6.nuBlock, C.Mlev, U.Mlev]
    push_cast
    linear_combination ((S.G.k : ℝ) + 2 * ρ + 1) * hZl

end loc2

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities

theorem Formalism.FourierDecayAlt.P.germ_null_set_compact : Formalism.FourierDecayAlt.P.FormNormSumIdentities.GNSetC := Formalism.FourierDecayAlt.P.FormNormSumIdentities.gNSetC

theorem Formalism.FourierDecayAlt.P.germ_constant : Formalism.FourierDecayAlt.P.FormNormSumIdentities.GermConst := Formalism.FourierDecayAlt.P.FormNormSumIdentities.germConst
