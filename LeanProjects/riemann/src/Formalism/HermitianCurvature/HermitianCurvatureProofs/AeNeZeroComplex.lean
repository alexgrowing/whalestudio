import Formalism.HermitianCurvature.HermitianCurvatureProofs.FormPos

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt NumberField MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBD
open scoped ComplexConjugate

noncomputable section

section rr

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

theorem rr_eq_form (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (j : ℕ) (hj : j ≤ P.r)
    (w : List C.Letter) (a b : C.LPt) (ha : D.IsLocPt a j) (hb : D.IsLocPt b j) :
    p.RR F j w a b = p.form j hj w (KB.slv p.T F j hj w a ha.2) (KB.slv p.T F j hj w b hb.2) := by
  unfold KB.Pl.RR D.RRplace
  rw [dif_pos (⟨ha, hb⟩ : D.IsLocPt a j ∧ D.IsLocPt b j), dif_pos hj]
  rfl

end rr

section frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def nnS (S : C.HidaSetting E Wp Wq) (P : C.LPt) : ℝ := C.nLoc S.G.k S.G.r S.fr (D.ptGG (S.T * S.T')) P

def bS (S : C.HidaSetting E Wp Wq) (P : C.LPt) : ℝ := D.bSt (D.kapG (S.g : ℝ) (S6.rd E)) P

def ΓS (S : C.HidaSetting E Wp Wq) (i : ℕ) : ℝ :=
  D.GamLev S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) i

def stdS (S : C.HidaSetting E Wp Wq) (P : C.LPt) : C.LPt := D.toStd S.G.r (S.g : ℝ) 1 P

def lamS (S : C.HidaSetting E Wp Wq) (j : ℕ) : ℝ :=
  ((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock (S.G.r : ℤ) ((j + 1 : ℕ) : ℤ) ((1 : ℕ) : ℤ)

def sW (S : C.HidaSetting E Wp Wq) (j : ℕ) (l : ℂ) : ℂ :=
  Complex.I * (((2 * Real.pi / ((S.g : ℝ) * lamS S j)) : ℝ) : ℂ) * l

def dW (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (j : ℕ) (w : List C.Letter) (h h' : C.LPt) : ℝ :=
  √(nnS S h) * √(nnS S h') / (bS S h * bS S h' * ΓS S j) / S.sizeAt v w

private theorem tsize_lemma (r : ℕ) (g : ℝ) (P : C.LPt) :
    ∀ x : ℕ, D.ptSize (D.toStd r g x P) = D.ptSize P := by
  induction P with
  | nil => intro x; simp only [D.toStd]
  | cons a l ih =>
    intro x
    simp only [D.toStd, D.ptSize, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]

theorem stdS_size (S : C.HidaSetting E Wp Wq) (P : C.LPt) : D.ptSize (stdS S P) = D.ptSize P := by
  unfold stdS
  exact tsize_lemma _ _ P 1

theorem sizeAt_nonneg (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (w : List C.Letter) : 0 ≤ S.sizeAt v w := by
  unfold C.HidaSetting.sizeAt
  apply List.prod_nonneg
  intro x hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
  exact abs_nonneg _

theorem g_pos_of_built {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) : (0 : ℝ) < (S.g : ℝ) := by
  obtain ⟨hg1, hg2, -⟩ := hB
  unfold C.HidaSetting.g; exact_mod_cast Nat.mul_pos hg1 hg2

theorem dW_nonneg {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) (j : ℕ) (w : List C.Letter) (h h' : C.LPt) :
    0 ≤ dW S v j w h h' := by
  have hg := g_pos_of_built hB
  have hrd := rd_pos' E
  have hκ : 0 < D.kapG (S.g : ℝ) (S6.rd E) := by unfold D.kapG; positivity
  have hδ : 0 < D.deG (S.g : ℝ) (S6.rd E) := by unfold D.deG; positivity
  unfold dW bS ΓS
  have := bSt_pos' _ hκ h
  have := bSt_pos' _ hκ h'
  have := gamLev_pos S.G.k S.G.r _ _ hκ hδ j
  have := sizeAt_nonneg S v w
  positivity

theorem pdG_of_built {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) :
    (S.pd v).G = D.ptGG (S.T * S.T') ∧
      Tz S.G.k S.G.r (p v).T.base.z * Tz S.G.k S.G.r (p v).T.base.z' = S.T * S.T' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv⟩ := hB
  obtain ⟨-, -, hpd, -, -⟩ := hv v
  have hTT : Tz S.G.k S.G.r (p v).T.base.z * Tz S.G.k S.G.r (p v).T.base.z' = S.T * S.T' := by
    have h := S.hT v
    rw [hpd] at h
    rw [← h.1, ← h.2]
    rfl
  refine ⟨?_, hTT⟩
  rw [hpd, ← hTT]
  rfl

theorem gramLoc_setC {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (v : Fin S.f) (ε : ℝ) (i : ℕ) (w : List C.Letter) (P Q : C.LPt) :
    (setC S p F).gramLoc v ε i w P Q =
      ((√(nnS S P) * √(nnS S Q) : ℝ) : ℂ) * ((1 / (bS S P * bS S Q * ΓS S i) : ℝ) : ℂ) *
        (p v).RR (F v ε) i w (stdS S P) (stdS S Q) := by
  have hG := (pdG_of_built hB v).1
  show ((√(C.nLoc S.G.k S.G.r S.fr (S.pd v).G P) * √(C.nLoc S.G.k S.G.r S.fr (S.pd v).G Q) : ℝ) : ℂ) *
    rrC S p F v ε i w P Q = _
  rw [hG]
  simp only [rrC, nnS, bS, ΓS, stdS, mul_assoc]

theorem gN_setC {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (v : Fin S.f) (ε : ℝ) (i : ℕ) (w : List C.Letter) (P Q : C.LPt) :
    KB.gN (setC S p F) v ε i w P Q =
      ((√(nnS S P) * √(nnS S Q) / (bS S P * bS S Q * ΓS S i) / S.sizeAt v w : ℝ) : ℂ) *
        (p v).RR (F v ε) i w (stdS S P) (stdS S Q) := by
  unfold KB.gN
  rw [gramLoc_setC hB F v ε i w P Q]
  have hs : (setC S p F).sizeAt v w = S.sizeAt v w := rfl
  rw [hs]
  push_cast
  ring

end frame

section main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem lamS_pos (S : C.HidaSetting E Wp Wq) (hg : (0 : ℝ) < S.g) (j : ℕ) : 0 < lamS S j := by
  unfold lamS
  first
    | exact zpow_pos (div_pos hg (by positivity)) _
    | exact pow_pos (div_pos hg (by positivity)) _
    | exact zpow_pos_of_pos (div_pos hg (by positivity)) _

theorem psiL_eq_fsv (S : C.HidaSetting E Wp Wq) (hg : (0 : ℝ) < S.g) (j : ℕ) (l c : ℂ) :
    KB.psiL S l c = P5.fsv (sW S j l) ((lamS S j : ℂ) * c) := by
  have hl := lamS_pos S hg j
  unfold KB.psiL P5.fsv sW
  congr 1
  set lm := lamS S j with hlm
  set A : ℝ := 2 * Real.pi / ((S.g : ℝ) * lm) with hA
  have hAl : A * lm = 2 * Real.pi / (S.g : ℝ) := by
    rw [hA]
    field_simp
  have hz : l * c + (starRingEnd ℂ) l * (starRingEnd ℂ) c = ((2 * (l * c).re : ℝ) : ℂ) := by
    rw [← map_mul, Complex.add_conj]
  rw [map_mul, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]
  calc 2 * (Real.pi : ℂ) * Complex.I * (((2 * (l * c).re / (S.g : ℝ)) : ℝ) : ℂ)
      = Complex.I * ((A * lm : ℝ) : ℂ) * ((2 * (l * c).re : ℝ) : ℂ) := by
        rw [hAl]; push_cast; ring
    _ = Complex.I * (A : ℂ) * l * ((lm : ℂ) * c) -
          -Complex.I * (A : ℂ) * (starRingEnd ℂ) l * ((lm : ℂ) * (starRingEnd ℂ) c) := by
        rw [← hz]; push_cast; ring

theorem ae_ne_zero_complex : ∀ᵐ c : ℂ, c ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  simp

end main

section main2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def rhoS (S : C.HidaSetting E Wp Wq) (j : ℕ) : ℝ :=
  (S.fr (j + 1) 1 / lamS S j) ^ (2 * (C.Mlev S.G.k S.G.r (j + 1) - 2))

def Kc (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (j : ℕ) (w : List C.Letter) (h h' : C.LPt) : ℝ :=
  √(nnS S h) * √(nnS S h') * (1 / (bS S h * bS S h' * ΓS S (j + 1))) * rhoS S j / S.sizeAt v w

private theorem tapp_lemma (r : ℕ) (g : ℝ) (H L : C.LPt) :
    ∀ x : ℕ, D.toStd r g x (H ++ L) = D.toStd r g x H ++ D.toStd r g (x + D.ptSize H) L := by
  induction H with
  | nil => intro x; simp [D.toStd, D.ptSize]
  | cons a l ih =>
    intro x
    simp only [List.cons_append, D.toStd]
    rw [ih]
    simp only [D.ptSize, List.map_cons, List.sum_cons, Nat.add_assoc]

theorem stdS_app (S : C.HidaSetting E Wp Wq) (j : ℕ) (H : C.LPt) (c : ℂ) (hH : D.ptSize H = j) :
    stdS S (H ++ [(1, c)]) = stdS S H ++ [(1, (lamS S j : ℂ) * c)] := by
  unfold stdS
  rw [tapp_lemma, hH]
  simp only [D.toStd, Nat.sub_self, pow_zero, mul_one, List.append_nil]
  unfold lamS
  rw [Nat.add_comm 1 j]

theorem nnS_app (S : C.HidaSetting E Wp Wq) (j : ℕ) (hj : j ≤ S.G.r) (H : C.LPt) (c : ℂ) (hH : D.ptSize H = j) :
    nnS S (H ++ [(1, c)]) = nnS S H *
      C.nAux S.G.k S.G.r (Complex.normSq c - S.T * S.T') S.fr (j + 1) [(1, c)] := by
  simp only [nnS, C.nLoc]
  rw [weight_product_append, hH, show 1 + j = j + 1 by omega]
  have hG : D.ptGG (S.T * S.T') (H ++ [(1, c)]) = Complex.normSq c - S.T * S.T' := by simp [D.ptGG, D.ptLast]
  rw [hG, weight_product_indep_of_real_parameter _ _ _ (D.ptGG (S.T * S.T') H) _ H 1 le_rfl (by omega)]

theorem gN_setC_app {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (v : Fin S.f) (ε : ℝ) (j : ℕ) (hj : j ≤ S.G.r) (w : List C.Letter) (h h' : C.LPt)
    (hsz : D.ptSize h = j) (hsz' : D.ptSize h' = j) (c : ℂ) (hc : c ≠ 0) :
    KB.gN (setC S p F) v ε (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)]) =
      ((Kc S v j w h h' : ℝ) : ℂ) * ((KB.levW (D.parOf S v) (j + 1) ((lamS S j : ℂ) * c) : ℝ) : ℂ) *
        (p v).RR (F v ε) (j + 1) w (stdS S h ++ [(1, (lamS S j : ℂ) * c)])
          (stdS S h' ++ [(1, (lamS S j : ℂ) * c)]) := by
  have hgpos := g_pos_of_built hB
  have hTT := (pdG_of_built hB v).2
  have hrd := rd_pos' E
  have hfr : ∀ b s, 0 < S.fr b s := fun b s => Real.rpow_pos_of_pos hrd _
  set lam := lamS S j with hlam
  have hlam_pos : 0 < lam := lamS_pos S hgpos j
  set xw : ℂ → ℝ := fun c => C.nAux S.G.k S.G.r (Complex.normSq c - S.T * S.T') S.fr (j + 1) [(1, c)] with hxw
  have hn_nonneg : ∀ H, D.ptSize H = j → 0 ≤ nnS S H := fun H hH =>
    lpt_value_nonneg_of_pos_of_size_le _ _ _ _ hfr H 1 le_rfl (by omega)
  have hsq : √(nnS S (h ++ [(1, c)])) * √(nnS S (h' ++ [(1, c)])) =
      √(nnS S h) * √(nnS S h') * (√(xw c) * √(xw c)) := by
    rw [nnS_app S j hj h c hsz, nnS_app S j hj h' c hsz', Real.sqrt_mul (hn_nonneg h hsz),
      Real.sqrt_mul (hn_nonneg h' hsz')]
    ring
  set RRs : ℕ → C.LPt → C.LPt → ℂ := fun i P Q => (p v).RR (F v ε) i w P Q with hRRs
  set Mj : ℤ := C.Mlev S.G.k S.G.r (j + 1) with hMj
  have hW : ∀ (H H' : C.LPt), D.ptSize H = j →
      ((√(xw c) * √(xw c) : ℝ) : ℂ) * RRs (j + 1) (H ++ [(1, (lam : ℂ) * c)]) (H' ++ [(1, (lam : ℂ) * c)]) =
        ((rhoS S j * KB.levW (D.parOf S v) (j + 1) ((lam : ℂ) * c) : ℝ) : ℂ) *
          RRs (j + 1) (H ++ [(1, (lam : ℂ) * c)]) (H' ++ [(1, (lam : ℂ) * c)]) := by
    intro H H' hH
    by_cases hjt : j = S.G.r
    · have hnu : S6.nuBlock (S.G.r : ℤ) ((j + 1 : ℕ) : ℤ) ((1 : ℕ) : ℤ) = 0 := by
        unfold S6.nuBlock; rw [hjt]; push_cast; ring
      have hlam1 : lam = 1 := by rw [hlam, lamS, hnu, zpow_zero]
      have hfr1 : S.fr (j + 1) 1 = 1 := by
        unfold C.HidaSetting.fr
        have : ((S6.nuBlock (S.G.r : ℤ) (Nat.cast (j + 1)) (Nat.cast 1) : ℤ) : ℝ) = 0 := by
          unfold S6.nuBlock; rw [hjt]; push_cast; ring
        rw [this]; simp
      have hρ1 : rhoS S j = 1 := by rw [rhoS, ← hlam, hlam1, hfr1]; simp
      have hx : xw c = (Complex.normSq c - S.T * S.T') ^ (S.G.k - 1) := by
        simp only [hxw, C.nAux]
        rw [if_pos (by constructor <;> first | trivial | omega), mul_one]
      have hlev : KB.levW (D.parOf S v) (j + 1) ((lam : ℂ) * c) = B2.zWeight S.G.k S.T S.T' c := by
        rw [hlam1, Complex.ofReal_one, one_mul]
        unfold KB.levW
        rw [if_pos (by simp [hjt])]
      rw [hρ1, hlev, one_mul, hx]
      by_cases hc2 : S.T * S.T' ≤ Complex.normSq c
      · rw [Real.mul_self_sqrt (pow_nonneg (by linarith) _)]
        unfold B2.zWeight
        rw [if_pos hc2]
      · have h0 : RRs (j + 1) (H ++ [(1, (lam : ℂ) * c)]) (H' ++ [(1, (lam : ℂ) * c)]) = 0 := by
          have := rrTop_zero (D.parOf S v) (p v).l0 (p v).T (p v).ν' (p v).m₀ (p v).Θ (p v).TP
            (M.sgn (D.parOf S v) (p v).l0) (F v ε) w H (H' ++ [(1, (lam : ℂ) * c)])
            ((lam : ℂ) * c) (by rw [hH, hjt]) (by
              rw [hlam1, Complex.ofReal_one, one_mul]
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
      rw [hx, rhoS, ← hlam, ← hMj]
      unfold KB.levW
      rw [if_neg (by show ¬ (j + 1 = S.G.r + 1); omega)]
      have hnorm : ‖(lam : ℂ) * c‖ = lam * ‖c‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hlam_pos.le]
      rw [hnorm, ← mul_zpow]
      congr 1
      field_simp
  rw [gN_setC hB, stdS_app S j h c hsz, stdS_app S j h' c hsz']
  have hWc := hW (stdS S h) (stdS S h') (by rw [stdS_size]; exact hsz)
  have hb1 : bS S (h ++ [(1, c)]) = bS S h := bSt_append_one _ _ _
  have hb2 : bS S (h' ++ [(1, c)]) = bS S h' := bSt_append_one _ _ _
  rw [hb1, hb2]
  rw [show √(nnS S (h ++ [(1, c)])) * √(nnS S (h' ++ [(1, c)])) /
      (bS S h * bS S h' * ΓS S (j + 1)) / S.sizeAt v w =
      (√(nnS S h) * √(nnS S h') / (bS S h * bS S h' * ΓS S (j + 1)) / S.sizeAt v w) * (√(xw c) * √(xw c)) by
    rw [hsq]; ring]
  simp only [hRRs] at hWc
  unfold Kc
  push_cast at hWc ⊢
  linear_combination ((√(nnS S h) : ℂ) * (√(nnS S h') : ℂ) / ((bS S h : ℂ) * (bS S h' : ℂ) * (ΓS S (j + 1) : ℂ)) /
    (S.sizeAt v w : ℂ)) * hWc

end main2

section main3

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem kc_scal {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) (j : ℕ) (hj : j ≤ S.G.r) (w : List C.Letter)
    (h h' : C.LPt) :
    (KB.dlB S (j + 1) 1)⁻¹ * (Kc S v j w h h' * |(lamS S j ^ 2)⁻¹|) = dW S v j w h h' := by
  have hgpos := g_pos_of_built hB
  have hrd := rd_pos' E
  have hκ : 0 < D.kapG (S.g : ℝ) (S6.rd E) := by unfold D.kapG; positivity
  have hδ : 0 < D.deG (S.g : ℝ) (S6.rd E) := by unfold D.deG; positivity
  have hlam_pos := lamS_pos S hgpos j
  have hfac := gamLev_succ S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) j hj
  have hΓpos : 0 < ΓS S (j + 1) := gamLev_pos _ _ _ _ hκ hδ _
  have hbh : 0 < bS S h := bSt_pos' _ hκ h
  have hbh' : 0 < bS S h' := bSt_pos' _ hκ h'
  have hgl : (S.g : ℝ) / (2 * Real.pi) = (D.kapG (S.g : ℝ) (S6.rd E) * S6.rd E)⁻¹ := by
    unfold D.kapG; field_simp
  have hfrj : S.fr (j + 1) 1 = S6.rd E ^ (-(S6.nuBlock (S.G.r : ℤ) ((j + 1 : ℕ) : ℤ) ((1 : ℕ) : ℤ))) := by
    unfold C.HidaSetting.fr
    rw [← Real.rpow_intCast]
    push_cast
    ring_nf
  have hkey : rhoS S j * (lamS S j ^ 2)⁻¹ =
      S6.rd E ^ (2 * S6.nuBlock (S.G.r : ℤ) ((j + 1 : ℕ) : ℤ) ((1 : ℕ) : ℤ)) *
        D.kapG (S.g : ℝ) (S6.rd E) ^ (4 * ((S.G.r : ℤ) + 1 - ((j + 1 : ℕ) : ℤ)) * (C.Mlev S.G.k S.G.r (j + 1) - 1)) := by
    rw [rhoS, hfrj, lamS, hgl, ← div_eq_mul_inv, scal_id _ _ hκ hrd]
    congr 1
    congr 1
    unfold S6.nuBlock
    push_cast
    ring
  set K : ℝ := √(nnS S h) * √(nnS S h') * (1 / (bS S h * bS S h' * ΓS S (j + 1))) * rhoS S j with hK
  have hscal : K * |(lamS S j ^ 2)⁻¹| =
      KB.dlB S (j + 1) 1 * (√(nnS S h) * √(nnS S h') * (1 / (bS S h * bS S h' * ΓS S j))) := by
    rw [abs_of_pos (inv_pos.2 (pow_pos hlam_pos 2))]
    have hΓj : ΓS S j = _ := hfac
    rw [hΓj]
    have e2 : K * (lamS S j ^ 2)⁻¹ =
        √(nnS S h) * √(nnS S h') * (1 / (bS S h * bS S h' * ΓS S (j + 1))) * (rhoS S j * (lamS S j ^ 2)⁻¹) := by
      rw [hK]; ring
    rw [e2, hkey]
    unfold KB.dlB
    have hΓ1 : ΓS S (j + 1) =
        D.GamLev S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) (j + 1) := rfl
    rw [← hΓ1, zpow_neg]
    have hκX := zpow_pos hκ (4 * ((S.G.r : ℤ) + 1 - ((j + 1 : ℕ) : ℤ)) * (C.Mlev S.G.k S.G.r (j + 1) - 1))
    field_simp
  have hdl : 0 < KB.dlB S (j + 1) 1 := by unfold KB.dlB; exact div_pos (zpow_pos hrd _) hδ
  have e3 : Kc S v j w h h' * |(lamS S j ^ 2)⁻¹| = (K * |(lamS S j ^ 2)⁻¹|) / S.sizeAt v w := by
    unfold Kc; rw [hK]; ring
  rw [e3, hscal, mul_div_assoc, ← mul_assoc, inv_mul_cancel₀ hdl.ne', one_mul]
  unfold dW
  ring

theorem hatB_setC (hA : P5.ThmPActual) (hPS : KB.PStd) {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq}
    {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε))
    (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ) (hj : j ≤ S.G.r) (w : List C.Letter)
    (hw : KB.CutWord (D.parOf S v) (S.l + 1) w) (l : ℂ) (h h' : C.LPt) (hh : D.IsLocPt h j)
    (hh' : D.IsLocPt h' j) :
    KB.hatB (setC S p F) v ε (j + 1) 1 w l h h' =
      ((dW S v j w h h' : ℝ) : ℂ) * (p v).form j hj w
        (KB.waveG ((p v).T.bs j) (sW S j l) w
          (KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2)))
        (KB.slv (p v).T (F v ε) j hj w (stdS S h') ((stdS_size S h').trans hh'.2)) := by
  have hgpos := g_pos_of_built hB
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, hInD, -, -, -⟩ := hv v
  have hH : D.IsLocPt (stdS S h) j := (isLocPt_toStd_iff _ _ hgpos h 1 j).2 hh
  have hH' : D.IsLocPt (stdS S h') j := (isLocPt_toStd_iff _ _ hgpos h' 1 j).2 hh'
  obtain ⟨φ, -, -, hφ, hφint⟩ := hPS hA (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (F v ε) j hj w
    (stdS S h) (stdS S h') hH hH' Cb (by rw [hl0]; exact hInD) (hF v ε hε) (by rw [hl0]; exact hw)
  have hlam_pos := lamS_pos S hgpos j
  obtain ⟨g, hgdef⟩ : ∃ g : ℂ → ℂ, g = fun c' => P5.fsv (sW S j l) c' * φ c' := ⟨_, rfl⟩
  have hae : (fun c : ℂ => KB.gN (setC S p F) v ε (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)]) *
      KB.psiL (setC S p F) l c) =ᵐ[volume]
      fun c => ((Kc S v j w h h' : ℝ) : ℂ) * g (lamS S j • c) := by
    filter_upwards [ae_ne_zero_complex] with c hc
    have hlc : (lamS S j : ℂ) * c ≠ 0 := mul_ne_zero (by exact_mod_cast hlam_pos.ne') hc
    simp only [hgdef, Complex.real_smul]
    rw [gN_setC_app hB F v ε j hj w h h' hh.2 hh'.2 c hc, hφ _ hlc]
    have : KB.psiL (setC S p F) l c = KB.psiL S l c := rfl
    rw [this, psiL_eq_fsv S hgpos j l c]
    ring
  have hint : KB.hatB (setC S p F) v ε (j + 1) 1 w l h h' = ((KB.dlB S (j + 1) 1 : ℝ) : ℂ)⁻¹ *
      ∫ c, ((Kc S v j w h h' : ℝ) : ℂ) * g (lamS S j • c) := by
    unfold KB.hatB
    rw [show j + 1 + 1 - 1 = j + 1 by omega, integral_congr_ae hae]
    rfl
  have hcs : ∫ c, ((Kc S v j w h h' : ℝ) : ℂ) * g (lamS S j • c) =
      ((Kc S v j w h h' : ℝ) : ℂ) * (((|(lamS S j ^ 2)⁻¹| : ℝ) : ℂ) * ∫ c, P5.fsv (sW S j l) c * φ c) := by
    rw [integral_const_mul, Measure.integral_comp_smul, Complex.finrank_real_complex, Complex.real_smul, hgdef]
  have gen : ∀ X : ℂ, ((KB.dlB S (j + 1) 1 : ℝ) : ℂ)⁻¹ *
      (((Kc S v j w h h' : ℝ) : ℂ) * (((|(lamS S j ^ 2)⁻¹| : ℝ) : ℂ) * X)) = ((dW S v j w h h' : ℝ) : ℂ) * X := by
    intro X
    rw [← kc_scal hB v j hj w h h']
    push_cast
    ring
  exact (hint.trans ((congrArg (fun Z => ((KB.dlB S (j + 1) 1 : ℝ) : ℂ)⁻¹ * Z) hcs).trans (gen _))).trans
    (congrArg (fun X => ((dW S v j w h h' : ℝ) : ℂ) * X) (hφint (sW S j l)))

end main3

section main4

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem rr_zero_of_not {Wp' Wq' : Type} [NormedAddCommGroup Wp'] [InnerProductSpace ℂ Wp'] [NormedAddCommGroup Wq']
    [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wp'] [FiniteDimensional ℂ Wq'] {P : M.Par}
    (p : KB.Pl P Wp' Wq') (F : B.Mat P.k P.r → (Wq' →L[ℂ] Wp')) (i : ℕ) (w : List C.Letter) (a b : C.LPt)
    (hn : ¬ (D.IsLocPt a i ∧ D.IsLocPt b i)) : p.RR F i w a b = 0 := by
  unfold KB.Pl.RR D.RRplace
  rw [dif_neg hn]

private theorem tent_lemma (r : ℕ) (g : ℝ) (hg : g ≠ 0) (P : C.LPt) :
    ∀ x : ℕ, (∀ b ∈ D.toStd r g x P, 1 ≤ b.1 ∧ b.2 ≠ 0) ↔ (∀ b ∈ P, 1 ≤ b.1 ∧ b.2 ≠ 0) := by
  have hX : ∀ (n : ℤ) (m : ℕ), (((g / (2 * Real.pi)) ^ n : ℝ) : ℂ) * Complex.I ^ m ≠ 0 := by
    intro n m
    apply mul_ne_zero
    · exact_mod_cast zpow_ne_zero n (div_ne_zero hg (by positivity))
    · exact pow_ne_zero _ Complex.I_ne_zero
  induction P with
  | nil => intro x; simp only [D.toStd]
  | cons a l ih =>
    intro x
    simp only [D.toStd, List.forall_mem_cons]
    rw [ih (x + a.1)]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, right_ne_zero_of_mul h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, mul_ne_zero (hX _ _) h2⟩, h3⟩

theorem gN_setC_form {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (v : Fin S.f) (ε : ℝ) (i : ℕ) (hi : i ≤ S.G.r) (w : List C.Letter) (P Q : C.LPt) (hP : D.IsLocPt P i)
    (hQ : D.IsLocPt Q i) :
    KB.gN (setC S p F) v ε i w P Q =
      ((dW S v i w P Q : ℝ) : ℂ) * (p v).form i hi w
        (KB.slv (p v).T (F v ε) i hi w (stdS S P) ((stdS_size S P).trans hP.2))
        (KB.slv (p v).T (F v ε) i hi w (stdS S Q) ((stdS_size S Q).trans hQ.2)) := by
  have hg := g_pos_of_built hB
  have key : ∀ R : C.LPt, D.IsLocPt R i → D.IsLocPt (stdS S R) i := by
    intro R hR
    exact And.intro ((tent_lemma _ _ hg.ne' R 1).mpr hR.1) ((stdS_size S R).trans hR.2)
  rw [gN_setC hB F v ε i w P Q, rr_eq_form (p v) (F v ε) i hi w (stdS S P) (stdS S Q) (key P hP) (key Q hQ)]
  unfold dW
  rfl

theorem gN_setC_zero {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (v : Fin S.f) (ε : ℝ) (i : ℕ) (w : List C.Letter) (P Q : C.LPt)
    (hn : ¬ (D.IsLocPt P i ∧ D.IsLocPt Q i)) : KB.gN (setC S p F) v ε i w P Q = 0 := by
  have hg := g_pos_of_built hB
  have key : ∀ R : C.LPt, D.IsLocPt (stdS S R) i → D.IsLocPt R i := by
    intro R hR
    exact And.intro ((tent_lemma _ _ hg.ne' R 1).mp hR.1) ((stdS_size S R).symm.trans hR.2)
  rw [gN_setC hB F v ε i w P Q, rr_zero_of_not (p v) (F v ε) i w (stdS S P) (stdS S Q), mul_zero]
  intro h
  exact hn ⟨key P h.1, key Q h.2⟩

theorem hatB_setC_zero {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (v : Fin S.f) (ε : ℝ) (j : ℕ) (w : List C.Letter) (l : ℂ) (h h' : C.LPt) (hsz : D.ptSize h = j)
    (hsz' : D.ptSize h' = j) (hn : ¬ (D.IsLocPt h j ∧ D.IsLocPt h' j)) :
    KB.hatB (setC S p F) v ε (j + 1) 1 w l h h' = 0 := by
  unfold KB.hatB
  have h0 : ∀ c : ℂ, KB.gN (setC S p F) v ε (j + 1 + 1 - 1) w (h ++ [(1, c)]) (h' ++ [(1, c)]) = 0 := by
    intro c
    apply gN_setC_zero hB F v ε _ w _ _
    rintro ⟨h1, h2⟩
    apply hn
    have key : ∀ R : C.LPt, D.ptSize R = j → D.IsLocPt (R ++ [(1, c)]) (j + 1 + 1 - 1) → D.IsLocPt R j := by
      intro R hR hRl
      exact And.intro (fun b hb => hRl.1 b (List.mem_append_left _ hb)) hR
    exact ⟨key h hsz h1, key h' hsz' h2⟩
  simp only [h0, zero_mul, MeasureTheory.integral_zero, mul_zero]

end main4

end

end Formalism.FourierDecayAlt.P.PBL
