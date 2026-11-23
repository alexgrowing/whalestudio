import Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveLocalPositiveCompactSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftLocalBuiltPlaces

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField Formalism.FourierDecayAlt.P.LiftDegreeLemmas
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section blockLC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem blockK_liftC (hA : P5.ThmPActualCpt) (hDL : KB.DegLift) (hSS : KB.SizeStdCpt) (hFP : FormPosCpt)
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (b s : ℕ) (hb : 1 ≤ b)
    (a : List C.Letter) (ha : D.AdmAt S v a) (haN : a.length ≤ S.Ntop) (K : ℕ)
    (grid : Fin K → Fin (2 * (j - s) + s + 1) → ℝ) (hinj : ∀ c, Function.Injective (grid c))
    (hnodes : ∀ n : Fin K → Fin (2 * (j - s) + s + 1),
        D.AdmAt S v (KB.plusW (List.ofFn fun c => grid c (n c)) a) ∧
        D.AdmAt S v (KB.minusW (List.ofFn fun c => grid c (n c)) a) ∧
        KB.CutWord (D.parOf S v) (S.l + 1) (KB.plusW (List.ofFn fun c => grid c (n c)) a) ∧
        KB.CutWord (D.parOf S v) (S.l + 1) (KB.minusW (List.ofFn fun c => grid c (n c)) a) ∧
        (List.ofFn fun c => grid c (n c)).Pairwise (fun y y' => 2 < |y - y'|) ∧
        ∀ y ∈ (List.ofFn fun c => grid c (n c)), NodeOK S v a false y)
    (Xc : ℝ) (hXc0 : 0 ≤ Xc)
    (hXc : (∏ c, ∑ i, |F7.lagCo (grid c) i|) * ‖lamB S b s‖ ^ K *
      (Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v)) ^ K ≤ Xc ^ K)
    (t t' : ℂ) (Y : Finset C.LPt) (hY : ∀ h ∈ Y, D.ptSize h = b - 1) :
    KB.BlockPSD Y Y
      (fun p' q' => ((Xc ^ K : ℝ) : ℂ) * ∑ n : Fin K → Fin (2 * (j - s) + s + 1), (F7.thGrid grid n : ℂ) *
        KB.gN (setC S p F) v ε j (KB.plusW (List.ofFn fun c => grid c (n c)) a) (p' ++ [(s, t)]) (q' ++ [(s, t)]))
      (fun p' q' => (((‖lamB S b s‖ : ℝ) : ℂ) * (-1) ^ (s - 1) * (lamB S b s)⁻¹) ^ K * (t⁻¹ - t'⁻¹) ^ K *
        KB.gN (setC S p F) v ε j a (p' ++ [(s, t)]) (q' ++ [(s, t')]))
      (fun p' q' => ((Xc ^ K : ℝ) : ℂ) * ∑ n : Fin K → Fin (2 * (j - s) + s + 1), (F7.thGrid grid n : ℂ) *
        KB.gN (setC S p F) v ε j (KB.minusW (List.ofFn fun c => grid c (n c)) a) (p' ++ [(s, t')])
          (q' ++ [(s, t')])) := by
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGo, -, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, -, -, -, -⟩ := hv v
  have hgpos := g_pos_of_built hB
  have hΓ := gam_pos hB j
  have hsa := sizeAt_pos S hGo v a ha
  set T : ℝ := ‖lamB S b s‖ with hT
  have hT0 : 0 < T := norm_pos_iff.2 (lamB_ne S hgpos b s)
  set c0 : ℝ := 1 / (ΓS S j * S.sizeAt v a) with hc0
  set ys : (Fin K → Fin (2 * (j - s) + s + 1)) → List ℝ := fun n => List.ofFn fun c => grid c (n c) with hys
  set Λ : ℝ := ∏ c, ∑ i, |F7.lagCo (grid c) i| with hΛ
  set θ : (Fin K → Fin (2 * (j - s) + s + 1)) → ℝ := fun n => F7.thGrid grid n with hθ
  set lag : (Fin K → Fin (2 * (j - s) + s + 1)) → ℝ := fun n => ∏ c, F7.lagCo (grid c) (n c) with hlag
  set S' := setC S p F with hS'
  set Pn : (Fin K → Fin (2 * (j - s) + s + 1)) → C.LPt → C.LPt → ℂ := fun n p' q' =>
    (((lag n / θ n) * T ^ K * c0 : ℝ) : ℂ) * KB.pairJ ((p v).form j hj a) (ys n)
      (uS S p F v ε j hj (KB.plusW (ys n) a) Y (s, t) p') (uS S p F v ε j hj (KB.minusW (ys n) a) Y (s, t') q')
    with hPn
  have hCS : ∀ n (c d : C.LPt → ℂ), ‖∑ p' ∈ Y, ∑ q' ∈ Y, c p' * conj (d q') * Pn n p' q'‖ ^ 2 ≤
      (Xc ^ K) ^ 2 * ((∑ p' ∈ Y, ∑ p'' ∈ Y, c p' * conj (c p'') *
          KB.gN S' v ε j (KB.plusW (ys n) a) (p' ++ [(s, t)]) (p'' ++ [(s, t)])).re *
        (∑ q' ∈ Y, ∑ q'' ∈ Y, d q' * conj (d q'') *
          KB.gN S' v ε j (KB.minusW (ys n) a) (q' ++ [(s, t')]) (q'' ++ [(s, t')])).re) := by
    intro n c d
    obtain ⟨hAp, hAm, hCp, hCm, hpw, hnd⟩ := hnodes n
    have hCp' : KB.CutWord (D.parOf S v) (p v).l0 (KB.plusW (ys n) a) := by rw [hl0]; exact hCp
    have hCm' : KB.CutWord (D.parOf S v) (p v).l0 (KB.minusW (ys n) a) := by rw [hl0]; exact hCm
    obtain ⟨hqpos, hcs⟩ := hSS hA (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) j hj a (ys n) hCp' hCm' hpw
    set qv : ℝ → ℝ := fun y => (Wd.qw (M.qC (D.parOf S v)) (D.positionted a) (y : ℂ)).re with hqv
    set Q : ℝ := ((ys n).map qv).prod with hQd
    have hQ : 0 < Q := List.prod_pos fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact hqpos y hy
    have hsp := sizeAt_pos S hGo v _ hAp
    have hsm := sizeAt_pos S hGo v _ hAm
    set cp : ℝ := 1 / (ΓS S j * S.sizeAt v (KB.plusW (ys n) a)) with hcp
    set cm : ℝ := 1 / (ΓS S j * S.sizeAt v (KB.minusW (ys n) a)) with hcm
    have hcp0 : 0 < cp := by positivity
    have hcm0 : 0 < cm := by positivity
    set κ : ℂ := (((lag n / θ n) * T ^ K * c0 : ℝ) : ℂ) with hκ
    have hc := cs_choice (CV ((p v).T.bs j) (S := Fin (KB.plusW (ys n) a).length))
      (CV ((p v).T.bs j) (S := Fin (KB.minusW (ys n) a).length))
      ((p v).form j hj (KB.plusW (ys n) a)) ((p v).form j hj (KB.minusW (ys n) a))
      (KB.pairJ ((p v).form j hj a) (ys n))
      cv_zero (fun x y hx hy => cv_add hx hy) (fun c x hx => cv_smul c hx)
      cv_zero (fun x y hx hy => cv_add hx hy) (fun c x hx => cv_smul c hx)
      (fun x₁ x₂ y c h₁ h₂ hy => form_slC (p v) j hj _ x₁ x₂ y c h₁ h₂ hy)
      (fun x y₁ y₂ c hx h₁ h₂ => form_srC (p v) j hj _ x y₁ y₂ c hx h₁ h₂)
      (fun x₁ x₂ y c h₁ h₂ hy => form_slC (p v) j hj _ x₁ x₂ y c h₁ h₂ hy)
      (fun x y₁ y₂ c hx h₁ h₂ => form_srC (p v) j hj _ x y₁ y₂ c hx h₁ h₂)
      (fun x₁ x₂ y c h₁ h₂ hy => pj_slC (p v) j hj a (ys n) x₁ x₂ y c h₁ h₂ hy)
      (fun x y₁ y₂ c hx h₁ h₂ => pj_srC (p v) j hj a (ys n) x y₁ y₂ c hx h₁ h₂)
      id (fun x hx => hx) (fun x y c _ _ => rfl) (fun x y _ _ => rfl)
      Q hQ (fun x y hx hy => hcs x y hx hy) Y (uS S p F v ε j hj (KB.plusW (ys n) a) Y (s, t))
      (uS S p F v ε j hj (KB.minusW (ys n) a) Y (s, t')) (fun h => uY_cv hB F hF v ε hε j hj _ _ _)
      (fun h => uY_cv hB F hF v ε hε j hj _ _ _) κ cp cm hcp0 hcm0 c d
    have eA : ∑ p' ∈ Y, ∑ p'' ∈ Y, c p' * conj (c p'') *
        KB.gN S' v ε j (KB.plusW (ys n) a) (p' ++ [(s, t)]) (p'' ++ [(s, t)]) =
        ∑ p' ∈ Y, ∑ p'' ∈ Y, c p' * conj (c p'') * ((cp : ℂ) * (p v).form j hj (KB.plusW (ys n) a)
          (uS S p F v ε j hj (KB.plusW (ys n) a) Y (s, t) p') (uS S p F v ε j hj (KB.plusW (ys n) a) Y (s, t) p'')) := by
      refine Finset.sum_congr rfl fun p' hp' => Finset.sum_congr rfl fun p'' hp'' => ?_
      rw [uS_mem S p F v ε j hj _ Y _ p' hp', uS_mem S p F v ε j hj _ Y _ p'' hp'', gN_uB hB F hF v ε hε j hj _ _ _]
    have eB : ∑ q' ∈ Y, ∑ q'' ∈ Y, d q' * conj (d q'') *
        KB.gN S' v ε j (KB.minusW (ys n) a) (q' ++ [(s, t')]) (q'' ++ [(s, t')]) =
        ∑ q' ∈ Y, ∑ q'' ∈ Y, d q' * conj (d q'') * ((cm : ℂ) * (p v).form j hj (KB.minusW (ys n) a)
          (uS S p F v ε j hj (KB.minusW (ys n) a) Y (s, t') q')
          (uS S p F v ε j hj (KB.minusW (ys n) a) Y (s, t') q'')) := by
      refine Finset.sum_congr rfl fun p' hp' => Finset.sum_congr rfl fun p'' hp'' => ?_
      rw [uS_mem S p F v ε j hj _ Y _ p' hp', uS_mem S p F v ε j hj _ Y _ p'' hp'', gN_uB hB F hF v ε hε j hj _ _ _]
    have hnnA : 0 ≤ (∑ p' ∈ Y, ∑ p'' ∈ Y, c p' * conj (c p'') *
        KB.gN S' v ε j (KB.plusW (ys n) a) (p' ++ [(s, t)]) (p'' ++ [(s, t)])).re :=
      quad_nonneg (psd_shift (s, t) (gN_psdC hA hFP hB F hF v ε hε j hj _ hCp _)) c
    have hnnB : 0 ≤ (∑ q' ∈ Y, ∑ q'' ∈ Y, d q' * conj (d q'') *
        KB.gN S' v ε j (KB.minusW (ys n) a) (q' ++ [(s, t')]) (q'' ++ [(s, t')])).re :=
      quad_nonneg (psd_shift (s, t') (gN_psdC hA hFP hB F hF v ε hε j hj _ hCm _)) d
    rw [eA] at hnnA ⊢
    rw [eB] at hnnB ⊢
    refine hc.trans (mul_le_mul_of_nonneg_right ?_ (mul_nonneg hnnA hnnB))

    have hth := lam_div_theta grid hinj n
    have hκn : ‖κ‖ = Λ * T ^ K * c0 := by
      rw [hκ, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_div, abs_of_pos hth.1,
        abs_of_pos (pow_pos hT0 K), abs_of_pos (by positivity : (0 : ℝ) < c0)]
      rw [hth.2]
    have hPp : ∀ c, S.P v (grid c (n c)) ≠ 0 := by
      have h1 := hsp
      rw [sizeAt_plusW, prod_ofFn_map'] at h1
      have h2 := (pos_of_mul_pos_left h1 hsa.le).ne'
      intro c hc0'
      exact h2 (Finset.prod_eq_zero (Finset.mem_univ c) (by rw [hc0', abs_zero]))
    have hPm : ∀ c, S.P v (grid c (n c) + 1) ≠ 0 := by
      have h1 := hsm
      rw [sizeAt_minusW, prod_ofFn_map'] at h1
      have h2 := (pos_of_mul_pos_left h1 hsa.le).ne'
      intro c hc0'
      exact h2 (Finset.prod_eq_zero (Finset.mem_univ c) (by rw [hc0', abs_zero]))
    have hrb := ratio_bound (fun c => grid c (n c)) (S.P v) qv Λ T (ΓS S j) (S.sizeAt v a)
      (Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v)) Xc hΓ hsa
      (fun c => hqpos _ (List.mem_ofFn.2 ⟨c, rfl⟩)) hPp hPm
      (fun c => (node_bound hB v a ha haN _ false (hnd _ (List.mem_ofFn.2 ⟨c, rfl⟩))).2)
      (Finset.prod_nonneg fun c _ => Finset.sum_nonneg fun i _ => abs_nonneg _) hT0.le
      (mul_nonneg (Real.exp_pos 1).le (supA_nonneg S (glob_pos' hB).1 (glob_pos' hB).2 v false)) hXc
    have eQ : Q = ∏ c, qv (grid c (n c)) := prod_ofFn_map' _ _
    have ecp : cp = 1 / (ΓS S j * ((∏ c, |S.P v (grid c (n c))|) * S.sizeAt v a)) := by
      rw [hcp, sizeAt_plusW, prod_ofFn_map']
    have ecm : cm = 1 / (ΓS S j * ((∏ c, |S.P v (grid c (n c) + 1)|) * S.sizeAt v a)) := by
      rw [hcm, sizeAt_minusW, prod_ofFn_map']
    rw [hκn, eQ, ecp, ecm]
    exact hrb
  have hblock := block_of_choices Y
    (fun n p' q' => KB.gN S' v ε j (KB.plusW (ys n) a) (p' ++ [(s, t)]) (q' ++ [(s, t)]))
    (fun n p' q' => KB.gN S' v ε j (KB.minusW (ys n) a) (p' ++ [(s, t')]) (q' ++ [(s, t')])) Pn θ (Xc ^ K) (Xc ^ K)
    (fun n => (lam_div_theta grid hinj n).1.le)
    (fun n => psd_shift (s, t) (gN_psdC hA hFP hB F hF v ε hε j hj _ (hnodes n).2.2.1 _))
    (fun n => psd_shift (s, t') (gN_psdC hA hFP hB F hF v ε hε j hj _ (hnodes n).2.2.2.1 _))
    (pow_nonneg hXc0 K) le_rfl hCS
  refine blockPSD_congr (fun _ _ _ _ => rfl) (fun p' hp' q' hq' => ?_) (fun _ _ _ _ => rfl) hblock
  show ∑ n, (θ n : ℂ) * Pn n p' q' =
    ((T : ℂ) * (-1) ^ (s - 1) * (lamB S b s)⁻¹) ^ K * (t⁻¹ - t'⁻¹) ^ K * KB.gN S' v ε j a (p' ++ [(s, t)]) (q' ++ [(s, t')])
  rw [gN_uB hB F hF v ε hε j hj a _ _, show (((1 / (ΓS S j * S.sizeAt v a)) : ℝ) : ℂ) = (c0 : ℂ) from rfl]
  have hdeg := deg_uB_lift hDL hB F hF v ε hε j hj b s hb a K grid hinj p' q' (hY p' hp') (hY q' hq') t t'
  have hlm : (lamB S b s * t)⁻¹ - (lamB S b s * t')⁻¹ = (lamB S b s)⁻¹ * (t⁻¹ - t'⁻¹) := by
    rw [mul_inv, mul_inv]; ring
  rw [hlm] at hdeg
  have eR : ((T : ℂ) * (-1) ^ (s - 1) * (lamB S b s)⁻¹) ^ K * (t⁻¹ - t'⁻¹) ^ K *
      ((c0 : ℂ) * (p v).form j hj a (uB S p F v ε j hj a (p' ++ [(s, t)])) (uB S p F v ε j hj a (q' ++ [(s, t')]))) =
      ((T : ℂ) ^ K * c0) * (((-1) ^ (s - 1) * ((lamB S b s)⁻¹ * (t⁻¹ - t'⁻¹))) ^ K *
        (p v).form j hj a (uB S p F v ε j hj a (p' ++ [(s, t)])) (uB S p F v ε j hj a (q' ++ [(s, t')]))) := by
    simp only [mul_pow]; ring
  rw [eR, hdeg, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hth := (lam_div_theta grid hinj n).1
  have hθ0 : ((F7.thGrid grid n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hth.ne'
  simp only [hPn, uS_mem S p F v ε j hj _ Y _ p' hp', uS_mem S p F v ε j hj _ Y _ q' hq', hlag, hθ]
  push_cast
  field_simp
  ring

end blockLC

def LiftLocBC : Prop :=
  P5.ThmPActualCpt → KB.SizeStdCpt → KB.DegLift → Formalism.FourierDecayAlt.P.PBL.FormPosCpt →
  ∀ (Cb Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    28 * Real.exp 1 ≤ Cc → KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    ∃ Λ : ℕ → ℕ → Fin S.f → ℝ,
      (∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, 0 ≤ Λ b s v ∧ Λ b s v ≤ S.base.szL b s v) ∧
      ∀ F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
        (∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) → ∀ v, KB.LiftLoc (setC S p F) v fun b s => Λ b s v

def LiftLocBPCpt : Prop :=
  P5.ThmPActualCpt → KB.DegLift →
  ∀ (Cb Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    28 * Real.exp 1 ≤ Cc → KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    ∃ Λ : ℕ → ℕ → Fin S.f → ℝ,
      (∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, 0 ≤ Λ b s v ∧ Λ b s v ≤ S.base.szL b s v) ∧
      ∀ F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
        (∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) → ∀ v, KB.LiftLoc (setC S p F) v fun b s => Λ b s v

end

end Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBL Formalism.FourierDecayAlt.P.LiftDegreeLemmas in

theorem Formalism.FourierDecayAlt.P.lift_local_compact_support_route : Formalism.FourierDecayAlt.P.PBL.LiftLocBC := by
  intro hA hSS hDL hFP Cb Cc E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hCc hB
  refine ⟨fun b s v => lamLift S b s v, fun b s hb hs hbs v => thr_lift hCc hB b s hb hs hbs v, fun F hF v => ?_⟩
  intro b s hb hs hbs a ha haK
  have hbs' : b + s ≤ S.G.r + 1 := hbs
  have haK' : a.length + C.Kst ≤ S.Ntop := haK
  have ha' : D.AdmAt S v a := ha
  have haN : a.length ≤ S.Ntop := by omega
  have hgpos := g_pos_of_built hB
  have hj : b + s - 1 ≤ S.G.r := by omega
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGo, hGr, -⟩ := hB'
  have hCI := Formalism.FourierDecayAlt.P.PBCut.cutInside_of_built hB
  obtain ⟨-, grid, hinj, hl1, hmem, hall, hlp, hlm⟩ :=
    Formalism.FourierDecayAlt.P.new_letters_admissible E Wp Wq S hGo hGr hCI v a C.Kst (2 * (b + s - 1 - s) + s) ha' haK' (by omega)
  have hnodes : ∀ n : Fin C.Kst → Fin (2 * (b + s - 1 - s) + s + 1),
      D.AdmAt S v (KB.plusW (List.ofFn fun c => grid c (n c)) a) ∧
      D.AdmAt S v (KB.minusW (List.ofFn fun c => grid c (n c)) a) ∧
      KB.CutWord (D.parOf S v) (S.l + 1) (KB.plusW (List.ofFn fun c => grid c (n c)) a) ∧
      KB.CutWord (D.parOf S v) (S.l + 1) (KB.minusW (List.ofFn fun c => grid c (n c)) a) ∧
      (List.ofFn fun c => grid c (n c)).Pairwise (fun y y' => 2 < |y - y'|) ∧
      ∀ y ∈ (List.ofFn fun c => grid c (n c)), NodeOK S v a false y := fun n => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hall n
    refine ⟨h1, h2, h3, h4, h5.imp fun h => by linarith, fun y hy => Or.inl ⟨rfl, ?_⟩⟩
    obtain ⟨c, rfl⟩ := List.mem_ofFn.1 hy
    exact ⟨a.length + C.Kst - c, by omega, by omega, hmem c (n c)⟩
  refine ⟨PBD.pushU grid (fun ys => KB.plusW ys a), PBD.pushTh grid (fun ys => KB.plusW ys a),
    PBD.pushU grid (fun ys => KB.minusW ys a), PBD.pushTh grid (fun ys => KB.minusW ys a), hlp, hlm,
    fun ε hε t t' Y _ _ hY => ⟨((((‖lamB S b s‖ : ℝ) : ℂ) * (-1) ^ (s - 1) * (lamB S b s)⁻¹) ^ C.Kst),
      norm_u S hgpos b s C.Kst, ?_⟩⟩
  have hK := blockK_liftC hA hDL hSS hFP hB F hF v ε hε (b + s - 1) hj b s hb a ha' haN C.Kst grid hinj hnodes
    (lamLift S b s v) (lamLift_nonneg hB b s v) (lift_K hB v b s (b + s - 1) C.Kst (by omega) grid hl1) t t' Y hY
  refine blockPSD_congr (fun p' _ q' _ => ?_) (fun _ _ _ _ => rfl) (fun p' _ q' _ => ?_) hK
  · show ((lamLift S b s v ^ C.Kst : ℝ) : ℂ) * ∑ n, (F7.thGrid grid n : ℂ) *
        KB.gN (setC S p F) v ε (b + s - 1) (KB.plusW (List.ofFn fun c => grid c (n c)) a) (p' ++ [(s, t)])
          (q' ++ [(s, t)]) =
      ((lamLift S b s v ^ C.Kst : ℝ) : ℂ) * KB.mix (setC S p F) v ε (b + s - 1)
        (PBD.pushU grid fun ys => KB.plusW ys a) (PBD.pushTh grid fun ys => KB.plusW ys a) (p' ++ [(s, t)])
          (q' ++ [(s, t)])
    rw [mix_push]
  · show ((lamLift S b s v ^ C.Kst : ℝ) : ℂ) * ∑ n, (F7.thGrid grid n : ℂ) *
        KB.gN (setC S p F) v ε (b + s - 1) (KB.minusW (List.ofFn fun c => grid c (n c)) a) (p' ++ [(s, t')])
          (q' ++ [(s, t')]) =
      ((lamLift S b s v ^ C.Kst : ℝ) : ℂ) * KB.mix (setC S p F) v ε (b + s - 1)
        (PBD.pushU grid fun ys => KB.minusW ys a) (PBD.pushTh grid fun ys => KB.minusW ys a) (p' ++ [(s, t')])
          (q' ++ [(s, t')])
    rw [mix_push]

theorem Formalism.FourierDecayAlt.P.lift_local_positive_compact_support : Formalism.FourierDecayAlt.P.PBL.LiftLocBPCpt := fun hA hDL =>
  Formalism.FourierDecayAlt.P.lift_local_compact_support_route hA Formalism.FourierDecayAlt.P.size_standard_compact hDL Formalism.FourierDecayAlt.P.module_form_pos_compact_support
