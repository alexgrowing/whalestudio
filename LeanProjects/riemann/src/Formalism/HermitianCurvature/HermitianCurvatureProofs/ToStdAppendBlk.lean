import Formalism.HermitianCurvature.HermitianCurvatureProofs.RatioBound

namespace Formalism.FourierDecayAlt.P.LiftDegreeLemmas

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField Formalism.FourierDecayAlt.P.PBL
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem toStd_append_blk (r : ℕ) (g : ℝ) (s : ℕ) (c : ℂ) : ∀ (h : C.LPt) (b : ℕ),
    D.toStd r g b (h ++ [(s, c)]) = D.toStd r g b h ++
      [(s, (((g / (2 * Real.pi)) ^ S6.nuBlock r ((b + D.ptSize h : ℕ) : ℤ) (s : ℤ) : ℝ) : ℂ) *
        Complex.I ^ (s - 1) * c)]
  | [], b => by simp [D.toStd, D.ptSize]
  | (s', t) :: rest, b => by
    have ih := toStd_append_blk r g s c rest (b + s')
    simp only [List.cons_append, D.toStd, ih, D.ptSize, List.map_cons, List.sum_cons, add_assoc]

theorem slv_congr {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (T : D.LevTower k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (i : ℕ) (hi : i ≤ r)
    (w : List C.Letter) {P P' : C.LPt} (e : P = P') (hP : D.ptSize P = i) (hP' : D.ptSize P' = i) :
    KB.slv T F i hi w P hP = KB.slv T F i hi w P' hP' := by
  subst e; rfl

theorem psd_shift {Y : Finset C.LPt} {k : C.LPt → C.LPt → ℂ} (blk : ℕ × ℂ)
    (hk : TB.PSDOn (Y.image fun h => h ++ [blk]) k) : TB.PSDOn Y fun p q => k (p ++ [blk]) (q ++ [blk]) := by
  have hinj : Set.InjOn (fun h : C.LPt => h ++ [blk]) Y := fun x _ y _ hxy => List.append_cancel_right hxy
  rw [PBA.psd_iff_qf] at hk ⊢
  obtain ⟨hh, hq⟩ := hk
  refine ⟨fun x hx y hy => hh _ (Finset.mem_image_of_mem _ hx) _ (Finset.mem_image_of_mem _ hy), fun c => ?_⟩
  have e : PBA.qf Y (fun p q => k (p ++ [blk]) (q ++ [blk])) c =
      PBA.qf (Y.image fun h => h ++ [blk]) k (fun z => c z.dropLast) := by
    unfold PBA.qf
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp
  rw [e]; exact hq _

section lam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def lamB (S : C.HidaSetting E Wp Wq) (b s : ℕ) : ℂ :=
  ((((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r (b : ℤ) (s : ℤ) : ℝ) : ℂ) * Complex.I ^ (s - 1)

theorem stdS_blk (S : C.HidaSetting E Wp Wq) (b s : ℕ) (hb : 1 ≤ b) (H : C.LPt) (hH : D.ptSize H = b - 1) (t : ℂ) :
    stdS S (H ++ [(s, t)]) = stdS S H ++ [(s, lamB S b s * t)] := by
  unfold stdS lamB
  rw [toStd_append_blk, hH, show 1 + (b - 1) = b by omega]

theorem norm_lamB (S : C.HidaSetting E Wp Wq) (hg : (0 : ℝ) < S.g) (b s : ℕ) :
    ‖lamB S b s‖ = ((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r (b : ℤ) (s : ℤ) := by
  unfold lamB
  rw [norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one, Complex.norm_real, Real.norm_of_nonneg]
  exact zpow_nonneg (by positivity) _

theorem lamB_ne (S : C.HidaSetting E Wp Wq) (hg : (0 : ℝ) < S.g) (b s : ℕ) : lamB S b s ≠ 0 := by
  intro h
  have := norm_lamB S hg b s
  rw [h, norm_zero] at this
  exact (zpow_pos (by positivity : (0 : ℝ) < (S.g : ℝ) / (2 * Real.pi)) _).ne this

end lam

section deg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem uB_blk (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (b s : ℕ) (hb : 1 ≤ b) (H : C.LPt) (hH : D.ptSize H = b - 1) (t : ℂ)
    (hP : D.IsLocPt (H ++ [(s, t)]) j) :
    ∃ hX : D.IsLocPt (stdS S H ++ [(s, lamB S b s * t)]) j,
      uB S p F v ε j hj w (H ++ [(s, t)]) = (((√(nnS S (H ++ [(s, t)])) / bS S (H ++ [(s, t)]) : ℝ) : ℂ)) •
        KB.slv (p v).T (F v ε) j hj w (stdS S H ++ [(s, lamB S b s * t)]) hX.2 := by
  have hgpos := g_pos_of_built hB
  have e := stdS_blk S b s hb H hH t
  have hX : D.IsLocPt (stdS S H ++ [(s, lamB S b s * t)]) j := by
    rw [← e]; exact (PBD.isLocPt_toStd_iff _ _ hgpos _ 1 j).2 hP
  refine ⟨hX, ?_⟩
  rw [uB_pos S p F v ε j hj w _ hP]
  congr 1
  exact slv_congr _ _ _ _ _ e _ _

theorem deg_uB_lift (hDL : KB.DegLift) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (b s : ℕ) (hb : 1 ≤ b) (a : List C.Letter) (K : ℕ)
    (grid : Fin K → Fin (2 * (j - s) + s + 1) → ℝ) (hinj : ∀ c, Function.Injective (grid c))
    (H H' : C.LPt) (hH : D.ptSize H = b - 1) (hH' : D.ptSize H' = b - 1) (t t' : ℂ) :
    ((-1) ^ (s - 1) * ((lamB S b s * t)⁻¹ - (lamB S b s * t')⁻¹)) ^ K *
        (p v).form j hj a (uB S p F v ε j hj a (H ++ [(s, t)])) (uB S p F v ε j hj a (H' ++ [(s, t')])) =
      ∑ n : Fin K → Fin (2 * (j - s) + s + 1), ((∏ c, F7.lagCo (grid c) (n c) : ℝ) : ℂ) *
        KB.pairJ ((p v).form j hj a) (List.ofFn fun c => grid c (n c))
          (uB S p F v ε j hj (KB.plusW (List.ofFn fun c => grid c (n c)) a) (H ++ [(s, t)]))
          (uB S p F v ε j hj (KB.minusW (List.ofFn fun c => grid c (n c)) a) (H' ++ [(s, t')])) := by
  by_cases hloc : D.IsLocPt (H ++ [(s, t)]) j ∧ D.IsLocPt (H' ++ [(s, t')]) j
  · obtain ⟨hP, hP'⟩ := hloc
    obtain ⟨hX, eX⟩ := uB_blk hB F v ε j hj a b s hb H hH t hP
    obtain ⟨hX', eX'⟩ := uB_blk hB F v ε j hj a b s hb H' hH' t' hP'
    have hdeg := hDL (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (F v ε) j s hj a (stdS S H) (stdS S H')
      (lamB S b s * t) (lamB S b s * t') hX hX' K grid (hF v ε hε) hinj
    rw [rr_eq_form (p v) (F v ε) j hj a _ _ hX hX'] at hdeg
    set Dh : ℂ := (((√(nnS S (H ++ [(s, t)])) / bS S (H ++ [(s, t)]) : ℝ) : ℂ)) with hDh
    set Dh' : ℂ := (((√(nnS S (H' ++ [(s, t')])) / bS S (H' ++ [(s, t')]) : ℝ) : ℂ)) with hDh'
    obtain ⟨ε2, hε2, hs, hs'⟩ := nv_pair (slv_nv (p v) (hF v ε hε) j hj a _ hX)
      (slv_nv (p v) (hF v ε hε) j hj a _ hX')
    rw [eX, eX', form_smul_l (p v) j hj a _ _ _ hs (nv_smul _ hs'), form_smul_r (p v) j hj a _ _ _ hs hs']
    have hL : ((-1) ^ (s - 1) * ((lamB S b s * t)⁻¹ - (lamB S b s * t')⁻¹)) ^ K *
        (Dh * (conj Dh' * (p v).form j hj a (KB.slv (p v).T (F v ε) j hj a _ hX.2)
          (KB.slv (p v).T (F v ε) j hj a _ hX'.2))) =
        Dh * conj Dh' * (((-1) ^ (s - 1) * ((lamB S b s * t)⁻¹ - (lamB S b s * t')⁻¹)) ^ K *
          (p v).form j hj a (KB.slv (p v).T (F v ε) j hj a _ hX.2) (KB.slv (p v).T (F v ε) j hj a _ hX'.2)) := by
      ring
    rw [hL, hdeg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    set ys := List.ofFn fun c => grid c (n c) with hys
    obtain ⟨hXp, eXp⟩ := uB_blk hB F v ε j hj (KB.plusW ys a) b s hb H hH t hP
    obtain ⟨hXm, eXm⟩ := uB_blk hB F v ε j hj (KB.minusW ys a) b s hb H' hH' t' hP'
    obtain ⟨ε3, hε3, hp, hm⟩ := nv_pair (slv_nv (p v) (hF v ε hε) j hj (KB.plusW ys a) _ hX)
      (slv_nv (p v) (hF v ε hε) j hj (KB.minusW ys a) _ hX')
    rw [eXp, eXm, pj_smul (p v) j hj a ys _ _ _ _ hp hm]
    ring
  · have h0 : ∀ w : List C.Letter, uB S p F v ε j hj w (H ++ [(s, t)]) = 0 ∨
        uB S p F v ε j hj w (H' ++ [(s, t')]) = 0 := by
      intro w
      by_cases hh : D.IsLocPt (H ++ [(s, t)]) j
      · exact Or.inr (uB_neg S p F v ε j hj w _ fun hh' => hloc ⟨hh, hh'⟩)
      · exact Or.inl (uB_neg S p F v ε j hj w _ hh)
    obtain ⟨ε1, hε1, hx, hx'⟩ := nv_pair (uB_nv hB F hF v ε hε j hj a (H ++ [(s, t)]))
      (uB_nv hB F hF v ε hε j hj a (H' ++ [(s, t')]))
    have lhs0 : (p v).form j hj a (uB S p F v ε j hj a (H ++ [(s, t)])) (uB S p F v ε j hj a (H' ++ [(s, t')])) = 0 := by
      rcases h0 a with h0 | h0
      · rw [h0, form_zero_l (p v) j hj a _ hx']
      · rw [h0, form_zero_r (p v) j hj a _ hx]
    rw [lhs0, mul_zero]
    symm
    refine Finset.sum_eq_zero fun n _ => ?_
    set ys := List.ofFn fun c => grid c (n c) with hys
    obtain ⟨ε3, hε3, hp, hm⟩ := nv_pair (uB_nv hB F hF v ε hε j hj (KB.plusW ys a) (H ++ [(s, t)]))
      (uB_nv hB F hF v ε hε j hj (KB.minusW ys a) (H' ++ [(s, t')]))
    by_cases hh : D.IsLocPt (H ++ [(s, t)]) j
    · rw [uB_neg S p F v ε j hj (KB.minusW ys a) _ fun hh' => hloc ⟨hh, hh'⟩, pj_zero_r (p v) j hj a ys _ hp, mul_zero]
    · rw [uB_neg S p F v ε j hj (KB.plusW ys a) _ hh, pj_zero_l (p v) j hj a ys _ hm, mul_zero]

end deg

end

end Formalism.FourierDecayAlt.P.LiftDegreeLemmas
