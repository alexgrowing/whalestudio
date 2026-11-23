import Formalism.HermitianCurvature.HermitianCurvatureProofs.SizeAtMinusW

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section pj

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
  (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (ys : List ℝ) {ε : ℝ}

theorem pj_sl (x₁ x₂ : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (y : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (h₁ : NV (p.T.bs j) ε x₁) (h₂ : NV (p.T.bs j) ε x₂) (hy : NV (p.T.bs j) ε y) :
    KB.pairJ (p.form j hj w) ys (x₁ + c • x₂) y =
      KB.pairJ (p.form j hj w) ys x₁ y + c * KB.pairJ (p.form j hj w) ys x₂ y :=
  PBG.pairJ_sesq_left P p.T (M.sgn P p.l0) ⟨j, by omega⟩ w ys x₁ x₂ y c (PBG.decV_of_nice h₁)
    (PBG.decV_of_nice h₂) (PBG.decV_of_nice hy)

theorem pj_sr (x : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (y₁ y₂ : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : NV (p.T.bs j) ε x) (h₁ : NV (p.T.bs j) ε y₁) (h₂ : NV (p.T.bs j) ε y₂) :
    KB.pairJ (p.form j hj w) ys x (y₁ + c • y₂) =
      KB.pairJ (p.form j hj w) ys x y₁ + conj c * KB.pairJ (p.form j hj w) ys x y₂ :=
  PBG.pairJ_sesq_right P p.T (M.sgn P p.l0) ⟨j, by omega⟩ w ys x y₁ y₂ c (PBG.decV_of_nice hx)
    (PBG.decV_of_nice h₁) (PBG.decV_of_nice h₂)

theorem pj_zero_l (y : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (hy : NV (p.T.bs j) ε y) : KB.pairJ (p.form j hj w) ys 0 y = 0 := by
  have h := pj_sl p j hj w ys 0 0 y 1 nv_zero nv_zero hy
  simp only [one_smul, add_zero, one_mul] at h
  linear_combination -h

theorem pj_zero_r (x : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (hx : NV (p.T.bs j) ε x) : KB.pairJ (p.form j hj w) ys x 0 = 0 := by
  have h := pj_sr p j hj w ys x 0 0 1 hx nv_zero nv_zero
  simp only [one_smul, add_zero, map_one, one_mul] at h
  linear_combination -h

theorem pj_smul (x : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (y : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c d : ℂ)
    (hx : NV (p.T.bs j) ε x) (hy : NV (p.T.bs j) ε y) :
    KB.pairJ (p.form j hj w) ys (c • x) (d • y) = c * conj d * KB.pairJ (p.form j hj w) ys x y := by
  have h1 := pj_sl p j hj w ys 0 x (d • y) c nv_zero hx (nv_smul d hy)
  have h2 := pj_sr p j hj w ys x 0 y d hx nv_zero hy
  rw [zero_add, pj_zero_l p j hj w ys _ (nv_smul d hy), zero_add] at h1
  rw [zero_add, pj_zero_r p j hj w ys x hx, zero_add] at h2
  rw [h1, h2]; ring

end pj

section deg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem uB_pos (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j) :
    uB S p F v ε j hj w h = (((√(nnS S h) / bS S h : ℝ) : ℂ)) •
      KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2) := by
  unfold uB; rw [dif_pos hh]

theorem uB_neg (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (h : C.LPt) (hh : ¬ D.IsLocPt h j) : uB S p F v ε j hj w h = 0 := by
  unfold uB; rw [dif_neg hh]

theorem waveG_smul' {k ρ : ℕ} {Wp' Wq' : Type} [NormedAddCommGroup Wp'] [InnerProductSpace ℂ Wp']
    [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] (Bs : B.RealPlaceData k ρ Wp' Wq') (s : ℂ) (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq' →L[ℂ] Wp')) (c : ℂ) :
    KB.waveG Bs s w (c • x) = c • KB.waveG Bs s w x := by
  have := PBG.waveG_add_smul Bs s w 0 x c
  rwa [zero_add, PBG.waveG_zero, zero_add] at this

theorem deg_uB (hDW : KB.DegWave) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (a : List C.Letter) (K : ℕ) (grid : Fin K → Fin (2 * j + 1) → ℝ)
    (hinj : ∀ b, Function.Injective (grid b)) (s : ℂ) (h h' : C.LPt) :
    s ^ K * (p v).form j hj a (KB.waveG ((p v).T.bs j) s a (uB S p F v ε j hj a h)) (uB S p F v ε j hj a h') =
      ∑ n : Fin K → Fin (2 * j + 1), ((∏ b, F7.lagCo (grid b) (n b) : ℝ) : ℂ) *
        KB.pairJ ((p v).form j hj a) (List.ofFn fun b => grid b (n b))
          (KB.waveG ((p v).T.bs j) s _ (uB S p F v ε j hj (KB.plusW (List.ofFn fun b => grid b (n b)) a) h))
          (uB S p F v ε j hj (KB.minusW (List.ofFn fun b => grid b (n b)) a) h') := by
  have hgpos := g_pos_of_built hB
  by_cases hloc : D.IsLocPt h j ∧ D.IsLocPt h' j
  · obtain ⟨hh, hh'⟩ := hloc
    have hH : D.IsLocPt (stdS S h) j := (PBD.isLocPt_toStd_iff _ _ hgpos h 1 j).2 hh
    have hH' : D.IsLocPt (stdS S h') j := (PBD.isLocPt_toStd_iff _ _ hgpos h' 1 j).2 hh'
    have hdeg := hDW (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (F v ε) j hj a (stdS S h) (stdS S h') hH hH' K
      grid s LinearMap.id (fun ε x hx => hx) (hF v ε hε) hinj
    simp only [LinearMap.id_apply, onOld_id] at hdeg
    set Dh : ℂ := (((√(nnS S h) / bS S h : ℝ) : ℂ)) with hDh
    set Dh' : ℂ := (((√(nnS S h') / bS S h' : ℝ) : ℂ)) with hDh'
    rw [uB_pos S p F v ε j hj a h hh, uB_pos S p F v ε j hj a h' hh', waveG_smul']
    obtain ⟨ε2, hε2, hs, hs'⟩ := nv_pair (slv_nv (p v) (hF v ε hε) j hj a (stdS S h) hH)
      (slv_nv (p v) (hF v ε hε) j hj a (stdS S h') hH')
    have hws := PBFV.waveG_nice ((p v).T.bs j) ε2 s a _ hs
    rw [form_smul_l (p v) j hj a _ _ _ hws (nv_smul _ hs'), form_smul_r (p v) j hj a _ _ _ hws hs']
    have hL : s ^ K * (Dh * (conj Dh' * (p v).form j hj a (KB.waveG ((p v).T.bs j) s a
        (KB.slv (p v).T (F v ε) j hj a (stdS S h) ((stdS_size S h).trans hh.2)))
        (KB.slv (p v).T (F v ε) j hj a (stdS S h') ((stdS_size S h').trans hh'.2)))) =
        Dh * conj Dh' * (s ^ K * (p v).form j hj a (KB.waveG ((p v).T.bs j) s a
        (KB.slv (p v).T (F v ε) j hj a (stdS S h) hH.2)) (KB.slv (p v).T (F v ε) j hj a (stdS S h') hH'.2)) := by
      ring
    rw [hL, hdeg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    set ys := List.ofFn fun b => grid b (n b) with hys
    obtain ⟨ε3, hε3, hp, hm⟩ := nv_pair (slv_nv (p v) (hF v ε hε) j hj (KB.plusW ys a) (stdS S h) hH)
      (slv_nv (p v) (hF v ε hε) j hj (KB.minusW ys a) (stdS S h') hH')
    have hwp := PBFV.waveG_nice ((p v).T.bs j) ε3 s _ _ hp
    rw [uB_pos S p F v ε j hj (KB.plusW ys a) h hh, uB_pos S p F v ε j hj (KB.minusW ys a) h' hh', waveG_smul',
      pj_smul (p v) j hj a ys _ _ _ _ hwp hm]
    ring
  · have h0 : uB S p F v ε j hj a h = 0 ∨ uB S p F v ε j hj a h' = 0 := by
      by_cases hh : D.IsLocPt h j
      · exact Or.inr (uB_neg S p F v ε j hj a h' fun hh' => hloc ⟨hh, hh'⟩)
      · exact Or.inl (uB_neg S p F v ε j hj a h hh)
    obtain ⟨ε1, hε1, hx, hx'⟩ := nv_pair (uB_nv hB F hF v ε hε j hj a h) (uB_nv hB F hF v ε hε j hj a h')
    have hwx := PBFV.waveG_nice ((p v).T.bs j) ε1 s a _ hx
    have lhs0 : (p v).form j hj a (KB.waveG ((p v).T.bs j) s a (uB S p F v ε j hj a h)) (uB S p F v ε j hj a h') = 0 := by
      rcases h0 with h0 | h0
      · rw [h0, PBG.waveG_zero, form_zero_l (p v) j hj a _ hx']
      · rw [h0, form_zero_r (p v) j hj a _ hwx]
    rw [lhs0, mul_zero]
    symm
    refine Finset.sum_eq_zero fun n _ => ?_
    set ys := List.ofFn fun b => grid b (n b) with hys
    obtain ⟨ε3, hε3, hp, hm⟩ := nv_pair (uB_nv hB F hF v ε hε j hj (KB.plusW ys a) h)
      (uB_nv hB F hF v ε hε j hj (KB.minusW ys a) h')
    have hwp := PBFV.waveG_nice ((p v).T.bs j) ε3 s _ _ hp
    by_cases hh : D.IsLocPt h j
    · rw [uB_neg S p F v ε j hj (KB.minusW ys a) h' fun hh' => hloc ⟨hh, hh'⟩, pj_zero_r (p v) j hj a ys _ hwp, mul_zero]
    · rw [uB_neg S p F v ε j hj (KB.plusW ys a) h hh, PBG.waveG_zero, pj_zero_l (p v) j hj a ys _ hm, mul_zero]

end deg

section kern

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem gam_pos (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (j : ℕ) : 0 < ΓS S j := by
  have hgpos := g_pos_of_built hB
  have hrd := PBD.rd_pos' E
  unfold ΓS
  exact PBD.gamLev_pos _ _ _ _ (by unfold D.kapG; positivity) (by unfold D.deG; positivity) _

def uY (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (Y : Finset C.LPt) (h : C.LPt) :
    Wd.Ix (Fin w.length) → B.Mat S.G.k (S.G.r - j) → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) :=
  if h ∈ Y then uB S p F v ε j hj w h else 0

theorem uY_nv (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (Y : Finset C.LPt) :
    ∃ ε', 0 < ε' ∧ ∀ h, NV ((p v).T.bs j) ε' (uY S p F v ε j hj w Y h) := by
  obtain ⟨ε0, hε0, hall⟩ := nv_common Y (uB S p F v ε j hj w) (fun h _ => uB_nv hB F hF v ε hε j hj w h)
  refine ⟨ε0, hε0, fun h => ?_⟩
  unfold uY
  split_ifs with hh
  · exact hall h hh
  · exact nv_zero

theorem uY_mem (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (Y : Finset C.LPt) (h : C.LPt) (hh : h ∈ Y) :
    uY S p F v ε j hj w Y h = uB S p F v ε j hj w h := by
  unfold uY; rw [if_pos hh]

theorem gN_psd (hA : P5.ThmPActual) (hFP : FormPos) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (hw : KB.CutWord (D.parOf S v) (S.l + 1) w) (Y : Finset C.LPt) :
    TB.PSDOn Y (KB.gN (setC S p F) v ε j w) := by
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, -, -, -, -⟩ := hv v
  have hw' : KB.CutWord (D.parOf S v) (p v).l0 w := by rw [hl0]; exact hw
  obtain ⟨ε0, hε0, hu⟩ := uY_nv hB F hF v ε hε j hj w Y
  set c0 : ℝ := 1 / (ΓS S j * S.sizeAt v w) with hc0
  have hc0n : 0 ≤ c0 := by
    have := gam_pos hB j
    have := sizeAt_nonneg S v w
    positivity
  set Dv := NV ((p v).T.bs j) ε0 (S := Fin w.length) with hDv
  have hG := gram_psd Dv (fun x y => (c0 : ℂ) * (p v).form j hj w x y) nv_zero (fun x y hx hy => nv_add hx hy)
    (fun c x hx => nv_smul c hx)
    (fun x₁ x₂ y c h₁ h₂ hy => by simp only [form_sl (p v) j hj w x₁ x₂ y c h₁ h₂ hy]; ring)
    (fun x y₁ y₂ c hx h₁ h₂ => by simp only [form_sr (p v) j hj w x y₁ y₂ c hx h₁ h₂]; ring)
    (fun x hx => mul_nonneg (by exact_mod_cast hc0n) (hFP hA _ _ (D.parOf S v) (p v) j hj w hw' x ε0 hε0 hx))
    Y (uY S p F v ε j hj w Y) hu
  refine psd_congr (fun x hx y hy => ?_) hG
  show (c0 : ℂ) * (p v).form j hj w (uY S p F v ε j hj w Y x) (uY S p F v ε j hj w Y y) = _
  rw [uY_mem S p F v ε j hj w Y x hx, uY_mem S p F v ε j hj w Y y hy, gN_uB hB F hF v ε hε j hj w x y]

theorem blockPSD_congr {α : Type} {Y : Finset α} {a a' b b' w w' : α → α → ℂ}
    (ha : ∀ x ∈ Y, ∀ y ∈ Y, a x y = a' x y) (hw : ∀ x ∈ Y, ∀ y ∈ Y, w x y = w' x y)
    (hb : ∀ x ∈ Y, ∀ y ∈ Y, b x y = b' x y) (h : KB.BlockPSD Y Y a w b) : KB.BlockPSD Y Y a' w' b' := by
  rw [PBA.blockPSD_iff] at h ⊢
  refine psd_congr (fun x hx y hy => ?_) h
  cases x with
  | inl x =>
    cases y with
    | inl y => exact ha x (Finset.inl_mem_disjSum.1 hx) y (Finset.inl_mem_disjSum.1 hy)
    | inr y => exact hw x (Finset.inl_mem_disjSum.1 hx) y (Finset.inr_mem_disjSum.1 hy)
  | inr x =>
    cases y with
    | inl y =>
      show conj (w y x) = conj (w' y x)
      rw [hw y (Finset.inl_mem_disjSum.1 hy) x (Finset.inr_mem_disjSum.1 hx)]
    | inr y => exact hb x (Finset.inr_mem_disjSum.1 hx) y (Finset.inr_mem_disjSum.1 hy)

end kern

theorem lam_div_theta {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (hinj : ∀ b, Function.Injective (grid b))
    (n : Fin K → Fin (d + 1)) :
    0 < F7.thGrid grid n ∧
      |∏ b, F7.lagCo (grid b) (n b)| / F7.thGrid grid n = ∏ b, ∑ i, |F7.lagCo (grid b) i| := by
  have hs : ∀ b, 0 < ∑ i, |F7.lagCo (grid b) i| := fun b =>
    lt_of_lt_of_le (abs_pos.2 (PBD.lagCo_ne_zero _ (hinj b) (n b)))
      (Finset.single_le_sum (f := fun i => |F7.lagCo (grid b) i|) (fun i _ => abs_nonneg _) (Finset.mem_univ _))
  have hl : ∀ b, 0 < |F7.lagCo (grid b) (n b)| := fun b => abs_pos.2 (PBD.lagCo_ne_zero _ (hinj b) (n b))
  have hth : 0 < F7.thGrid grid n := Finset.prod_pos fun b _ => div_pos (hl b) (hs b)
  refine ⟨hth, ?_⟩
  unfold F7.thGrid
  rw [Finset.abs_prod, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun b _ => ?_
  field_simp [(hl b).ne', (hs b).ne']

theorem ratio_bound {K : ℕ} (ys : Fin K → ℝ) (Pv qv : ℝ → ℝ) (Λ T Γ sa B Xc : ℝ) (hΓ : 0 < Γ) (hsa : 0 < sa)
    (hq : ∀ b, 0 < qv (ys b)) (hP : ∀ b, Pv (ys b) ≠ 0) (hP' : ∀ b, Pv (ys b + 1) ≠ 0)
    (hnode : ∀ b, |Pv (ys b) * Pv (ys b + 1)| / qv (ys b) ≤ B ^ 2) (hΛ : 0 ≤ Λ) (hT : 0 ≤ T) (hB0 : 0 ≤ B)
    (hX : Λ * T ^ K * B ^ K ≤ Xc ^ K) :
    (Λ * T ^ K * (1 / (Γ * sa))) ^ 2 / ((∏ b, qv (ys b)) * (1 / (Γ * ((∏ b, |Pv (ys b)|) * sa))) *
      (1 / (Γ * ((∏ b, |Pv (ys b + 1)|) * sa)))) ≤ (Xc ^ K) ^ 2 := by
  have hQ : 0 < ∏ b, qv (ys b) := Finset.prod_pos fun b _ => hq b
  have hPp : 0 < ∏ b, |Pv (ys b)| := Finset.prod_pos fun b _ => abs_pos.2 (hP b)
  have hPm : 0 < ∏ b, |Pv (ys b + 1)| := Finset.prod_pos fun b _ => abs_pos.2 (hP' b)
  have e : (Λ * T ^ K * (1 / (Γ * sa))) ^ 2 / ((∏ b, qv (ys b)) * (1 / (Γ * ((∏ b, |Pv (ys b)|) * sa))) *
      (1 / (Γ * ((∏ b, |Pv (ys b + 1)|) * sa)))) =
      (Λ * T ^ K) ^ 2 * ∏ b, (|Pv (ys b) * Pv (ys b + 1)| / qv (ys b)) := by
    rw [Finset.prod_div_distrib]
    simp only [abs_mul, Finset.prod_mul_distrib]
    field_simp
  rw [e]
  have hprod : ∏ b, (|Pv (ys b) * Pv (ys b + 1)| / qv (ys b)) ≤ (B ^ 2) ^ K := by
    calc ∏ b, (|Pv (ys b) * Pv (ys b + 1)| / qv (ys b)) ≤ ∏ _b : Fin K, B ^ 2 :=
          Finset.prod_le_prod (fun b _ => div_nonneg (abs_nonneg _) (hq b).le) fun b _ => hnode b
      _ = (B ^ 2) ^ K := by simp
  have h0 : 0 ≤ Λ * T ^ K * B ^ K := by positivity
  calc (Λ * T ^ K) ^ 2 * ∏ b, (|Pv (ys b) * Pv (ys b + 1)| / qv (ys b)) ≤ (Λ * T ^ K) ^ 2 * (B ^ 2) ^ K :=
        mul_le_mul_of_nonneg_left hprod (sq_nonneg _)
    _ = (Λ * T ^ K * B ^ K) ^ 2 := by ring
    _ ≤ (Xc ^ K) ^ 2 := pow_le_pow_left₀ h0 hX 2

end

end Formalism.FourierDecayAlt.P.PBL
