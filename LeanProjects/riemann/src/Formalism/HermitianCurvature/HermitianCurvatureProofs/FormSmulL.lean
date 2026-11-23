import Formalism.HermitianCurvature.HermitianCurvatureProofs.AeNeZeroComplex
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftDegreeLemmas
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVnice

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section formh

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
  (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) {ε : ℝ}

theorem form_zero_l (y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (hy : NV (p.T.bs j) ε y) :
    p.form j hj w 0 y = 0 := by
  have h := form_sl p j hj w 0 0 y 1 nv_zero nv_zero hy
  simp only [one_smul, add_zero, one_mul] at h
  linear_combination -h

theorem form_zero_r (x : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (hx : NV (p.T.bs j) ε x) :
    p.form j hj w x 0 = 0 := by
  have h := form_sr p j hj w x 0 0 1 hx nv_zero nv_zero
  simp only [one_smul, add_zero, map_one, one_mul] at h
  linear_combination -h

theorem form_smul_l (x y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : NV (p.T.bs j) ε x) (hy : NV (p.T.bs j) ε y) : p.form j hj w (c • x) y = c * p.form j hj w x y := by
  have h := form_sl p j hj w 0 x y c nv_zero hx hy
  rw [zero_add, form_zero_l p j hj w y hy, zero_add] at h
  exact h

theorem form_smul_r (x y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : NV (p.T.bs j) ε x) (hy : NV (p.T.bs j) ε y) : p.form j hj w x (c • y) = conj c * p.form j hj w x y := by
  have h := form_sr p j hj w x 0 y c hx nv_zero hy
  rw [zero_add, form_zero_r p j hj w x hx, zero_add] at h
  exact h

end formh

section block0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def uB (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (h : C.LPt) :
    Wd.Ix (Fin w.length) → B.Mat S.G.k (S.G.r - j) → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) :=
  if hh : D.IsLocPt h j then
    (((√(nnS S h) / bS S h : ℝ) : ℂ)) • KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2)
  else 0

theorem dW_split (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (j : ℕ) (w : List C.Letter) (h h' : C.LPt) :
    dW S v j w h h' = (√(nnS S h) / bS S h) * (√(nnS S h') / bS S h') * (1 / (ΓS S j * S.sizeAt v w)) := by
  unfold dW; ring

theorem uB_nv {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (h : C.LPt) :
    ∃ ε', 0 < ε' ∧ NV ((p v).T.bs j) ε' (uB S p F v ε j hj w h) := by
  have hgpos := g_pos_of_built hB
  unfold uB
  split_ifs with hh
  · have hH : D.IsLocPt (stdS S h) j := (PBD.isLocPt_toStd_iff _ _ hgpos h 1 j).2 hh
    obtain ⟨ε', hε', hn⟩ := slv_nv (p v) (hF v ε hε) j hj w (stdS S h) hH
    exact ⟨ε', hε', nv_smul _ hn⟩
  · exact ⟨1, one_pos, nv_zero⟩

end block0

section block0b

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem nv_pair {k ρ : ℕ} {Wp' Wq' : Type} [NormedAddCommGroup Wp'] [InnerProductSpace ℂ Wp'] [NormedAddCommGroup Wq']
    [InnerProductSpace ℂ Wq'] {Sx Sy : Type} {Bs : B.RealPlaceData k ρ Wp' Wq'} {x : Wd.Ix Sx → B.Mat k ρ → (Wq' →L[ℂ] Wp')}
    {y : Wd.Ix Sy → B.Mat k ρ → (Wq' →L[ℂ] Wp')}
    (hx : ∃ ε, 0 < ε ∧ NV Bs ε x) (hy : ∃ ε, 0 < ε ∧ NV Bs ε y) : ∃ ε, 0 < ε ∧ NV Bs ε x ∧ NV Bs ε y := by
  obtain ⟨a, ha, hxa⟩ := hx
  obtain ⟨b, hb, hyb⟩ := hy
  exact ⟨min a b, lt_min ha hb, nv_mono hxa (min_le_left _ _), nv_mono hyb (min_le_right _ _)⟩

theorem gN_uB (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (h h' : C.LPt) :
    KB.gN (setC S p F) v ε j w h h' =
      ((1 / (ΓS S j * S.sizeAt v w) : ℝ) : ℂ) * (p v).form j hj w (uB S p F v ε j hj w h) (uB S p F v ε j hj w h') := by
  have hgpos := g_pos_of_built hB
  obtain ⟨ε1, hε1, hx, hx'⟩ := nv_pair (uB_nv hB F hF v ε hε j hj w h) (uB_nv hB F hF v ε hε j hj w h')
  by_cases hloc : D.IsLocPt h j ∧ D.IsLocPt h' j
  · obtain ⟨hh, hh'⟩ := hloc
    have hH : D.IsLocPt (stdS S h) j := (PBD.isLocPt_toStd_iff _ _ hgpos h 1 j).2 hh
    have hH' : D.IsLocPt (stdS S h') j := (PBD.isLocPt_toStd_iff _ _ hgpos h' 1 j).2 hh'
    obtain ⟨ε2, hε2, hs, hs'⟩ := nv_pair (slv_nv (p v) (hF v ε hε) j hj w (stdS S h) hH)
      (slv_nv (p v) (hF v ε hε) j hj w (stdS S h') hH')
    rw [gN_setC_form hB F v ε j hj w h h' hh hh']
    have e1 : uB S p F v ε j hj w h = (((√(nnS S h) / bS S h : ℝ) : ℂ)) •
        KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2) := by
      unfold uB; rw [dif_pos hh]
    have e2 : uB S p F v ε j hj w h' = (((√(nnS S h') / bS S h' : ℝ) : ℂ)) •
        KB.slv (p v).T (F v ε) j hj w (stdS S h') ((stdS_size S h').trans hh'.2) := by
      unfold uB; rw [dif_pos hh']
    rw [e1, e2, form_smul_l (p v) j hj w _ _ _ hs (nv_smul _ hs'), form_smul_r (p v) j hj w _ _ _ hs hs',
      Complex.conj_ofReal, dW_split]
    push_cast
    ring
  · rw [gN_setC_zero hB F v ε j w h h' hloc]
    have : uB S p F v ε j hj w h = 0 ∨ uB S p F v ε j hj w h' = 0 := by
      by_cases hh : D.IsLocPt h j
      · right; unfold uB; rw [dif_neg (fun hh' => hloc ⟨hh, hh'⟩)]
      · left; unfold uB; rw [dif_neg hh]
    rcases this with h0 | h0
    · rw [h0, form_zero_l (p v) j hj w _ hx', mul_zero]
    · rw [h0, form_zero_r (p v) j hj w _ hx, mul_zero]

theorem hatB_uB (hA : P5.ThmPActual) (hPS : KB.PStd) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (hw : KB.CutWord (D.parOf S v) (S.l + 1) w) (l : ℂ) (h h' : C.LPt)
    (hsz : D.ptSize h = j) (hsz' : D.ptSize h' = j) :
    KB.hatB (setC S p F) v ε (j + 1) 1 w l h h' =
      ((1 / (ΓS S j * S.sizeAt v w) : ℝ) : ℂ) * (p v).form j hj w
        (KB.waveG ((p v).T.bs j) (sW S j l) w (uB S p F v ε j hj w h)) (uB S p F v ε j hj w h') := by
  have hgpos := g_pos_of_built hB
  obtain ⟨ε1, hε1, hx, hx'⟩ := nv_pair (uB_nv hB F hF v ε hε j hj w h) (uB_nv hB F hF v ε hε j hj w h')
  have hwx := PBFV.waveG_nice ((p v).T.bs j) ε1 (sW S j l) w _ hx
  by_cases hloc : D.IsLocPt h j ∧ D.IsLocPt h' j
  · obtain ⟨hh, hh'⟩ := hloc
    have hH : D.IsLocPt (stdS S h) j := (PBD.isLocPt_toStd_iff _ _ hgpos h 1 j).2 hh
    have hH' : D.IsLocPt (stdS S h') j := (PBD.isLocPt_toStd_iff _ _ hgpos h' 1 j).2 hh'
    obtain ⟨ε2, hε2, hs, hs'⟩ := nv_pair (slv_nv (p v) (hF v ε hε) j hj w (stdS S h) hH)
      (slv_nv (p v) (hF v ε hε) j hj w (stdS S h') hH')
    rw [hatB_setC hA hPS hB F hF v ε hε j hj w hw l h h' hh hh']
    have e1 : uB S p F v ε j hj w h = (((√(nnS S h) / bS S h : ℝ) : ℂ)) •
        KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2) := by
      unfold uB; rw [dif_pos hh]
    have e2 : uB S p F v ε j hj w h' = (((√(nnS S h') / bS S h' : ℝ) : ℂ)) •
        KB.slv (p v).T (F v ε) j hj w (stdS S h') ((stdS_size S h').trans hh'.2) := by
      unfold uB; rw [dif_pos hh']
    have hws := PBFV.waveG_nice ((p v).T.bs j) ε2 (sW S j l) w _ hs
    have ew : KB.waveG ((p v).T.bs j) (sW S j l) w ((((√(nnS S h) / bS S h : ℝ) : ℂ)) •
        KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2)) =
        (((√(nnS S h) / bS S h : ℝ) : ℂ)) • KB.waveG ((p v).T.bs j) (sW S j l) w
          (KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2)) := by
      have := PBG.waveG_add_smul ((p v).T.bs j) (sW S j l) w 0
        (KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2)) (((√(nnS S h) / bS S h : ℝ) : ℂ))
      rw [zero_add, PBG.waveG_zero, zero_add] at this
      exact this
    rw [e1, e2, ew, form_smul_l (p v) j hj w _ _ _ hws (nv_smul _ hs'), form_smul_r (p v) j hj w _ _ _ hws hs',
      Complex.conj_ofReal, dW_split]
    push_cast
    ring
  · rw [hatB_setC_zero hB F v ε j w l h h' hsz hsz' hloc]
    have : uB S p F v ε j hj w h = 0 ∨ uB S p F v ε j hj w h' = 0 := by
      by_cases hh : D.IsLocPt h j
      · right; unfold uB; rw [dif_neg (fun hh' => hloc ⟨hh, hh'⟩)]
      · left; unfold uB; rw [dif_neg hh]
    rcases this with h0 | h0
    · rw [h0, PBG.waveG_zero, form_zero_l (p v) j hj w _ hx', mul_zero]
    · rw [h0, form_zero_r (p v) j hj w _ hwx, mul_zero]

theorem block0 (hA : P5.ThmPActual) (hPS : KB.PStd) (hVI : KB.VIso) (hFP : FormPos)
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (hw : KB.CutWord (D.parOf S v) (S.l + 1) w) (l : ℂ) (Y : Finset C.LPt)
    (hY : ∀ h ∈ Y, D.ptSize h = j) :
    KB.BlockPSD Y Y (KB.gN (setC S p F) v ε j w) (KB.hatB (setC S p F) v ε (j + 1) 1 w l)
      (KB.gN (setC S p F) v ε j w) := by
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, -, -, -, -⟩ := hv v
  have hw' : KB.CutWord (D.parOf S v) (p v).l0 w := by rw [hl0]; exact hw
  obtain ⟨ε0, hε0, hall⟩ := nv_common Y (uB S p F v ε j hj w) (fun h _ => uB_nv hB F hF v ε hε j hj w h)
  set Dv := NV ((p v).T.bs j) ε0 (S := Fin w.length) with hDv
  refine block_iso Dv ((p v).form j hj w) nv_zero (fun x y hx hy => nv_add hx hy) (fun c x hx => nv_smul c hx)
    (fun x₁ x₂ y c h₁ h₂ hy => form_sl (p v) j hj w x₁ x₂ y c h₁ h₂ hy)
    (fun x y₁ y₂ c hx h₁ h₂ => form_sr (p v) j hj w x y₁ y₂ c hx h₁ h₂)
    (fun x hx => hFP hA _ _ (D.parOf S v) (p v) j hj w hw' x ε0 hε0 hx)
    (KB.waveG ((p v).T.bs j) (sW S j l) w) (fun x hx => PBFV.waveG_nice ((p v).T.bs j) ε0 (sW S j l) w x hx)
    (fun x y hx hy => (hVI hA _ _ (D.parOf S v) (p v) j hj w hw' (sW S j l) x y ε0 hε0 hx hy).2)
    Y (fun h => if h ∈ Y then uB S p F v ε j hj w h else 0)
    (fun h => by by_cases hh : h ∈ Y <;> simp only [hh, if_true, if_false] <;> first | exact hall h hh | exact nv_zero)
    (1 / (ΓS S j * S.sizeAt v w)) ?_ _ _ ?_ ?_
  · have : 0 ≤ ΓS S j * S.sizeAt v w := by
      refine mul_nonneg ?_ (sizeAt_nonneg S v w)
      unfold ΓS
      have hgpos := g_pos_of_built hB
      have hrd := PBD.rd_pos' E
      exact (PBD.gamLev_pos _ _ _ _ (by unfold D.kapG; positivity) (by unfold D.deG; positivity) _).le
    positivity
  · intro h hh h' hh'
    simp only [hh, hh', if_true]
    exact gN_uB hB F hF v ε hε j hj w h h'
  · intro h hh h' hh'
    simp only [hh, hh', if_true]
    exact hatB_uB hA hPS hB F hF v ε hε j hj w hw l h h' (hY h hh) (hY h' hh')

end block0b

end

end Formalism.FourierDecayAlt.P.PBL
