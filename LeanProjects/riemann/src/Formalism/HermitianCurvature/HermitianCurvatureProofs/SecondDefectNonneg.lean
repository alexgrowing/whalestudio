import Formalism.HermitianCurvature.HermitianCurvatureProofs.PtEntryAppendStart
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AeNeZeroComplex

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem toStd_append_blkT (r : ℕ) (g : ℝ) (s : ℕ) (c : ℂ) : ∀ (h : C.LPt) (b : ℕ),
    D.toStd r g b (h ++ [(s, c)]) = D.toStd r g b h ++
      [(s, (((g / (2 * Real.pi)) ^ S6.nuBlock r ((b + D.ptSize h : ℕ) : ℤ) (s : ℤ) : ℝ) : ℂ) * Complex.I ^ (s - 1) * c)]
  | [], b => by simp [D.toStd, D.ptSize]
  | (s', t) :: rest, b => by
    have ih := toStd_append_blkT r g s c rest (b + s')
    simp only [List.cons_append, D.toStd, ih, D.ptSize, List.map_cons, List.sum_cons, add_assoc]

section rr

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

theorem rr_top_eq (hVT : Top.VecVTypes) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter)
    (P1 Q1 : C.LPt) (hP : D.IsLocPt P1 (P.r + 1)) (hQ : D.IsLocPt Q1 (P.r + 1)) :
    p.RR F (P.r + 1) w P1 Q1 = Top.topOf P p.l0 p.T p.ν' p.m₀ p.Θ p.TP F w P1 Q1 := by
  unfold KB.Pl.RR D.RRplace
  rw [dif_pos ⟨hP, hQ⟩, dif_neg (by omega), if_pos rfl]
  split_ifs with hw
  · subst hw
    set TT := Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' with hTT
    by_cases h1 : 0 < D.ptG TT P.r P1
    · by_cases h2 : 0 < D.ptG TT P.r Q1
      · exact (Formalism.FourierDecayAlt.P.top_of_empty hVT Wp Wq P p.l0 p.T p.ν' p.m₀ p.Θ p.TP F P1 Q1 p.hP p.hF hP hQ
          h1 h2).symm
      · unfold Top.topOf
        rw [vecV_of_G _ _ _ _ _ h2, hsInner_zero_right']
        symm
        refine Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun ρ _ => ?_
        rw [p.Θ.nil, vecV_of_G _ _ _ _ _ h2, ContinuousLinearMap.comp_zero, hsInner_zero_right', mul_zero]
    · unfold Top.topOf
      rw [vecV_of_G _ _ _ _ _ h1, Formalism.FourierDecayAlt.P.PBD.hsInner_zero_left]
      symm
      refine Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun ρ _ => ?_
      rw [p.Θ.nil, vecV_of_G _ _ _ _ _ h1, ContinuousLinearMap.comp_zero, Formalism.FourierDecayAlt.P.PBD.hsInner_zero_left, mul_zero]
  · rfl

end rr

section gramtop

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

abbrev HV (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : Type :=
  PiLp 2 (fun _ : Fin (Module.finrank ℂ (Wq (S.pl v))) => Wp (S.pl v))

def vecT (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (s : ℕ)
    (t : ℂ) (w : List C.Letter) (e : Wd.Ix (Fin w.length)) (ρ : M.Ty (D.parOf S v)) (P : C.LPt) : HV S v :=
  if D.IsLocPt (P ++ [(s, t)]) (S.G.r + 1) then
    B.hsVec (((p v).TP.E ρ).comp (D.vecV (p v).T.base (p v).ν' (p v).m₀ ((p v).Θ.Θ w e (F v ε))
      (stdS S (P ++ [(s, t)]))))
  else 0

def omT (S : C.HidaSetting E Wp Wq) (s : ℕ) (t : ℂ) (P : C.LPt) : ℝ :=
  √(nnS S (P ++ [(s, t)])) / bS S (P ++ [(s, t)])

def del2 (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))) (v : Fin S.f)
    (w : List C.Letter) (e : Wd.Ix (Fin w.length)) (ρ : M.Ty (D.parOf S v)) : ℝ :=
  √((Top.cW (D.parOf S v) (p v).l0 w e ρ).re) * √((Top.cW (D.parOf S v) (p v).l0 w e ρ).re)

theorem second_defect_nonneg (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))) (v : Fin S.f)
    (w : List C.Letter) (e : Wd.Ix (Fin w.length)) (ρ : M.Ty (D.parOf S v)) : 0 ≤ del2 S p v w e ρ :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem gN_top (hVT : Top.VecVTypes) {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq}
    {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (s : ℕ)
    (hs : 2 ≤ s) (t : ℂ) (w : List C.Letter) (P Q : C.LPt) (hP : D.ptSize P + s = S.G.r + 1)
    (hQ : D.ptSize Q + s = S.G.r + 1) :
    KB.gN (setC S p F) v ε (S.G.r + 1) w (P ++ [(s, t)]) (Q ++ [(s, t)]) =
      (omT S s t P : ℂ) * (omT S s t Q : ℂ) * ((1 / (ΓS S (S.G.r + 1) * S.sizeAt v w) : ℝ) : ℂ) *
        ∑ e : Wd.Ix (Fin w.length), ∑ ρ : M.Ty (D.parOf S v),
          (del2 S p v w e ρ : ℂ) * gramH (vecT S p F v ε s t w e ρ) P Q := by
  have hgpos := g_pos_of_built hB
  by_cases hloc : D.IsLocPt (P ++ [(s, t)]) (S.G.r + 1) ∧ D.IsLocPt (Q ++ [(s, t)]) (S.G.r + 1)
  · obtain ⟨hPl, hQl⟩ := hloc
    rw [gN_setC hB]
    have hPs : D.IsLocPt (stdS S (P ++ [(s, t)])) (S.G.r + 1) := (PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).2 hPl
    have hQs : D.IsLocPt (stdS S (Q ++ [(s, t)])) (S.G.r + 1) := (PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).2 hQl
    rw [rr_top_eq hVT (p v) (F v ε) w _ _ hPs hQs]
    have eP : stdS S (P ++ [(s, t)]) = stdS S P ++ [(s, (((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r
        ((1 + D.ptSize P : ℕ) : ℤ) (s : ℤ) : ℝ) * Complex.I ^ (s - 1) * t)] := toStd_append_blkT _ _ _ _ _ _
    have eQ : stdS S (Q ++ [(s, t)]) = stdS S Q ++ [(s, (((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r
        ((1 + D.ptSize Q : ℕ) : ℤ) (s : ℤ) : ℝ) * Complex.I ^ (s - 1) * t)] := toStd_append_blkT _ _ _ _ _ _
    have hPQ : D.ptSize P = D.ptSize Q := by omega
    have hgr : ∀ e ρ, gramH (vecT S p F v ε s t w e ρ) P Q =
        B.hsInner (((p v).TP.E ρ).comp (D.vecV (p v).T.base (p v).ν' (p v).m₀ ((p v).Θ.Θ w e (F v ε))
          (stdS S (P ++ [(s, t)]))))
          (((p v).TP.E ρ).comp (D.vecV (p v).T.base (p v).ν' (p v).m₀ ((p v).Θ.Θ w e (F v ε))
          (stdS S (Q ++ [(s, t)])))) := by
      intro e ρ
      unfold gramH vecT
      rw [if_pos hPl, if_pos hQl]
      rfl
    simp only [hgr]
    rw [eP, eQ, hPQ]
    rw [topOf_big (p v) (F v ε) w (stdS S P) (stdS S Q) s _ _ hs (by rw [stdS_size]; omega)
      (by rw [stdS_size]; omega)]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun ρ _ => ?_
    unfold del2 omT
    push_cast
    ring
  · rw [gN_setC_zero hB F v ε (S.G.r + 1) w _ _ hloc]
    symm
    have hz : ∀ e ρ, gramH (vecT S p F v ε s t w e ρ) P Q = 0 := by
      intro e ρ
      unfold gramH vecT
      by_cases h1 : D.IsLocPt (P ++ [(s, t)]) (S.G.r + 1)
      · rw [if_neg (fun h2 => hloc ⟨h1, h2⟩), inner_zero_left]
      · rw [if_neg h1, inner_zero_right]
    simp [hz]

theorem hsVec_smul {Wp' Wq' : Type} [NormedAddCommGroup Wp'] [InnerProductSpace ℂ Wp'] [NormedAddCommGroup Wq']
    [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq'] (c : ℂ) (X : Wq' →L[ℂ] Wp') :
    B.hsVec (c • X) = c • B.hsVec X := by
  unfold B.hsVec; rfl

theorem hsVec_sum {Wp' Wq' : Type} [NormedAddCommGroup Wp'] [InnerProductSpace ℂ Wp'] [NormedAddCommGroup Wq']
    [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq'] {ι : Type} (s : Finset ι) (X : ι → Wq' →L[ℂ] Wp') :
    B.hsVec (∑ i ∈ s, X i) = ∑ i ∈ s, B.hsVec (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => unfold B.hsVec; simp; rfl
  | insert b t hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb, ← ih]
    unfold B.hsVec; rfl

theorem vecT_deg (hDT : KB.DegTop) {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq}
    {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ)
    (hF : KB.CptCoef (p v).T.base (F v ε)) (s : ℕ) (hs : 2 ≤ s) (t : ℂ) (ht : t ≠ 0) (d : ℕ) (hd : d + s = S.G.r + 1)
    (w : List C.Letter) (e : Wd.Ix (Fin w.length)) (ρ : M.Ty (D.parOf S v)) {K : ℕ} (grid : Fin K → Fin (d + 1) → ℝ)
    (hinj : ∀ b, Function.Injective (grid b))
    (hcut : ∀ n : Fin K → Fin (d + 1), KB.CutWord (D.parOf S v) (S.l + 1) (KB.plusW (List.ofFn fun b => grid b (n b)) w))
    (P : C.LPt) (hP : D.ptSize P = d) :
    vecT S p F v ε s t w e ρ P =
      ((((-1 : ℂ) ^ (s - 1) / ((((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r ((1 + d : ℕ) : ℤ) (s : ℤ) : ℝ) *
        Complex.I ^ (s - 1) * t)) ^ K)⁻¹) •
        ∑ n : Fin K → Fin (d + 1), (((∏ b, F7.lagCo (grid b) (n b) : ℝ) : ℂ)) •
          vecT S p F v ε s t (KB.plusW (List.ofFn fun b => grid b (n b)) w) (KB.firstSt _ e) ρ P := by
  have hgpos := g_pos_of_built hB
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, hInD, -, -, -⟩ := hv v
  set τ : ℂ := (((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r ((1 + d : ℕ) : ℤ) (s : ℤ) : ℝ) *
    Complex.I ^ (s - 1) * t with hτ
  have hτ0 : τ ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ Complex.I_ne_zero)) ht
    have : 0 < ((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r ((1 + d : ℕ) : ℤ) (s : ℤ) := zpow_pos (by positivity) _
    exact_mod_cast this.ne'
  have hc0 : ((-1 : ℂ) ^ (s - 1) / τ) ^ K ≠ 0 :=
    pow_ne_zero _ (div_ne_zero (pow_ne_zero _ (by norm_num)) hτ0)
  by_cases hloc : D.IsLocPt (P ++ [(s, t)]) (S.G.r + 1)
  · have eP : stdS S (P ++ [(s, t)]) = stdS S P ++ [(s, τ)] := by
      rw [hτ, ← hP]; exact toStd_append_blkT _ _ _ _ _ _
    have hPs : D.IsLocPt (stdS S P ++ [(s, τ)]) ((D.parOf S v).r + 1) := by
      rw [← eP]; exact (PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).2 hloc
    have hdeg : ∀ (h : C.LPt) (hh : D.ptSize h = d), D.IsLocPt (h ++ [(s, τ)]) ((D.parOf S v).r + 1) →
        ((-1 : ℂ) ^ (s - 1) / τ) ^ K • (p v).V ((p v).Θ.Θ w e (F v ε)) (h ++ [(s, τ)]) =
          ∑ n : Fin K → Fin (d + 1), ((∏ b, F7.lagCo (grid b) (n b) : ℝ) : ℂ) •
            (p v).V ((p v).Θ.Θ (KB.plusW (List.ofFn fun b => grid b (n b)) w) (KB.firstSt _ e) (F v ε))
              (h ++ [(s, τ)]) := by
      intro h hh hloc'
      subst hh
      exact hDT _ _ (D.parOf S v) (p v) (F v ε) s w h τ K grid e Cb (by rw [hl0]; exact hInD) hs hloc' hF hinj
        (fun n => by rw [hl0]; exact hcut n)
    have h1 := hdeg (stdS S P) (by rw [stdS_size]; exact hP) hPs
    have hV : (p v).V ((p v).Θ.Θ w e (F v ε)) (stdS S P ++ [(s, τ)]) =
        (((-1 : ℂ) ^ (s - 1) / τ) ^ K)⁻¹ • ∑ n : Fin K → Fin (d + 1), ((∏ b, F7.lagCo (grid b) (n b) : ℝ) : ℂ) •
          (p v).V ((p v).Θ.Θ (KB.plusW (List.ofFn fun b => grid b (n b)) w) (KB.firstSt _ e) (F v ε))
            (stdS S P ++ [(s, τ)]) := by
      rw [← h1, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    unfold vecT
    rw [if_pos hloc]
    simp only [if_pos hloc]
    rw [eP]
    change B.hsVec (((p v).TP.E ρ).comp ((p v).V ((p v).Θ.Θ w e (F v ε)) (stdS S P ++ [(s, τ)]))) = _
    rw [hV, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_finset_sum, hsVec_smul, hsVec_sum]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [ContinuousLinearMap.comp_smul, hsVec_smul]
    rfl
  · unfold vecT
    simp only [if_neg hloc, smul_zero, Finset.sum_const_zero]

end gramtop

end

end Formalism.FourierDecayAlt.P.PBL
