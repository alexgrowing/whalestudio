import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopVec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSumLeOfGram
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OneSubPowLe

namespace Formalism.FourierDecayAlt.P.CutBP.GT

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

theorem norm_sum_le_of_gram' {ι κ I : Type} [Fintype I] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (v : ι → H) (c : I → ℝ) (hc : ∀ i, 0 ≤ c i)
    (Y : I → ι → W) (J : Finset κ) (P : κ → ι)
    (hk : ∀ j ∈ J, ∀ l ∈ J, ⟪v (P j), v (P l)⟫_ℂ = ∑ i, (c i : ℂ) * ⟪Y i (P j), Y i (P l)⟫_ℂ) (a : κ → ℂ) :
    ‖∑ j ∈ J, a j • v (P j)‖ ≤ ∑ i, √(c i) * ‖∑ j ∈ J, a j • Y i (P j)‖ := by
  set u := ∑ j ∈ J, a j • v (P j) with hu
  set y : I → W := fun i => ∑ j ∈ J, a j • Y i (P j) with hy
  have hinner : ⟪u, u⟫_ℂ = ∑ i, (c i : ℂ) * ⟪y i, y i⟫_ℂ := by
    have e1 : ⟪u, u⟫_ℂ = ∑ j ∈ J, ∑ l ∈ J, ∑ i,
        (c i : ℂ) * (conj (a j) * (a l * ⟪Y i (P j), Y i (P l)⟫_ℂ)) := by
      show ⟪∑ j ∈ J, a j • v (P j), ∑ j ∈ J, a j • v (P j)⟫_ℂ = _
      rw [sum_inner]
      simp_rw [inner_sum, inner_smul_left, inner_smul_right]
      refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun l hl => ?_
      rw [hk j hj l hl, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have e2 : ∑ i, (c i : ℂ) * ⟪y i, y i⟫_ℂ = ∑ i, ∑ j ∈ J, ∑ l ∈ J,
        (c i : ℂ) * (conj (a j) * (a l * ⟪Y i (P j), Y i (P l)⟫_ℂ)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      show (c i : ℂ) * ⟪∑ j ∈ J, a j • Y i (P j), ∑ j ∈ J, a j • Y i (P j)⟫_ℂ = _
      rw [sum_inner]
      simp_rw [inner_sum, inner_smul_left, inner_smul_right, Finset.mul_sum]
    rw [e1, e2]
    calc _ = ∑ j ∈ J, ∑ i, ∑ l ∈ J, (c i : ℂ) * (conj (a j) * (a l * ⟪Y i (P j), Y i (P l)⟫_ℂ)) :=
          Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  have hsq : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x : E), ‖⟪x, x⟫_ℂ‖ = ‖x‖ ^ 2 := by
    intro E _ _ x
    rw [inner_self_eq_norm_sq_to_K]
    simp
  have hle : ‖u‖ ^ 2 ≤ ∑ i, (√(c i) * ‖y i‖) ^ 2 := by
    rw [← hsq u, hinner]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [norm_mul, hsq, mul_pow, Real.sq_sqrt (hc i), Complex.norm_real, Real.norm_of_nonneg (hc i)]
  have hsum : ∑ i, (√(c i) * ‖y i‖) ^ 2 ≤ (∑ i, √(c i) * ‖y i‖) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hnn : 0 ≤ ∑ i, √(c i) * ‖y i‖ :=
    Finset.sum_nonneg fun i _ => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  calc ‖u‖ = √(‖u‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ √((∑ i, √(c i) * ‖y i‖) ^ 2) := Real.sqrt_le_sqrt (hle.trans hsum)
    _ = ∑ i, √(c i) * ‖y i‖ := Real.sqrt_sq hnn

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]

theorem cvec_utT (p : KB.Pl P Wp Wq) (N : ℕ) (c : I → ℝ) (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq) (s : ℕ) (h : C.LPt) (x : ℂ) (hx : x ≠ 0) (cc : ℂ) :
    PBK.cvec s (utT p N c Fi L s h) x cc = vecT p N c Fi L ((h ++ [(s - 1, x⁻¹)]) ++ [(1, cc)]) := by
  have hx' : x ^ (s - 1) ≠ 0 := pow_ne_zero _ hx
  have hn : ‖x‖ ^ (s - 1) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  rw [PBK.cvec, utT, smul_smul, mul_div_cancel₀ cc hx', ← Complex.ofReal_mul, inv_mul_cancel₀ hn,
    Complex.ofReal_one, one_smul]
  simp

theorem inner_vecT_np (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter)
    (c : I → ℝ) (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq)
    (hV : VecHyp p nn F w c Fi L) (Q Q' : C.LPt) :
    ⟪vecT p w.length c Fi L Q, vecT p w.length c Fi L Q'⟫_ℂ = TBB.NP p nn F (P.r + 1) w Q' Q := by
  rw [inner_vecT p w.length c hV.hc Fi L Q Q', hV.gram Q' Q]

end place

theorem germDataTopAll_of_parts (hTG : TopGram1) (hTC : TopCore1) (hFT : FibreTop) (hYC : YCont)
    (hMU : FieldMemU) (hSU : FieldSup) (hME : FieldMeas) (hLO : FieldLoc) : GermDataTopAll := by
  intro hA Wp Wq _ _ _ _ _ _ P p nn F Y K N Cb hCb hF hnn
  intro b s hb hs hbs hlev h hh w hw hN hBdd
  have hbs' : b + s = P.r + 2 := by omega
  have hr2 : b + s - 2 = P.r := by omega
  have hr1 : b + s - 1 = P.r + 1 := by omega
  obtain ⟨I, _, c, Fi, L, hc, hFi, hgram⟩ := hTG Wp Wq P p nn F w Cb hCb hF hw.1 hnn
  have hFib := hFT hA Wp Wq P p nn F w Cb hCb hF hw.1
  have hV : VecHyp p nn F w c Fi L :=
    { hc := hc, hFi := hFi, gram := hgram, int := fun a ha => (hFib a a ha ha).1,
      fibre := fun a a' ha ha' => (hFib a a' ha ha').2,
      cont := fun i m h' hh' hm hsz => hYC Wp Wq P p (Fi i) (hFi i) w.length m h' hh' hm hsz }
  obtain ⟨SS, hSS⟩ := hBdd w (TBBx5.isExt_self P p.l0 Y N K w hw (by omega))
  have hs0 : s ≠ 0 := by omega
  have hsz : D.ptSize h = b - 1 := hh.2

  have hloc : ∀ t : ℂ, t ≠ 0 → D.IsLocPt (h ++ [(s - 1, t)]) P.r := by
    intro t ht
    refine ⟨fun q hq => ?_, ?_⟩
    · rcases List.mem_append.1 hq with hq | hq
      · exact hh.1 q hq
      · simp only [List.mem_singleton] at hq
        subst hq
        exact ⟨by simp only; omega, ht⟩
    · have e : D.ptSize (h ++ [(s - 1, t)]) = D.ptSize h + (s - 1) := by simp [D.ptSize]
      rw [e, hsz]
      omega
  set ut := utT p w.length c Fi L s h with hut
  set bt := btT p w.length c Fi L s h with hbt
  have hpi : (1 : ℝ) ≤ Real.pi ^ (s - 1) := one_le_pow₀ (by linarith [Real.pi_gt_three])
  refine ⟨HT I Wp Wq, inferInstance, inferInstance, inferInstance, ut, bt, U.betaU, epsT s, -1, SS, 1,
    ((Real.pi ^ (s - 1))⁻¹) ^ 2, by positivity, ?_, Or.inr rfl, ?_, ?_, ?_, ?_⟩
  ·
    have h1 : ((Real.pi ^ (s - 1))⁻¹) ^ 2 ≤ 1 := by
      have : (Real.pi ^ (s - 1))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hpi
      have h0 : 0 ≤ (Real.pi ^ (s - 1))⁻¹ := by positivity
      nlinarith
    linarith [Real.pi_gt_three]
  ·
    refine ⟨hs0, Formalism.FourierDecayAlt.P.scale_matching.2.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [epsT]
    · intro _ _ x hx
      exact hMU p nn F w c Fi L hV b s hb hs hbs' h hh x hx
    · intro _ _ x hx
      rw [hSU p nn F w c Fi L hV b s hb hs hbs' h hh x hx]
      have := hSS ⟨⟨x⁻¹, inv_ne_zero hx⟩, rfl⟩
      simp only at this
      rwa [hr2] at this
    · intro _ _
      exact hME p nn F w c Fi L hV b s hb hs hbs' h hh
    · intro _ _ K' hK' hK0
      exact hLO p nn F w c Fi L hV b s hb hs hbs' h hh K' hK' hK0
    · intro _ _ K' hK' hK0
      choose Ci hCi using fun i => hTC Wp Wq P p (Fi i) (hFi i) w.length b s hb hs hbs' h hh K' hK' hK0
      refine ⟨∑ i, √(c i) * ‖L i‖ * Ci i, fun x hx => Eventually.of_forall fun D hD => ?_⟩
      have hD0 : D ≠ 0 := fun h0 => hK0 (h0 ▸ hD)
      have heD : epsT s * D ≠ 0 := mul_ne_zero (by simp [epsT]) hD0
      have hroot : ∀ z ∈ G.rootSet s (epsT s * D), z ≠ 0 := by
        intro z hz h0
        unfold G.rootSet at hz
        rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by omega)] at hz
        rw [h0, zero_pow hs0] at hz
        exact heD hz.symm

      have hsum : ut x D - PBK.mainD s U.betaU (epsT s) bt x D =
          ∑ j ∈ Finset.insertNone (G.rootSet s (epsT s * D)), coT s x j • vecT p w.length c Fi L (ptT s h x D j) := by
        rw [Finset.sum_insertNone, sub_eq_add_neg]
        refine congrArg₂ (· + ·) rfl ?_
        · unfold PBK.mainD
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun z hzm => ?_
          simp only [hbt, btT, if_neg (hroot z hzm), coT, ptT, smul_smul, neg_smul, neg_mul]
      rw [hsum]
      have hk : ∀ j ∈ Finset.insertNone (G.rootSet s (epsT s * D)), ∀ l ∈ Finset.insertNone (G.rootSet s (epsT s * D)),
          ⟪vecT p w.length c Fi L (ptT s h x D j), vecT p w.length c Fi L (ptT s h x D l)⟫_ℂ =
            ∑ i, (c i : ℂ) * ⟪(omT p w.length (ptT s h x D j) : ℂ) • L i (p.V (Fi i) (ptT s h x D j)),
              (omT p w.length (ptT s h x D l) : ℂ) • L i (p.V (Fi i) (ptT s h x D l))⟫_ℂ :=
        fun j _ l _ => inner_vecT p w.length c hc Fi L _ _
      refine (norm_sum_le_of_gram' (vecT p w.length c Fi L) c hc
        (fun i Q => (omT p w.length Q : ℂ) • L i (p.V (Fi i) Q)) _ (ptT s h x D) hk (coT s x)).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      have e : ∑ j ∈ Finset.insertNone (G.rootSet s (epsT s * D)),
          coT s x j • ((omT p w.length (ptT s h x D j) : ℂ) • L i (p.V (Fi i) (ptT s h x D j))) =
          L i (∑ j ∈ Finset.insertNone (G.rootSet s (epsT s * D)),
            (coT s x j * (omT p w.length (ptT s h x D j) : ℂ)) • p.V (Fi i) (ptT s h x D j)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, smul_smul]
      rw [e]
      have h3 := hCi i x hx D hD
      have hsq := Real.sqrt_nonneg (c i)
      calc √(c i) * ‖L i (∑ j ∈ Finset.insertNone (G.rootSet s (epsT s * D)),
            (coT s x j * (omT p w.length (ptT s h x D j) : ℂ)) • p.V (Fi i) (ptT s h x D j))‖
          ≤ √(c i) * (‖L i‖ * ‖∑ j ∈ Finset.insertNone (G.rootSet s (epsT s * D)),
            (coT s x j * (omT p w.length (ptT s h x D j) : ℂ)) • p.V (Fi i) (ptT s h x D j)‖) :=
            mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) hsq
        _ ≤ √(c i) * (‖L i‖ * (Ci i * ‖x‖⁻¹)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)) hsq
        _ = √(c i) * ‖L i‖ * Ci i * ‖x‖⁻¹ := by ring
  ·
    intro σ z
    have hbU : U.betaU = 2 * Complex.I := by
      unfold U.betaU Formalism.QuantumDeterminants.cStd; ring
    unfold P5.fsv G.psi
    rw [hbU]
    congr 1
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im] <;> ring
  ·
    intro t t' ht ht'
    have hx : t⁻¹ ≠ 0 := inv_ne_zero ht
    have hx' : t'⁻¹ ≠ 0 := inv_ne_zero ht'
    have hg : PBK.gramL volume (PBK.Uc s fun _ : Unit => ut) (PBK.Uc s fun _ : Unit => ut) ((), t⁻¹) ((), t'⁻¹) =
        ∫ cc : ℂ, TBB.NP p nn F (P.r + 1) w ((h ++ [(s - 1, t')]) ++ [(1, cc)]) ((h ++ [(s - 1, t)]) ++ [(1, cc)]) := by
      unfold PBK.gramL PBK.Uc
      refine integral_congr_ae (Eventually.of_forall fun cc => ?_)
      simp only [hut]
      rw [cvec_utT p w.length c Fi L s h _ hx, cvec_utT p w.length c Fi L s h _ hx', inv_inv, inv_inv,
        inner_vecT_np p nn F w c Fi L hV]
    have hn : TBB.NP p nn F (b + s - 2) w (h ++ [(s - 1, t)]) (h ++ [(s - 1, t')]) =
        conj (PBK.gramL volume (PBK.Uc s fun _ : Unit => ut) (PBK.Uc s fun _ : Unit => ut) ((), t⁻¹) ((), t'⁻¹)) := by
      rw [hg, hr2, hV.fibre _ _ (hloc t ht) (hloc t' ht'), ← integral_conj]
      refine integral_congr_ae (Eventually.of_forall fun cc => ?_)
      simp only
      rw [← inner_vecT_np p nn F w c Fi L hV, ← inner_vecT_np p nn F w c Fi L hV, inner_conj_symm]
    rw [hn, RCLike.norm_conj, one_mul]
  ·
    intro z hz
    have hQ : TBB.Ew p nn F (b + s - 1) w (h ++ [(s, z)]) = ‖vecT p w.length c Fi L (h ++ [(s, z)])‖ ^ 2 := by
      unfold TBB.Ew
      rw [hr1, ← inner_vecT_np p nn F w c Fi L hV, inner_self_eq_norm_sq_to_K]
      norm_cast
    have hbz : PBK.bz s bt z = ((Real.pi ^ (s - 1) : ℝ) : ℂ) • vecT p w.length c Fi L (h ++ [(s, z)]) := by
      simp only [PBK.bz, hbt, btT, if_neg hz, smul_smul, ← Complex.ofReal_mul]
      congr 2
      have hpos : (0 : ℝ) < (s : ℝ) * ‖z‖ ^ (s - 1) := by
        have : (0 : ℝ) < ‖z‖ ^ (s - 1) := pow_pos (norm_pos_iff.mpr hz) _
        have hs' : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero hs0
        positivity
      field_simp
    rw [hQ, hbz, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_pow, ← mul_assoc,
      ← mul_pow, inv_mul_cancel₀ (by positivity), one_pow, one_mul]

end

end Formalism.FourierDecayAlt.P.CutBP.GT
