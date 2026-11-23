import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResChiIndex
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ResSymGram
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ResChiIndexLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

namespace ResChiIndex

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

section Forms

variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]

theorem exists_int_mul (f : MvPolynomial J ℚ) :
    ∃ (N : ℕ) (g : MvPolynomial J ℤ), N ≠ 0 ∧ map (Int.castRingHom ℚ) g = C (N : ℚ) * f := by
  refine MvPolynomial.induction_on' f (fun u a => ?_) (fun p q hp hq => ?_)
  · refine ⟨a.den, monomial u a.num, a.den_nz, ?_⟩
    rw [map_monomial, C_mul_monomial, Rat.den_mul_eq_num]
    simp
  · obtain ⟨N₁, g₁, h₁, e₁⟩ := hp
    obtain ⟨N₂, g₂, h₂, e₂⟩ := hq
    refine ⟨N₁ * N₂, C (N₂ : ℤ) * g₁ + C (N₁ : ℤ) * g₂, mul_ne_zero h₁ h₂, ?_⟩
    rw [map_add, map_mul, map_mul, map_C, map_C, e₁, e₂]
    simp only [eq_intCast, Int.cast_natCast, Nat.cast_mul, C_mul]
    ring

theorem isHomogeneous_of_map {f : MvPolynomial J ℚ} {n : ℕ} (hf : f.IsHomogeneous n) {N : ℕ}
    {g : MvPolynomial J ℤ} (hg : map (Int.castRingHom ℚ) g = C (N : ℚ) * f) : g.IsHomogeneous n := by
  intro s hs
  apply hf
  intro h0
  apply hs
  have h := congrArg (coeff s) hg
  rw [coeff_map, coeff_C_mul, h0, mul_zero] at h
  simpa using h

theorem secFun_eq_zero {x : J → Ω} {f : MvPolynomial J ℚ} {n : ℕ} (hf : f.IsHomogeneous n)
    (hx : aeval x f = 0) {z : J → ℂ} (hz : z ∈ pts (coordIdeal ℤ x)) : secFun f z = 0 := by
  obtain ⟨N, g, hN, hg⟩ := exists_int_mul f
  have hgx : aeval x g = 0 := by
    rw [← aeval_map_int, hg, map_mul, hx, mul_zero]
  have h0 := hz.2 g (mem_coordIdeal_of_isHomogeneous ℤ x (isHomogeneous_of_map hf hg) hgx)
  have e : eval z (map (Int.castRingHom ℂ) g) = (N : ℂ) * secFun f z := by
    rw [show Int.castRingHom ℂ = (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) from RingHom.ext_int _ _,
      ← MvPolynomial.map_map, hg, secFun]
    simp
  rw [e] at h0
  exact (mul_eq_zero.mp h0).resolve_left (by exact_mod_cast hN)

theorem aeval_matSubst (B : Matrix J J ℚ) (x : J → Ω) (b : MvPolynomial J ℚ) :
    aeval x (matSubst B b) = aeval (matAct B x) b := by
  rw [matSubst, ← AlgHom.comp_apply, comp_aeval]
  refine congrArg (fun y => aeval y b) (funext fun i => ?_)
  simp [matAct]

theorem isHomogeneous_matSubst (B : Matrix J J ℚ) {b : MvPolynomial J ℚ} {n : ℕ} (hb : b.IsHomogeneous n) :
    (matSubst B b).IsHomogeneous n := by
  have hg : ∀ i, (∑ j, C (B i j) * X j : MvPolynomial J ℚ).IsHomogeneous 1 := fun i =>
    IsHomogeneous.sum _ _ _ fun j _ => (isHomogeneous_X ℚ j).C_mul _
  simpa [matSubst] using hb.aeval _ hg

theorem mem_span_rat_sec (A : Matrix J J ℚ) (x : J → Ω) (n : ℕ) :
    ∀ s ∈ sec ℤ (matAct A x) n, s ∈ Submodule.span ℚ (sec ℤ x n : Set Ω) := by
  intro s hs
  obtain ⟨c, hc0, hc⟩ := ChangeOfLattice.exists_clear_den A
  have hi : ∀ i, (c : ℤ) • matAct A x i ∈ Submodule.span ℤ (Set.range x) := by
    intro i
    have e : (c : ℤ) • matAct A x i = matAct ((c : ℚ) • A) x i := by
      simp [matAct, Finset.mul_sum, zsmul_eq_mul, mul_assoc]
    rw [e]
    refine ChangeOfLattice.matAct_mem_span (fun i j => ?_) x i
    obtain ⟨k, hk⟩ := hc i j
    exact ⟨k, by rw [Matrix.smul_apply, smul_eq_mul, hk]⟩
  have hy : ∀ l ∈ Submodule.span ℤ (Set.range (matAct A x)), (c : ℤ) • l ∈ Submodule.span ℤ (Set.range x) := by
    intro l hl
    have hle : Submodule.span ℤ (Set.range (matAct A x)) ≤
        (Submodule.span ℤ (Set.range x)).comap ((c : ℤ) • LinearMap.id) :=
      Submodule.span_le.2 (Set.range_subset_iff.2 fun i => by simpa using hi i)
    simpa using hle hl
  rw [ChangeOfLattice.sec_eq_pow] at hs
  have hcs := ChangeOfLattice.smul_pow_mem hy n s hs
  rw [← ChangeOfLattice.sec_eq_pow] at hcs
  have hc' : ((c : ℚ) ^ n : Ω) ≠ 0 := by exact_mod_cast pow_ne_zero n hc0
  have e2 : s = (((c : ℚ) ^ n)⁻¹ : ℚ) • ((c : ℤ) ^ n • s) := by
    rw [Rat.smul_def, zsmul_eq_mul]
    push_cast
    field_simp
  rw [e2]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hcs)

end Forms

section Gram

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem resGram_change (d : HSMDatum D Ω κ) {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ}
    (hb : ∀ k, ∃ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n ∧ b k = map (Int.castRingHom ℚ) f)
    (c : Fin r → MvPolynomial (Ix κ) ℚ) (T : Matrix (Fin r) (Fin r) ℚ)
    (hc : ∀ k, ∀ z ∈ pts (coordIdeal ℤ d.x), secFun (c k) z = ∑ l, (T k l : ℂ) * secFun (b l) z) :
    resGram d n c = T.map (Rat.cast : ℚ → ℝ) * resGram d n b * (T.map (Rat.cast : ℚ → ℝ)).transpose := by

  have hpt : ∀ z ∈ pts (coordIdeal ℤ d.x), ∀ k l, pairVal d.m n (c k) (c l) z =
      ∑ i, ∑ j, ((T k i * T l j : ℚ) : ℂ) * pairVal d.m n (b i) (b j) z := by
    intro z hz k l
    have e1 : ∀ p q : MvPolynomial (Ix κ) ℚ, pairVal d.m n p q z =
        secFun p z * starRingEnd ℂ (secFun q z) / ((d.m.ρ z ^ (2 * n) : ℝ) : ℂ) := fun p q => rfl
    simp only [e1, hc k z hz, hc l z hz, map_sum, map_mul, map_ratCast, Finset.sum_mul, Finset.mul_sum,
      Finset.sum_div]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring

  have hprob := d.vol.1
  have hpv : ∀ i j, pairVal d.m n (b i) (b j) = fun z =>
      starRingEnd ℂ (starRingEnd ℂ (secFun (b i) z) * secFun (b j) z * (wgt d.m n z : ℂ)) :=
    fun i j => funext (ResSym.pairVal_eq_conj d.m n (b i) (b j))
  have hcont : ∀ i j, ContinuousOn (pairVal d.m n (b i) (b j)) {0}ᶜ := fun i j => by
    rw [hpv]
    exact Complex.continuous_conj.comp_continuousOn (ResSym.continuousOn_gramFun d.smooth n (b i) (b j))
  have hdeg : ∀ i j, ∀ (a : ℂ) z, a ≠ 0 → pairVal d.m n (b i) (b j) (a • z) = pairVal d.m n (b i) (b j) z :=
    fun i j a z ha => by
      rw [hpv]
      simp only
      rw [ResSym.gramFun_smul (hb i) (hb j) a z ha]
  have hint1 : ∀ i j, Integrable (fun y => pairVal d.m n (b i) (b j) (resPt d y)) d.dV := fun i j =>
    integrableOn_univ.1 ((ResSym.continuous_degZero_resPt d (hcont i j) (hdeg i j)).continuousOn.integrableOn_compact
      isCompact_univ)
  have hint2 : ∀ i j, Integrable (fun y => pairVal d.m n (b i) (b j) (conjPt (resPt d y))) d.dV := fun i j =>
    integrableOn_univ.1
      ((ResSym.continuous_degZero_conj_resPt d (hcont i j) (hdeg i j)).continuousOn.integrableOn_compact
        isCompact_univ)
  have hsum : ∀ (g : d.R.X → Ix κ → ℂ), (∀ y, g y ∈ pts (coordIdeal ℤ d.x)) →
      (∀ i j, Integrable (fun y => pairVal d.m n (b i) (b j) (g y)) d.dV) → ∀ k l,
      ∫ y, pairVal d.m n (c k) (c l) (g y) ∂d.dV =
        ∑ i, ∑ j, ((T k i * T l j : ℚ) : ℂ) * ∫ y, pairVal d.m n (b i) (b j) (g y) ∂d.dV := by
    intro g hg hgi k l
    rw [integral_congr_ae (Filter.Eventually.of_forall fun y => hpt _ (hg y) k l),
      integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hgi i j).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (hgi i j).const_mul _]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  ext k l
  rw [show resGram d n c k l = (1 / 2) * ((∫ y, pairVal d.m n (c k) (c l) (resPt d y) ∂d.dV).re +
      (∫ y, pairVal d.m n (c k) (c l) (conjPt (resPt d y)) ∂d.dV).re) from rfl,
    hsum (resPt d) (ResSym.resPt_mem_pts d) hint1,
    hsum (fun y => conjPt (resPt d y)) (fun y => ResSym.conjPt_mem_pts (ResSym.resPt_mem_pts d y)) hint2]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  simp only [resGram, Complex.re_sum, Complex.mul_re, Complex.ratCast_re, Complex.ratCast_im, zero_mul, sub_zero,
    Finset.mul_sum, mul_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring

theorem resChi_sub_of_bases (d d' : HSMDatum D Ω κ) (B : Matrix (Ix κ) (Ix κ) ℚ) (hB : IsInvMat B)
    (hx : d'.x = matAct B d.x)
    (hG : ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), resGram d' n b = resGram d n fun k => matSubst B (b k))
    (n : ℕ) {r r' : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ} {b' : Fin r' → MvPolynomial (Ix κ) ℚ}
    (hb : IsSecBasis d.x n b) (hb' : IsSecBasis d'.x n b') :
    -(1 / 2) * Real.log (resGram d' n b').det - -(1 / 2) * Real.log (resGram d n b).det =
      latLogIndex d.x d'.x n := by
  classical
  have hli := linIndep_rat_of_isSecBasis hb
  have hli' := linIndep_rat_of_isSecBasis hb'
  obtain ⟨B', hB'B, -⟩ := ChangeOfLattice.exists_inv_of_isInvMat hB
  have hx' : d.x = matAct B' d'.x := by rw [hx, ChangeOfLattice.matAct_mul, hB'B, matAct_one]

  have hspan : ∀ {y : Ix κ → Ω} {s : ℕ} {c : Fin s → MvPolynomial (Ix κ) ℚ}, IsSecBasis y n c →
      Submodule.span ℚ (sec ℤ y n : Set Ω) = Submodule.span ℚ (Set.range fun i => aeval y (c i)) := by
    intro y s c hc
    rw [← hc.2.2, Submodule.span_span_of_tower]
  have hV : Submodule.span ℚ (Set.range fun k => aeval d'.x (b' k)) =
      Submodule.span ℚ (Set.range fun i => aeval d.x (b i)) := by
    apply le_antisymm
    · rw [← hspan hb, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      refine mem_span_rat_sec B d.x n _ ?_
      rw [← hx, ← hb'.2.2]
      exact Submodule.subset_span ⟨k, rfl⟩
    · rw [← hspan hb', Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      refine mem_span_rat_sec B' d'.x n _ ?_
      rw [← hx', ← hb.2.2]
      exact Submodule.subset_span ⟨k, rfl⟩
  have hrr : r' = r := by
    have h1 := finrank_span_eq_card hli
    have h2 := finrank_span_eq_card hli'
    rw [hV, h1] at h2
    simpa using h2.symm
  subst hrr

  have hmem : ∀ k, aeval d'.x (b' k) ∈ Submodule.span ℚ (Set.range fun i => aeval d.x (b i)) :=
    fun k => hV ▸ Submodule.subset_span ⟨k, rfl⟩
  choose T hT using fun k => (Submodule.mem_span_range_iff_exists_fun ℚ).1 (hmem k)
  have hTΩ : ∀ k, aeval d'.x (b' k) = ∑ l, ((Matrix.of T) k l : Ω) * aeval d.x (b l) := fun k => by
    rw [← hT k]
    simp only [Rat.smul_def, Matrix.of_apply]
  have hdet : (Matrix.of T).det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    apply hv0
    have hrel : ∑ k, v k • aeval d'.x (b' k) = 0 := by
      calc ∑ k, v k • aeval d'.x (b' k)
          = ∑ l, (Matrix.vecMul v (Matrix.of T)) l • aeval d.x (b l) := by
            simp only [← hT, Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul,
              Matrix.of_apply]
            exact Finset.sum_comm
        _ = 0 := by rw [hv]; simp
    funext k
    exact linearIndependent_iff'.1 hli' Finset.univ v hrel k (Finset.mem_univ k)

  have hidx : latLogIndex d.x d'.x n = -Real.log |((Matrix.of T).det : ℝ)| := by
    unfold latLogIndex
    rw [← hb.2.2, ← hb'.2.2]
    exact log_relIndex_sub hb.2.1 hb'.2.1 (Matrix.of T) hTΩ hdet

  have hpt : ∀ k, ∀ z ∈ pts (coordIdeal ℤ d.x), secFun (matSubst B (b' k)) z =
      ∑ l, ((Matrix.of T) k l : ℂ) * secFun (b l) z := by
    intro k z hz
    obtain ⟨f, hf, hfb⟩ := hb'.1 k
    have hh : (matSubst B (b' k) - ∑ l, C ((Matrix.of T) k l) * b l).IsHomogeneous n := by
      refine (isHomogeneous_matSubst B (hfb ▸ hf.map _)).sub
        (IsHomogeneous.sum _ _ _ fun l _ => ?_)
      obtain ⟨g, hg, hgb⟩ := hb.1 l
      rw [hgb]
      exact (hg.map _).C_mul _
    have hx0 : aeval d.x (matSubst B (b' k) - ∑ l, C ((Matrix.of T) k l) * b l) = 0 := by
      rw [map_sub, aeval_matSubst, ← hx, hTΩ k]
      simp
    have h0 := secFun_eq_zero hh hx0 hz
    simp only [secFun, map_sub, map_sum, map_mul, map_C, eval_C, eq_ratCast]
      at h0 ⊢
    exact sub_eq_zero.1 h0
  have hchange : resGram d' n b' =
      (Matrix.of T).map (Rat.cast : ℚ → ℝ) * resGram d n b * ((Matrix.of T).map (Rat.cast : ℚ → ℝ)).transpose := by
    rw [hG n _ b']
    exact resGram_change d hb.1 _ (Matrix.of T) hpt

  have hGpos : 0 < (resGram d n b).det := by
    rw [ResSym.det_resGram d hb.1]
    exact (Complex.pos_iff.1 (ResSym.posDef_gram d hb).det_pos).1
  have hTd : ((Matrix.of T).map (Rat.cast : ℚ → ℝ)).det = ((Matrix.of T).det : ℝ) :=
    (RingHom.map_det (Rat.castHom ℝ) (Matrix.of T)).symm
  have hTr : ((Matrix.of T).det : ℝ) ≠ 0 := by exact_mod_cast hdet
  rw [hidx, hchange, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hTd,
    show ((Matrix.of T).det : ℝ) * (resGram d n b).det * ((Matrix.of T).det : ℝ) =
      ((Matrix.of T).det : ℝ) ^ 2 * (resGram d n b).det by ring,
    Real.log_mul (pow_ne_zero 2 hTr) hGpos.ne', Real.log_pow, ← Real.log_abs ((Matrix.of T).det : ℝ)]
  push_cast
  ring

end Gram

theorem proof : ResChiIndex.Statement := by
  intro D Ω _ _ κ _ d d' B hB hx hG n
  have h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n p.2 :=
    ⟨⟨_, _⟩, (exists_isSecBasis d.x n).choose_spec⟩
  have h' : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d'.x n p.2 :=
    ⟨⟨_, _⟩, (exists_isSecBasis d'.x n).choose_spec⟩
  unfold resChi
  rw [dif_pos h, dif_pos h']
  exact resChi_sub_of_bases d d' B hB hx hG n h.choose_spec h'.choose_spec

end

end ResChiIndex

end GroundTheory.Heights₂.Heights.HilbertSamuel
