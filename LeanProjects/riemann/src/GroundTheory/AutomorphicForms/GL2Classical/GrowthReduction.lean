import Mathlib
import GroundTheory.AutomorphicForms.Reduction
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Height
import GroundTheory.AutomorphicForms.GL2Classical.Cuspidal
import GroundTheory.AutomorphicForms.GL2Classical.KFinite

open NumberField IsDedekindDomain Matrix Set Filter Topology CongruenceSubgroup
open UpperHalfPlane hiding I I_re I_im
open scoped NumberField.AdeleRing MatrixGroups ModularForm Manifold

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm Reduction GroundTheory.Global GroundTheory.Global.IdeleGroup

section Heights

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem height_eq_prod_locHeight (g : AdelicGLn.AdelicGL K n) :
    AutomorphicForm.height g = (∏ w : InfinitePlace K, locHeight (infAt w g) ^ w.mult) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), locHeight (finAt v g) :=
  rfl

theorem one_le_const_mul_height_mul_vecHeight (g : AdelicGLn.AdelicGL K n) {x : Fin n → K}
    (hx : x ≠ 0) :
    1 ≤ (∏ w : InfinitePlace K, (√(n : ℝ) * n) ^ w.mult) * AutomorphicForm.height g *
      Reduction.height g x := by
  set y' := ratVec x ᵥ* (g : Matrix (Fin n) (Fin n) 𝔸[K]) with hy'
  have hy : ratVec x = y' ᵥ* ((g⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) := by
    rw [hy', vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]
  have hfc : HasFiniteContent y' := hasFiniteContent_height g hx
  have hinfb : ∀ w, euclidNorm (infComp w (ratVec x)) ≤ √(n : ℝ) * (n * locHeight (infAt w g⁻¹)) *
      euclidNorm (infComp w y') := fun w => by
    conv_lhs => rw [hy, infComp_vecMul_GL]
    exact euclidNorm_vecMul_le (locHeight_pos _).le (fun i j => norm_apply_le_locHeight _ i j) _
  have hfinb : ∀ v, ‖finComp v (ratVec x)‖ ≤ locHeight (finAt v g⁻¹) * ‖finComp v y'‖ := fun v => by
    conv_lhs => rw [hy, finComp_vecMul_GL]
    exact norm_vecMul_le_of_norm_le v (locHeight_pos _).le
      (fun i j => norm_apply_le_locHeight _ i j) _
  have hb1 : ∀ v, v ∉ (finite_mulSupport_locHeight_finAt g⁻¹).toFinset →
      locHeight (finAt v g⁻¹) = 1 := fun v hv => by
    by_contra h
    exact hv ((finite_mulSupport_locHeight_finAt g⁻¹).mem_toFinset.2 h)
  have key := adelicNorm_le_of_local (hasFiniteContent_ratVec hx) hfc
    (fun w => √(n : ℝ) * (n * locHeight (infAt w g⁻¹))) (fun v => locHeight (finAt v g⁻¹))
    (finite_mulSupport_locHeight_finAt g⁻¹).toFinset hinfb hb1 hfinb
  have hinf : ∏ w : InfinitePlace K, (√(n : ℝ) * (n * locHeight (infAt w g⁻¹))) ^ w.mult =
      (∏ w : InfinitePlace K, (√(n : ℝ) * n) ^ w.mult) *
        ∏ w : InfinitePlace K, locHeight (infAt w g⁻¹) ^ w.mult := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [← mul_pow, mul_assoc]
  rw [hinf, ← finprod_eq_prod _ (finite_mulSupport_locHeight_finAt g⁻¹)] at key
  have hH : Reduction.height g x = adelicNorm y' := rfl
  rw [← height_inv g, height_eq_prod_locHeight g⁻¹, hH]
  calc (1 : ℝ) ≤ adelicNorm (ratVec x) := one_le_adelicNorm_ratVec hx
    _ ≤ _ := key
    _ = _ := by ring

theorem norm_det_fin_two_le {E : Type*} [NormedField E] (M : Matrix (Fin 2) (Fin 2) E) {m : ℝ}
    (hM : ∀ i j, ‖M i j‖ ≤ m) : ‖M.det‖ ≤ 2 * m ^ 2 := by
  have hm : 0 ≤ m := (norm_nonneg _).trans (hM 0 0)
  rw [det_fin_two]
  calc ‖M 0 0 * M 1 1 - M 0 1 * M 1 0‖ ≤ ‖M 0 0 * M 1 1‖ + ‖M 0 1 * M 1 0‖ := norm_sub_le _ _
    _ ≤ m * m + m * m := by
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul (hM 0 0) (hM 1 1) (norm_nonneg _) hm)
          (mul_le_mul (hM 0 1) (hM 1 0) (norm_nonneg _) hm)
    _ = 2 * m ^ 2 := by ring

theorem norm_det_fin_two_le_of_ultrametric {E : Type*} [NormedField E] [IsUltrametricDist E]
    (M : Matrix (Fin 2) (Fin 2) E) {m : ℝ} (hM : ∀ i j, ‖M i j‖ ≤ m) : ‖M.det‖ ≤ m ^ 2 := by
  have hm : 0 ≤ m := (norm_nonneg _).trans (hM 0 0)
  rw [det_fin_two, sq, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact mul_le_mul (hM 0 0) (hM 1 1) (norm_nonneg _) hm
  · rw [norm_neg, norm_mul]
    exact mul_le_mul (hM 0 1) (hM 1 0) (norm_nonneg _) hm

theorem det_infAt_eq (w : InfinitePlace K) (g : AdelicGLn.AdelicGL K 2) :
    ((AdelicGLn.det K 2 g : 𝔸[K])).1 w = (infAt w g : Matrix (Fin 2) (Fin 2) w.Completion).det := by
  rw [AdelicGLn.coe_det]
  have : (infAt w g : Matrix (Fin 2) (Fin 2) w.Completion) =
      (infEval w).mapMatrix (g : Matrix (Fin 2) (Fin 2) 𝔸[K]) := by
    ext a b; rfl
  rw [this, ← RingHom.map_det]
  rfl

theorem det_finAt_eq (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGLn.AdelicGL K 2) :
    ((AdelicGLn.det K 2 g : 𝔸[K])).2 v =
      (finAt v g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det := by
  rw [AdelicGLn.coe_det]
  have : (finAt v g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      (finEval v).mapMatrix (g : Matrix (Fin 2) (Fin 2) 𝔸[K]) := by
    ext a b; rfl
  rw [this, ← RingHom.map_det]
  rfl

theorem ideleModule_det_le_height_sq (g : AdelicGLn.AdelicGL K 2) :
    (ideleModule K (AdelicGLn.det K 2 g) : ℝ) ≤
      (∏ w : InfinitePlace K, (2 : ℝ) ^ w.mult) * AutomorphicForm.height g ^ 2 := by
  rw [ideleModule_eq]
  have hinf : ∏ w : InfinitePlace K, ‖((AdelicGLn.det K 2 g : IdeleGroup K) : 𝔸[K]).1 w‖ ^ w.mult ≤
      (∏ w : InfinitePlace K, (2 : ℝ) ^ w.mult) *
        (∏ w : InfinitePlace K, locHeight (infAt w g) ^ w.mult) ^ 2 := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun w _ => pow_nonneg (norm_nonneg _) _) fun w _ => ?_
    rw [det_infAt_eq]
    calc ‖(infAt w g : Matrix (Fin 2) (Fin 2) w.Completion).det‖ ^ w.mult
        ≤ (2 * locHeight (infAt w g) ^ 2) ^ w.mult :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_det_fin_two_le _
            fun i j => norm_apply_le_locHeight (infAt w g) i j) _
      _ = 2 ^ w.mult * (locHeight (infAt w g) ^ w.mult) ^ 2 := by ring
  have hf1 : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) =>
      ‖((AdelicGLn.det K 2 g : IdeleGroup K) : 𝔸[K]).2 v‖).Finite :=
    GroundTheory.Global.IdeleGroup.finite_mulSupport_norm _
  have hf2 := finite_mulSupport_locHeight_finAt g
  have hfin : ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖((AdelicGLn.det K 2 g : IdeleGroup K) : 𝔸[K]).2 v‖ ≤
      (∏ᶠ v : HeightOneSpectrum (𝓞 K), locHeight (finAt v g)) ^ 2 := by
    rw [finprod_pow hf2]
    refine finprod_le_finprod_of_nonneg hf1 (hf2.subset (Function.mulSupport_pow _ 2))
      (fun v => norm_nonneg _) fun v => ?_
    rw [det_finAt_eq]
    exact norm_det_fin_two_le_of_ultrametric _ fun i j => norm_apply_le_locHeight (finAt v g) i j
  calc (∏ w : InfinitePlace K, ‖((AdelicGLn.det K 2 g : IdeleGroup K) : 𝔸[K]).1 w‖ ^ w.mult) *
        ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖((AdelicGLn.det K 2 g : IdeleGroup K) : 𝔸[K]).2 v‖
      ≤ ((∏ w : InfinitePlace K, (2 : ℝ) ^ w.mult) *
          (∏ w : InfinitePlace K, locHeight (infAt w g) ^ w.mult) ^ 2) *
        (∏ᶠ v : HeightOneSpectrum (𝓞 K), locHeight (finAt v g)) ^ 2 :=
        mul_le_mul hinf hfin (finprod_nonneg fun _ => norm_nonneg _)
          (mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity) (sq_nonneg _))
    _ = _ := by rw [AutomorphicForm.height]; ring

end Heights

section Rational

open RationalIdeles

theorem ideleModule_eq_realPart_of_mem {u : IdeleGroup ℚ} (hu : u ∈ positiveSubgroup) :
    (ideleModule ℚ u : ℝ) = (RationalIdeles.realPart u : ℝ) := by
  obtain ⟨h1, h2⟩ := mem_positiveSubgroup.1 hu
  have hw := isReal_infinitePlace (default : InfinitePlace ℚ)
  have hmult : (default : InfinitePlace ℚ).mult = 1 := by
    simp [InfinitePlace.mult, hw]
  have hn : ‖(u : 𝔸[ℚ]).1 default‖ = (RationalIdeles.realPart u : ℝ) := by
    rw [← (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
      (map_zero _), ← realEquiv_apply, ← coe_realPart, Real.norm_eq_abs, abs_of_pos h2]
  rw [ideleModule_apply, finiteModule_eq_one_of_mem h1, mul_one, IdeleGroup.infiniteModule,
    Fintype.prod_subsingleton _ (default : InfinitePlace ℚ), hmult, pow_one, hn]

theorem exists_eq_diagonal_mul_borelGL_mul {b : AdelicGL ℚ 2} (hb : b ∈ adelicBorel) :
    ∃ (δ : GL (Fin 2) ℚ) (z : ℍ) (r : ℝ) (hr : (r : ℂ) ≠ 0),
      z.im = adeleAbs ((b : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) 0 0) /
        adeleAbs ((b : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) 1 1) ∧
      ∃ w ∈ integralFiniteGL ℚ 2,
        b = diagonal ℚ 2 δ * realEmb (borelGL z * kGL (r : ℂ) hr) * finEmb ℚ 2 w := by
  have hb10 : (b : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) 1 0 = 0 := hb (show (0 : Fin 2) < 1 by decide)
  set A := (isUnit_apply_self_of_mem_adelicBorel hb 0).unit with hAdef
  set D := (isUnit_apply_self_of_mem_adelicBorel hb 1).unit with hDdef
  have hA0 : (A : 𝔸[ℚ]) = (b : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) 0 0 := IsUnit.unit_spec _
  have hD0 : (D : 𝔸[ℚ]) = (b : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) 1 1 := IsUnit.unit_spec _
  obtain ⟨⟨qa, ua⟩, hA⟩ := mulMap_bijective.2 A
  obtain ⟨⟨qd, ud⟩, hD⟩ := mulMap_bijective.2 D
  rw [mulMap_apply] at hA hD
  have hua := mem_positiveSubgroup.1 ua.2
  have hud := mem_positiveSubgroup.1 ud.2
  set c : IdeleGroup ℚ := IdeleGroup.diagonal ℚ qa * (ud : IdeleGroup ℚ) with hc
  set y : 𝔸[ℚ] := (b : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) 0 1 * ((c⁻¹ : IdeleGroup ℚ) : 𝔸[ℚ]) with hy
  obtain ⟨s, hs⟩ := exists_sub_mem_integralFiniteAdeles y.2
  set t : 𝔸[ℚ] := y - algebraMap ℚ 𝔸[ℚ] s with ht
  have ht2 : t.2 ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := hs
  set P : AdelicGL ℚ 2 := unipAdele t * diagUnits 2 ![(ua : IdeleGroup ℚ), (ud : IdeleGroup ℚ)] with hP
  set δ : GL (Fin 2) ℚ := diagUnits 2 ![qa, qd] * unipGL (n := 2) (r := 1) (fun _ => s) with hδ
  have hcc : (c : 𝔸[ℚ]) * ((c⁻¹ : IdeleGroup ℚ) : 𝔸[ℚ]) = 1 := Units.mul_inv c
  have hcv : (c : 𝔸[ℚ]) = algebraMap ℚ 𝔸[ℚ] qa * ((ud : IdeleGroup ℚ) : 𝔸[ℚ]) := by
    rw [hc, Units.val_mul, IdeleGroup.coe_diagonal]
  have hbP : b = diagonal ℚ 2 δ * P := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    fin_cases i <;> fin_cases j <;>
      simp [hP, hδ, Matrix.mul_apply, Fin.sum_univ_two, AdelicGLn.diagonal_apply, unipAdele,
        unipGL, unipMatrix_apply]
    · rw [← hA0, ← hA, Units.val_mul, IdeleGroup.coe_diagonal]
    · rw [ht, hy]
      linear_combination (-((b : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) 0 1)) * hcc +
        ((b : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) 0 1 * ((c⁻¹ : IdeleGroup ℚ) : 𝔸[ℚ])) * hcv
    · exact hb10
    · rw [← hD0, ← hD, Units.val_mul, IdeleGroup.coe_diagonal]

  have hPe : (P : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) = !![((ua : IdeleGroup ℚ) : 𝔸[ℚ]),
      t * ((ud : IdeleGroup ℚ) : 𝔸[ℚ]); 0, ((ud : IdeleGroup ℚ) : 𝔸[ℚ])] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hP, Matrix.mul_apply, Fin.sum_univ_two, unipAdele, unipGL, unipMatrix_apply]
  have hPinv : P⁻¹ = diagUnits 2 ![(ua : IdeleGroup ℚ)⁻¹, (ud : IdeleGroup ℚ)⁻¹] * unipAdele (-t) := by
    have hu : (unipAdele t)⁻¹ = unipAdele (-t) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← unipAdele_add, add_neg_cancel]
      exact unipGL_zero
    have hd : (diagUnits 2 ![(ua : IdeleGroup ℚ), (ud : IdeleGroup ℚ)])⁻¹ =
        diagUnits 2 ![(ua : IdeleGroup ℚ)⁻¹, (ud : IdeleGroup ℚ)⁻¹] := by
      rw [← map_inv]
      congr 1
      funext i
      fin_cases i <;> rfl
    rw [hP, _root_.mul_inv_rev, hu, hd]
  have hPie : ((P⁻¹ : AdelicGL ℚ 2) : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) =
      !![(((ua : IdeleGroup ℚ)⁻¹ : IdeleGroup ℚ) : 𝔸[ℚ]),
        (((ua : IdeleGroup ℚ)⁻¹ : IdeleGroup ℚ) : 𝔸[ℚ]) * -t;
        0, (((ud : IdeleGroup ℚ)⁻¹ : IdeleGroup ℚ) : 𝔸[ℚ])] := by
    rw [hPinv]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, unipAdele, unipGL, unipMatrix_apply]
  set ra : ℝ := (RationalIdeles.realPart (ua : IdeleGroup ℚ) : ℝ) with hra
  set rd : ℝ := (RationalIdeles.realPart (ud : IdeleGroup ℚ) : ℝ) with hrd
  have hra0 : 0 < ra := hua.2
  have hrd0 : 0 < rd := hud.2
  set x : ℝ := realEquiv t.1 with hx
  have hzpos : 0 < ((x : ℂ) + ((ra / rd : ℝ) : ℂ) * Complex.I).im := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.I_re, mul_zero, zero_add, mul_one]
    positivity
  set z : ℍ := ⟨(x : ℂ) + ((ra / rd : ℝ) : ℂ) * Complex.I, hzpos⟩ with hz
  have hzim : z.im = ra / rd := by
    change ((x : ℂ) + ((ra / rd : ℝ) : ℂ) * Complex.I).im = _
    simp
  have hzre : z.re = x := by
    change ((x : ℂ) + ((ra / rd : ℝ) : ℂ) * Complex.I).re = _
    simp
  have hr : ((rd : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hrd0.ne'
  have hreal : realPart P = borelGL z * kGL (rd : ℂ) hr := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    have e : ∀ i j, (realPart P : Matrix (Fin 2) (Fin 2) ℝ) i j =
        realEquiv (((P : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) i j).1) := fun _ _ => rfl
    rw [e, hPe, Units.val_mul, coe_borelGL, coe_kGL, hzim, hzre]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · rw [hra, coe_realPart]
    · rfl
    · rw [hrd, coe_realPart]
  have hint : ∀ u : IdeleGroup ℚ, u ∈ standardOpenSubgroup ℚ →
      (u : 𝔸[ℚ]).2 ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := fun u hu =>
    mem_integralFiniteAdeles.2 fun v => ((mem_standardOpenSubgroup ℚ).1 hu v).1
  have hw : (prodEquiv ℚ 2 P).2 ∈ integralFiniteGL ℚ 2 := by
    rw [mem_integralFiniteGL_iff]
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [AdelicGLn.prodEquiv_apply_snd, hPe]
      fin_cases i <;> fin_cases j
      · exact hint _ hua.1
      · show t.2 * ((ud : IdeleGroup ℚ) : 𝔸[ℚ]).2 ∈ _
        exact Subring.mul_mem _ ht2 (hint _ hud.1)
      · show (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ _
        exact Subring.zero_mem _
      · exact hint _ hud.1
    · have h1 : ((((ua : IdeleGroup ℚ)⁻¹ : IdeleGroup ℚ) : 𝔸[ℚ])).2 ∈ integralFiniteAdeles (𝓞 ℚ) ℚ :=
        hint _ (inv_mem hua.1)
      have h2 : ((((ud : IdeleGroup ℚ)⁻¹ : IdeleGroup ℚ) : 𝔸[ℚ])).2 ∈ integralFiniteAdeles (𝓞 ℚ) ℚ :=
        hint _ (inv_mem hud.1)
      have h3 : ((((ua : IdeleGroup ℚ)⁻¹ : IdeleGroup ℚ) : 𝔸[ℚ]) * -t).2 ∈
          integralFiniteAdeles (𝓞 ℚ) ℚ :=
        Subring.mul_mem _ h1 (Subring.neg_mem _ ht2)
      have h4 : (0 : 𝔸[ℚ]).2 ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := Subring.zero_mem _
      have e : ((prodEquiv ℚ 2 P).2)⁻¹ = (prodEquiv ℚ 2 P⁻¹).2 := by
        rw [map_inv, Prod.snd_inv]
      rw [e, AdelicGLn.prodEquiv_apply_snd, hPie]
      fin_cases i <;> fin_cases j
      · exact h1
      · exact h3
      · exact h4
      · exact h2
  refine ⟨δ, z, rd, hr, ?_, (prodEquiv ℚ 2 P).2, hw, ?_⟩
  · rw [hzim, ← hA0, ← hD0, adeleAbs_units, adeleAbs_units, ← hA, ← hD, map_mul, map_mul,
      ideleModule_diagonal, ideleModule_diagonal, one_mul, one_mul,
      ideleModule_eq_realPart_of_mem ua.2, ideleModule_eq_realPart_of_mem ud.2]
  · rw [hbP, ← hreal, mul_assoc, realEmb_realPart_mul_finEmb]

end Rational

section Ratio

variable {K : Type*} [Field K] [NumberField K]

theorem det_diagonal_eq (γ : GL (Fin 2) K) :
    AdelicGLn.det K 2 (diagonal K 2 γ) = IdeleGroup.diagonal K (Matrix.GeneralLinearGroup.det γ) := by
  refine Units.ext ?_
  rw [AdelicGLn.coe_det, IdeleGroup.coe_diagonal]
  have : ((diagonal K 2 γ : AdelicGLn.AdelicGL K 2) : Matrix (Fin 2) (Fin 2) 𝔸[K]) =
      (algebraMap K 𝔸[K]).mapMatrix (γ : Matrix (Fin 2) (Fin 2) K) := by
    ext a b
    rw [AdelicGLn.diagonal_apply]
    rfl
  rw [this, ← RingHom.map_det]
  rfl

theorem adeleAbs_div_le_height_pow_four {g b k : AdelicGLn.AdelicGL K 2} {γ : GL (Fin 2) K}
    (hb : b ∈ adelicBorel) (hk : k ∈ maxCompact) (h : diagonal K 2 γ * g = b * k) :
    adeleAbs ((b : Matrix (Fin 2) (Fin 2) 𝔸[K]) 0 0) / adeleAbs ((b : Matrix (Fin 2) (Fin 2) 𝔸[K]) 1 1) ≤
      (∏ w : InfinitePlace K, (2 : ℝ) ^ w.mult) *
        (∏ w : InfinitePlace K, (√((2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ)) ^ w.mult) ^ 2 *
          AutomorphicForm.height g ^ 4 := by
  have hb10 : (b : Matrix (Fin 2) (Fin 2) 𝔸[K]) 1 0 = 0 := hb (show (0 : Fin 2) < 1 by decide)
  set A := (isUnit_apply_self_of_mem_adelicBorel hb 0).unit with hAdef
  set D := (isUnit_apply_self_of_mem_adelicBorel hb 1).unit with hDdef
  have hA0 : (A : 𝔸[K]) = (b : Matrix (Fin 2) (Fin 2) 𝔸[K]) 0 0 := IsUnit.unit_spec _
  have hD0 : (D : 𝔸[K]) = (b : Matrix (Fin 2) (Fin 2) 𝔸[K]) 1 1 := IsUnit.unit_spec _
  set e₁ : Fin 2 → K := Pi.single 1 1 with he₁
  have he₁0 : e₁ ≠ 0 := by
    intro h0
    have := congrFun h0 1
    simp [he₁] at this

  have hrow : ratVec e₁ ᵥ* (b : Matrix (Fin 2) (Fin 2) 𝔸[K]) = (D : 𝔸[K]) • ratVec e₁ := by
    funext j
    fin_cases j <;> simp [he₁, vecMul, dotProduct, Fin.sum_univ_two, ratVec, hb10, hD0]
  have hD : Reduction.height g (e₁ ᵥ* (γ : Matrix (Fin 2) (Fin 2) K)) = (ideleModule K D : ℝ) := by
    rw [← height_diagonal_mul, h, height_mul_maxCompact _ hk, Reduction.height, hrow,
      adelicNorm_smul (hasFiniteContent_ratVec he₁0) D, adelicNorm_ratVec_single, mul_one]
  have hne : e₁ ᵥ* (γ : Matrix (Fin 2) (Fin 2) K) ≠ 0 := by
    intro h0
    apply he₁0
    have := congrArg (fun v => v ᵥ* ((γ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) h0
    simpa [vecMul_vecMul, ← Units.val_mul] using this
  have hV := one_le_const_mul_height_mul_vecHeight g hne
  rw [hD] at hV

  have hdetb : AdelicGLn.det K 2 b = A * D := by
    refine Units.ext ?_
    rw [AdelicGLn.coe_det, det_fin_two, hb10, mul_zero, sub_zero, Units.val_mul, hA0, hD0]
  have hdet : (ideleModule K (AdelicGLn.det K 2 g) : ℝ) =
      (ideleModule K A : ℝ) * (ideleModule K D : ℝ) := by
    have e := congrArg (fun x => (ideleModule K (AdelicGLn.det K 2 x) : ℝ)) h
    simp only [map_mul, Positive.val_mul, det_diagonal_eq, ideleModule_diagonal, hdetb] at e
    rw [mem_normOneGL.1 (maxCompact_le_normOneGL hk)] at e
    simpa using e
  have hdetle := ideleModule_det_le_height_sq g
  rw [hdet] at hdetle
  rw [← hA0, ← hD0, adeleAbs_units, adeleAbs_units]
  set a := (ideleModule K A : ℝ)
  set d := (ideleModule K D : ℝ)
  set H := AutomorphicForm.height g
  set Cd := ∏ w : InfinitePlace K, (2 : ℝ) ^ w.mult
  set Cv := ∏ w : InfinitePlace K, (√((2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ)) ^ w.mult
  have hd : 0 < d := (ideleModule K D).2
  have ha : 0 < a := (ideleModule K A).2
  have hCv : 0 ≤ Cv * H := by nlinarith [hV, hd]
  have h1d : d⁻¹ ≤ Cv * H := by
    rw [inv_le_iff_one_le_mul₀ hd]
    linarith
  calc a / d = (a * d) * (d⁻¹ * d⁻¹) := by field_simp
    _ ≤ (Cd * H ^ 2) * ((Cv * H) * (Cv * H)) :=
        mul_le_mul hdetle (mul_le_mul h1d h1d (inv_nonneg.2 hd.le) hCv)
          (mul_nonneg (inv_nonneg.2 hd.le) (inv_nonneg.2 hd.le))
          (le_trans (mul_nonneg ha.le hd.le) hdetle)
    _ = Cd * Cv ^ 2 * H ^ 4 := by ring

end Ratio

end GL2Classical

end

end GroundTheory.Automorphic
