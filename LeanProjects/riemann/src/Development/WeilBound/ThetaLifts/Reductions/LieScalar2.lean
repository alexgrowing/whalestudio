import Mathlib
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.TraceBlocks
import Development.WeilBound.ThetaLifts.Reductions.SymplOfMem

noncomputable section

open scoped TensorProduct Matrix Classical Real SchwartzMap
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift Complex

namespace PositivityTheory.ThKR

open PositivityTheory.RL PositivityTheory.RL.Up

theorem lieSecond2 (hM : LocalLift) : GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.LieSecond := by
  intro hD0 F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ om χ m hcm hψ hfr hΦ hW hm γ hγ Y hY T
  obtain ⟨hom, dd, omd, hdd, ⟨-, homd, hS⟩, hres⟩ := hW
  obtain ⟨D, hD⟩ := hD0 F E σ α β κ ψ JA JB d hψ
  obtain ⟨Dd, hDd⟩ := hD0 F E σ α (β ⊕ β) (κ ⊕ κ) ψ JA (dbl JB) dd hψ
  have iD : IsD d D := fun u hu f => (hD u hu f).2
  have iDd : IsD dd Dd := fun u hu f => (hDd u hu f).2
  obtain ⟨c, hc⟩ := main2 hM hcm hψ τ (fun w => (b • JB.map (piInf (τ w))).map star)
    (fun w => (frame_K (hfr.2.2 w)).1) (fun w => (frame_K (hfr.2.2 w)).2) (fun w => iff_K (frame_K (hfr.2.2 w)).2) hom iD
  have eK : ∀ w, (b • (dbl JB).map (piInf (τ w))).map star = Matrix.fromBlocks ((b • JB.map (piInf (τ w))).map star) 0 0
      (-(b • JB.map (piInf (τ w))).map star) := fun w => by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [dbl]
  have uK : ∀ w, IsUnit ((b • (dbl JB).map (piInf (τ w))).map star).det := fun w => by
    rw [eK, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
    exact (frame_K (hfr.2.2 w)).2.mul ((isUnit_one.neg.pow _).mul (frame_K (hfr.2.2 w)).2)
  obtain ⟨c', hc'⟩ := main2 hM hcm hψ τ (fun w => (b • (dbl JB).map (piInf (τ w))).map star)
    (fun w => by
      simp only [eK, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_neg, Matrix.conjTranspose_zero,
        (frame_K (hfr.2.2 w)).1]) uK (fun w => iff_K (uK w)) homd iDd
  obtain ⟨Z, tr, hZ, hdet, hre, u, v, hu, hv, huv, hq⟩ := fock_data hcm hfr hΦ (fun u hu f => (hD u hu f).1) hY
  have split : ∀ x : Matrix α (β ⊕ β) (AE F E), At (evI F) x → ∃ x₁ x₂, At (evI F) x₁ ∧ At (evI F) x₂ ∧
      x = Matrix.fromCols x₁ x₂ := fun x hx =>
    ⟨x.toCols₁, x.toCols₂, fun s hs => congrArg Matrix.toCols₁ (hx s hs), fun s hs => congrArg Matrix.toCols₂ (hx s hs),
      (Matrix.fromCols_toCols x).symm⟩
  have z0 : At (evI F) (0 : Matrix α β (AE F E)) := fun _ _ => smul_zero _
  have step2 : ∑ w, c w * (Y w).trace = ∑ w, c' w * (Y w).trace := by
    obtain ⟨δ, hδ, hδ'⟩ := exists_dbl hγ (γ' := 1) ⟨continuous_const, fun t s _ => by simp⟩
    obtain ⟨f, B, r, hB, hf, -, -, hr0⟩ := exists_box F κ
    obtain ⟨g, hg, y, hy⟩ := SeminormBoundRestriction.exists_SB (F := F) (κ := κ)
    let x := SeminormBoundRestriction.pt (0 : κ → mixedEmbedding.mixedSpace F) y
    have h1 := hc' δ hδ (fun w => Matrix.fromBlocks (Z w) 0 0 0) (fun t w => by
      rw [hδ', Matrix.fromBlocks_map, hZ, Matrix.fromBlocks_smul, smul_zero, exp_blocks, NormedSpace.exp_zero]
      simp) _ (fun j => Matrix.fromCols (u j) 0) (fun j => Matrix.fromCols (v j) 0) (fun j => at_cols (hu j) z0)
      (fun j => at_cols (hv j) z0) (fun x hx w => by
        obtain ⟨x₁, x₂, h₁, h₂, rfl⟩ := split x hx
        simp only [sB_dbl hdd, sB_zero d, sub_zero, Matrix.fromBlocks_transpose, Matrix.fromCols_map,
          Matrix.fromCols_mul_fromBlocks, Matrix.transpose_zero, Matrix.mul_zero, add_zero, huv x₁ h₁]
        ext i j
        rcases j with j | j <;> simp [Matrix.sum_apply]) B _ (box_SB hg hg) _ (SeminormBoundRestriction.eval_adm (Sum.elim x x))
    have h2 := (hc γ hγ Z hZ _ u v hu hv huv f g hg _ (SeminormBoundRestriction.eval_adm x)).mul_const (pureA F f g x)
    have eB : ∀ (B : SInf F (κ ⊕ κ)), pureA F B (boxFun g g) (Sum.elim x x) = B 0 := fun B => by
      have : Sum.elim x x = SeminormBoundRestriction.pt 0 (Sum.elim y y) := funext fun i => by rcases i with i | i <;> rfl
      rw [this, SeminormBoundRestriction.pureA_pt]
      show _ * (g y * g y) = _
      rw [hy, mul_one, mul_one]
    have ef : ∀ f : SInf F κ, pureA F f g x = f 0 := fun f => by rw [SeminormBoundRestriction.pureA_pt, hy, mul_one]
    have e3 : pureA F B (boxFun g g) = boxFun (pureA F f g) (pureA F f g) := by
      funext p
      simp only [pureA, boxFun, hB]
      exact mul_mul_mul_comm _ _ _ _
    have h3 := h1.unique (h2.congr_of_eventuallyEq (.of_forall fun t => by
      show omd _ _ _ = _
      rw [e3, hres (γ (Multiplicative.ofAdd t)) _ (hδ' _) _ (pure_mem f hg) _ (pure_mem f hg)]
      rfl))
    have f0 : f 0 = 1 := by rw [hf, hr0, ofReal_one]
    have bb : ∀ p q : Matrix α β (AE F E), At (evI F) p → At (evI F) q →
        Dd (Matrix.fromCols p 0) (Dd (Matrix.fromCols q 0) B) 0 = D p (D q f) 0 := fun p q hp hq =>
      (box_D hdd iD iDd hp (box_D hdd iD iDd hq hB) 0).trans (by
        show D p (D q f) 0 * f 0 = _
        rw [f0, mul_one])
    have B0 : B 0 = 1 := (hB 0).trans (by
      show f 0 * f 0 = 1
      rw [f0, mul_one])
    simp only [LinearMap.proj_apply, eB, ef, SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.sum_apply,
      bb _ _ (hu _) (hv _), bb _ _ (hv _) (hu _), f0, B0, mul_one, smul_eq_mul, add_right_inj, trace_blocks,
      Matrix.trace_zero, add_zero, tr] at h3
    exact h3.symm
  have step1 : ∑ w, c' w * (Y w).trace = ∑ w, (m w : ℂ) / 2 * (Y w).trace := by
    obtain ⟨δ, hδ, hδ'⟩ := exists_dbl hγ hγ
    obtain ⟨l, hl, hinv, B, G, hG, hne⟩ := exists_form F κ ψ
    obtain ⟨T0, hT0⟩ := hl G hG
    have kill : ∀ y, At (evI F) y → ∀ B', T0 (Dd (Matrix.fromCols y y) B') = 0 := fun y hy B' => by
      have h1 := (hDd _ (at_cols hy hy) B').1 G hG l hl
      have e : ∀ t : ℝ, l (dd.rho ψ (realAd F t • Matrix.fromCols y y) (pureA F B' G)) = l (pureA F B' G) := fun t => by
        rw [show realAd F t • Matrix.fromCols y y = Matrix.fromCols (realAd F t • y) (realAd F t • y) by
          ext i j
          rcases j with j | j <;> rfl, Darboux.rho, hdd, hinv _ _ _ (pure_mem B' hG)]
      simp only [e] at h1
      rw [← hT0]
      exact h1.unique (hasDerivAt_const _ _)
    let hf : AF F := realAd F (1 / 2)
    have hh : ∀ j, At (evI F) (hf • u j) := fun j s hs => by rw [smul_comm, hu j s hs, smul_zero]
    have ng : ∀ {p : Matrix α β (AE F E)}, At (evI F) p → At (evI F) (-p) := fun hp s hs => by
      rw [smul_neg, hp s hs, neg_zero]
    have h1 := hc' δ hδ (fun w => Matrix.fromBlocks (Z w) 0 0 (Z w)) (fun t w => by
      rw [hδ', Matrix.fromBlocks_map, hZ, Matrix.fromBlocks_smul, smul_zero, exp_blocks]
      simp) _
      (Sum.elim (fun j => Matrix.fromCols (hf • u j) (hf • u j)) fun j => Matrix.fromCols (hf • u j) (-(hf • u j)))
      (Sum.elim (fun j => Matrix.fromCols (v j) (-v j)) fun j => Matrix.fromCols (v j) (v j))
      (by rintro (j | j); exacts [at_cols (hh j) (hh j), at_cols (hh j) (ng (hh j))])
      (by rintro (j | j); exacts [at_cols (hv j) (ng (hv j)), at_cols (hv j) (hv j)]) (fun x hx w => by
        obtain ⟨x₁, x₂, h₁, h₂, rfl⟩ := split x hx
        simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, sB_dbl hdd, sB_neg d, Matrix.fromBlocks_transpose,
          Matrix.fromCols_map, Matrix.fromCols_mul_fromBlocks, Matrix.transpose_zero, Matrix.mul_zero, add_zero, zero_add,
          huv x₁ h₁, huv x₂ h₂, ← Finset.sum_add_distrib]
        ext i k
        rcases k with k | k <;>
        · simp only [Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Matrix.sum_apply, Matrix.add_apply,
            Matrix.smul_apply, Matrix.map_apply, Matrix.neg_apply, map_neg, hf, Fock.piInf_realAd hcm.1, real_smul]
          refine Finset.sum_congr rfl fun j _ => ?_
          push_cast
          ring) B G hG l hl
    have h2 : ∀ t : ℝ, l (omd (δ (Multiplicative.ofAdd t)) (pureA F B G)) =
        cexp (t * ∑ w, (m w : ℂ) * (Y w).trace) * l (pureA F B G) := fun t => by
      have n1 : ∀ w, ‖cexp (t * (Y w).trace)‖ = 1 := fun w => by simp [norm_exp, hre]
      have ad := at_det (hγ.2 (Multiplicative.ofAdd t))
      rw [hS l hl (fun z φ hφ => by
        rw [show z * (diagCols β : Matrix (β ⊕ β) β (AE F E))ᵀ = Matrix.fromCols z z by
          simp [diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols], Darboux.rho, hdd, hinv _ _ _ hφ])
        (δ (Multiplicative.ofAdd t)) (γ (Multiplicative.ofAdd t)).1 (by
          rw [hδ']
          simp [diagCols, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul]) _ (pure_mem B hG),
        show Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det (γ (Multiplicative.ofAdd t)).1) = 1
          from Units.ext (norm_eq_one hcm τ ad fun w => (congrArg norm (hdet t w)).trans (n1 w)),
        hm _ ad]
      simp only [Matrix.GeneralLinearGroup.val_det_apply, hdet, n1, map_one, NNReal.coe_one, Real.one_rpow, ofReal_one,
        mul_one, div_one, ← Complex.exp_int_mul, ← Complex.exp_sum, Finset.mul_sum]
      congr 2
      exact Finset.sum_congr rfl fun w _ => by ring
    simp only [h2] at h1
    have h3 := h1.unique ((((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const
      (∑ w, (m w : ℂ) * (Y w).trace)).cexp).mul_const (l (pureA F B G)))
    have t1 : ∀ j, T0 (Dd (Matrix.fromCols (v j) (-v j)) (Dd (Matrix.fromCols (hf • u j) (hf • u j)) B)) =
        2 * π * I * (2 * sB σ JA JB (v j) (hf • u j) : ℝ) * T0 B := fun j => by
      rw [iDd.comm (at_cols (hv j) (ng (hv j))) (at_cols (hh j) (hh j)), map_add, kill _ (hh j), map_smul, sB_dbl hdd,
        sB_neg d, zero_add, smul_eq_mul]
      congr 3
      ring
    have t2 : ∀ j, T0 (Dd (Matrix.fromCols (hf • u j) (-(hf • u j))) (Dd (Matrix.fromCols (v j) (v j)) B)) =
        -(2 * π * I * (2 * sB σ JA JB (v j) (hf • u j) : ℝ) * T0 B) := fun j => by
      rw [iDd.comm (at_cols (hh j) (ng (hh j))) (at_cols (hv j) (hv j)), map_add, kill _ (hv j), map_smul, sB_dbl hdd,
        sB_neg d, zero_add, smul_eq_mul, sB_anti d]
      push_cast
      ring
    rw [hT0] at hne
    simp only [hT0, map_add, map_smul, map_sum, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, kill _ (hh _),
      kill _ (hv _), t1, t2, zero_add, add_zero, Finset.sum_neg_distrib, add_neg_cancel, smul_zero, smul_eq_mul,
      trace_blocks, tr, id, ofReal_zero, zero_mul, Complex.exp_zero, one_mul, ofReal_one, mul_zero] at h3
    have h4 := mul_right_cancel₀ hne h3
    simp only [mul_add, Finset.sum_add_distrib] at h4
    simp only [div_mul_eq_mul_div, ← Finset.sum_div, ← h4]
    ring
  have := hc γ hγ Z hZ _ u v hu hv huv (Φ T)
  simp only [tr, hq, step2, step1] at this
  rw [sumPl_add]
  exact this

end PositivityTheory.ThKR

end
