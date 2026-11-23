import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemContraIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeAdelicMatrixIntegralTranslate
import GroundTheory.AutomorphicForms.FourierWhittaker.PartialCoeffDiagonalBlockGLEqVecCoeff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableOnMinAbsDetInvFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MellinTypeIntegralEntireOfRapidDecayStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchwartzBruhatIntegrableMomentsStatement

noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.ShortVecDecay

namespace GlobalTheory.RSnm

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [IsTotallyComplex E] in

theorem invT_invT (g : GA E a) : invT a (Ad E) (invT a (Ad E) g) = g :=
  Units.ext (by change ((g.val)ᵀ)ᵀ = g.val; exact transpose_transpose _)

omit [IsTotallyComplex E] in

theorem continuous_invT : Continuous (invT a (Ad E)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · change Continuous fun g : GA E a => ((g⁻¹ : GA E a).val)ᵀ
    exact (Units.continuous_val.comp continuous_inv).matrix_transpose
  · change Continuous fun g : GA E a => (g.val)ᵀ
    exact Units.continuous_val.matrix_transpose

theorem bounded_of_decays (ha : 0 < a) {F : GA E a → ℂ} (hF : Decays F) : ∃ C, ∀ g, ‖F g‖ ≤ C := by
  obtain ⟨C, hC⟩ := hF (Set.univ.pi fun _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)))
    (isCompact_univ_pi fun _ => GroundTheory.Global.isCompact_integralFiniteAdeles E) {1} isCompact_singleton 0
  refine ⟨C, fun g => ?_⟩
  set e : Fin a → E := Pi.single ⟨0, ha⟩ 1
  obtain ⟨d, hd, hmem⟩ := GlobalTheory.AdelicMatLat.exists_nat_mul_mem_family E
    (fun i => pFin E (((fun j => algebraMap E (Ad E) (e j)) ᵥ* g.val) i))
  have hξ : (fun j => (d : E) * e j) ≠ 0 := by
    intro h
    have := congrFun h ⟨0, ha⟩
    simp [e] at this
    omega
  have key := hC g 1 rfl (fun j => (d : E) * e j) hξ (fun i _ => by
    have h1 : pFin E (((fun j => algebraMap E (Ad E) ((d : E) * e j)) ᵥ* g.val) i) =
        (d : Af E) * pFin E (((fun j => algebraMap E (Ad E) (e j)) ᵥ* g.val) i) := by
      simp only [vecMul, dotProduct, map_mul, map_natCast, Finset.mul_sum, map_sum, mul_assoc]
    show pFin E _ ∈ _
    rw [h1]
    exact hmem i)
  simpa using key

theorem decays_smoothInf_invT {F : GA E a → ℂ} (hF : Decays fun g => F (invT a (Ad E) g)) {f : Lie E a → ℂ}
    (hf : Continuous f) (hc : HasCompactSupport f) (hs : tsupport f ⊆ invSet E a) :
    Decays fun g => GlobalTheory.JSW.smoothInf f F (invT a (Ad E) g) := by
  intro L hL C₀ hC₀ N
  have hK : IsCompact ((fun y : GL (Fin a) (Cinf E) => toL y.val) ⁻¹' tsupport f) :=
    GlobalTheory.CuspQuot.isOpenEmbedding_val.isInducing.isCompact_preimage' hc fun x hx => hs hx
  obtain ⟨C, h⟩ := hF L hL _ (hC₀.mul ((hK.image GlobalTheory.CuspQuot.continuous_infGL).image continuous_invT)) N
  haveI : IsFiniteMeasureOnCompacts (volume : Measure (Lie E a)) :=
    MeasureTheory.Measure.pi.isFiniteMeasureOnCompacts _
  have hi : Integrable f := hf.integrable_of_hasCompactSupport hc
  refine ⟨(∫ x, ‖f x‖) * C, fun g c hcC ξ hξ hm => ?_⟩
  rw [mul_assoc, ← integral_mul_const]
  refine norm_integral_le_of_norm_le (hi.norm.mul_const _) (.of_forall fun x => ?_)
  by_cases hx : x ∈ tsupport f
  · obtain ⟨u, hu⟩ := hs hx
    obtain rfl : x = toL u.val := hu.symm
    rw [norm_mul, chart_val]
    have e : invT a (Ad E) (g * c) * infGL E a u =
        invT a (Ad E) (g * (c * invT a (Ad E) (infGL E a u))) := by
      rw [map_mul, map_mul, map_mul, invT_invT, mul_assoc]
    rw [e]
    exact mul_le_mul_of_nonneg_left (h g _ (Set.mul_mem_mul hcC ⟨_, ⟨u, hx, rfl⟩, rfl⟩) ξ hξ hm) (norm_nonneg _)
  · simp [image_eq_zero_of_notMem_tsupport hx]

variable (a) in

def goodFns : Submodule ℂ (GA E a → ℂ) where
  carrier := {F | Continuous F ∧ Decays F ∧ Decays fun g => F (invT a (Ad E) g)}
  zero_mem' := ⟨continuous_const, Decays.zero, Decays.zero⟩
  add_mem' := fun h h' => ⟨h.1.add h'.1, h.2.1.add h'.2.1, h.2.2.add h'.2.2⟩
  smul_mem' := fun z _ h => ⟨h.1.const_smul z, h.2.1.smul z, h.2.2.smul z⟩

theorem mem_goodFns (ha : 0 < a) {π : CuspSub E a} (hπ : π.IsUnitary) {F : GA E a → ℂ}
    (hF : F ∈ π.V.map (Sm E a).subtype ⊔ GlobalTheory.JSW.smoothSpan π) : F ∈ goodFns a := by
  have hV : ∀ φ ∈ π.V, φ.1 ∈ goodFns (E := E) a := fun φ hφ =>
    ⟨ContAut.continuous_of_isOpen_stab E a φ (π.cusp φ hφ).1.level, decays_of_mem hπ hφ,
      decays_of_mem hπ.contra (show UpperTheory.V.TC.dualFn E a φ ∈ π.contra.V from ⟨φ, hφ, rfl⟩)⟩
  refine (sup_le ?_ (Submodule.span_le.2 ?_) : _ ≤ goodFns a) hF
  · rintro _ ⟨φ, hφ, rfl⟩
    exact hV φ hφ
  · rintro _ ⟨f, φ, hf, hφ, rfl⟩
    obtain ⟨h1, h2, h3⟩ := hV φ hφ
    obtain ⟨C, hC⟩ := bounded_of_decays ha h2
    exact ⟨(GlobalTheory.CuspQuot.continuous_smoothing (volume : Measure (Lie E a)) ⟨hf.1, hf.2⟩ h1 hC :),
      h2.smoothInf hf.1.continuous hf.2.1 hf.2.2, decays_smoothInf_invT h3 hf.1.continuous hf.2.1 hf.2.2⟩

end GlobalTheory.RSnm

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.ShortVecDecay
open GroundTheory.Automorphic.FourierWhittaker (colGL uMat uMat_apply colX colX_apply coe_uGL blockGL blockMat blockMat_apply
  coe_blockGL partialCoeff stepCoeff vecCoeff vecDomain vecMeasure det_uMat)

namespace GlobalTheory.RSnm

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a n m : ℕ}

omit [IsTotallyComplex E] in

theorem mul_apply_of_row {R : Type} [CommRing R] {A B : Matrix (Fin n) (Fin n) R} {j : Fin n}
    (hA : ∀ t, A j t = (1 : Matrix (Fin n) (Fin n) R) j t) (l : Fin n) : (A * B) j l = B j l := by
  rw [mul_apply, ← one_mul B, mul_apply]
  simp only [hA, one_mul]

omit [IsTotallyComplex E] in

theorem mul_apply_of_col {R : Type} [CommRing R] {A B : Matrix (Fin n) (Fin n) R} {l : Fin n}
    (hB : ∀ t, B t l = (1 : Matrix (Fin n) (Fin n) R) t l) (i : Fin n) : (A * B) i l = A i l := by
  rw [mul_apply]
  simp only [hB]
  rw [← mul_apply, mul_one]

omit [IsTotallyComplex E] in

theorem colGL_row_last {R : Type} [CommRing R] (k : ℕ) (y : Fin k → R) {j : Fin n} (hj : j.val + 1 = n) (t : Fin n) :
    (colGL (n := n) k y : Matrix (Fin n) (Fin n) R) j t = (1 : Matrix (Fin n) (Fin n) R) j t := by
  rw [colGL, coe_uGL, uMat_apply, one_apply]
  split_ifs with h1 h2
  · rfl
  · exact absurd h2 (by rw [Fin.lt_def]; omega)
  · rfl

omit [IsTotallyComplex E] in

theorem colGL_col {R : Type} [CommRing R] {k : ℕ} (hk : k ≠ m) (y : Fin k → R) {l : Fin n} (hl : l.val = m)
    (i : Fin n) : (colGL (n := n) k y : Matrix (Fin n) (Fin n) R) i l = (1 : Matrix (Fin n) (Fin n) R) i l := by
  rw [colGL, coe_uGL, uMat_apply, one_apply]
  split_ifs with h1 h2
  · rfl
  · rw [colX_apply, dif_neg (by simp only; omega)]
  · rfl

omit [IsTotallyComplex E] in
theorem blockGL_row_last {R : Type} [CommRing R] (hmn : m < n) (h : GL (Fin m) R) {j : Fin n} (hj : j.val + 1 = n)
    (t : Fin n) : (blockGL hmn.le h : Matrix (Fin n) (Fin n) R) j t = (1 : Matrix (Fin n) (Fin n) R) j t := by
  rw [coe_blockGL, blockMat_apply, dif_neg (by omega), one_apply]

omit [IsTotallyComplex E] in
theorem blockGL_col {R : Type} [CommRing R] (hmn : m < n) (h : GL (Fin m) R) {l : Fin n} (hl : l.val = m)
    (i : Fin n) : (blockGL hmn.le h : Matrix (Fin n) (Fin n) R) i l = (1 : Matrix (Fin n) (Fin n) R) i l := by
  rw [coe_blockGL, blockMat_apply, one_apply]
  split_ifs with h1 h2 h3 <;> first | rfl | omega | (subst h3; omega)

omit [IsTotallyComplex E] in
theorem det_colGL {R : Type} [CommRing R] (k : ℕ) (y : Fin k → R) :
    GeneralLinearGroup.det (colGL (n := n) k y) = 1 :=
  Units.ext (by rw [GeneralLinearGroup.val_det_apply, colGL, coe_uGL, det_uMat, Units.val_one])

omit [IsTotallyComplex E] in
theorem det_blockGL {R : Type} [CommRing R] (hmn : m ≤ n) (h : GL (Fin m) R) :
    GeneralLinearGroup.det (blockGL hmn h) = GeneralLinearGroup.det h := by
  refine Units.ext ?_
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply, coe_blockGL, blockMat,
    det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_one, mul_one]

omit [IsTotallyComplex E] in
theorem continuous_blockGL (hmn : m ≤ n) : Continuous fun h : GA E m => (blockGL hmn h : GA E n) := by
  have hc : ∀ M : GA E m → Matrix (Fin m) (Fin m) (Ad E), Continuous M →
      Continuous fun h => blockMat (n := n) hmn (M h) := fun M hM => by
    refine continuous_matrix fun a b => ?_
    simp only [blockMat_apply]
    split_ifs
    · exact hM.matrix_elem _ _
    all_goals exact continuous_const
  refine Units.continuous_iff.2 ⟨hc _ Units.continuous_val, ?_⟩
  have e : (fun h : GA E m => ((blockGL hmn h)⁻¹ : GA E n).val) = fun h => blockMat hmn (h⁻¹ : GA E m).val := by
    funext h; rw [← map_inv, coe_blockGL]
  rw [e]
  exact hc _ (Units.continuous_val.comp continuous_inv)

end GlobalTheory.RSnm

namespace GlobalTheory.RSnm

open GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a n m : ℕ}

def detAbs (g : GA E a) : ℝ := (ideleModule E (GeneralLinearGroup.det g) : ℝ)

omit [IsTotallyComplex E] in
theorem detAbs_pos (g : GA E a) : 0 < detAbs g := (ideleModule E _).2

omit [IsTotallyComplex E] in
theorem detAbs_mul (g h : GA E a) : detAbs (g * h) = detAbs g * detAbs h := by
  simp only [detAbs, map_mul, Positive.val_mul]

omit [IsTotallyComplex E] in
theorem continuous_detAbs : Continuous (detAbs (E := E) (a := a)) :=
  continuous_subtype_val.comp (continuous_ideleModule.comp (AdelicGLn.continuous_det E a))

theorem detAbs_invT (g : GA E a) : detAbs (invT a (Ad E) g) = (detAbs g)⁻¹ := by
  have h : GeneralLinearGroup.det (invT a (Ad E) g) = (GeneralLinearGroup.det g)⁻¹ := by
    refine Units.ext ?_
    rw [GeneralLinearGroup.val_det_apply, invT_val_eq, det_nonsing_inv, det_transpose,
      ← GeneralLinearGroup.val_det_apply, Ring.inverse_unit]
  rw [detAbs, h, map_inv, Positive.coe_inv]
  rfl

omit [IsTotallyComplex E] in
theorem detAbs_colGL (k : ℕ) (y : Fin k → Ad E) : detAbs (colGL (n := a) k y) = 1 := by
  rw [detAbs, det_colGL, map_one]; rfl

omit [IsTotallyComplex E] in
theorem detAbs_blockGL (hmn : m ≤ n) (h : GA E m) : detAbs (blockGL hmn h : GA E n) = detAbs h := by
  rw [detAbs, detAbs, det_blockGL]

variable (m) in

def InS (g : GA E n) : Prop :=
  (∀ j t : Fin n, j.val + 1 = n → g.val j t = (1 : Matrix (Fin n) (Fin n) (Ad E)) j t) ∧
    ∀ i l : Fin n, l.val = m → g.val i l = (1 : Matrix (Fin n) (Fin n) (Ad E)) i l

theorem single_vecMul_eq (j : Fin n) (M : Matrix (Fin n) (Fin n) (Ad E)) :
    (fun i => algebraMap E (Ad E) ((Pi.single j 1 : Fin n → E) i)) ᵥ* M = fun t => M j t := by
  have : (fun i => algebraMap E (Ad E) ((Pi.single j 1 : Fin n → E) i)) = Pi.single j 1 := by
    funext i; by_cases h : i = j
    · subst h; simp
    · simp [h]
  rw [this, single_one_vecMul]
  rfl

theorem norm_le_of_inS (hmn : m < n) {φ : GA E n → ℂ} (hφ : φ ∈ goodFns n) {L : Set (Fin m → Af E)}
    (hL : IsCompact L) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : GA E n, InS m g → ∀ x : Fin m → Ad E, (fun i => pFin E (x i)) ∈ L →
      ‖φ (g * colGL m x)‖ ≤
        C * (1 + ‖fun i => pInf E (x i)‖) ^ (n * Module.finrank ℚ E * N) * (min (detAbs g) (detAbs g)⁻¹) ^ N := by
  set last : Fin n := ⟨n - 1, by omega⟩
  set mm : Fin n := ⟨m, hmn⟩
  set d := n * Module.finrank ℚ E
  set r : Fin n → Ad E := fun t => (1 : Matrix (Fin n) (Fin n) (Ad E)) last t
  set Φ : (Fin m → Af E) → (Fin n → Af E) := fun v t => if t = mm then 1 else if h : t.val < m then -v ⟨t, h⟩ else 0
  have hΦ : Continuous Φ := continuous_pi fun t => by
    simp only [Φ]
    split_ifs
    · exact continuous_const
    · exact (continuous_apply _).neg
    · exact continuous_const
  obtain ⟨C₁, h₁⟩ := hφ.2.1 {fun i => pFin E (r i)} isCompact_singleton {1} isCompact_singleton N
  obtain ⟨C₂, h₂⟩ := hφ.2.2 (Φ '' L) (hL.image hΦ) {1} isCompact_singleton N
  refine ⟨max (max C₁ C₂) 0, le_max_right _ _, fun g hg x hx => ?_⟩
  set T := detAbs g
  have hT : 0 < T := detAbs_pos g
  set X := ‖fun i => pInf E (x i)‖
  have hX : 0 ≤ X := norm_nonneg _
  set u := (colGL (n := n) m x : GA E n)
  have hTu : detAbs (g * u) = T := by rw [detAbs_mul, detAbs_colGL, mul_one]

  have hrow : (fun i => algebraMap E (Ad E) ((Pi.single last 1 : Fin n → E) i)) ᵥ* (g * u).val = r := by
    rw [single_vecMul_eq]
    funext t
    rw [Units.val_mul, mul_apply_of_row (fun t => hg.1 last t (by simp only [last]; omega))]
    exact colGL_row_last m x (by simp only [last]; omega) t
  have hne1 : (Pi.single last 1 : Fin n → E) ≠ 0 := fun h => by simpa using congrFun h last
  have b1 := h₁ (g * u) 1 rfl _ hne1 (by rw [hrow]; rfl)
  rw [mul_one, hrow] at b1
  change ‖φ (g * u)‖ ≤ C₁ * (_ / detAbs (g * u)) ^ N at b1
  rw [hTu] at b1
  have hr : ‖fun i => pInf E (r i)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun t => ?_
    simp only [r, one_apply]
    split_ifs
    · rw [map_one]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun w => by simp
    · simp
  have b1' : ‖φ (g * u)‖ ≤ max (max C₁ C₂) 0 * T⁻¹ ^ N := by
    refine b1.trans ?_
    have e1 : (‖fun i => pInf E (r i)‖ ^ d / T) ^ N ≤ T⁻¹ ^ N := by
      refine pow_le_pow_left₀ (by positivity) ?_ N
      rw [div_eq_mul_inv]
      exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ (norm_nonneg _) hr)
    calc C₁ * (‖fun i => pInf E (r i)‖ ^ d / T) ^ N ≤ max (max C₁ C₂) 0 * (‖fun i => pInf E (r i)‖ ^ d / T) ^ N :=
          mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_left _ _)) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left e1 (le_max_right _ _)

  set w : Fin n → Ad E := fun t => ((colGL (n := n) m (-x) : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) t mm
  have hginv : ∀ t, ((g⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) t mm = (1 : Matrix (Fin n) (Fin n) (Ad E)) t mm := by
    intro t
    have := mul_apply_of_col (A := ((g⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E))) (B := g.val) (l := mm)
      (fun t => hg.2 t mm rfl) t
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one] at this
    exact this.symm
  have hcol : (fun i => algebraMap E (Ad E) ((Pi.single mm 1 : Fin n → E) i)) ᵥ* (invT n (Ad E) (g * u)).val = w := by
    rw [single_vecMul_eq]
    funext t
    change (((g * u)⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E))ᵀ mm t = _
    rw [transpose_apply, _root_.mul_inv_rev, Units.val_mul, mul_apply_of_col hginv]
    simp only [w, u]
    rw [← GroundTheory.Automorphic.FourierWhittaker.colGL_neg]
  have hne2 : (Pi.single mm 1 : Fin n → E) ≠ 0 := fun h => by simpa using congrFun h mm
  have hmm : mm.val = m := rfl
  have hw : (fun t => pFin E (w t)) = Φ fun i => pFin E (x i) := by
    funext t
    simp only [w, Φ, colGL, coe_uGL, uMat_apply, colX_apply]
    split_ifs <;> first | (simp; done) | (exfalso; simp only [Fin.lt_def] at *; omega) | (simp only [Fin.lt_def] at *; omega)
  have b2 := h₂ (invT n (Ad E) (g * u)) 1 rfl _ hne2 (by rw [hcol, hw]; exact ⟨_, hx, rfl⟩)
  rw [mul_one, hcol] at b2
  change ‖φ (invT n (Ad E) (invT n (Ad E) (g * u)))‖ ≤ C₂ * (_ / detAbs (invT n (Ad E) (g * u))) ^ N at b2
  rw [invT_invT, detAbs_invT, hTu] at b2
  have hw' : ‖fun t => pInf E (w t)‖ ≤ 1 + X := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun t => ?_
    simp only [w, colGL, coe_uGL, uMat_apply, colX_apply]
    split_ifs with h1 h2 h3
    · rw [map_one]
      exact ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun w => by simp).trans (le_add_of_nonneg_right hX)
    · rw [Pi.neg_apply, map_neg, norm_neg]
      exact (norm_le_pi_norm (fun i => pInf E (x i)) _).trans (le_add_of_nonneg_left zero_le_one)
    · simp only [map_zero, norm_zero]; positivity
  have b2' : ‖φ (g * u)‖ ≤ max (max C₁ C₂) 0 * (1 + X) ^ (d * N) * T ^ N := by
    refine b2.trans ?_
    have e2 : (‖fun t => pInf E (w t)‖ ^ d / T⁻¹) ^ N ≤ (1 + X) ^ (d * N) * T ^ N := by
      rw [div_inv_eq_mul, mul_pow, ← pow_mul]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hw' _) (by positivity)
    calc C₂ * (‖fun t => pInf E (w t)‖ ^ d / T⁻¹) ^ N ≤ max (max C₁ C₂) 0 * (‖fun t => pInf E (w t)‖ ^ d / T⁻¹) ^ N :=
          mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_right _ _)) (by positivity)
      _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left e2 (le_max_right _ _)
  have hX1 : 1 ≤ (1 + X) ^ (d * N) := one_le_pow₀ (le_add_of_nonneg_right hX)
  rcases le_total T 1 with hT1 | hT1
  · rw [min_eq_left (hT1.trans ((one_le_inv₀ hT).mpr hT1))]
    exact b2'
  · rw [min_eq_right (by exact (inv_le_one_of_one_le₀ hT1).trans hT1)]
    refine b1'.trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
    exact le_mul_of_one_le_left (by positivity) hX1

end GlobalTheory.RSnm

namespace GlobalTheory.RSnm

open GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff_self partialCoeff_of_lt continuous_partialCoeff continuous_colGL
  vecMeasure_vecDomain measurableSet_vecDomain)

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a n m : ℕ}

theorem inS_colGL_mul {k : ℕ} (hk : k ≠ m) (y : Fin k → Ad E) {g : GA E n} (hg : InS m g) :
    InS m (colGL (n := n) k y * g) := by
  refine ⟨fun j t hj => ?_, fun i l hl => ?_⟩
  · rw [Units.val_mul, mul_apply_of_row (fun t => colGL_row_last k y hj t)]
    exact hg.1 j t hj
  · rw [Units.val_mul, mul_apply_of_col (fun t => hg.2 t l hl)]
    exact colGL_col hk y hl i

theorem inS_blockGL (hmn : m < n) (h : GA E m) : InS m (blockGL hmn.le h : GA E n) :=
  ⟨fun j t hj => blockGL_row_last hmn h hj t, fun i l hl => blockGL_col hmn h hl i⟩

variable (m) in

def colSmooth (F : (Fin m → Ad E) → ℂ) (φ : GA E n → ℂ) (g : GA E n) : ℂ :=
  ∫ x, F x * φ (g * colGL m x) ∂GJMatrix.adeleMeasurePi E

theorem continuous_colSmooth {F : (Fin m → Ad E) → ℂ} (hF : F ∈ GJMatrix.schwartzBruhatPi E (Fin m))
    {φ : GA E n → ℂ} (hc : Continuous φ) {C : ℝ} (hC : ∀ g, ‖φ g‖ ≤ C) : Continuous (colSmooth m F φ) :=
  continuous_of_dominated (bound := fun x => ‖F x‖ * C)
    (fun g => ((GJMatrix.continuous_of_mem_schwartzBruhatPi hF).mul
      (hc.comp (continuous_const.mul (continuous_colGL m)))).aestronglyMeasurable)
    (fun g => .of_forall fun x => (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)))
    ((GJMatrix.integrable_of_mem_schwartzBruhatPi hF).norm.mul_const C)
    (.of_forall fun x => continuous_const.mul (hc.comp (continuous_id.mul continuous_const)))

theorem colSmooth_bound (hmn : m < n) {φ : GA E n → ℂ} (hφ : φ ∈ goodFns n) {F : (Fin m → Ad E) → ℂ}
    (hF : F ∈ GJMatrix.schwartzBruhatPi E (Fin m)) (N : ℕ) :
    ∃ C : ℝ, ∀ g, InS m g → ‖colSmooth m F φ g‖ ≤ C * (min (detAbs g) (detAbs g)⁻¹) ^ N := by
  obtain ⟨⟨L, hL, hsupp⟩, hint⟩ := GlobalTheory.T.schwartz_bruhat_integrable_moments E m F hF
  obtain ⟨C, hC0, hC⟩ := norm_le_of_inS hmn hφ hL N
  set k := n * Module.finrank ℚ E * N
  refine ⟨C * ∫ x, ‖F x‖ * (1 + ‖fun i => pInf E (x i)‖) ^ k ∂GJMatrix.adeleMeasurePi E, fun g hg => ?_⟩
  set W := (min (detAbs g) (detAbs g)⁻¹) ^ N
  have hW : 0 ≤ W := pow_nonneg (le_min (detAbs_pos g).le (inv_nonneg.2 (detAbs_pos g).le)) N
  refine (norm_integral_le_of_norm_le ((hint k).mul_const (C * W)) (.of_forall fun x => ?_)).trans_eq ?_
  · rw [norm_mul]
    by_cases hx : F x = 0
    · rw [hx, norm_zero, zero_mul, zero_mul, zero_mul]
    · rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ((hC g hg x (hsupp x hx)).trans_eq ?_) (norm_nonneg _)
      ring
  · rw [integral_mul_const]
    ring

theorem partialCoeff_bound (hmn : m < n) {G : GA E n → ℂ} {b : ℝ → ℝ}
    (hG : ∀ g, InS m g → ‖G g‖ ≤ b (detAbs g)) :
    ∀ i j, j + i = n → m + 1 ≤ j → ∀ g, InS m g → ‖partialCoeff G j g‖ ≤ b (detAbs g) := by
  intro i
  induction i with
  | zero =>
    intro j hj _ g hg
    rw [add_zero] at hj
    subst hj
    rw [partialCoeff_self]
    exact hG g hg
  | succ i ih =>
    intro j hj hmj g hg
    have hjn : j < n := by omega
    rw [partialCoeff_of_lt G hjn]
    have hb : 0 ≤ b (detAbs g) := (norm_nonneg _).trans (hG g hg)
    refine (norm_setIntegral_le_of_norm_le_const (C := b (detAbs g)) (by rw [vecMeasure_vecDomain]; exact ENNReal.one_lt_top)
      fun x _ => ?_).trans_eq ?_
    · rw [norm_mul, Circle.norm_coe, mul_one]
      have := ih (j + 1) (by omega) (by omega) _ (inS_colGL_mul (by omega) x hg)
      rwa [detAbs_mul, detAbs_colGL, one_mul] at this
    · rw [measureReal_def, vecMeasure_vecDomain, ENNReal.toReal_one, mul_one]

end GlobalTheory.RSnm

namespace GlobalTheory.RSnm

open GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic.FourierWhittaker (continuous_partialCoeff)
open scoped ComplexConjugate nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n m : ℕ}

variable (m) in

def rsIntegrand (hmn : m ≤ n) (F : (Fin m → Ad E) → ℂ) (φ : GA E n → ℂ) (φ' : GA E m → ℂ) (s : ℂ) (h : GA E m) : ℂ :=
  FourierWhittaker.partialCoeff (colSmooth m F φ) (m + 1) (blockGL hmn h) * conj (φ' h) *
    ((detAbs h : ℝ) : ℂ) ^ (s - ((n : ℂ) - m) / 2)

end GlobalTheory.RSnm
