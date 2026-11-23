import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnnSeqShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricShortExactIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantMetricIsometric

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame
open GlobalTheory.Twist (resM app_resM)
open scoped ComplexOrder

namespace GlobalTheory.DualGrLine

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem det_dualGram_re {n : Type} [Fintype n] [DecidableEq n] {G : Matrix n n ℂ} (hG : G.PosDef) :
    (dualGram G).det.re = (G.det.re)⁻¹ := by
  have h₁ := hG.det_pos
  have e : G.det = ((G.det.re : ℝ) : ℂ) := by
    have := (Complex.lt_def.1 h₁).2
    exact Complex.ext rfl (by simpa using this.symm)
  rw [dualGram, Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', e]
  rw [← Complex.ofReal_inv, Complex.ofReal_re, Complex.ofReal_re]

theorem isometric_dual_det {E : X.Modules} {r : ℕ} {h : VMetric p E r} (H : h.IsCInf) :
    (VMetric.det H).dual.Isometric (VMetric.det H.dual) := by
  refine HermLB.isometric_of_chart (fun c : Chart E r => c.dual) (fun _ => le_rfl) (fun x c c' hx hx' => ?_)
    (fun σ c y hy => ?_)
  · exact congrArg _ (IsFrame.detUnit_dual c.isFrame c'.isFrame _ _).symm
  · change -Real.log ((h.met σ).dual.G c.dual y).det.re = -(-Real.log ((h.met σ).G c y).det.re)
    rw [(h.met σ).dual_G c hy, det_dualGram_re ((h.met σ).posDef c y hy), Real.log_inv]

theorem quotGram_chg_dualGram {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
    {G T : Matrix (m ⊕ l) (m ⊕ l) ℂ} {U : Matrix (m ⊕ l) l ℂ} {T₀ : Matrix l l ℂ} (hG : G.PosDef)
    (hT : IsUnit T.det) (hT₀ : IsUnit T₀.det)
    (hU : Tᵀ * U = Matrix.of fun u i => Sum.elim (fun _ => (0 : ℂ)) (fun j => T₀ i j) u) :
    quotGram (chg T (dualGram G)) = chg T₀ (dualGram (chg U G)) := by
  have hTu : IsUnit T := (isUnit_iff_isUnit_det _).2 hT
  have hM : (chg T (dualGram G)).PosDef := posDef_chg hTu (posDef_dualGram hG)
  set M := chg T (dualGram G) with hMd
  have hMi : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hM.isUnit)
  have hA : IsUnit M.toBlocks₁₁.det := (posDef_subGram hM).det_pos.ne'.isUnit
  set X := M⁻¹ with hX

  have eS : quotGram M * X.toBlocks₂₂ = 1 := by
    have h := hMi
    rw [← fromBlocks_toBlocks M, ← fromBlocks_toBlocks X, fromBlocks_multiply, ← fromBlocks_one,
      fromBlocks_inj] at h
    obtain ⟨-, h12, -, h22⟩ := h
    have x12 : X.toBlocks₁₂ = -(M.toBlocks₁₁⁻¹ * M.toBlocks₁₂ * X.toBlocks₂₂) := by
      have := congrArg (M.toBlocks₁₁⁻¹ * ·) h12
      simp only [Matrix.mul_add, Matrix.mul_zero, ← Matrix.mul_assoc, nonsing_inv_mul _ hA,
        Matrix.one_mul] at this
      exact eq_neg_of_add_eq_zero_left this
    rw [quotGram, Matrix.sub_mul, ← h22, x12, Matrix.mul_neg]
    simp only [Matrix.mul_assoc]
    abel
  rw [(inv_eq_left_inv eS).symm]

  have hTt : IsUnit Tᵀ.det := by rwa [det_transpose]
  have eX : X = (Tᵀ⁻¹)ᴴ * Gᵀ * Tᵀ⁻¹ := by
    rw [hX]
    refine inv_eq_left_inv ?_
    have hG' : Gᵀ * G⁻¹ᵀ = 1 := by
      rw [← transpose_mul, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hG.isUnit), transpose_one]
    have hT' : (Tᵀ⁻¹)ᴴ * Tᴴᵀ = 1 := by
      rw [show Tᴴᵀ = Tᵀᴴ from rfl, ← conjTranspose_mul, mul_nonsing_inv _ hTt, conjTranspose_one]
    rw [hMd, chg, dualGram]
    simp only [Matrix.mul_assoc]
    rw [nonsing_inv_mul_cancel_left _ _ hTt, ← Matrix.mul_assoc Gᵀ, hG', Matrix.one_mul, hT']

  set N₂ := (Tᵀ⁻¹).submatrix id Sum.inr with hN₂
  have hT₀t : IsUnit T₀ᵀ.det := by rwa [det_transpose]
  have eU : U = N₂ * T₀ᵀ := by
    have e₁ : U = Tᵀ⁻¹ * (Tᵀ * U) := (nonsing_inv_mul_cancel_left _ _ hTt).symm
    rw [e₁, hU]
    ext w i
    simp [Matrix.mul_apply, Fintype.sum_sum_type, hN₂]
  have eN : N₂ = U * T₀ᵀ⁻¹ := by rw [eU, mul_nonsing_inv_cancel_right _ _ hT₀t]
  have eS₂ : X.toBlocks₂₂ = N₂ᴴ * Gᵀ * N₂ := by
    rw [eX]
    ext i j
    simp [toBlocks₂₂, Matrix.mul_apply, hN₂, conjTranspose_apply]
  have eC : N₂ᴴ * Gᵀ * N₂ = (chg T₀ᵀ⁻¹ (chg U G))ᵀ := by
    rw [chg_chg, ← eN, chg, transpose_mul, transpose_mul, transpose_transpose, transpose_transpose,
      Matrix.mul_assoc]
  rw [eS₂, eC, ← transpose_nonsing_inv]
  change dualGram (chg T₀ᵀ⁻¹ (chg U G)) = _
  rw [dualGram_chg (nonsing_inv_mul _ hT₀t), transpose_transpose]

theorem ev_dualApp_eq_sum {σ : k →+* ℂ} {E : X.Modules} {r : ℕ} (c : Chart E r) {V : X.Opens}
    (l : Γ(VB.dual E, V)) (s : Γ(E, V)) {y : CxPts p σ} (hy : y ∈ ptsIn p σ V)
    (hc : y ∈ ptsIn p σ c.U) :
    ev p σ V (dualApp l le_rfl s) y = ∑ j, c.dual.crd p σ l y j * c.crd p σ s y j := by
  have hW : y ∈ ptsIn p σ (V ⊓ c.U) := mem_ptsIn_inf.2 ⟨hy, hc⟩
  have e (j : Fin r) : c.dual.crd p σ l y j =
      ev p σ (V ⊓ c.U) (dualApp l inf_le_left (resM E inf_le_right (c.e j))) y :=
    (c.dual.crd_eq l inf_le_left inf_le_right hW j).trans
      (congrArg (ev p σ _ · y) (c.isFrame.dual_basis_repr _ _ j))
  simp only [e]
  rw [← ev_res (inf_le_left : V ⊓ c.U ≤ V) hW, ← dualApp_resM l le_rfl inf_le_left s]
  conv_lhs => rw [← (c.isFrame.basis (inf_le_right : V ⊓ c.U ≤ c.U)).sum_repr (resM E inf_le_left s)]
  simp only [map_sum, map_smul, smul_eq_mul, Chart.crd, IsFrame.basis_apply]
  rw [ev_eq hW]
  simp only [map_sum, map_mul, ev_eq hW]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

section Ann

variable {F E : X.Modules} (ι : F ⟶ E) [Epi (dualMap ι)]

abbrev annihSeq : ShortComplex X.Modules :=
  .mk (kernel.ι (dualMap ι)) (dualMap ι) (kernel.condition _)

theorem annihSeq_shortExact : (annihSeq ι).ShortExact :=
  { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _) }

variable {ι}

theorem quot_dual_eq {a b : ℕ} (h : VMetric p E (a + b)) (hι : IsSubbundle ι) (hF : IsVB F b)
    (hK : IsVB (kernel (dualMap ι)) a) :
    h.dual.quot (annihSeq_shortExact ι) hK hF.dual = (h.restrict hι hF).dual := by
  have hS := annihSeq_shortExact ι
  refine VMetric.ext (funext fun σ => Met.ext_of_exists fun y => ?_)
  obtain ⟨a', ha'⟩ := Met.exists_adapted (p := p) (σ := σ) hS hK hF.dual y
  refine ⟨a'.quot, ha', ?_⟩
  change ((h.met σ).dual.quot hS hK hF.dual).G a'.quot y = ((h.met σ).restrict hι hF).dual.G a'.quot y
  rw [Met.quot_G _ hS hK hF.dual a' ha']
  have hE : y ∈ ptsIn p σ (h.isVB.pick y).U := h.isVB.mem_pick y
  have hc : y ∈ ptsIn p σ (hF.pick y).U := hF.mem_pick y
  rw [((h.met σ).restrict hι hF).dual.trans (hF.pick y).dual a'.quot y hc, Met.dual_G _ _ hc,
    (h.met σ).dual.gram_frame hS a' ha', (h.met σ).dual.trans (h.isVB.pick y).dual (a'.mid hS) y hE,
    Met.dual_G _ _ hE]
  change _ = chg _ (dualGram ((h.met σ).gram (fun i => ι.app (hF.pick y).U ((hF.pick y).e i)) y))
  rw [(h.met σ).gram_eq _ hE _ hc]
  set T := Chart.tr p σ (h.isVB.pick y).dual (VBExt.AdaptedChart.mid hS a') y with hT
  set G := (h.met σ).G (h.isVB.pick y) y with hG
  set T₀ := Chart.tr p σ (hF.pick y).dual a'.quot y with hT₀
  set U := Matrix.of fun a b => (h.isVB.pick y).crd p σ (ι.app (hF.pick y).U ((hF.pick y).e b)) y a with hU
  have e₁ : (dualGram G).submatrix finSumFinEquiv finSumFinEquiv =
      dualGram (G.submatrix finSumFinEquiv finSumFinEquiv) := by
    rw [dualGram, dualGram, ← Matrix.transpose_submatrix, Matrix.inv_submatrix_equiv]
  rw [← chg_submatrix T (dualGram G) finSumFinEquiv finSumFinEquiv, e₁,
    ← Matrix.submatrix_id_id (chg U G), ← chg_submatrix U G finSumFinEquiv id]
  refine quotGram_chg_dualGram ((h.met σ).posDef _ y hE |>.submatrix finSumFinEquiv.injective) ?_ ?_ ?_
  · rw [Matrix.det_submatrix_equiv_self]
    exact (isUnit_iff_isUnit_det _).1 (Chart.isUnit_tr _ _ hE (ptsIn_mono le_rfl ha'))
  · exact (isUnit_iff_isUnit_det _).1 (Chart.isUnit_tr _ _ hc ha')
  · have hW : y ∈ ptsIn p σ (a'.U ⊓ (hF.pick y).U) := mem_ptsIn_inf.2 ⟨ha', hc⟩
    ext u i
    rw [Matrix.mul_apply]
    simp only [transpose_apply, submatrix_apply, id, of_apply]
    rw [Fintype.sum_equiv finSumFinEquiv _ (fun j => T j (finSumFinEquiv u) * U j i) (fun _ => rfl)]
    simp only [hT, hU, Chart.tr, of_apply]
    have hm : (a'.mid hS).e (finSumFinEquiv u) = a'.frame u := by
      simp [VBExt.AdaptedChart.mid]
    rw [hm]
    erw [← (h.isVB.pick y).dual.crd_resM (a'.frame u) (inf_le_left : a'.U ⊓ (hF.pick y).U ≤ a'.U) hW,
      ← (h.isVB.pick y).crd_resM _ (inf_le_right : a'.U ⊓ (hF.pick y).U ≤ (hF.pick y).U) hW,
      ← ev_dualApp_eq_sum _ _ _ hW hE]
    rw [dualApp_res, ← app_resM]
    rcases u with m | j
    · have h0 : (dualMap ι).app a'.U ((kernel.ι (dualMap ι)).app a'.U (a'.e m)) = 0 :=
        congr(($((annihSeq ι).zero)).app a'.U (a'.e m))
      change ev p σ _ (dualApp ((dualMap ι).app a'.U ((kernel.ι (dualMap ι)).app a'.U (a'.e m)))
        (inf_le_left : a'.U ⊓ (hF.pick y).U ≤ a'.U) _) y = 0
      rw [h0, dualApp_zero, LinearMap.zero_apply, ev_eq hW, map_zero]
    · change ev p σ _ (dualApp (resM (VB.dual F) (inf_le_left : a'.U ⊓ (hF.pick y).U ≤ a'.U) (a'.quot.e j))
        le_rfl (resM F inf_le_right ((hF.pick y).e i))) y = T₀ i j
      rw [ev_dualApp_eq_sum (hF.pick y) _ _ hW hc]
      erw [(hF.pick y).dual.crd_resM (a'.quot.e j) (inf_le_left : a'.U ⊓ (hF.pick y).U ≤ a'.U) hW,
        (hF.pick y).crd_resM ((hF.pick y).e i) (inf_le_right : a'.U ⊓ (hF.pick y).U ≤ (hF.pick y).U) hW, (hF.pick y).crd_frame hc]
      simp [hT₀, Chart.tr, Pi.single_apply]

theorem isometric_det_of_eq {G : X.Modules} {n : ℕ} {g g' : VMetric p G n} (hg : g.IsCInf)
    (hg' : g'.IsCInf) (e : g = g') : (VMetric.det hg).Isometric (VMetric.det hg') := by
  subst e
  exact HermLB.Isometric.refl _

theorem icls_det_restrict_annih {a b n : ℕ} (hn : a + b = n) (h : VMetric p E n) (H : h.IsCInf)
    (hι : IsSubbundle ι) (hF : IsVB F b) (hK : IsVB (kernel (dualMap ι)) a)
    (hKs : IsSubbundle (kernel.ι (dualMap ι))) :
    (VMetric.det (H.dual.restrict hKs hK)).icls =
      (VMetric.det (H.restrict hι hF)).icls - (VMetric.det H).icls := by
  subst hn
  have e₁ := VMetric.isometric_det_tens_det k X p (annihSeq ι) a b h.dual H.dual
    (annihSeq_shortExact ι) hK hF.dual hKs
  have e₂ := isometric_det_of_eq (H.dual.quot (annihSeq_shortExact ι) hK hF.dual)
    (H.restrict hι hF).dual (quot_dual_eq h hι hF hK)
  have e₃ := HermLB.icls_eq_iff.2 (isometric_dual_det (H.restrict hι hF))
  have e₄ := HermLB.icls_eq_iff.2 (isometric_dual_det H)
  have e₅ := HermLB.icls_eq_iff.2 e₁
  have e₆ := HermLB.icls_eq_iff.2 e₂
  rw [HermLB.icls_tens] at e₅
  rw [HermLB.icls_dual] at e₃ e₄
  rw [e₆, ← e₃, ← e₄] at e₅
  rw [sub_eq_add_neg, ← e₅]
  abel

end Ann

section Flag

variable {E : X.Modules} {N : ℕ} {h : VMetric p E N} (H : h.IsCInf) (fl : Vert.Flag E N)

def stepDet (j : Fin (N + 1)) : HermLB p := VMetric.det (H.restrict (fl.isSubbundle j) (fl.isVB j))

theorem icls_grLB (i : Fin N) :
    (VMetric.grLB fl i H).icls = (stepDet H fl i.succ).icls - (stepDet H fl i.castSucc).icls := by
  have H₁ : (h.stepMet fl i).IsCInf := H.restrict _ _
  have hf : IsSubbundle (VMetric.stepSeq fl i).f := ⟨inferInstance, 1, fl.isVB_gr i⟩
  have e₁ := VMetric.isometric_det_tens_det k X p (VMetric.stepSeq fl i) i 1 (h.stepMet fl i) H₁
    (VMetric.stepSeq_shortExact fl i) (fl.isVB i.castSucc) (fl.isVB_gr i) hf
  have e₀ : (VMetric.det (H₁.restrict hf (fl.isVB i.castSucc))).Isometric (stepDet H fl i.castSucc) :=
    VMetric.isometric_det_of_isIsometry k X p _ _ _ _ _ (Iso.refl _) _ _
      fun σ V s t y hy => by
        refine Eq.trans ?_ ((((h.met σ).restrict (fl.isSubbundle _) (fl.isVB _)).form_restrict hf
          (fl.isVB i.castSucc) s t hy).trans
          ((h.met σ).form_restrict (fl.isSubbundle _) _ _ _ hy)).symm
        refine ((h.met σ).form_restrict (fl.isSubbundle _) _ s t hy).trans ?_
        congr 1
        · exact congr(($(fl.step_ι i)).app V s).symm
        · exact congr(($(fl.step_ι i)).app V t).symm
  have e₂ := HermLB.icls_eq_iff.2 e₁
  rw [HermLB.icls_tens, HermLB.icls_eq_iff.2 e₀] at e₂
  change _ = (VMetric.det H₁).icls - _
  rw [← e₂]
  change _ = _ + (VMetric.grLB fl i H).icls - _
  abel

theorem icls_stepDet_dualFlag (j : Fin (N + 1)) :
    (stepDet H.dual (DualFlag.dualFlag fl) j).icls = (stepDet H fl j.rev).icls - (VMetric.det H).icls :=
  icls_det_restrict_annih (ι := fl.ι j.rev) (by rw [Fin.val_rev]; omega) h H (fl.isSubbundle j.rev)
    (fl.isVB j.rev) ((DualFlag.dualFlag fl).isVB j) ((DualFlag.dualFlag fl).isSubbundle j)

end Flag

end GlobalTheory.DualGrLine

open GlobalTheory.DualGrLine in

theorem GlobalTheory.VMetric.isometric_dual_grLB_rev : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    (E : X.Modules) (r : ℕ) (h : VMetric p E r) (H : h.IsCInf) (fl : Vert.Flag E r) (i : Fin r),
    (VMetric.grLB fl i.rev H).dual.Isometric (VMetric.grLB (GlobalTheory.DualFlag.dualFlag fl) i H.dual) := by
  intro k _ X p E r h H fl i
  refine HermLB.icls_eq_iff.1 ?_
  rw [HermLB.icls_dual, icls_grLB, icls_grLB, icls_stepDet_dualFlag H fl,
    icls_stepDet_dualFlag H fl, Fin.rev_succ, Fin.rev_castSucc]
  abel
