import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernIntegralEqDegree
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoGenResMapSmulHom

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame
open GlobalTheory.LB (resG_resG resG_self toMod)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.VBExt (AdaptedChart)
open ReciprocityTheory.L2DbarEstimates (V)
open MeasureTheory
open scoped ContDiff ComplexOrder ENNReal

namespace GlobalTheory

namespace HermFrame

variable {m l n n' : Type} [Fintype m] [Fintype l] [Fintype n] [Fintype n'] [DecidableEq m]
  [DecidableEq l]

omit [Fintype n'] in

theorem chg_submatrix {m' : Type} [Fintype m'] (A : Matrix n n' ℂ) (H : Matrix n n ℂ) (e : m' ≃ n)
    {l' : Type} (f : l' → n') :
    chg (A.submatrix e f) (H.submatrix e e) = (chg A H).submatrix f f := by
  ext a b
  simp only [chg, mul_apply, submatrix_apply, transpose_apply, conjTranspose_apply]
  rw [← e.sum_comp]
  exact Finset.sum_congr rfl fun j _ => by rw [← e.sum_comp]

variable (A₁ : Matrix m m ℂ) (B : Matrix m l ℂ) (A₂ : Matrix l l ℂ) (H : Matrix (m ⊕ l) (m ⊕ l) ℂ)

omit [DecidableEq m] [DecidableEq l] in

theorem chg_fromBlocks : chg (fromBlocks A₁ B 0 A₂) H = fromBlocks (chg A₁ H.toBlocks₁₁)
    (A₁ᵀ * (H.toBlocks₁₁ * Bᴴᵀ + H.toBlocks₁₂ * A₂ᴴᵀ)) ((Bᵀ * H.toBlocks₁₁ + A₂ᵀ * H.toBlocks₂₁) * A₁ᴴᵀ)
    ((Bᵀ * H.toBlocks₁₁ + A₂ᵀ * H.toBlocks₂₁) * Bᴴᵀ + (Bᵀ * H.toBlocks₁₂ + A₂ᵀ * H.toBlocks₂₂) * A₂ᴴᵀ) := by
  conv_lhs => rw [← fromBlocks_toBlocks H]
  simp [chg, fromBlocks_transpose, fromBlocks_conjTranspose, fromBlocks_multiply, Matrix.mul_add,
    Matrix.mul_assoc]

omit [DecidableEq m] [DecidableEq l] in

theorem subGram_chg : subGram (chg (fromBlocks A₁ B 0 A₂) H) = chg A₁ (subGram H) := by
  rw [chg_fromBlocks]; rfl

omit [DecidableEq l] in
variable {A₁ H} in

theorem quotGram_chg (hA : IsUnit A₁.det) (hH : IsUnit (subGram H).det) :
    quotGram (chg (fromBlocks A₁ B 0 A₂) H) = chg A₂ (quotGram H) := by
  have h₁ : IsUnit A₁ᵀ.det := by rwa [det_transpose]
  have h₂ : IsUnit A₁ᴴᵀ.det := by rw [det_transpose, det_conjTranspose]; exact hA.star
  have h₃ : IsUnit H.toBlocks₁₁.det := hH
  rw [chg_fromBlocks]
  simp only [quotGram, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂, chg, Matrix.mul_inv_rev, Matrix.mul_assoc,
    mul_nonsing_inv_cancel_left _ _ h₂, nonsing_inv_mul_cancel_left _ _ h₁, Matrix.mul_add,
    Matrix.add_mul, nonsing_inv_mul_cancel_left _ _ h₃, mul_nonsing_inv_cancel_left _ _ h₃,
    Matrix.mul_sub, Matrix.sub_mul]
  abel

open scoped MatrixOrder in

theorem trace_mul_adj_nonneg {S : Matrix m m ℂ} {Q : Matrix l l ℂ} (hS : S.PosDef) (hQ : Q.PosDef)
    (b : Matrix l m ℂ) : 0 ≤ (b * adj S Q b).trace := by
  obtain ⟨R, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hQ.transpose.posSemidef.nonneg
    |>.imp fun R (h : Qᵀ = star R * R) => (transpose_transpose Q).symm.trans (congrArg transpose h)
  have := (hS.transpose.inv.posSemidef.mul_mul_conjTranspose_same (R * b)).trace_nonneg
  rw [adj, transpose_transpose, ← Matrix.mul_assoc, ← Matrix.mul_assoc, trace_mul_comm]
  simpa only [conjTranspose_mul, Matrix.mul_assoc, star_eq_conjTranspose] using this

theorem trace_mul_adj_chg {A₁ : Matrix m m ℂ} {A₂ : Matrix l l ℂ} (h₁ : IsUnit A₁.det)
    (h₂ : IsUnit A₂.det) (S : Matrix m m ℂ) (Q : Matrix l l ℂ) (b b' : Matrix l m ℂ) :
    (A₂⁻¹ * b * A₁ * adj (chg A₁ S) (chg A₂ Q) (A₂⁻¹ * b' * A₁)).trace = (b * adj S Q b').trace := by
  have h₃ : IsUnit A₁ᴴ.det := by rw [det_conjTranspose]; exact h₁.star
  have h₄ : IsUnit A₂ᴴ.det := by rw [det_conjTranspose]; exact h₂.star
  simp only [adj, chg, transpose_mul, transpose_transpose, Matrix.mul_inv_rev, conjTranspose_mul,
    conjTranspose_nonsing_inv, Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ h₁,
    nonsing_inv_mul_cancel_left _ _ h₃, nonsing_inv_mul_cancel_left _ _ h₄]
  rw [trace_mul_comm]
  simp only [Matrix.mul_assoc, mul_nonsing_inv _ h₂, Matrix.mul_one]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {K : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E}

theorem extTrace_eq (h : MContDiffAt 1 K z) (hp : ∀ᶠ x in 𝓝 z, (K x).PosDef) (ξ η : E) :
    extTrace K z ξ η = kappa * (secondForm K z ξ * secondFormAdj K z η).trace := by
  have hh := hp.mono fun x hx => hx.isHermitian
  have hu := hp.self_of_nhds.det_pos.ne'.isUnit
  have hs := (posDef_subGram hp.self_of_nhds).det_pos.ne'.isUnit
  rw [extTrace, extFormAdj_eq_neg_secondForm h hh hu hs, extForm_eq_neg_secondFormAdj h hh hu hs,
    Matrix.neg_mul, Matrix.mul_neg, neg_neg]

theorem diagVal_extTrace_nonneg (h : MContDiffAt 1 K z) (hp : ∀ᶠ x in 𝓝 z, (K x).PosDef) (ξ : E) :
    0 ≤ diagVal (extTrace K z) ξ := by
  have := trace_mul_adj_nonneg (posDef_subGram hp.self_of_nhds) (posDef_quotGram hp.self_of_nhds)
    (secondForm K z ξ)
  have e : -Complex.I * kappa = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
    rw [kappa, ← mul_div_assoc, neg_mul, Complex.I_mul_I]; simp
  rw [diagVal, extTrace_eq h hp, ← mul_assoc, e, Complex.re_ofReal_mul]
  exact mul_nonneg (by positivity) (Complex.nonneg_iff.1 this).1

theorem extTrace_congr {K' : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} (h : K =ᶠ[𝓝 z] K') :
    extTrace K z = extTrace K' z := by
  have e (η : E) : extForm K z η = extForm K' z η := by
    rw [extForm, extForm, h.eq_of_nhds, mdbar_congr (A := fun x => orthLift (K x)) (B := fun x => orthLift (K' x))
      (h.fun_comp orthLift)]
  funext ξ η
  simp only [extTrace, extFormAdj, e, h.eq_of_nhds]

theorem extTrace_chg {A : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} (h : MContDiffAt 1 K z)
    (hp : ∀ᶠ x in 𝓝 z, (K x).PosDef) (hA : MContDiffAt 1 A z) (hu : IsUnit (A z).det)
    (hA0 : ∀ η, mdbar A z η = 0) (ht : ∀ᶠ x in 𝓝 z, (A x).toBlocks₂₁ = 0) :
    extTrace (fun x => chg (A x) (K x)) z = extTrace K z := by
  have eA : A z = fromBlocks (A z).toBlocks₁₁ (A z).toBlocks₁₂ 0 (A z).toBlocks₂₂ := by
    rw [← ht.self_of_nhds, fromBlocks_toBlocks]
  have hd := hu
  rw [eA, det_fromBlocks_zero₂₁, IsUnit.mul_iff] at hd
  have hK := hp.self_of_nhds
  have hb (ξ : E) : secondForm (fun x => chg (A x) (K x)) z ξ =
      (A z).toBlocks₂₂⁻¹ * secondForm K z ξ * (A z).toBlocks₁₁ := by
    have e := congrArg (A z * ·) (conn_changeFrame h hK.det_pos.ne'.isUnit hA hu hA0 ξ)
    simp only [mul_nonsing_inv_cancel_left _ _ hu] at e
    have e₀ : (mdel A z ξ).toBlocks₂₁ = 0 := by
      rw [← mdel_const (0 : Matrix l m ℂ) z ξ, ← mdel_congr ht]; rfl
    have e₁ := congrArg toBlocks₂₁ e
    rw [← fromBlocks_toBlocks (conn _ z ξ), ← fromBlocks_toBlocks (conn K z ξ),
      ← fromBlocks_toBlocks (mdel A z ξ), e₀, eA] at e₁
    simp only [fromBlocks_multiply, fromBlocks_add, toBlocks_fromBlocks₂₁, Matrix.zero_mul,
      Matrix.mul_zero, zero_add, add_zero] at e₁
    rw [secondForm_eq, secondForm_eq, Matrix.mul_assoc, ← e₁, nonsing_inv_mul_cancel_left _ _ hd.2]
    rfl
  have hp' : ∀ᶠ x in 𝓝 z, (chg (A x) (K x)).PosDef := by
    filter_upwards [hp, hA.eventually_isUnit hu] with x h₁ h₂
    exact posDef_chg ((isUnit_iff_isUnit_det _).2 h₂) h₁
  funext ξ η
  rw [extTrace_eq (K := fun x => chg (A x) (K x))
    ((hA.transpose.mul h).mul hA.conjTranspose.transpose) hp', extTrace_eq h hp,
    secondFormAdj, secondFormAdj, hb, hb, ← trace_mul_adj_chg hd.1 hd.2 (subGram (K z)),
    ← subGram_chg _ (A z).toBlocks₁₂ (A z).toBlocks₂₂,
    ← quotGram_chg (A z).toBlocks₁₂ _ hd.1 (posDef_subGram hK).det_pos.ne'.isUnit, ← eA]

theorem extTrace_comp_holo {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [NormedSpace ℝ E']
    [IsScalarTower ℝ ℂ E'] {φ : E' → E} {w : E'} (h : MContDiffAt 1 K (φ w))
    (hp : ∀ᶠ x in 𝓝 (φ w), (K x).PosDef) (hφ : ContDiffAt ℂ 1 φ w) (ξ η : E') :
    extTrace (fun x => K (φ x)) w ξ η = extTrace K (φ w) (fderiv ℂ φ w ξ) (fderiv ℂ φ w η) := by
  have hd := hφ.differentiableAt one_ne_zero
  rw [extTrace_eq (K := fun x => K (φ x)) (fun a b => (h a b).comp w (hφ.restrict_scalars ℝ))
    (hφ.continuousAt.eventually hp), extTrace_eq h hp]
  simp only [secondFormAdj, secondForm, conn_comp_holo h hd]

theorem diagVal_extTrace_smul (h : MContDiffAt 1 K z) (hp : ∀ᶠ x in 𝓝 z, (K x).PosDef) (c : ℂ)
    (ξ : E) : diagVal (extTrace K z) (c • ξ) = ‖c‖ ^ 2 * diagVal (extTrace K z) ξ := by
  have e : secondForm K z (c • ξ) = c • secondForm K z ξ := by
    rw [secondForm_eq, secondForm_eq, conn_smul_vec]; rfl
  rw [diagVal, diagVal, extTrace_eq h hp, extTrace_eq h hp, ← Complex.re_ofReal_mul]
  congr 1
  simp only [secondFormAdj, adj, e, conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul,
    trace_smul, smul_eq_mul, Complex.star_def, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_conj_mul_self]
  ring

end HermFrame

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ σ' : k →+* ℂ}

namespace VB.Chart

variable {E F : X.Modules} {r s : ℕ} (c₀ : Chart E r) (c : Chart F s) {U : X.Opens}
  {y : CxPts p σ}

theorem crd_app (φ : F ⟶ E) (t : Γ(F, U)) (hy : y ∈ ptsIn p σ U) (h : y ∈ ptsIn p σ c.U) :
    c₀.crd p σ (φ.app U t) y =
      (Matrix.of fun a b => c₀.crd p σ (φ.app c.U (c.e b)) y a) *ᵥ c.crd p σ t y := by
  have hW := mem_ptsIn_inf.2 ⟨hy, h⟩
  rw [← c₀.crd_resM _ inf_le_left hW, ← app_resM,
    ← (c.isFrame.basis inf_le_right).sum_repr (resM F _ t), map_sum, crd_sum]
  funext a
  simp only [Scheme.Modules.Hom.app_smul, crd_smul, IsFrame.basis_apply, app_resM,
    c₀.crd_resM _ _ hW, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, of_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem crd_of_notMem (t : Γ(E, U)) (hy : y ∉ ptsIn p σ U) : c₀.crd p σ t y = 0 :=
  funext fun _ => ev_of_notMem (fun h => hy (mem_ptsIn_inf.1 h).1) _

end VB.Chart

namespace Met

variable {E F : X.Modules} {r s : ℕ} (h : Met p σ E r) {U : X.Opens} {y : CxPts p σ} {ι : Type}

def gram (t : ι → Γ(E, U)) (y : CxPts p σ) : Matrix ι ι ℂ := Matrix.of fun a b => h.form (t a) (t b) y

theorem gram_eq [Fintype ι] (c : Chart E r) (hc : y ∈ ptsIn p σ c.U) (t : ι → Γ(E, U))
    (hy : y ∈ ptsIn p σ U) :
    h.gram t y = chg (Matrix.of fun a b => c.crd p σ (t b) y a) (h.G c y) := by
  ext a b
  rw [chg_apply, gram, of_apply, h.form_eq c hc _ _ hy]
  rfl

theorem gram_app_trans (φ : F ⟶ E) (c c' : Chart F s) (hc : y ∈ ptsIn p σ c.U) :
    h.gram (fun a => φ.app c'.U (c'.e a)) y =
      chg (c.tr p σ c' y) (h.gram (fun a => φ.app c.U (c.e a)) y) := by
  by_cases hc' : y ∈ ptsIn p σ c'.U
  · have h₀ := h.isVB.mem_pick y
    rw [h.gram_eq _ h₀ _ hc, h.gram_eq _ h₀ _ hc', chg_chg]
    congr 1
    ext a b
    exact congrFun (Chart.crd_app _ c φ (c'.e b) hc' hc) a
  · rw [Chart.tr_of_notMem _ _ hc', chg_zero]
    ext a b
    simp [gram, form, Chart.crd_of_notMem _ _ hc', HermFrame.form]

theorem IsCInf.gram {h : Met p σ E r} (H : h.IsCInf) [Fintype ι] (t : ι → Γ(E, U))
    (hy : y ∈ ptsIn p σ U) : MInfAt (h.gram t) y := by
  have h₀ := h.isVB.mem_pick y
  refine (MInfAt.chg (A := fun z => Matrix.of fun a b => (h.isVB.pick y).crd p σ (t b) z a)
    (fun a b => Chart.vInfAt_crd _ _ hy h₀ a) (H _ y h₀)).congr ?_
  filter_upwards [(isOpen_ptsIn _).mem_nhds h₀, (isOpen_ptsIn _).mem_nhds hy] with z h₁ h₂
  exact h.gram_eq _ h₁ t h₂

theorem IsConj.gram {h : Met p σ E r} {h' : Met p σ' E r} (H : h.IsConj h') (t : ι → Γ(E, U))
    {y' : CxPts p σ'} (e : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) (hy : y ∈ ptsIn p σ U) :
    h'.gram t y' = (h.gram t y).map star := by
  ext a b
  exact H.form_eq _ _ e hy

end Met

namespace VBExt.AdaptedChart

variable {S : ShortComplex X.Modules} {r s : ℕ} (hS : S.ShortExact) (a a' : AdaptedChart S r s)
  {U : X.Opens} {y : CxPts p σ}

def sub : Chart S.X₁ r := ⟨a.U, a.e, a.he⟩

def quot : Chart S.X₃ s := ⟨a.U, _, a.ht⟩

def frame : Fin r ⊕ Fin s → Γ(S.X₂, a.U) := Sum.elim (fun i => S.f.app a.U (a.e i)) a.t

def mid : Chart S.X₂ (r + s) :=
  ⟨a.U, a.frame ∘ finSumFinEquiv.symm,
    (isFrame_sumElim hS a.he a.ht).comp_equiv finSumFinEquiv.symm⟩

theorem crd_frame (hy : y ∈ ptsIn p σ a.U) (i j : Fin r ⊕ Fin s) :
    (a.mid hS).crd p σ (a.frame j) y (finSumFinEquiv i) = (1 : Matrix _ _ ℂ) i j := by
  have := congrFun ((a.mid hS).crd_frame hy (finSumFinEquiv j)) (finSumFinEquiv i)
  simpa [mid, Pi.single_apply, one_apply] using this

variable (p σ) in

def tr (y : CxPts p σ) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ :=
  ((a.mid hS).tr p σ (a'.mid hS) y).submatrix finSumFinEquiv finSumFinEquiv

theorem tr_apply (i j : Fin r ⊕ Fin s) :
    a.tr p σ hS a' y i j = (a.mid hS).crd p σ (a'.frame j) y (finSumFinEquiv i) := by
  simp [tr, Chart.tr, mid]

theorem tr_eq (hy : y ∈ ptsIn p σ a.U) (hy' : y ∈ ptsIn p σ a'.U) :
    a.tr p σ hS a' y = fromBlocks (a.sub.tr p σ a'.sub y) (a.tr p σ hS a' y).toBlocks₁₂ 0
      (a.quot.tr p σ a'.quot y) := by
  have h₁ (i) (j : Fin r) : a.tr p σ hS a' y i (.inl j) =
      Sum.elim (fun i => a.sub.tr p σ a'.sub y i j) 0 i := by
    rw [tr_apply]
    refine (congrFun ((a.mid hS).crd_app a.sub S.f (a'.e j) hy' hy) _).trans ?_
    have e (b : Fin r) := a.crd_frame hS hy i (.inl b)
    simp only [mulVec, dotProduct, of_apply]
    refine (Finset.sum_congr rfl fun b _ => congrArg (· * _) (e b)).trans ?_
    rcases i with i | i <;> simp [one_apply, Chart.tr, sub]
  have h₂ (i j : Fin s) : a.tr p σ hS a' y (.inr i) (.inr j) = a.quot.tr p σ a'.quot y i j := by
    rw [tr_apply]
    refine Eq.symm ((congrFun (a.quot.crd_app (a.mid hS) S.g (a'.t j) hy' hy) _).trans ?_)
    have e₁ (b : Fin r) : a.quot.crd p σ (S.g.app a.U (a.frame (.inl b))) y = 0 := by
      rw [show S.g.app a.U (a.frame (.inl b)) = 0 from congr(($(S.zero)).app a.U (a.e b)),
        Chart.crd_zero]
    have e₂ (b : Fin s) : a.quot.crd p σ (S.g.app a.U (a.frame (.inr b))) y = Pi.single b 1 :=
      a.quot.crd_frame hy b
    simp only [mulVec, dotProduct, of_apply]
    have e₃ (b) : (a.mid hS).e (finSumFinEquiv b) = a.frame b := by simp [mid]
    rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
    refine (congrArg₂ (· + ·) (Finset.sum_eq_zero fun b _ => ?_)
      (Finset.sum_congr rfl fun b _ => congrArg (· * _) (congrFun
        ((congrArg (fun t => a.quot.crd p σ (S.g.app a.U t) y) (e₃ _)).trans (e₂ b)) i))).trans ?_
    · exact mul_eq_zero_of_left (congrFun
        ((congrArg (fun t => a.quot.crd p σ (S.g.app a.U t) y) (e₃ _)).trans (e₁ b)) i) _
    · simp [Pi.single_apply, frame]
  ext (i | i) (j | j)
  exacts [h₁ _ j, rfl, h₁ _ j, h₂ i j]

end VBExt.AdaptedChart

namespace Met

variable {S : ShortComplex X.Modules} {r s : ℕ} (h : Met p σ S.X₂ (r + s)) (hS : S.ShortExact)
  (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) {y : CxPts p σ} (a a' : AdaptedChart S r s)

include hS in

theorem gram_frame (hy : y ∈ ptsIn p σ a.U) :
    h.gram a.frame y = (h.G (a.mid hS) y).submatrix finSumFinEquiv finSumFinEquiv := by
  ext i j
  rw [submatrix_apply, ← h.form_frame _ hy]
  simp [gram, AdaptedChart.mid]

include hS in

theorem posDef_gram_frame (hy : y ∈ ptsIn p σ a.U) : (h.gram a.frame y).PosDef := by
  rw [h.gram_frame hS a hy]
  exact (h.posDef _ y hy).submatrix finSumFinEquiv.injective

theorem gram_frame_trans (hy : y ∈ ptsIn p σ a.U) (hy' : y ∈ ptsIn p σ a'.U) :
    h.gram a'.frame y = chg (a.tr p σ hS a' y) (h.gram a.frame y) := by
  rw [h.gram_frame hS a hy, h.gram_frame hS a' hy', AdaptedChart.tr, chg_submatrix,
    ← h.trans _ _ y hy]

include hS h₁ h₃ in

theorem exists_adapted (y : CxPts p σ) : ∃ a : AdaptedChart S r s, y ∈ ptsIn p σ a.U :=
  (VBExt.exists_adaptedChart hS h₁ h₃ _).imp fun _ => mem_ptsIn.2

def quot : Met p σ S.X₃ s :=
  ofCover h₃ AdaptedChart.quot (exists_adapted hS h₁ h₃) (fun a y => quotGram (h.gram a.frame y))
    fun a _ hy => posDef_quotGram (h.posDef_gram_frame hS a hy)

theorem quot_G (hy : y ∈ ptsIn p σ a.U) :
    (h.quot hS h₁ h₃).G a.quot y = quotGram (h.gram a.frame y) :=
  ofCover_G (c := AdaptedChart.quot) (fun a a' y hy hy' => by
    rw [h.gram_frame_trans hS a a' hy hy', a.tr_eq hS a' hy hy', quotGram_chg _ _
      ((isUnit_iff_isUnit_det _).1 (a.sub.isUnit_tr a'.sub hy hy'))
      (posDef_subGram (h.posDef_gram_frame hS a hy)).det_pos.ne'.isUnit]) hy

variable {h}

theorem IsCInf.quot (H : h.IsCInf) : (h.quot hS h₁ h₃).IsCInf := isCInf_of_exists fun y => by
  obtain ⟨a, hy⟩ := exists_adapted hS h₁ h₃ y
  refine ⟨a.quot, hy, MInfAt.congr (A := fun z => quotGram (h.gram a.frame z)) (fun i j => ?_) ?_⟩
  · exact (H.gram a.frame hy).comp (Ψ := fun M => quotGram (of M) i j)
      (T := {M | IsUnit (subGram (of M)).det}) (isOpen_iff_mem_nhds.2 fun M hM =>
        (mContDiffAt_id M).subGram.eventually_isUnit hM)
      (posDef_subGram (h.posDef_gram_frame hS a hy)).det_pos.ne'.isUnit
      fun M hM => (mContDiffAt_id M).quotGram hM i j
  · filter_upwards [(isOpen_ptsIn _).mem_nhds hy] with z hz using h.quot_G hS h₁ h₃ a hz

theorem IsConj.quot {h' : Met p σ' S.X₂ (r + s)} (H : h.IsConj h') :
    (h.quot hS h₁ h₃).IsConj (h'.quot hS h₁ h₃) := isConj_of_exists fun y y' e => by
  obtain ⟨a, hy⟩ := exists_adapted hS h₁ h₃ y
  refine ⟨a.quot, hy, ?_⟩
  rw [h.quot_G hS h₁ h₃ a hy, h'.quot_G hS h₁ h₃ a ((mem_ptsIn_iff_of_conj e).2 hy), H.gram _ e hy]
  generalize h.gram a.frame y = M
  have e₁ : (M.map star).toBlocks₁₁⁻¹ = M.toBlocks₁₁⁻¹.map star :=
    congrArg transpose (dualGram_map_star M.toBlocks₁₁)
  rw [quotGram, quotGram, e₁]
  ext i j
  simp [mul_apply, toBlocks₂₁, toBlocks₁₂, toBlocks₂₂]

end Met

namespace Met

variable {E F : X.Modules} {r s : ℕ} (h : Met p σ E r) {i : F ⟶ E}

def restrict (hi : IsSubbundle i) (hF : IsVB F s) : Met p σ F s where
  isVB := hF
  G c := h.gram fun a => i.app c.U (c.e a)
  posDef c y hy := by
    obtain ⟨_, t, ht⟩ := hi
    have hS : (ShortComplex.mk i _ (Limits.cokernel.condition i)).ShortExact :=
      { exact := ShortComplex.exact_cokernel i }
    obtain ⟨hE, -⟩ := VBExt.isVB_and_cls_det_of_shortExact X _ s t hS hF ht
    have : Nonempty X := ⟨y.1 (IsLocalRing.closedPoint ℂ)⟩
    obtain rfl := hE.rank_unique h.isVB
    obtain ⟨a, ha⟩ := exists_adapted hS hF ht y
    rw [h.gram_app_trans i a.sub c ha]
    exact posDef_chg (a.sub.isUnit_tr c ha hy)
      (posDef_subGram (posDef_gram_frame (S := .mk i _ _) h hS a ha))
  trans c c' y hy := h.gram_app_trans i c c' hy

theorem form_restrict (hi : IsSubbundle i) (hF : IsVB F s) {U : X.Opens} (t t' : Γ(F, U))
    {y : CxPts p σ} (hy : y ∈ ptsIn p σ U) :
    (h.restrict hi hF).form t t' y = h.form (i.app U t) (i.app U t') y := by
  have h₀ := h.isVB.mem_pick y
  have h₁ := hF.mem_pick y
  rw [(h.restrict hi hF).form_eq _ h₁ _ _ hy, h.form_eq _ h₀ _ _ hy, Chart.crd_app _ _ i t hy h₁,
    Chart.crd_app _ _ i t' hy h₁, ← form_chg, ← h.gram_eq _ h₀ _ h₁]
  rfl

variable {h}

theorem IsCInf.restrict (H : h.IsCInf) (hi : IsSubbundle i) (hF : IsVB F s) :
    (h.restrict hi hF).IsCInf := fun _ _ hy => H.gram _ hy

theorem IsConj.restrict {h' : Met p σ' E r} (H : h.IsConj h') (hi : IsSubbundle i) (hF : IsVB F s) :
    (h.restrict hi hF).IsConj (h'.restrict hi hF) := isConj_of_exists fun y _ e =>
  ⟨_, hF.mem_pick y, H.gram _ e (hF.mem_pick y)⟩

end Met

namespace Met

variable {S : ShortComplex X.Modules} {r s : ℕ} (h : Met p σ S.X₂ (r + s)) (hS : S.ShortExact)
  (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) {y : CxPts p σ} (a a' : AdaptedChart S r s)
  {D : ℕ} (c c' : AlgChart p σ D)

def bcForm (y : CxPts p σ) : V D → V D → ℂ :=
  extTrace (fun v => h.gram a.frame (c.e.symm v)) (c.e y)

include hS in

theorem eventually_posDef (hy : y ∈ c.e.source) (ha : y ∈ ptsIn p σ a.U) :
    ∀ᶠ v in 𝓝 (c.e y), (h.gram a.frame (c.e.symm v)).PosDef :=
  eventually_of_mem ((ChartGlue.isOpen_over c.e (isOpen_ptsIn a.U)).mem_nhds
    (ChartGlue.mem_over c.e hy ha)) fun _ hv => h.posDef_gram_frame hS a hv.2

variable {h}

include hS in

theorem bcForm_eq (H : h.IsCInf) (hy : y ∈ c.e.source) (ha : y ∈ ptsIn p σ a.U)
    (ha' : y ∈ ptsIn p σ a'.U) : h.bcForm a' c y = h.bcForm a c y := by
  have hm := (ChartGlue.isOpen_over c.e (isOpen_ptsIn (a.U ⊓ a'.U))).mem_nhds
    (ChartGlue.mem_over c.e hy (mem_ptsIn_inf.2 ⟨ha, ha'⟩))
  have hA : MInfAt (a.tr p σ hS a') y := fun i j => (a.mid hS).vInfAt_crd _ ha' ha _
  rw [bcForm, extTrace_congr (K' := fun v => chg (a.tr p σ hS a' (c.e.symm v))
    (h.gram a.frame (c.e.symm v))) (eventually_of_mem hm fun v hv =>
      h.gram_frame_trans hS a a' (mem_ptsIn_inf.1 hv.2).1 (mem_ptsIn_inf.1 hv.2).2)]
  refine extTrace_chg (((H.gram _ ha).mContDiffAt c hy).of_le (by norm_cast))
    (h.eventually_posDef hS a c hy ha) ((hA.mContDiffAt c hy).of_le (by norm_cast)) ?_
    (fun η => Matrix.ext fun i j => ?_) (eventually_of_mem hm fun v hv => ?_)
  · rw [c.e.left_inv hy, AdaptedChart.tr, det_submatrix_equiv_self]
    exact (isUnit_iff_isUnit_det _).1 ((a.mid hS).isUnit_tr _ ha ha')
  · exact congr($(dbar_eq_zero (c.differentiableAt_ev _ hy (mem_ptsIn_inf.2 ⟨ha', ha⟩))) η)
  · rw [a.tr_eq hS a' (mem_ptsIn_inf.1 hv.2).1 (mem_ptsIn_inf.1 hv.2).2, toBlocks_fromBlocks₂₁]

variable (h) (c c' : AlgChart p σ 1)

def bcDens (y : CxPts p σ) : ℝ :=
  2 * diagVal (h.bcForm (exists_adapted hS h₁ h₃ y).choose c y) (EuclideanSpace.single 0 1)

def bcMeas : Measure (CxPts p σ) :=
  ChartGlue.glueMeas (fun c : AlgChart p σ 1 => c.e) fun c y => ENNReal.ofReal (h.bcDens hS h₁ h₃ c y)

variable {h}

theorem bcDens_eq (H : h.IsCInf) (hy : y ∈ c.e.source) (ha : y ∈ ptsIn p σ a.U) :
    h.bcDens hS h₁ h₃ c y = 2 * diagVal (h.bcForm a c y) (EuclideanSpace.single 0 1) := by
  rw [bcDens, bcForm_eq hS a _ c H hy ha (exists_adapted hS h₁ h₃ y).choose_spec]

theorem bcDens_nonneg (H : h.IsCInf) (hy : y ∈ c.e.source) : 0 ≤ h.bcDens hS h₁ h₃ c y :=
  have ha := (exists_adapted hS h₁ h₃ y).choose_spec
  mul_nonneg zero_le_two (diagVal_extTrace_nonneg
    (((H.gram _ ha).mContDiffAt c hy).of_le (by norm_cast)) (h.eventually_posDef hS _ c hy ha) _)

theorem bcDens_trans (H : h.IsCInf) (hy : y ∈ c.e.source) (hy' : y ∈ c'.e.source) :
    h.bcDens hS h₁ h₃ c y = ‖ChartGlue.transDet c.e c'.e y‖ ^ 2 * h.bcDens hS h₁ h₃ c' y := by
  obtain ⟨a, ha⟩ := exists_adapted hS h₁ h₃ y
  have ho := ChartGlue.isOpen_over c.e c'.e.open_source
  have hm := ho.mem_nhds (ChartGlue.mem_over c.e hy hy')
  have e₂ : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := congrArg c'.e (c.e.left_inv hy)
  have hd := ((H.gram a.frame ha).mContDiffAt c' hy').of_le (j := 1) (by norm_cast)
  have hp := h.eventually_posDef hS _ c' hy' ha
  have hl (L : V 1 →L[ℂ] V 1) :
      L (EuclideanSpace.single 0 1) = L.det • EuclideanSpace.single 0 1 := by
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 1) ℂ).toBasis,
      det_unique]
    ext i
    simp [LinearMap.toMatrix_apply, Subsingleton.elim i 0]
  rw [bcDens_eq hS h₁ h₃ a c H hy ha, bcDens_eq hS h₁ h₃ a c' H hy' ha, bcForm, bcForm,
    extTrace_congr (K' := fun v => h.gram a.frame (c'.e.symm ((c'.e ∘ c.e.symm) v))) (eventually_of_mem hm fun v hv => by
      simp only [Function.comp_apply, c'.e.left_inv hv.2]), ChartGlue.transDet, mul_left_comm,
    ← diagVal_extTrace_smul hd hp, ← hl, diagVal, diagVal,
    extTrace_comp_holo (K := fun v => h.gram a.frame (c'.e.symm v)) (e₂ ▸ hd) (e₂ ▸ hp)
      (contDiffAt_euclidean.2 fun i => ((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn 1 _ _ ho
        (differentiableOn_euclidean.1 (c.holo_trans c') i)).contDiffAt hm).of_le (by norm_cast)), e₂]

theorem bcMeas_apply [SecondCountableTopology (CxPts p σ)] (H : h.IsCInf) {T : Set (CxPts p σ)}
    (hT : MeasurableSet T) (hc : T ⊆ c.e.source) : h.bcMeas hS h₁ h₃ T =
      ∫⁻ v in c.e '' T, ENNReal.ofReal (h.bcDens hS h₁ h₃ c (c.e.symm v)) := by
  rw [bcMeas, ChartGlue.glueMeas_apply _ _ (fun c c' => c.holo_trans c') (fun c c' y hy hy' => by
    rw [bcDens_trans hS h₁ h₃ c c' H hy hy', ENNReal.ofReal_mul (sq_nonneg _)]) c hT hc,
    ChartGlue.chartMeas_apply_of_subset _ _ hT hc]

theorem bcMeas_eq_zero (H : ∀ (c : AlgChart p σ 1), ∀ y ∈ c.e.source, h.bcDens hS h₁ h₃ c y = 0) :
    h.bcMeas hS h₁ h₃ = 0 := by
  refine le_antisymm (iSup_le fun c => le_of_eq (Measure.measure_univ_eq_zero.1 ?_)) bot_le
  rw [ChartGlue.chartMeas_apply _ _ MeasurableSet.univ, inter_univ, c.e.image_source_eq_target]
  refine setLIntegral_eq_zero c.e.open_target.measurableSet fun v hv => ?_
  simp [H c _ (c.e.map_target hv)]

theorem bcMeas_rank_zero {h : Met p σ S.X₂ (0 + s)} (h₁ : IsVB S.X₁ 0) : h.bcMeas hS h₁ h₃ = 0 :=
  bcMeas_eq_zero hS h₁ h₃ fun c y _ => by
    simp [bcDens, bcForm, diagVal, extTrace, Matrix.mul_apply, trace]

end Met

namespace VMetric

section Seq

variable {S : ShortComplex X.Modules} {r s : ℕ} (h : VMetric p S.X₂ (r + s)) (hS : S.ShortExact)
  (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s)

def quot : VMetric p S.X₃ s :=
  ⟨h₃, fun σ => (h.met σ).quot hS h₁ h₃, fun σ σ' => (h.conj σ σ').quot hS h₁ h₃⟩

def BcFinite : Prop := ∀ σ, (h.met σ).bcMeas hS h₁ h₃ univ ≠ ⊤

def bcInt : ℝ := ∑ᶠ σ, ((h.met σ).bcMeas hS h₁ h₃ univ).toReal

variable {h} in

theorem IsCInf.quot (H : h.IsCInf) : (h.quot hS h₁ h₃).IsCInf := fun σ => (H σ).quot hS h₁ h₃

end Seq

variable {E F : X.Modules} {r s : ℕ} (h : VMetric p E r)

def restrict {i : F ⟶ E} (hi : IsSubbundle i) (hF : IsVB F s) : VMetric p F s :=
  ⟨hF, fun σ => (h.met σ).restrict hi hF, fun σ σ' => (h.conj σ σ').restrict hi hF⟩

variable {h} in

theorem IsCInf.restrict (H : h.IsCInf) {i : F ⟶ E} (hi : IsSubbundle i) (hF : IsVB F s) :
    (h.restrict hi hF).IsCInf := fun σ => (H σ).restrict hi hF

variable (fl : Vert.Flag E r) (i : Fin r)

abbrev stepSeq : ShortComplex X.Modules := .mk (fl.step i) (fl.π i) (Limits.cokernel.condition _)

theorem stepSeq_shortExact : (stepSeq fl i).ShortExact :=
  { exact := ShortComplex.exact_cokernel _ }

def stepMet : VMetric p (stepSeq fl i).X₂ (i + 1) :=
  h.restrict (fl.isSubbundle i.succ) (fl.isVB i.succ)

def grMet : VMetric p (fl.gr i) 1 :=
  (h.stepMet fl i).quot (stepSeq_shortExact fl i) (fl.isVB i.castSucc) (fl.isVB_gr i)

def FlagBcFinite : Prop :=
  ∀ i, (h.stepMet fl i).BcFinite (stepSeq_shortExact fl i) (fl.isVB i.castSucc) (fl.isVB_gr i)

def flagBc : ℝ :=
  ∑ i, (h.stepMet fl i).bcInt (stepSeq_shortExact fl i) (fl.isVB i.castSucc) (fl.isVB_gr i)

variable {h}

theorem IsCInf.grMet (H : h.IsCInf) : (h.grMet fl i).IsCInf :=
  IsCInf.quot (h := h.stepMet fl i) _ _ _ (H.restrict _ _)

def grLB (H : h.IsCInf) : HermLB p := det (H.grMet fl i)

theorem flagBc_rank_one (h : VMetric p E 1) (fl : Vert.Flag E 1) :
    h.FlagBcFinite fl ∧ h.flagBc fl = 0 := by
  have e (σ) : ((h.stepMet fl 0).met σ).bcMeas (stepSeq_shortExact fl 0) (fl.isVB (Fin.castSucc 0))
      (fl.isVB_gr 0) = 0 := Met.bcMeas_rank_zero _ _ _
  refine ⟨fun i σ => ?_, ?_⟩
  · rw [Subsingleton.elim i 0, e]; simp
  · simp only [flagBc, bcInt, Fin.sum_univ_one, e]; simp

end VMetric

example : 2 * diagVal (extTrace tautPairGram 0) 1 = 1 / Real.pi := by
  have hc : ContDiff ℝ 1 fun z : ℂ => starRingEnd ℂ z := Complex.conjCLE.contDiff
  have h : MContDiffAt 1 tautPairGram 0 := by
    rintro (_ | _) (_ | _)
    exacts [contDiffAt_const.add (contDiffAt_id.mul hc.contDiffAt), contDiffAt_id, hc.contDiffAt,
      contDiffAt_const]
  have hp : ∀ᶠ x in 𝓝 (0 : ℂ), (tautPairGram x).PosDef := .of_forall fun x => by
    have := posDef_chg (A := fromBlocks (1 : Matrix Unit Unit ℂ) 0 (of fun _ _ => x) (1 : Matrix Unit Unit ℂ))
      (H := 1)
      ((isUnit_iff_isUnit_det _).2 (by rw [det_fromBlocks_zero₁₂]; simp)) PosDef.one
    convert this using 1
    ext (_ | _) (_ | _) <;> simp [chg, tautPairGram, mul_apply]
  have h0 : tautPairGram 0 = 1 := by
    ext (_ | _) (_ | _) <;> simp [tautPairGram]
  have hb : secondForm tautPairGram 0 1 = 1 := by
    ext
    rw [secondForm_eq, conn, h0, transpose_one, inv_one, Matrix.one_mul]
    change del (fun z : ℂ => z) 0 1 = _
    rw [del_eq_fderiv differentiableAt_fun_id]
    simp
  have e : -Complex.I * kappa = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
    rw [kappa, ← mul_div_assoc, neg_mul, Complex.I_mul_I]; simp
  have hs : subGram (1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ) = 1 := by ext; simp [subGram, toBlocks₁₁]
  have hq : quotGram (1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ) = 1 := by
    ext; simp [quotGram, toBlocks₂₁, toBlocks₂₂, mul_apply]
  rw [diagVal, extTrace_eq h hp, ← mul_assoc, e, Complex.re_ofReal_mul, secondFormAdj, hb, h0, hs, hq]
  simp [adj]
  ring

end GlobalTheory
