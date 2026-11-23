import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.ZuckDualTOfZuckDual
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimBdPf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimBdPfKFin

noncomputable section

namespace CompanionTheory.LimBd.Main

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP PI.UpqRep Matrix
open scoped InnerProductSpace

def PStar {n : ℕ} (lam : Fin n → ℝ) (c y : ℝ) : ℝ := ∏ s, (|y + lam s| + c)

theorem norm_capP_le {n : ℕ} {lam μ : Fin n → ℝ} {c : ℝ} (h : μ ∈ Box lam c) (y : ℝ) :
    ‖Formalism.QuantumDeterminants.capP (fun s => (μ s : ℂ)) (y : ℂ)‖ ≤ PStar lam c y := by
  unfold Formalism.QuantumDeterminants.capP PStar
  rw [norm_prod]
  refine Finset.prod_le_prod (fun s _ => norm_nonneg _) fun s _ => ?_
  have e : (y : ℂ) + (μ s : ℂ) = ((y + μ s : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs]
  obtain ⟨h1, h2⟩ := abs_le.mp (h s)
  rcases abs_cases (y + μ s) with ⟨h3, _⟩ | ⟨h3, _⟩ <;>
  rcases abs_cases (y + lam s) with ⟨h4, _⟩ | ⟨h4, _⟩ <;> linarith

theorem gap_of_box {n : ℕ} {ε : Fin n → Bool} {lam μ : Fin n → ℝ} {c h h₀ : ℝ} (hμ : μ ∈ Box lam c)
    (hg : PI.ZuckTensor.GapAtLeast ε lam h) (hh : h₀ + 2 * c ≤ h) : PI.ZuckTensor.GapAtLeast ε μ h₀ := by
  intro a b hab
  have h1 := hg a b hab
  obtain ⟨ha1, ha2⟩ := abs_le.mp (hμ a)
  obtain ⟨hb1, hb2⟩ := abs_le.mp (hμ b)
  rcases abs_cases (lam a - lam b) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
  rcases abs_cases (μ a - μ b) with ⟨h3, _⟩ | ⟨h3, _⟩ <;> linarith

section W

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def Wsp (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (ε : Fin (2 * r + k + 1) → Bool) (μ : Fin (2 * r + k + 1) → ℝ) :
    Submodule ℂ (B.Mat k r → (Wq →L[ℂ] Wp)) :=
  Submodule.span ℂ {F | ∃ φ T, IsCoef k r ε μ φ ∧ F = fun g => φ g • T}

variable {ε : Fin (2 * r + k + 1) → Bool} {μ μ' : Fin (2 * r + k + 1) → ℝ}

private theorem ckOn_GV_of_mem_Wsp (hK : PI.KFinSmooth) (hS : CoefSmooth) {F : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hF : F ∈ Wsp k r Wp Wq ε μ) : B.CkOn ⊤ (B.GV k r) F := by
  letI : NormedAddCommGroup (B.Mat k r) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (B.Mat k r) := Matrix.normedSpace
  unfold Wsp at hF
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨φ, T, hc, rfl⟩ := hF
    exact hS hK k r ε μ φ _ T hc
  | zero =>
    intro g₀ _
    exact ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun g _ _ => rfl⟩
  | add F G _ _ hF hG =>
    intro g₀ hg₀
    obtain ⟨U, F', hU, hgU, hF', hFe⟩ := hF g₀ hg₀
    obtain ⟨V, G', hV, hgV, hG', hGe⟩ := hG g₀ hg₀
    refine ⟨U ∩ V, fun g => F' g + G' g, hU.inter hV, ⟨hgU, hgV⟩,
      (hF'.mono Set.inter_subset_left).add (hG'.mono Set.inter_subset_right), ?_⟩
    intro g hg hgG
    simp only [Pi.add_apply, hFe g hg.1 hgG, hGe g hg.2 hgG]
  | smul a F _ hF =>
    intro g₀ hg₀
    obtain ⟨U, F', hU, hgU, hF', hFe⟩ := hF g₀ hg₀
    refine ⟨U, fun g => a • F' g, hU, hgU, hF'.const_smul a, ?_⟩
    intro g hg hgG
    simp only [Pi.smul_apply, hFe g hg hgG]

theorem wsp_smooth (hK : PI.KFinSmooth) (hS : CoefSmooth) {F : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hF : F ∈ Wsp k r Wp Wq ε μ) : Q.SmoothLev k r 0 Set.univ F := by
  intro g₀ hg₀
  obtain ⟨U, F', hU, hgU, hF', hFe⟩ := ckOn_GV_of_mem_Wsp hK hS hF g₀ hg₀.1.1
  exact ⟨U, F', hU, hgU, hF', fun g hg hgl => hFe g hg hgl.1⟩

theorem wsp_ckOn (hK : PI.KFinSmooth) (hS : CoefSmooth) {F : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hF : F ∈ Wsp k r Wp Wq ε μ) : B.CkOn ⊤ (B.GV k r) F := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', he⟩ := wsp_smooth hK hS hF g₀ (Dx1.LZ.glev0 hg₀)
  exact ⟨U, f', hU, hgU, hf', fun g hg hgG => he g hg (Dx1.LZ.glev0 hgG).1⟩

theorem wsp_inCC (hK : PI.KFinSmooth) (hC : CoefCC) {A h : ℝ} (hD : KDecay k r ε A h)
    (hg : PI.ZuckTensor.GapAtLeast ε μ h) {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : F ∈ Wsp k r Wp Wq ε μ) :
    B.InCC A 5 F := by
  induction hF using Submodule.span_induction with
  | mem F h' =>
    obtain ⟨φ, T, hφ, rfl⟩ := h'
    exact hC hK k r ε A h hD μ φ _ T 5 hφ hg
  | zero => exact JCx2.sq_inCC_zero
  | add F F' _ _ h h' => exact JCx2.sq_inCC_add h h'
  | smul c F _ h => exact JCx2.sq_inCC_smul c h

theorem wsp_eig (hK : PI.KFinSmooth) (hS : CoefSmooth) (hE : CoefEig) (Y : ℂ) {F : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hF : F ∈ Wsp k r Wp Wq ε μ) :
    ∀ g ∈ B.GV k r, Q.CV k r Y F g = Formalism.QuantumDeterminants.capP (fun s => (μ s : ℂ)) Y • F g := by
  have hG := Dx1.LZ.good_CV (k := k) (r := r) (E := Wq →L[ℂ] Wp) Y
  induction hF using Submodule.span_induction with
  | mem F h =>
    obtain ⟨φ, T, hφ, rfl⟩ := h
    exact hE k r ε μ φ Wp Wq T hφ Y
  | zero =>
    intro g hg
    rw [Pi.zero_apply, smul_zero]
    exact hG.map_zero (Dx1.LZ.glev0 hg)
  | add F F' hF hF' h h' =>
    intro g hg
    have e := hG.lin F F' 1 (wsp_smooth hK hS hF) (wsp_smooth hK hS hF') g (Dx1.LZ.glev0 hg)
    simp only [one_smul] at e
    rw [Pi.add_apply, smul_add, ← h g hg, ← h' g hg]
    exact e
  | smul c F hF h =>
    intro g hg
    have e := Dx1.LZ.good_smul_in hG (wsp_smooth hK hS hF) c (Dx1.LZ.glev0 hg)
    rw [Pi.smul_apply, smul_comm, ← h g hg]
    exact e

theorem wsp_orth (hK : PI.KFinSmooth) (hC : CoefCC) (hE : CoefEig) (hP : PhZero) (hB : BetaInfZero)
    (D : B.RealPlaceData k r Wp Wq) {A h : ℝ} (hA : B.AB k r ≤ A) (hD : KDecay k r ε A h)
    (hg : PI.ZuckTensor.GapAtLeast ε μ h) (hg' : PI.ZuckTensor.GapAtLeast ε μ' h) (hne : μ ≠ μ')
    {F F' : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : F ∈ Wsp k r Wp Wq ε μ) (hF' : F' ∈ Wsp k r Wp Wq ε μ') :
    B.beta D F F' = 0 := by
  obtain ⟨c0, -, -, -, hβ, -⟩ := b_any_of_xi k r Wp Wq D A hA
  have cc : ∀ {G}, G ∈ Wsp k r Wp Wq ε μ → B.InCC A 5 G := fun h => wsp_inCC hK hC hD hg h
  have cc' : ∀ {G}, G ∈ Wsp k r Wp Wq ε μ' → B.InCC A 5 G := fun h => wsp_inCC hK hC hD hg' h
  induction hF using Submodule.span_induction with
  | mem F h1 =>
    have hFm : F ∈ Wsp k r Wp Wq ε μ := Submodule.subset_span h1
    induction hF' using Submodule.span_induction with
    | mem F' h2 =>
      have hFm' : F' ∈ Wsp k r Wp Wq ε μ' := Submodule.subset_span h2
      rw [hβ F F' (cc hFm) (cc' hFm')]
      obtain ⟨φ, T, hφ, rfl⟩ := h1
      obtain ⟨φ', T', hφ', rfl⟩ := h2
      rw [hB k r Wp Wq D _ _ (hP hE k r Wp Wq D ε μ μ' φ φ' T T' hφ hφ' hne), mul_zero]
    | zero => exact Dx1.LZ.beta_zero_right D F
    | add G G' hG hG' h h' =>
      have e := (JCx2.sq_beta_sesq D hA (cc' hG) (cc' hG') (cc hFm) 1).2
      rw [one_smul, h, h'] at e
      simpa using e
    | smul c G hG h =>
      have e := (JCx2.sq_beta_sesq D hA (cc' (Submodule.zero_mem _)) (cc' hG) (cc hFm) c).2
      rw [zero_add, h, Dx1.LZ.beta_zero_right] at e
      simpa using e
  | zero => exact beta_zero_left' D F'
  | add G G' hG hG' h h' =>
    have e := (JCx2.sq_beta_sesq D hA (cc hG) (cc hG') (cc' hF') 1).1
    rw [one_smul, h, h'] at e
    simpa using e
  | smul c G hG h =>
    have e := (JCx2.sq_beta_sesq D hA (cc (Submodule.zero_mem _)) (cc hG) (cc' hF') c).1
    rw [zero_add, h, beta_zero_left'] at e
    simpa using e

theorem smul_mem_iSup {lam : Fin (2 * r + k + 1) → ℝ} {e : ℝ} {ψ : B.Mat k r → ℂ} (hψ : ψ ∈ SpanBox k r ε lam e)
    (T : Wq →L[ℂ] Wp) : (fun g => ψ g • T) ∈ ⨆ ν : Box lam e, Wsp k r Wp Wq ε ν := by
  induction hψ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨μ, hμ, hc⟩ := hφ
    exact (le_iSup (fun ν : Box lam e => Wsp k r Wp Wq ε ν) ⟨μ, hμ⟩) (Submodule.subset_span ⟨φ, T, hc, rfl⟩)
  | zero =>
    convert Submodule.zero_mem (⨆ ν : Box lam e, Wsp k r Wp Wq ε ν) using 1
    funext g
    simp
  | add x y _ _ hx hy =>
    have hxy : (fun g => (x + y) g • T) = (fun g => x g • T) + (fun g => y g • T) := by
      funext g
      simp [add_smul]
    rw [hxy]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    have hax : (fun g => (a • x) g • T) = a • (fun g => x g • T) := by
      funext g
      simp [mul_smul]
    rw [hax]
    exact Submodule.smul_mem _ a hx

theorem op_expand (S : Wq →L[ℂ] Wp) :
    S = ∑ a, ∑ b, ⟪stdOrthonormalBasis ℂ Wp a, S (stdOrthonormalBasis ℂ Wq b)⟫_ℂ •
      (innerSL ℂ (stdOrthonormalBasis ℂ Wq b)).smulRight (stdOrthonormalBasis ℂ Wp a) := by
  ext v
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply]
  conv_lhs => rw [← (stdOrthonormalBasis ℂ Wq).sum_repr' v]
  rw [map_sum]
  simp_rw [map_smul]
  conv_lhs => arg 2; ext b; rw [← (stdOrthonormalBasis ℂ Wp).sum_repr' (S (stdOrthonormalBasis ℂ Wq b))]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => smul_comm _ _ _

end W

def SpanPow : Prop :=
  ∀ t : ∀ n : ℕ, (Fin n → Bool) → ℝ, ZuckT t → ZuckDualT t → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool)
    (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (d : ℕ) (q φ : B.Mat k r → ℂ), q ∈ Letters k r ^ d →
    IsCoef k r ε lam φ → PI.ZuckTensor.GapAtLeast ε lam h → t _ ε + 1 + 2 * (d : ℝ) < h →
    q * φ ∈ SpanBox k r ε lam (d : ℝ)

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem eigStr_of_steps [CompleteSpace Wp] (h1 : GfPoly) (h2 : SpanPow) (h3 : CoefSmooth) (h4 : CoefCC)
    (h5 : CoefEig) (h6 : PhZero) (h7 : BetaInfZero) (hK : PI.KFinSmooth)
    {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} (hZ : ZuckT t) (hZd : ZuckDualT t)
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (p₀ : ℕ) (nn : ℝ → ℝ) (Y : Finset ℝ)
    {ε : Fin (2 * P.r + P.k + 1) → Bool} {lam : Fin (2 * P.r + P.k + 1) → ℝ} {A h h₀ : ℝ}
    (hf : KFinDSCoef ε lam f) (hgap : PI.ZuckTensor.GapAtLeast ε lam h)
    (ht : t _ ε + 1 + 2 * (((2 * P.r + 2) * p₀ : ℕ) : ℝ) < h) (hA : B.AB P.k P.r ≤ A)
    (hD : KDecay P.k P.r ε A h₀) (hh : h₀ + 2 * (((2 * P.r + 2) * p₀ : ℕ) : ℝ) ≤ h)
    (hnn : ∀ y, LetPt Y y → PStar lam (((2 * P.r + 2) * p₀ : ℕ) : ℝ) y ≤ nn y) :
    EigStr p nn (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y := by
  classical
  obtain ⟨H, i1, i2, i3, σ, Pm, Qm, hlam, hσ, hQ, hP, hfG⟩ := hf
  set d : ℕ := (2 * P.r + 2) * p₀ with hd
  set q : B.Mat P.k P.r → ℂ := fun g => ((Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) with hq
  let ea := stdOrthonormalBasis ℂ Wp
  let eb := stdOrthonormalBasis ℂ Wq
  let φ : Fin (Module.finrank ℂ Wp) → Fin (Module.finrank ℂ Wq) → B.Mat P.k P.r → ℂ :=
    fun a b g => ⟪ContinuousLinearMap.adjoint Pm (ea a), σ g (Qm (eb b))⟫_ℂ
  have hφ : ∀ a b, IsCoef P.k P.r ε lam (φ a b) := fun a b =>
    ⟨H, i1, i2, i3, σ, Qm (eb b), ContinuousLinearMap.adjoint Pm (ea a), hlam, hσ, hQ _, hP _, fun _ _ => rfl⟩
  let F₁ : B.Mat P.k P.r → (Wq →L[ℂ] Wp) :=
    ∑ a, ∑ b, fun g => (q * φ a b) g • (innerSL ℂ (eb b)).smulRight (ea a)
  have hF₁ : F₁ ∈ ⨆ ν : Box lam (d : ℝ), Wsp P.k P.r Wp Wq ε ν :=
    Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
      smul_mem_iSup (h2 t hZ hZd P.k P.r ε lam h d q (φ a b) (h1 P.k P.r _ _ p₀) (hφ a b) hgap ht) _
  have hFF : ∀ g ∈ B.GV P.k P.r, TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀ g = F₁ g := by
    intro g hg
    show q g • (f g).comp (ContinuousLinearMap.id ℂ Wq) = F₁ g
    rw [ContinuousLinearMap.comp_id, op_expand (f g), hfG g hg]
    simp only [F₁, Finset.sum_apply, Finset.smul_sum, Pi.mul_apply, smul_smul, φ,
      ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.comp_apply, ea, eb]
  obtain ⟨c, hc, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ F₁).1 hF₁
  let e := c.support.equivFin.symm
  have hgν : ∀ ν : Box lam (d : ℝ), PI.ZuckTensor.GapAtLeast ε ν.1 h₀ := fun ν => gap_of_box ν.2 hgap hh
  refine ⟨A, c.support.card, fun i => c (e i), fun i y => Formalism.QuantumDeterminants.capP (fun s => ((e i).1.1 s : ℂ)) (y : ℂ), hA,
    fun i => wsp_ckOn hK h3 (hc _), fun i => wsp_inCC hK h4 hD (hgν _) (hc _), fun g hg => ?_,
    fun i y _ => wsp_eig hK h3 h5 _ (hc _), fun i y hy => (norm_capP_le (e i).1.2 y).trans (hnn y hy),
    fun i j hij => wsp_orth hK h4 h5 h6 h7 _ hA hD (hgν _) (hgν _)
      (fun hh' => hij (e.injective (Subtype.ext (Subtype.ext hh')))) (hc _) (hc _)⟩
  rw [hFF g hg, ← hsum, Finsupp.sum, Finset.sum_apply, ← Finset.sum_coe_sort]
  exact (Equiv.sum_comp e fun ν : c.support => c ν g).symm

end CompanionTheory.LimBd.Main
