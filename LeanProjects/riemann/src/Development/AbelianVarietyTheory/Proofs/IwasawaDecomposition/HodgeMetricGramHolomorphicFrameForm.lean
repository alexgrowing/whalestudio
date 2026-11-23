import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultOfNotMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInterior
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfConjEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedChartExponentialToroidalModel

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.LieBase
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.HodgeSmooth

open ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.FramePairGram Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.PointChern
open GlobalTheory.FlagBundle

namespace GlobalTheory.HodgeGramGen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ}

theorem gram_orth {U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (k : U.Comp) (x : (U.X k).dom) (hx : IsOrth (U.X k) x.1) (τ : E →+* ℂ) :
    (hodgeMet Z U).gram (cxPt Z (U.un k x)) (cxFrame Z (U.un k x)) τ = ((2 * Real.pi : ℝ) : ℂ) • 1 := by
  classical
  by_cases h0 : Dw.mult τ = 0
  · ext a
    exact (Fin.cast h0 a).elim0
  have h1 : 1 ≤ Dw.p + Dw.q := by
    unfold Datum.mult at h0
    split_ifs at h0 <;> omega
  suffices key : ∀ (V : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), unfFam U σ = V → ∀ (k : V.Comp)
      (x : (V.X k).dom), IsOrth (V.X k) x.1 →
      (hodgeMet Z U).gram (cxPt Z (V.un k x)) (cxFrame Z (V.un k x)) τ = ((2 * Real.pi : ℝ) : ℂ) • 1 from
    key U (unfFam_self U) k x hx
  rintro V rfl k x hx
  have hU' : Formalism.L2.PjFree.IsUnf (unfFam U σ) := by rw [unfFam_self]; exact hU
  obtain ⟨W, hinj⟩ := exists_unfWit_inj hσ hU' h1
  obtain ⟨d, hd0, hd⟩ := exists_diag_riem hσ hU' W
  have hex : ∃ g, IsHodgeFrame (unfFam U) (cxPt Z ((unfFam U σ).un k x)) g :=
    ⟨_, isHodgeFrame_cxFrame (U := unfFam U) hσ hx⟩
  have hg : (hodgeMet Z U).gram (cxPt Z ((unfFam U σ).un k x)) (cxFrame Z ((unfFam U σ).un k x)) τ =
      ((2 * Real.pi : ℝ) : ℂ) • ((hex.choose.co (cxFrame Z ((unfFam U σ).un k x)) τ)ᴴ *
        hex.choose.co (cxFrame Z ((unfFam U σ).un k x)) τ) := dif_pos hex
  obtain ⟨k₂, x₂, hx₂, hkx, hv⟩ := hodgeFrame_comp hσ hex.choose_spec
  have e : ((unfFam U σ).un k₂ x₂).x = ((unfFam U σ).un k x).x := x_eq_of_cxPt (congrArg Subtype.val hkx)
  have hik : W.ik k₂ = W.ik k := W.F.disj _ _ _ _ (W.period k₂ x₂) (W.period k x)
    ((W.lie k₂ x₂).1.symm.trans (e.trans (W.lie k x).1))
  obtain rfl : k₂ = k := hinj hik
  obtain ⟨-, -, -, -, Hm, -, -, hH⟩ := W.period k₂ x₂
  have hder : ∀ b, IsDerivAt0 (fun w => (W.F.ex (W.ik k₂) (W.Pm k₂ x₂) w).left)
      ((fun b : Fin (Dw.mult τ) => (Pi.single (W.e.symm ⟨τ, b⟩) 1 : Fin W.g → ℂ)) b)
      (((unfFam U σ).un k₂ x₂).u τ b) := fun b => (W.lie k₂ x₂).2 τ b
  have hc1 : ∀ b, IsCombAt ((unfFam U σ).un k₂ x₂).x (((unfFam U σ).un k₂ x₂).u τ)
      (show Fin (Dw.mult τ) → CAt σ from fun b' => (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) b' b)
      (((unfFam U σ).un k₂ x₂).u τ b) := fun b => by
    have := isCombAt_co (Z := Z) (y := (unfFam U σ).un k₂ x₂) (y' := (unfFam U σ).un k₂ x₂) rfl
      (g := cxFrame Z ((unfFam U σ).un k₂ x₂)) (fun _ _ => rfl) τ b
    rwa [EigFrame.co_self] at this
  have hT1 := hd k₂ x₂ hx₂ (W.ik k₂) (W.Pm k₂ x₂) (W.period k₂ x₂) Hm hH (W.lie k₂ x₂).1.symm τ _ _ 1 hder hc1
  have hT2 := hd k₂ x hx (W.ik k₂) (W.Pm k₂ x₂) (W.period k₂ x₂) Hm hH ((W.lie k₂ x₂).1.symm.trans e) τ _ _
    ((cxFrame Z ((unfFam U σ).un k₂ x)).co hex.choose τ) hder
    (fun b => isCombAt_co (Z := Z) e (g := hex.choose) hv τ b)
  set S := (cxFrame Z ((unfFam U σ).un k₂ x)).co hex.choose τ with hS
  have hSS : Sᴴ * S = 1 := by
    have := hT2.symm.trans hT1
    rw [conjTranspose_one, Matrix.one_mul] at this
    exact smul_right_injective _ (hd0 k₂ τ) this
  have hST : S * hex.choose.co (cxFrame Z ((unfFam U σ).un k₂ x)) τ = 1 := by
    rw [hS, EigFrame.co_mul, EigFrame.co_self]
  have hinv : hex.choose.co (cxFrame Z ((unfFam U σ).un k₂ x)) τ = Sᴴ := by
    have h2 : S * Sᴴ = 1 := mul_eq_one_comm.1 hSS
    calc _ = (Sᴴ * S) * hex.choose.co (cxFrame Z ((unfFam U σ).un k₂ x)) τ := by rw [hSS, Matrix.one_mul]
      _ = Sᴴ := by rw [Matrix.mul_assoc, hST, Matrix.mul_one]
  rw [hg, hinv, conjTranspose_conjTranspose, mul_eq_one_comm.1 hSS]

end GlobalTheory.HodgeGramGen
namespace GlobalTheory.HodgeGramGen

section Analytic

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {x₀ : V}

theorem an_mul {m n p : Type} [Fintype n] {A : V → Matrix m n ℂ} {B : V → Matrix n p ℂ}
    (hA : ∀ i j, AnalyticAt ℂ (fun x => A x i j) x₀) (hB : ∀ i j, AnalyticAt ℂ (fun x => B x i j) x₀)
    (i : m) (j : p) : AnalyticAt ℂ (fun x => (A x * B x) i j) x₀ := by
  simp only [mul_apply]
  exact Finset.analyticAt_fun_sum _ fun k _ => (hA i k).mul (hB k j)

end Analytic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem an_frameCo (X : Data E r) {j : ℕ} (hj : j ≤ r) (τ : X.Ψ) (x₀ : Frame X.Ψ r) (a b : Fin j ⊕ Fin (r - j)) :
    AnalyticAt ℂ (fun x : Frame X.Ψ r => frameCo X hj x τ a b) x₀ := by
  simp only [frameCo, reindex_apply, submatrix_apply]
  have h0 : AnalyticAt ℂ (fun x : Frame X.Ψ r => x) x₀ := analyticAt_id
  exact an_mul (V := Frame X.Ψ r) (n := Fin r) (A := fun _ => (mat (x0F X) τ)⁻¹) (B := fun x => mat x τ)
    (fun _ _ => analyticAt_const)
    (fun i k => analyticAt_pi_iff.1 (analyticAt_pi_iff.1 (analyticAt_pi_iff.1 h0 τ) i) k) _ _

theorem analyticAt_inv_lowerRightBlock_frame (X : Data E r) {j : ℕ} (hj : j ≤ r) (hp : X.p0 = r - j) (τ : X.Ψ) {x₀ : Frame X.Ψ r}
    (hx : x₀ ∈ X.dom) (a b : Fin (r - j)) :
    AnalyticAt ℂ (fun x : Frame X.Ψ r => ((frameCo X hj x τ).toBlocks₂₂)⁻¹ a b) x₀ :=
  GlobalTheory.ShFam.Hor.LogCh.analyticAt_inv_apply (fun _ _ => an_frameCo X hj τ x₀ _ _)
    (frameCo_isUnit₂₂ X hj hp hx τ).ne_zero a b

theorem an_moeb (X : Data E r) {j : ℕ} (hj : j ≤ r) (hp : X.p0 = r - j) (τ : X.Ψ) {x₀ : Frame X.Ψ r}
    (hx : x₀ ∈ X.dom) (a : Fin j) (b : Fin (r - j)) :
    AnalyticAt ℂ (fun x : Frame X.Ψ r => moeb (frameCo X hj x τ) 0 a b) x₀ := by
  simp only [moeb_zero]
  exact an_mul (fun _ _ => an_frameCo X hj τ x₀ _ _) (analyticAt_inv_lowerRightBlock_frame X hj hp τ hx) a b

theorem an_coW (X : Data E r) {j : ℕ} (hj : j ≤ r) (hp : X.p0 = r - j) (τ : X.Ψ) {x₀ : Frame X.Ψ r}
    (hx : x₀ ∈ X.dom) (a b : Fin j) : AnalyticAt ℂ (fun x : Frame X.Ψ r => coW X hj x τ a b) x₀ := by
  simp only [coW, Matrix.sub_apply]
  exact (an_frameCo X hj τ x₀ _ _).sub
    (an_mul (V := Frame X.Ψ r) (an_moeb X hj hp τ hx) (fun _ _ => an_frameCo X hj τ x₀ _ _) a b)

theorem an_coOm_inv (X : Data E r) {j : ℕ} (hj : j ≤ r) (hp : X.p0 = r - j) (τ : X.Ψ) {x₀ : Frame X.Ψ r}
    (hx : x₀ ∈ X.dom) (a b : Fin (r - j)) : AnalyticAt ℂ (fun x : Frame X.Ψ r => (coOm X hj x τ)⁻¹ a b) x₀ :=
  analyticAt_inv_lowerRightBlock_frame X hj hp τ hx a b

end GlobalTheory.HodgeGramGen
namespace GlobalTheory.HodgeGramGen

theorem gram_cm {j : ℕ} {W W₁ P : Matrix (Fin j) (Fin j) ℂ} (hW₁ : IsUnit W₁.det) (h : W₁ᴴ * P⁻¹ * W₁ = 1) :
    ((W₁⁻¹ * W)ᴴ * (W₁⁻¹ * W))ᵀ = Wᵀ * (Pᵀ)⁻¹ * (Wᵀ)ᴴ := by
  have hP' := GlobalTheory.HodgeOnDomain.eq_of_conj_eq_one hW₁ h
  calc ((W₁⁻¹ * W)ᴴ * (W₁⁻¹ * W))ᵀ = (Wᴴ * P⁻¹ * W)ᵀ := by
        rw [hP', conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Wᵀ * (P⁻¹)ᵀ * (Wᴴ)ᵀ := by rw [transpose_mul, transpose_mul, Matrix.mul_assoc]
    _ = Wᵀ * (Pᵀ)⁻¹ * (Wᵀ)ᴴ := by
        rw [transpose_nonsing_inv]
        congr 1

theorem gram_conj {m : ℕ} {Ω Ω₁ Q : Matrix (Fin m) (Fin m) ℂ} (hΩ₁ : IsUnit Ω₁.det) (h : Ω₁ᴴ * Q * Ω₁ = 1) :
    (((Ω⁻¹ * Ω₁)ᵀ)ᴴ * (Ω⁻¹ * Ω₁)ᵀ)ᵀ = Ω⁻¹ * Q⁻¹ * (Ω⁻¹)ᴴ := by
  have hQ' := GlobalTheory.HodgeOnDomain.eq_of_conj_eq_one hΩ₁ h
  have hQi : Q⁻¹ = Ω₁ * Ω₁ᴴ := by
    rw [hQ', Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ hΩ₁, ← conjTranspose_nonsing_inv,
      nonsing_inv_nonsing_inv _ hΩ₁]
  have e : (((Ω⁻¹ * Ω₁)ᵀ)ᴴ)ᵀ = (Ω⁻¹ * Ω₁)ᴴ := by
    ext a b
    simp only [transpose_apply, conjTranspose_apply]
  rw [transpose_mul, transpose_transpose, e, hQi, conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem hP_transpose {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ) : (hP z)ᵀ = 1 - z.map (starRingEnd ℂ) * zᵀ := by
  ext a b
  simp [hP, mul_apply, mul_comm, one_apply, eq_comm]

theorem cast_cols_map {p q q' : ℕ} (z : Matrix (Fin p) (Fin q) ℂ) (e : Fin q' ≃ Fin q) :
    (z.submatrix id e).map (starRingEnd ℂ) * (z.submatrix id e)ᵀ = z.map (starRingEnd ℂ) * zᵀ := by
  ext a b
  simp only [mul_apply, map_apply, transpose_apply, submatrix_apply, id]
  exact Fintype.sum_equiv e _ _ fun _ => rfl

theorem cast_cols_herm {p q q' : ℕ} (z : Matrix (Fin p) (Fin q) ℂ) (e : Fin q' ≃ Fin q) :
    (z.submatrix id e)ᴴ * z.submatrix id e = (zᴴ * z).submatrix e e := by
  rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ _ _ Function.bijective_id]

theorem sub3 {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ) (e₁ e₂ : m → n)
    (h : Function.Bijective e₂) :
    A.submatrix e₁ e₂ * B.submatrix e₂ e₂ * (A.submatrix e₁ e₂)ᴴ = (A * B * Aᴴ).submatrix e₁ e₁ := by
  rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ _ _ h, ← submatrix_mul _ _ _ _ _ h]

theorem one_sub_submatrix {m n : Type} [DecidableEq m] [DecidableEq n] (M : Matrix n n ℂ) (f : m ≃ n) :
    1 - M.submatrix f f = (1 - M).submatrix f f := by
  rw [← submatrix_one_equiv f]
  rfl

end GlobalTheory.HodgeGramGen

open MvPolynomial GlobalTheory.GoodMetric GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ChartGlue GlobalTheory.HermFrame Filter Topology
open scoped Matrix ComplexOrder

theorem GlobalTheory.HodgeGramGen.hodge_gram_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ k' : U.Comp, ∃ (G : ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k').Ψ (Dw.p + Dw.q) → Mat Dw.mult ℂ) (z : ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k').Ψ (Dw.p + Dw.q) → GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.p) (Fin Dw.q) ℂ) (cc : (E →+* ℂ) → ℝ), (∀ τ, 0 < cc τ) ∧ ∀ (x : ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k').Ψ (Dw.p + Dw.q)) (hx : x ∈ (U.X k').dom), (∀ τ a b, AnalyticAt ℂ (fun x' => G x' τ a b) x) ∧ (∀ τ a b, AnalyticAt ℂ (fun x' => z x' τ a b) x) ∧ (∀ τ, IsUnit (G x τ).det) ∧ InDom (z x) ∧ ∀ τ, ((hodgeMet Z U).gram (cxPt Z (U.un k' ⟨x, hx⟩)) (cxFrame Z (U.un k' ⟨x, hx⟩)) τ)ᵀ = (cc τ : ℂ) • (G x τ * modelGram H Dw (z x) τ * (G x τ)ᴴ) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ U hσ hU k'
  classical
  have hj : Dw.p ≤ Dw.p + Dw.q := Nat.le_add_right _ _
  have hp : (U.X k').p0 = Dw.p + Dw.q - Dw.p := by have := (hU.2.1 k').1; omega
  have hq : Dw.p + Dw.q - Dw.p = Dw.q := by omega
  obtain ⟨-, hrt, hcj, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  have hty := (hU.2.1 k').2
  let ρ : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (U.X k').Ψ := fun τ h =>
    ⟨Formalism.L2.PjFree.relab c σ τ, (hty _).2 ((hrt τ).2 h)⟩
  let zr : ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k').Ψ (Dw.p + Dw.q) → GlobalTheory.AllWt.Psi H →
      Matrix (Fin Dw.p) (Fin (Dw.p + Dw.q - Dw.p)) ℂ :=
    fun x τ => moeb (frameCo (U.X k') hj x (ρ τ.1 τ.2)) 0
  let cq : Fin Dw.q → Fin (Dw.p + Dw.q - Dw.p) := Fin.cast hq.symm
  refine ⟨fun x τ => if h : τ (H.rt : E) = H.rt0 then
      (coW (U.X k') hj x (ρ τ h))ᵀ.submatrix (Fin.cast (mult_of_mem Dw h)) (Fin.cast (mult_of_mem Dw h))
    else if h' : conjEmb τ (H.rt : E) = H.rt0 then
      ((coOm (U.X k') hj x (ρ _ h'))⁻¹).submatrix (fun a => Fin.rev (cq (Fin.cast (mult_of_not_mem Dw h) a)))
        (fun a => cq (Fin.cast (mult_of_not_mem Dw h) a))
    else 1,
    fun x τ => (zr x τ).submatrix id cq, fun _ => 2 * Real.pi, fun _ => Real.two_pi_pos, fun x hx => ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro τ a b
    by_cases h : τ (H.rt : E) = H.rt0
    · simp only [dif_pos h, submatrix_apply, transpose_apply]
      exact GlobalTheory.HodgeGramGen.an_coW _ hj hp _ hx _ _
    · by_cases h' : conjEmb τ (H.rt : E) = H.rt0
      · simp only [dif_neg h, dif_pos h', submatrix_apply]
        exact GlobalTheory.HodgeGramGen.an_coOm_inv _ hj hp _ hx _ _
      · simp only [dif_neg h, dif_neg h']
        exact analyticAt_const
  · intro τ a b
    exact GlobalTheory.HodgeGramGen.an_moeb _ hj hp _ hx _ _
  · intro τ
    by_cases h : τ (H.rt : E) = H.rt0
    · simp only [dif_pos h]
      rw [show (Fin.cast (mult_of_mem Dw h) : Fin (Dw.mult τ) → Fin Dw.p) = ⇑(finCongr (mult_of_mem Dw h)) from rfl,
        det_submatrix_equiv_self, det_transpose]
      exact isUnit_coW _ hj hp hx _
    · by_cases h' : conjEmb τ (H.rt : E) = H.rt0
      · simp only [dif_neg h, dif_pos h']
        rw [← isUnit_iff_isUnit_det]
        have e1 : (fun a => Fin.rev (cq (Fin.cast (mult_of_not_mem Dw h) a))) =
          ⇑((finCongr ((mult_of_not_mem Dw h).trans hq.symm)).trans Fin.revPerm) := rfl
        have e2 : (fun a => cq (Fin.cast (mult_of_not_mem Dw h) a)) =
          ⇑(finCongr ((mult_of_not_mem Dw h).trans hq.symm)) := rfl
        rw [e1, e2, isUnit_submatrix_equiv, isUnit_iff_isUnit_det]
        exact isUnit_nonsing_inv_det _ (isUnit_coOm _ hj hp hx _)
      · simp only [dif_neg h, dif_neg h', det_one]
        exact isUnit_one
  · intro τ
    have hd := domPt_mem (U.X k') hj (fun t : GlobalTheory.AllWt.Psi H => ρ t.1 t.2) hp hx τ
    have e : (1 - ((zr x τ).submatrix id ⇑(finCongr hq.symm))ᴴ * (zr x τ).submatrix id ⇑(finCongr hq.symm)) =
        (1 - (zr x τ)ᴴ * zr x τ).submatrix (finCongr hq.symm) (finCongr hq.symm) := by
      rw [GlobalTheory.HodgeGramGen.cast_cols_herm _ (finCongr hq.symm), ← submatrix_one_equiv (finCongr hq.symm)]
      rfl
    show (1 - ((zr x τ).submatrix id ⇑(finCongr hq.symm))ᴴ * (zr x τ).submatrix id ⇑(finCongr hq.symm)).PosDef
    rw [e]
    exact hd.submatrix (finCongr hq.symm).injective
  · intro τ
    obtain ⟨x1, h1, b, hb, ef⟩ := ortho_holds (Dw.p + Dw.q) (U.X k') x hx
    have hx1 : x1 ∈ (U.X k').dom := KU.orth_dom _ h1
    have hmo : ∀ τ' : (U.X k').Ψ, moeb (frameCo (U.X k') hj x τ') 0 = moeb (frameCo (U.X k') hj x1 τ') 0 :=
      fun τ' => by
        rw [ef]
        exact congrFun (domPt_rmul (U.X k') hj (fun t : (U.X k').Ψ => t) hb x1) τ'
    have h1' := fun τ' => PointWell.block_of_moeb_eq (U.X k') hj hp hx hx1 τ' (hmo τ')
    have h2' := fun τ' => PointWell.block_of_moeb_eq (U.X k') hj hp hx1 hx τ' (hmo τ').symm
    have hxe : (U.un k' ⟨x, hx⟩).x = (U.un k' ⟨x1, hx1⟩).x :=
      PointWell.pt_eq_of_block hU hσ k' ⟨x, hx⟩ ⟨x1, hx1⟩ h1' h2'
    have hg := GlobalTheory.HodgeOnDomain.eigGram_of_comb (hodgeMet Z U) _ _ hxe τ
      (Matrix.of fun b i : Fin (Dw.mult τ) => coef (U.X k') x x1 (Formalism.L2.PjFree.relab c σ τ) b i)
      (fun i => lie_comb_of_block hU hσ k' ⟨x, hx⟩ ⟨x1, hx1⟩ h1' h2' τ i)
    rw [GlobalTheory.HodgeGramGen.gram_orth hσ hU k' ⟨x1, hx1⟩ h1 τ, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul] at hg
    rw [hg, transpose_smul]
    congr 1
    by_cases h : τ (H.rt : E) = H.rt0
    · have hK := coef_eq_coW_change (U.X k') hj hp hx hx1 (ρ τ h) (hmo _)
      set e : Fin (Dw.mult τ) ≃ Fin Dw.p := finCongr (mult_of_mem Dw h) with he
      have hKe : (Matrix.of fun b i : Fin (Dw.mult τ) => coef (U.X k') x x1 (Formalism.L2.PjFree.relab c σ τ) b i) =
          ((coW (U.X k') hj x1 (ρ τ h))⁻¹ * coW (U.X k') hj x (ρ τ h)).submatrix e e := by
        rw [← hK]
        rfl
      obtain ⟨hco1, -⟩ := hodge_co (U.X k') hj hp h1 (ρ τ h)
      rw [hKe, conjTranspose_submatrix, ← submatrix_mul _ _ _ _ _ e.bijective, transpose_submatrix,
        GlobalTheory.HodgeGramGen.gram_cm (isUnit_coW (U.X k') hj hp hx1 _) hco1, ← hmo, GlobalTheory.HodgeGramGen.hP_transpose]
      simp only [dif_pos h]
      rw [modelGram, dif_pos h, reindex_apply]
      show _ = (coW (U.X k') hj x (ρ τ h))ᵀ.submatrix e e *
        ((1 - ((zr x ⟨τ, h⟩).submatrix id ⇑(finCongr hq.symm)).map (starRingEnd ℂ) *
          ((zr x ⟨τ, h⟩).submatrix id ⇑(finCongr hq.symm))ᵀ)⁻¹).submatrix e e *
        ((coW (U.X k') hj x (ρ τ h))ᵀ.submatrix e e)ᴴ
      rw [GlobalTheory.HodgeGramGen.cast_cols_map, GlobalTheory.HodgeGramGen.sub3 _ _ _ _ e.bijective]
    · by_cases h' : conjEmb τ (H.rt : E) = H.rt0
      · have hcc : conjEmb (ρ _ h').1 = Formalism.L2.PjFree.relab c σ τ := by
          show conjEmb (Formalism.L2.PjFree.relab c σ (conjEmb τ)) = _
          rw [hcj]
          exact RingHom.ext fun a => by simp [conjEmb]
        have hK := coef_conj_eq_coOm (U.X k') hj hp hx hx1 (ρ _ h') (hmo _)
        rw [hcc] at hK
        set e : Fin (Dw.mult τ) ≃ Fin (Dw.p + Dw.q - Dw.p) :=
          (finCongr (mult_of_not_mem Dw h)).trans (finCongr hq.symm) with he
        set er : Fin (Dw.mult τ) ≃ Fin (Dw.p + Dw.q - Dw.p) := e.trans Fin.revPerm with her
        have hKe : (Matrix.of fun b i : Fin (Dw.mult τ) => coef (U.X k') x x1 (Formalism.L2.PjFree.relab c σ τ) b i) =
            (((coOm (U.X k') hj x (ρ _ h'))⁻¹ * coOm (U.X k') hj x1 (ρ _ h'))ᵀ).submatrix er er := by
          ext b i
          exact congrFun (congrFun hK (e b)) (e i)
        obtain ⟨-, hco2⟩ := hodge_co (U.X k') hj hp h1 (ρ _ h')
        rw [hKe, conjTranspose_submatrix, ← submatrix_mul _ _ _ _ _ er.bijective, transpose_submatrix,
          GlobalTheory.HodgeGramGen.gram_conj (isUnit_coOm (U.X k') hj hp hx1 _) hco2, ← hmo]
        simp only [dif_neg h, dif_pos h']
        rw [modelGram, dif_neg h, dif_pos h', reindex_apply]
        show _ = (coOm (U.X k') hj x (ρ _ h'))⁻¹.submatrix er e *
          ((1 - ((zr x ⟨conjEmb τ, h'⟩).submatrix id ⇑(finCongr hq.symm))ᴴ *
            (zr x ⟨conjEmb τ, h'⟩).submatrix id ⇑(finCongr hq.symm))⁻¹).submatrix
              (finCongr (mult_of_not_mem Dw h)) (finCongr (mult_of_not_mem Dw h)) *
          ((coOm (U.X k') hj x (ρ _ h'))⁻¹.submatrix er e)ᴴ
        have hcomp : (⇑(finCongr hq.symm) ∘ ⇑(finCongr (mult_of_not_mem Dw h))) = ⇑e := rfl
        rw [GlobalTheory.HodgeGramGen.cast_cols_herm, GlobalTheory.HodgeGramGen.one_sub_submatrix, inv_submatrix_equiv,
          submatrix_submatrix, hcomp, GlobalTheory.HodgeGramGen.sub3 _ _ _ _ e.bijective, hQ]
      · exfalso
        exact h' ((hty _).1 (by_contra fun hc => h ((hty _).1 (((U.X k').cmType τ).2 hc))))
