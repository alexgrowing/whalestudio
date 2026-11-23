import Mathlib
import Formalism.LocalToGlobal.LatticeGeometry.NormDetInf
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf
import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.ExistsFundSetOrth
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuAllData
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnfFamily
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.InvariantDataMet

noncomputable section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain
open scoped ComplexOrder ENNReal

namespace GlobalTheory.TrueCx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def flagConst (r : ℕ) : ℝ := ∏ i ∈ Finset.range r, (i.factorial : ℝ) / Real.pi ^ i

theorem flagConst_pos (r : ℕ) : 0 < flagConst r :=
  Finset.prod_pos fun i _ => div_pos (by exact_mod_cast i.factorial_pos) (pow_pos Real.pi_pos _)

def grassConst (p q : ℕ) : ℝ := (∏ i ∈ Finset.range p, ((q + i).factorial : ℝ) / i.factorial) / Real.pi ^ (p * q)

theorem flagConst_add (p q : ℕ) : flagConst (p + q) = grassConst p q * flagConst p * flagConst q := by
  have hπ := Real.pi_pos.ne'
  induction p with
  | zero => simp [flagConst, grassConst]
  | succ p ih =>
    have h1 : ((p.factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast p.factorial_ne_zero
    have e1 : flagConst (p + 1 + q) = flagConst (p + q) * (((q + p).factorial : ℝ) / Real.pi ^ (q + p)) := by
      rw [show p + 1 + q = (p + q) + 1 by ring, flagConst, Finset.prod_range_succ, add_comm q p]; rfl
    have e2 : flagConst (p + 1) = flagConst p * ((p.factorial : ℝ) / Real.pi ^ p) := Finset.prod_range_succ _ _
    have e3 : grassConst (p + 1) q = grassConst p q * (((q + p).factorial : ℝ) / p.factorial) / Real.pi ^ q := by
      rw [grassConst, Finset.prod_range_succ, grassConst, add_mul, one_mul, pow_add]
      field_simp
    rw [e1, e2, e3, ih, pow_add]
    field_simp

example : flagConst 2 = 1 / Real.pi := by simp [flagConst, Finset.prod_range_succ]

example : grassConst 1 1 = 1 / Real.pi := by simp [grassConst]

theorem isOrth_x0F (X : Data E r) : IsOrth X (x0F X) := fun τ => (X.signature τ).choose_spec.2

theorem muF_fundSet_le (X : Data E r) {x0 x1 : Frame X.Ψ r} (ho : IsOrth X x0) (ho1 : IsOrth X x1)
    {FF CechHodgeFiltration : Set (V (nd X))} (hF : IsFundSet X x0 FF) (hF1 : IsFundSet X x1 CechHodgeFiltration) :
    muF X x0 FF ≤ muF X x1 CechHodgeFiltration := by
  classical
  have := KU.countable_Γ X
  have hM := measInv_holds (E := E)
  have hS1 : MeasurableSet (KU.Sset X x1 CechHodgeFiltration) := KU.meas_S X ho1 hF1.1
  set Bad : Set (Frame X.Ψ r) := ⋂ γ : X.Γ, (lact γ.1⁻¹ ⁻¹' KU.Sset X x1 CechHodgeFiltration)ᶜ with hBaddef
  have hBad : MeasurableSet Bad :=
    MeasurableSet.iInter fun γ => ((KU.cont_lact X γ.1⁻¹).measurable hS1).compl
  have hBadB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      Bad.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (rmul x b) = Bad.indicator 1 x := by
    intro x _ b hb
    have e : rmul x b ∈ Bad ↔ x ∈ Bad := by
      simp only [hBaddef, Set.mem_iInter, Set.mem_compl_iff, Set.mem_preimage, KU.lact_rmul', KU.rmul_mem_S X hb]
    simp only [Set.indicator_apply, e, Pi.one_apply]
  have hm : ∀ x : Frame X.Ψ r, Measurable fun z => Bad.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (cpt X x z) :=
    fun x => (measurable_one.indicator hBad).comp (KU.cont_cpt X x).measurable
  have h1 : ∫⁻ z, Bad.indicator 1 (cpt X x1 z) ∂muF X x1 = 0 := by
    rw [lintegral_eq_zero_iff (hm x1)]
    filter_upwards [KU.cover X hF1] with z ⟨γ, hγ, hSz⟩
    have : cpt X x1 z ∉ Bad := fun h => (Set.mem_iInter.mp h ⟨γ, hγ⟩) hSz
    simp [Set.indicator_of_notMem this]
  rw [← hM r X x0 x1 ho ho1 _ (measurable_one.indicator hBad) hBadB, lintegral_eq_zero_iff (hm x0)] at h1
  have hle := GlobalTheory.Unfold.lintegral_fundSet_inter_le hM r X x0 x1 ho ho1 FF hF (fun _ => 1) measurable_const
    (fun _ _ _ _ _ _ => rfl) CechHodgeFiltration hF1.1 hF1.2.1
  have hset : (FF ∩ {z | ∃ y ∈ CechHodgeFiltration, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r,
      cpt X x0 z = lact γ (rmul (cpt X x1 y) b)} : Set (V (nd X))) =ᵐ[muF X x0] FF := by
    filter_upwards [h1] with z hz
    refine propext ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    have hb : cpt X x0 z ∉ Bad := fun hb => by simp [Set.indicator_of_mem hb] at hz
    simp only [hBaddef, Set.mem_iInter, not_forall, Set.mem_compl_iff, not_not, Set.mem_preimage] at hb
    obtain ⟨γ, ⟨y, b⟩, ⟨hy, hb⟩, e⟩ := hb
    refine ⟨y, hy, γ.1, γ.2, b, hb, ?_⟩
    have e' : rmul (cpt X x1 y) b = lact γ.1⁻¹ (cpt X x0 z) := e
    rw [e', KU.lact_lact, mul_inv_cancel, KU.lact_one]
  rw [setLIntegral_congr hset] at hle
  simpa using hle

def covol (X : Data E r) : ℝ :=
  flagConst r ^ X.Ψ.card * (muF X (x0F X) (GlobalTheory.MetricWeightTest.exists_fundSet_orth X (isOrth_x0F X)).choose).toReal

theorem covol_eq (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {FF : Set (V (nd X))} (hF : IsFundSet X x0 FF) :
    muF X x0 FF < ⊤ ∧ covol X = flagConst r ^ X.Ψ.card * (muF X x0 FF).toReal := by
  have h0 := (GlobalTheory.MetricWeightTest.exists_fundSet_orth X (isOrth_x0F X)).choose_spec
  refine ⟨FundSetMeasStatement_holds r X x0 FF ho hF (GlobalTheory.finMu_all_data E r X), ?_⟩
  rw [covol, le_antisymm (muF_fundSet_le X (isOrth_x0F X) ho h0 hF) (muF_fundSet_le X ho (isOrth_x0F X) hF h0)]

theorem covol_pos (X : Data E r) : 0 < covol X := by
  have h0 := (GlobalTheory.MetricWeightTest.exists_fundSet_orth X (isOrth_x0F X)).choose_spec
  exact mul_pos (pow_pos (flagConst_pos r) _) (ENNReal.toReal_pos
    (GlobalTheory.MetricWeightTest.fundSet_pos X (isOrth_x0F X) h0) (covol_eq X (isOrth_x0F X) h0).1.ne)

def idx {r j : ℕ} (h : j ≤ r) : Fin r ≃ Fin j ⊕ Fin (r - j) :=
  ((finCongr (Nat.sub_add_cancel h).symm).trans finSumFinEquiv.symm).trans (Equiv.sumComm _ _)

theorem idx_symm_inl {r j : ℕ} (h : j ≤ r) (a : Fin j) : ((idx h).symm (Sum.inl a) : ℕ) = r - j + a := by
  simp [idx]

theorem idx_symm_inr {r j : ℕ} (h : j ≤ r) (a : Fin (r - j)) : ((idx h).symm (Sum.inr a) : ℕ) = a := by
  simp [idx]

theorem reindex_sgn {r j : ℕ} (h : j ≤ r) :
    reindex (idx h) (idx h) (diagonal fun a : Fin r => ((sgn (r - j) (a : ℕ) : ℝ) : ℂ)) = -Jpq j (r - j) := by
  have e : Jpq j (r - j) = diagonal (Sum.elim (fun _ => 1) fun _ => -1) := by
    rw [Jpq, ← fromBlocks_diagonal]; simp [← diagonal_neg]
  rw [reindex_apply, submatrix_diagonal_equiv, e, diagonal_neg]
  congr 1
  funext a
  rcases a with a | a
  · simp [sgn, idx_symm_inl]
  · simp [sgn, idx_symm_inr]

omit [NumberField E] [IsCMField E] in
theorem gram_eq_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    (gram τ G x)ᵀ = xᴴ * (G.map τ)ᵀ * x := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, transpose_apply, of_apply, mul_apply, conjTranspose_apply, map_apply,
    Finset.sum_mul, RCLike.star_def]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

variable (X : Data E r) {j : ℕ} (hj : j ≤ r) {Tau : Type} (ι : Tau → X.Ψ)

theorem det_x0F (τ : X.Ψ) : (mat (x0F X) τ).det ≠ 0 := (X.signature τ).choose_spec.1

def frameCo (x : Frame X.Ψ r) (τ : X.Ψ) : Matrix (Fin j ⊕ Fin (r - j)) (Fin j ⊕ Fin (r - j)) ℂ :=
  reindex (idx hj) (idx hj) ((mat (x0F X) τ)⁻¹ * mat x τ)

def baseGL (τ : X.Ψ) : GL (Fin j ⊕ Fin (r - j)) ℂ :=
  GeneralLinearGroup.mkOfDetNeZero (reindex (idx hj) (idx hj) (mat (x0F X) τ))
    (by rw [det_reindex_self]; exact det_x0F X τ)

def toUpq : GL (Fin r) E →* (Tau → GL (Fin j ⊕ Fin (r - j)) ℂ) :=
  embI (fun t => (ι t).1) (fun _ => idx hj) fun t => baseGL X hj (ι t)

theorem toUpq_val (γ : GL (Fin r) E) (t : Tau) :
    (toUpq X hj ι γ t).1 = frameCo X hj (lact γ (x0F X)) (ι t) := by
  show ((baseGL X hj (ι t))⁻¹).1 * reindex (idx hj) (idx hj) (γ.1.map (ι t).1) * ((baseGL X hj (ι t))⁻¹⁻¹).1 = _
  rw [inv_inv, coe_units_inv]
  show (reindex (idx hj) (idx hj) (mat (x0F X) (ι t)))⁻¹ * _ * reindex (idx hj) (idx hj) (mat (x0F X) (ι t)) = _
  rw [inv_reindex]
  simp only [frameCo, reindex_apply, submatrix_mul_equiv, Matrix.mul_assoc]
  rfl

def gammaU : Subgroup (Tau → GL (Fin j ⊕ Fin (r - j)) ℂ) := X.Γ.map (toUpq X hj ι)

theorem frameCo_orth (hp : X.p0 = r - j) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) :
    (frameCo X hj x τ)ᴴ * Jpq j (r - j) * frameCo X hj x τ = Jpq j (r - j) := by
  have h0 := congrArg transpose (isOrth_x0F X τ)
  have h1 := congrArg transpose (hx τ)
  rw [gram_eq_mul, diagonal_transpose, hp] at h0 h1
  set M := (mat (x0F X) τ)⁻¹ * mat x τ with hM
  have e : mat x τ = mat (x0F X) τ * M := by
    rw [hM, mul_nonsing_inv_cancel_left _ _ (det_x0F X τ).isUnit]
  have h2 : Mᴴ * (diagonal fun a : Fin r => ((sgn (r - j) (a : ℕ) : ℝ) : ℂ)) * M =
      diagonal fun a : Fin r => ((sgn (r - j) (a : ℕ) : ℝ) : ℂ) := by
    conv_rhs => rw [← h1, e]
    rw [← h0]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  have h3 := congrArg (reindex (idx hj) (idx hj)) h2
  have h4 := reindex_sgn hj
  rw [h4] at h3
  rw [← neg_inj, ← h3, ← Matrix.neg_mul, ← Matrix.mul_neg, ← h4]
  simp only [frameCo, reindex_apply, conjTranspose_submatrix, submatrix_mul_equiv, ← hM]

theorem gammaU_le [Fintype Tau] (hp : X.p0 = r - j) : gammaU X hj ι ≤ UpqI Tau j (r - j) := by
  rintro _ ⟨γ, hγ, rfl⟩ t -
  refine upq_iff.2 ?_
  rw [toUpq_val]
  exact frameCo_orth X hj hp (KU.isOrth_lact X hγ (isOrth_x0F X)) _

def domPt (x : Frame X.Ψ r) : Pt Tau j (r - j) := fun t => moeb (frameCo X hj x (ι t)) 0

theorem moeb_zero {p q : ℕ} (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    moeb g 0 = g.toBlocks₁₂ * g.toBlocks₂₂⁻¹ := by simp [moeb]

theorem frameCo_rmul_blocks {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (x : Frame X.Ψ r) (τ : X.Ψ) :
    ∃ B : Matrix (Fin (r - j)) (Fin (r - j)) ℂ, IsUnit B.det ∧
      (frameCo X hj (rmul x b) τ).toBlocks₁₂ = (frameCo X hj x τ).toBlocks₁₂ * B ∧
      (frameCo X hj (rmul x b) τ).toBlocks₂₂ = (frameCo X hj x τ).toBlocks₂₂ * B := by
  set B := reindex (idx hj) (idx hj) (mat b τ) with hB
  have h12 : B.toBlocks₁₂ = 0 := by
    ext a c
    refine (hb τ).2 _ _ ?_
    rw [Fin.lt_def, idx_symm_inl, idx_symm_inr]
    have := c.2; omega
  have hd : B.det ≠ 0 := by rw [hB, det_reindex_self]; exact (hb τ).1
  rw [← fromBlocks_toBlocks B, h12, det_fromBlocks_zero₁₂] at hd
  have e : frameCo X hj (rmul x b) τ = frameCo X hj x τ * B := by
    simp only [frameCo, hB, reindex_apply, submatrix_mul_equiv, Matrix.mul_assoc]
    rfl
  refine ⟨B.toBlocks₂₂, (right_ne_zero_of_mul hd).isUnit, ?_, ?_⟩ <;>
  · rw [e]
    conv_lhs => rw [← fromBlocks_toBlocks (frameCo X hj x τ), ← fromBlocks_toBlocks B, h12, fromBlocks_multiply]
    simp

theorem domPt_rmul {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (x : Frame X.Ψ r) :
    domPt X hj ι (rmul x b) = domPt X hj ι x := by
  funext t
  obtain ⟨B, hB, h1, h2⟩ := frameCo_rmul_blocks X hj hb x (ι t)
  simp only [domPt, moeb_zero]
  rw [h1, h2, Matrix.mul_inv_rev, ← Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hB]

theorem zero_mem_hcDom (p q : ℕ) : (0 : Matrix (Fin p) (Fin q) ℂ) ∈ hcDom p q := by
  simpa [hcDom] using PosDef.one

theorem exists_upq_of_orth (hp : X.p0 = r - j) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) :
    ∃ g ∈ Upq j (r - j), g.1 = frameCo X hj x τ := by
  have h := frameCo_orth X hj hp hx τ
  have hd : (frameCo X hj x τ).det ≠ 0 := by
    intro h0
    have h1 := congrArg det h
    have h2 := congrArg det (Jpq_sq (p := j) (q := r - j))
    rw [det_mul, h0, mul_zero] at h1
    rw [det_mul, ← h1] at h2
    simp at h2
  exact ⟨GeneralLinearGroup.mkOfDetNeZero _ hd, upq_iff.2 h, rfl⟩

theorem domPt_mem (hp : X.p0 = r - j) {x : Frame X.Ψ r} (hx : x ∈ X.dom) : domPt X hj ι x ∈ DomI Tau j (r - j) := by
  obtain ⟨x1, h1, b, hb, rfl⟩ := ortho_holds r X x hx
  rw [domPt_rmul X hj ι hb]
  intro t
  obtain ⟨g, hg, e⟩ := exists_upq_of_orth X hj hp h1 (ι t)
  have := moeb_mem hg (zero_mem_hcDom _ _)
  rwa [e] at this

theorem frameCo_isUnit₂₂ (hp : X.p0 = r - j) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) :
    IsUnit (frameCo X hj x τ).toBlocks₂₂.det := by
  obtain ⟨x1, h1, b, hb, rfl⟩ := ortho_holds r X x hx
  obtain ⟨B, hB, -, h2⟩ := frameCo_rmul_blocks X hj hb x1 τ
  obtain ⟨g, hg, e⟩ := exists_upq_of_orth X hj hp h1 τ
  have := kapQ_isUnit hg (zero_mem_hcDom _ _)
  rw [kapQ, Matrix.mul_zero, zero_add, e] at this
  rw [h2, det_mul]
  exact this.mul hB

theorem domPt_lact [Fintype Tau] (hp : X.p0 = r - j) (γ : GL (Fin r) E) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    domPt X hj ι (lact γ x) = moebI (toUpq X hj ι γ) (domPt X hj ι x) := by
  funext t
  have hu := frameCo_isUnit₂₂ X hj hp hx (ι t)
  have e : frameCo X hj (lact γ x) (ι t) = (toUpq X hj ι γ t).1 * frameCo X hj x (ι t) := by
    rw [toUpq_val]
    simp only [frameCo, reindex_apply, submatrix_mul_equiv]
    congr 1
    show _ * (γ.1.map (ι t).1 * mat x (ι t)) = _ * (γ.1.map (ι t).1 * mat (x0F X) (ι t)) * _
    simp only [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ (det_x0F X (ι t)).isUnit]
  simp only [domPt, moebI, moeb_zero]
  rw [e]
  set g := (toUpq X hj ι γ t).1
  set f := frameCo X hj x (ι t)
  have e1 : (g * f).toBlocks₁₂ = (g.toBlocks₁₁ * (f.toBlocks₁₂ * f.toBlocks₂₂⁻¹) + g.toBlocks₁₂) * f.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks g, ← fromBlocks_toBlocks f, fromBlocks_multiply]
    simp [Matrix.add_mul, Matrix.mul_assoc, nonsing_inv_mul _ hu]
  have e2 : (g * f).toBlocks₂₂ = (g.toBlocks₂₁ * (f.toBlocks₁₂ * f.toBlocks₂₂⁻¹) + g.toBlocks₂₂) * f.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks g, ← fromBlocks_toBlocks f, fromBlocks_multiply]
    simp [Matrix.add_mul, Matrix.mul_assoc, nonsing_inv_mul _ hu]
  rw [e1, e2, Matrix.mul_inv_rev, ← Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hu, moeb]

def hodgeC (t : Tau) : ℝ := Real.pi * X.c (ι t)

theorem hodgeC_pos (t : Tau) : 0 < hodgeC X ι t :=
  mul_pos Real.pi_pos (mul_pos two_pos (norm_pos_iff.2 ((map_ne_zero _).2 X.ξ0_ne)))

theorem psi_nonempty : Nonempty X.Ψ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases h : τ ∈ X.Ψ
  · exact ⟨⟨τ, h⟩⟩
  · exact ⟨⟨ComplexEmbedding.conjugate τ, by_contra fun h' => h ((X.cmType τ).2 h')⟩⟩

theorem sum_nonempty {r j : ℕ} (hj : j ≤ r) (hr : 0 < r) : Nonempty (Fin j ⊕ Fin (r - j)) := ⟨idx hj ⟨0, hr⟩⟩

section Models

variable {Comp : Type} [Fintype Comp] [Fintype Tau] (Y : Comp → Data E r) (hr : 0 < r)
  (hp : ∀ k, (Y k).p0 = r - j) (κ : ∀ k, Tau ≃ (Y k).Ψ)
  (B : ∀ k, BdData Tau j (r - j) (gammaU (Y k) hj (κ k))) (s : Comp → Tau → ℂˣ)

def cxOfModels : CxPkg Tau r j Comp where
  Γ := fun k => gammaU (Y k) hj (κ k)
  Γ_le := fun k => gammaU_le (Y k) hj (κ k) (hp k)
  volC := fun k => covol (Y k)
  volC_pos := fun k => covol_pos (Y k)
  rfn := fun z => onQuot (B z.1).r z.2
  rfn_ge := fun z => (B z.1).exp_le_r (Quot.out z.2).2
  hLo := fun z => onQuot (fun w => eigLo (hodgeI (hodgeC (Y z.1) (κ z.1)) w) ((B z.1).met w)) z.2
  hUp := fun z => onQuot (fun w => eigUp (hodgeI (hodgeC (Y z.1) (κ z.1)) w) ((B z.1).met w)) z.2
  hLo_le := fun z =>
    haveI : Nonempty Tau := (psi_nonempty (Y z.1)).map (κ z.1).symm
    haveI := sum_nonempty hj hr
    eigLo_pos (fun t => hodge_posDef (hodgeC_pos _ _ t) ((Quot.out z.2).2 t)) ((B z.1).met_posDef (Quot.out z.2).2)
  connN := fun z => onQuot (connNorm (hodgeI (hodgeC (Y z.1) (κ z.1))) (B z.1).met (B z.1).beta) z.2
  curvN := fun z => onQuot (curvNorm (hodgeI (hodgeC (Y z.1) (κ z.1))) (B z.1).beta) z.2
  normDetInf := fun t z => onQuot
    (fun w => detNorm (hodgeC (Y z.1) (κ z.1)) ((s z.1 t : ℂ) / (mat (x0F (Y z.1)) (κ z.1 t)).det) w t) z.2

def ptOfFrame (k : Comp) (x : (Y k).dom) : (cxOfModels hj Y hr hp κ B s).XC :=
  ⟨k, Quot.mk _ ⟨domPt (Y k) hj (κ k) x, domPt_mem (Y k) hj (κ k) (hp k) x.2⟩⟩

theorem ptOfFrame_eq (k : Comp) (x x' : (Y k).dom) {γ : GL (Fin r) E} (hγ : γ ∈ (Y k).Γ) {b : Frame (Y k).Ψ r}
    (hb : b ∈ Bor (Y k).Ψ r) (e : x'.1 = rmul (lact γ x.1) b) :
    ptOfFrame hj Y hr hp κ B s k x = ptOfFrame hj Y hr hp κ B s k x' := by
  refine congrArg (Sigma.mk k) (Quot.sound ⟨_, ⟨γ, hγ, rfl⟩, ?_⟩)
  show moebI _ (domPt (Y k) hj (κ k) x) = domPt (Y k) hj (κ k) x'
  rw [e, domPt_rmul _ _ _ hb, domPt_lact _ _ _ (hp k) _ x.2]

def invariantB (k : Comp) : BdData Tau j (r - j) (gammaU (Y k) hj (κ k)) :=
  invariantData (gammaU_le (Y k) hj (κ k) (hp k)) (hodgeC (Y k) (κ k)) (hodgeC_pos _ _)

end Models

section Moduli

open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.PjFree

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}
  (U : Unf Xo c σ r) (hU : IsUnf U) (e : Dw.p = j)

include hU e in
theorem le_of_isUnf : j ≤ r := by have := hU.1; omega

include hU e in
theorem first_index_eq_of_unfolded (k : U.Comp) : (U.X k).p0 = r - j := by
  have := hU.1; have := (hU.2.1 k).1; omega

def cmEquiv (T : Tau ≃ {τ : E →+* ℂ // τ (H.rt : E) = H.rt0}) (k : U.Comp) : Tau ≃ (U.X k).Ψ :=
  T.trans (Equiv.subtypeEquivRight fun τ => ((hU.2.1 k).2 τ).symm)

def letterAt (hσ : GoodEmb c σ) :
    {τ : E →+* ℂ // τ (H.rt : E) = H.rt0} ≃ {τ : E →+* ℂ // τ (H.rt : E) = H.rt0} :=
  (Equiv.ofBijective _ (GlobalTheory.Relab.relab_good E H l c σ hσ).1).subtypeEquiv
    fun τ => ((GlobalTheory.Relab.relab_good E H l c σ hσ).2.1 τ).symm

variable [Fintype Tau] (hr : 0 < r) (T : Tau ≃ {τ : E →+* ℂ // τ (H.rt : E) = H.rt0})
  (B : ∀ k, BdData Tau j (r - j) (gammaU (U.X k) (le_of_isUnf U hU e) (cmEquiv U hU T k))) (s : U.Comp → Tau → ℂˣ)

def cxTrue : CxPkg Tau r j U.Comp :=
  cxOfModels (le_of_isUnf U hU e) U.X hr (first_index_eq_of_unfolded U hU e) (cmEquiv U hU T) B s

theorem ptOfFrame_eq_of_frBor {k k' : U.Comp} (x : (U.X k).dom) (x' : (U.X k').dom)
    (h : ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (U.un k x) (U.un k' x')) :
    ptOfFrame (le_of_isUnf U hU e) U.X hr (first_index_eq_of_unfolded U hU e) (cmEquiv U hU T) B s k x =
      ptOfFrame (le_of_isUnf U hU e) U.X hr (first_index_eq_of_unfolded U hU e) (cmEquiv U hU T) B s k' x' := by
  obtain ⟨γ, hγ, b, hb, h1⟩ := (hU.2.2.2.1 k k' x x').1 h
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj h1
  exact ptOfFrame_eq _ _ _ _ _ _ _ _ x x' hγ hb (eq_of_heq h2)

end Moduli

end GlobalTheory.TrueCx
