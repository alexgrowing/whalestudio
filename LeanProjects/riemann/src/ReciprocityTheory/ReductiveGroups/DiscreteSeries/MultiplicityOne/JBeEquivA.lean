import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.UHMulInv

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

theorem measurable_rmul_mt (a : Mat k r) :
    @Measurable (Mt k r) (Mt k r) _ _ (fun x => (Matrix.of x * a : Mat k r)) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem measurable_lmul_mt (a : Mat k r) :
    @Measurable (Mt k r) (Mt k r) _ _ (fun x => (a * Matrix.of x : Mat k r)) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem sigmaFinite_of_haarOn {U : Set (Mat k r)} {μ : Measure (Mt k r)} (hH : IsHaarOn U μ) : SigmaFinite μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => hH.finite_compact K hK⟩
  infer_instance

theorem ae_mem_of_haarOn {U : Set (Mat k r)} {μ : Measure (Mt k r)} (hH : IsHaarOn U μ) :
    ∀ᵐ x ∂μ, (Matrix.of x : Mat k r) ∈ U := ae_iff.mpr hH.conc

theorem inner_sig_move (X : SigData k r) (g : Mat k r) (hg : g ∈ GV k r) (hgi : g⁻¹ ∈ GV k r)
    (hgg : g * g⁻¹ = 1) (a b : X.Hs) : ⟪X.σ g a, b⟫_ℂ = ⟪a, X.σ g⁻¹ b⟫_ℂ := by
  obtain ⟨h1, h2⟩ := X.rep.1
  have hσ : X.σ g (X.σ g⁻¹ b) = b := by
    have h3 := h2 g hg g⁻¹ hgi
    rw [hgg, h1] at h3
    have h4 := congrArg (fun L => L b) h3
    simpa using h4.symm
  let L : X.Hs →ₗᵢ[ℂ] X.Hs := ⟨(X.σ g : X.Hs →ₗ[ℂ] X.Hs), fun v => X.rep.2.1 g hg v⟩
  calc ⟪X.σ g a, b⟫_ℂ = ⟪L a, L (X.σ g⁻¹ b)⟫_ℂ := by rw [show L (X.σ g⁻¹ b) = b from hσ]; rfl
    _ = ⟪a, X.σ g⁻¹ b⟫_ℂ := L.inner_map_map a _

theorem psiD_norm {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) (m : Mat k r) :
    ‖psiD D m‖ = 1 := by
  unfold psiD psi
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem psiD_star_mul {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) (m : Mat k r) :
    star (psiD D m) * psiD D m = 1 := by
  rw [Complex.star_def, Complex.conj_mul', psiD_norm]
  simp

end ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

theorem gv_mul {a b : Mat k r} (ha : a ∈ GV k r) (hb : b ∈ GV k r) : a * b ∈ GV k r := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

private theorem hpk_sq_lemma : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single
    (⟨if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val, by split_ifs <;> omega⟩ :
      Fin (2 * r + k + 1))]
  · simp only [Hpk, Matrix.one_apply, Fin.ext_iff, Fin.val_mk]
    split_ifs <;> first | (norm_num; done) | omega
  · intro l _ hl
    rw [Ne, Fin.ext_iff] at hl
    simp only [Hpk, Fin.ext_iff, Fin.val_mk] at hl ⊢
    split_ifs at hl ⊢ <;> first | (simp; done) | omega
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem isUnit_det_of_mem_GV' {a : Mat k r} (ha : a ∈ GV k r) : IsUnit a.det := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have h1 : (Hpk k r * aᴴ * Hpk k r) * a = 1 := by
    calc (Hpk k r * aᴴ * Hpk k r) * a = Hpk k r * (aᴴ * Hpk k r * a) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [ha', hpk_sq_lemma]
  exact Matrix.isUnit_det_of_left_inverse h1

theorem gv_inv {a : Mat k r} (ha : a ∈ GV k r) : a⁻¹ ∈ GV k r := by
  have h1 : a * a⁻¹ = 1 := ReciprocityTheory.ChartRestriction.DS.Xi.StepA.UH_mul_inv k r ha
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  show (a⁻¹)ᴴ * Hpk k r * a⁻¹ = Hpk k r
  calc (a⁻¹)ᴴ * Hpk k r * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * Hpk k r * a) * a⁻¹ := by rw [ha']
    _ = (a * a⁻¹)ᴴ * Hpk k r * (a * a⁻¹) := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [h1]; simp

theorem gv_inv_mul {a : Mat k r} (ha : a ∈ GV k r) : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul a (isUnit_det_of_mem_GV' ha)

theorem gv_mul_inv {a : Mat k r} (ha : a ∈ GV k r) : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a (isUnit_det_of_mem_GV' ha)

theorem gv_inv_inv {a : Mat k r} (ha : a ∈ GV k r) : a⁻¹⁻¹ = a := Matrix.nonsing_inv_nonsing_inv a (isUnit_det_of_mem_GV' ha)

theorem fix_inv {a : Mat k r} (ha : a ∈ GV k r) {v : Fin (2 * r + k + 1) → ℂ} (hv : a *ᵥ v = v) :
    a⁻¹ *ᵥ v = v := by
  calc a⁻¹ *ᵥ v = a⁻¹ *ᵥ (a *ᵥ v) := by rw [hv]
    _ = v := by rw [Matrix.mulVec_mulVec, gv_inv_mul ha, Matrix.one_mulVec]

theorem uw_inv {z : Fin (2 * r + k + 1) → ℂ} {a : Mat k r} (ha : a ∈ UWset k r z) : a⁻¹ ∈ UWset k r z := by
  simp only [UWset, Set.mem_setOf_eq] at ha ⊢
  obtain ⟨ha1, ha2, ha3⟩ := ha
  exact ⟨gv_inv ha1, fun i => ⟨fix_inv ha1 (ha2 i).1, fix_inv ha1 (ha2 i).2⟩, fix_inv ha1 ha3⟩

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

structure BEFacts (D : RealPlaceData k r Wp Wp) : Prop where
  nmul : ∀ a ∈ Nset k r, ∀ b ∈ Nset k r, a * b ∈ Nset k r
  ninv : ∀ a ∈ Nset k r, a⁻¹ ∈ Nset k r
  nrm : ∀ h ∈ UWset k r D.z, ∀ m ∈ Nset k r, h * m * h⁻¹ ∈ Nset k r ∧ psiD D (h * m * h⁻¹) = psiD D m
  pmul : ∀ a ∈ Nset k r, ∀ b ∈ Nset k r, psiD D (a * b) = psiD D a * psiD D b
  conj : ∀ h ∈ UWset k r D.z, D.μN.map (conjM h) = D.μN

theorem beFacts_of (h : UnitaryGroupStructuralFacts) (D : RealPlaceData k r Wp Wp) : BEFacts D := by
  obtain ⟨hB2, hBS, hR1, hBC, hUWb, hCH, hLB, hJ, hPh, hRB, hRA, hUn, hAe, hDJ, hIN, hUWN, hEll, hNS⟩ := h
  refine ⟨fun a ha b hb => (hNS k r).2.1 a ha b hb, fun a ha => (hNS k r).2.2 a ha, ?_, ?_, ?_⟩
  · intro g hg m hm
    obtain ⟨hmem, hell⟩ := hUWN k r D.z D.z_mem g hg m hm
    refine ⟨hmem, ?_⟩
    simp only [psiD, psi, hell]
  · intro a ha b hb
    simp only [psiD, psi, hEll k r D.z D.z_mem a ha b hb, mul_add, Complex.add_re, Complex.ofReal_add,
      Complex.exp_add]
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hCI, _⟩ := hB2
    have hc := hCI k r Wp Wp D
    exact fun g hg => hc g (Set.mem_union_left _ hg)

end ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv
