import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.NrmContPf
import Formalism.LocalToGlobal.ProjectiveLattices.AxHSup
import Formalism.LocalToGlobal.ProjectiveLattices.DivFinOfLawA3
import Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaPointsChangeLevelIsometryLinearMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSecGeneratorFibre
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi MeasureTheory
open scoped Matrix

noncomputable section

namespace GlobalTheory.UnitFrameGen

theorem eq_of_norm_periodic {g : ℕ} (Λ : AddSubgroup (Fin g → ℂ))
    (hΛ : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (ρ : (Fin g → ℂ) → ℂ) (hρ : Differentiable ℂ ρ)
    (hp : ∀ a ∈ Λ, ∀ z, ‖ρ (z + a)‖ = ‖ρ z‖) (z w : Fin g → ℂ) : ρ z = ρ w := by
  let b := Module.Basis.ofSpan hΛ.ge
  have hb : Set.range b ⊆ Λ := Module.Basis.ofSpan_subset _
  haveI := FiniteDimensional.fintypeBasisIndex b
  have hs : Submodule.span ℤ (Set.range b) ≤ Λ.toIntSubmodule := Submodule.span_le.2 hb
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Fin g → ℂ) (∑ i, ‖b i‖)).exists_bound_of_continuousOn
    hρ.continuous.continuousOn
  refine hρ.apply_eq_apply_of_bounded (isBounded_iff_forall_norm_le.2 ⟨C, ?_⟩) z w
  rintro _ ⟨y, rfl⟩
  have h1 : y = ZSpan.fract b y + (ZSpan.floor b y : Fin g → ℂ) := by rw [ZSpan.fract_apply]; abel
  rw [h1, hp _ (hs (ZSpan.floor b y).2)]
  exact hC _ (mem_closedBall_zero_iff.2 (ZSpan.norm_fract_le b y))

theorem hermForm_add_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := by
  simp only [hermForm, add_dotProduct]

theorem hermForm_add_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := by
  simp only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add]

theorem hermForm_smul_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm (a • z) w = a * hermForm Hm z w := by
  simp only [hermForm, smul_dotProduct, smul_eq_mul]

theorem hermForm_smul_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm z (a • w) = star a * hermForm Hm z w := by
  simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hermForm_swap_re {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) (z w : Fin g → ℂ) :
    (hermForm Hm w z).re = (hermForm Hm z w).re := by
  have : hermForm Hm w z = star (hermForm Hm z w) := by
    simp only [hermForm, dotProduct, Matrix.mulVec, star_sum, star_mul', Pi.star_apply, star_star, h.apply,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [this]
  exact Complex.conj_re _

theorem hermForm_eq_of_im {g : ℕ} (S : Set (Fin g → ℂ)) (hS : Submodule.span ℝ S = ⊤)
    (Hm Hm' h : Matrix (Fin g) (Fin g) ℂ)
    (him : ∀ a ∈ S, ∀ b ∈ S, (hermForm Hm' (h *ᵥ a) (h *ᵥ b)).im = (hermForm Hm a b).im) (z w : Fin g → ℂ) :
    hermForm Hm' (h *ᵥ z) (h *ᵥ w) = hermForm Hm z w := by
  have key : ∀ z w, (hermForm Hm' (h *ᵥ z) (h *ᵥ w)).im = (hermForm Hm z w).im := fun z w => by
    have hz : z ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
    have hw : w ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem a ha =>
      induction hw using Submodule.span_induction with
      | mem b hb => exact him a ha b hb
      | zero => simp [hermForm]
      | add x y _ _ h1 h2 => simp only [Matrix.mulVec_add, hermForm_add_right, Complex.add_im, h1, h2]
      | smul r x _ h1 =>
        rw [← Complex.coe_smul, Matrix.mulVec_smul, hermForm_smul_right, hermForm_smul_right]
        simp [h1]
    | zero => simp [hermForm]
    | add x y _ _ h1 h2 => simp only [Matrix.mulVec_add, hermForm_add_left, Complex.add_im, h1, h2]
    | smul r x _ h1 =>
      rw [← Complex.coe_smul, Matrix.mulVec_smul, hermForm_smul_left, hermForm_smul_left]
      simp [h1]
  refine Complex.ext ?_ (key z w)
  have := key (Complex.I • z) w
  rw [Matrix.mulVec_smul, hermForm_smul_left, hermForm_smul_left] at this
  simpa using this

theorem mean_comp_eq {g : ℕ} (Λ Λ' : AddSubgroup (Fin g → ℂ)) [Countable Λ] (h : Matrix (Fin g) (Fin g) ℂ)
    (hdet : IsUnit h.det) (hΛ : ∀ z, h *ᵥ z ∈ Λ' ↔ z ∈ Λ) (Fd Fd' : Set (Fin g → ℂ))
    (hF : IsAddFundamentalDomain Λ Fd volume) (hF' : IsAddFundamentalDomain Λ' Fd' volume)
    (f : (Fin g → ℂ) → ℝ) (hf : ∀ a ∈ Λ, ∀ z, f (h *ᵥ (z + a)) = f (h *ᵥ z)) :
    (∫ z in Fd, f (h *ᵥ z)) / (volume Fd).toReal = (∫ z in Fd', f z) / (volume Fd').toReal := by
  haveI := Matrix.invertibleOfIsUnitDet h hdet
  let L : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ) := (Matrix.toLinearEquiv' h inferInstance).restrictScalars ℝ
  have hL : ∀ z, L z = h *ᵥ z := fun z => rfl
  let e : (Fin g → ℂ) ≃ᵐ (Fin g → ℂ) := L.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have he : ∀ z, e z = h *ᵥ z := fun z => rfl
  have hd : LinearMap.det (L : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)) ≠ 0 := (LinearEquiv.isUnit_det' L).ne_zero
  have hmap : Measure.map e volume = ENNReal.ofReal |(LinearMap.det (L : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)))⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hd
  have hc : 0 < |(LinearMap.det (L : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)))⁻¹| := abs_pos.2 (inv_ne_zero hd)
  generalize |(LinearMap.det (L : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)))⁻¹| = c at hmap hc
  have hq : Measure.QuasiMeasurePreserving e volume volume :=
    ⟨e.measurable, by rw [hmap]; exact Measure.smul_absolutelyContinuous⟩
  let ε : Λ' → Λ := fun a => ⟨L.symm a, (hΛ _).1 (by rw [← hL, L.apply_symm_apply]; exact a.2)⟩
  have hε : Function.Bijective ε :=
    ⟨fun a b hab => Subtype.ext (L.symm.injective (congrArg Subtype.val hab)),
      fun a => ⟨⟨L a, (hΛ _).2 a.2⟩, Subtype.ext (L.symm_apply_apply _)⟩⟩
  have hF2 : IsAddFundamentalDomain Λ (e ⁻¹' Fd') volume :=
    hF'.preimage_of_equiv hq hε fun a z => by
      change L (L.symm a + z) = a + L z
      rw [map_add, L.apply_symm_apply]
  have i1 : ∫ z in Fd, f (h *ᵥ z) = ∫ z in e ⁻¹' Fd', f (h *ᵥ z) :=
    hF.setIntegral_eq hF2 fun a z => by
      change f (h *ᵥ ((a : Fin g → ℂ) + z)) = _
      rw [add_comm, hf _ a.2]
  have i2 : ∫ z in e ⁻¹' Fd', f (h *ᵥ z) = c * ∫ z in Fd', f z := by
    have := setIntegral_map_equiv (μ := volume) e f Fd'
    rw [hmap, Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_ofReal hc.le, smul_eq_mul] at this
    exact this.symm
  have i3 : (volume Fd).toReal = c * (volume Fd').toReal := by
    rw [hF.measure_eq hF2, ← e.map_apply, hmap, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hc.le]
  rw [i1, i2, i3, mul_div_mul_left _ _ hc.ne']

theorem frames_eq {g : ℕ} {ι : Type} (Λ : AddSubgroup (Fin g → ℂ))
    (hΛ : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (O : ι → Set (Fin g → ℂ)) (ho : ∀ j, IsOpen (O j))
    (hcov : ∀ z, ∃ j, z ∈ O j) (hper : ∀ j, ∀ a ∈ Λ, ∀ z ∈ O j, z + a ∈ O j)
    (fr fr' : ι → (Fin g → ℂ) → ℂ) (c : ι → ι → (Fin g → ℂ) → ℂ) (m : (Fin g → ℂ) → (Fin g → ℂ) → ℝ)
    (hd : ∀ j, DifferentiableOn ℂ (fr j) (O j)) (hd' : ∀ j, DifferentiableOn ℂ (fr' j) (O j))
    (hn : ∀ j, ∀ z ∈ O j, fr j z ≠ 0)
    (hc : ∀ j j' z, z ∈ O j → z ∈ O j' → fr j z = c j j' z * fr j' z)
    (hc' : ∀ j j' z, z ∈ O j → z ∈ O j' → fr' j z = c j j' z * fr' j' z)
    (h0 : ∀ j, 0 ∈ O j → fr' j 0 = fr j 0)
    (hm : ∀ j, ∀ a ∈ Λ, ∀ z ∈ O j, ‖fr j z‖ = m a z * ‖fr j (z + a)‖)
    (hm' : ∀ j, ∀ a ∈ Λ, ∀ z ∈ O j, ‖fr' j z‖ = m a z * ‖fr' j (z + a)‖) :
    ∀ j, ∀ z ∈ O j, fr' j z = fr j z := by
  choose J hJ using hcov
  obtain ⟨ρ, hρ⟩ : ∃ ρ : (Fin g → ℂ) → ℂ, ∀ j, ∀ z ∈ O j, fr' j z = ρ z * fr j z :=
    ⟨fun z => fr' (J z) z / fr (J z) z, fun j z h => by
      have := hn _ _ (hJ z)
      rw [hc j (J z) z h (hJ z), hc' j (J z) z h (hJ z)]
      field_simp⟩
  have hdρ : Differentiable ℂ ρ := fun z => by
    have d3 := ((hd' (J z)).mul ((hd (J z)).inv (hn _))).congr (f₁ := ρ) (fun z' h => by
      have := hn _ _ h
      show ρ z' = fr' (J z) z' * (fr (J z) z')⁻¹
      rw [hρ _ _ h]; field_simp)
    exact d3.differentiableAt ((ho _).mem_nhds (hJ z))
  have h1 : ρ 0 = 1 := by
    have e := hρ _ _ (hJ 0)
    rw [h0 _ (hJ 0)] at e
    exact (mul_eq_right₀ (hn _ _ (hJ 0))).1 e.symm
  have hp : ∀ a ∈ Λ, ∀ z, ‖ρ (z + a)‖ = ‖ρ z‖ := fun a ha z => by
    have e1 := hm _ a ha z (hJ z)
    have e2 := hm' _ a ha z (hJ z)
    rw [hρ _ _ (hJ z), hρ _ _ (hper _ a ha z (hJ z)), norm_mul, norm_mul] at e2
    apply mul_right_cancel₀ (norm_ne_zero_iff.2 (hn _ _ (hJ z)))
    rw [e2, e1]; ring
  intro j z hz
  rw [hρ j z hz, eq_of_norm_periodic Λ hΛ ρ hdρ hp z 0, h1, one_mul]

theorem norm_factor {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (χ u v : ℂ) (z a : Fin g → ℂ) (hχ : ‖χ‖ = 1)
    (h : u = χ * Complex.exp (Real.pi * hermForm Hm z a + Real.pi / 2 * hermForm Hm a a) * v) :
    ‖u‖ = Real.exp (Real.pi * (hermForm Hm z a).re + Real.pi / 2 * (hermForm Hm a a).re) * ‖v‖ := by
  rw [h, norm_mul, norm_mul, hχ, one_mul, Complex.norm_exp]
  congr 2
  have : (Real.pi : ℂ) / 2 = ((Real.pi / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]

theorem normSq_periodic {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (θ θ' u v : ℂ)
    (z a : Fin g → ℂ) (hv : v ≠ 0) (e : θ' * v = θ * u)
    (h : ‖u‖ = Real.exp (Real.pi * (hermForm Hm z a).re + Real.pi / 2 * (hermForm Hm a a).re) * ‖v‖) :
    ‖θ'‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm (z + a) (z + a)).re) =
      ‖θ‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re) := by
  have e1 : ‖θ'‖ = ‖θ‖ * Real.exp (Real.pi * (hermForm Hm z a).re + Real.pi / 2 * (hermForm Hm a a).re) := by
    apply mul_right_cancel₀ (norm_ne_zero_iff.2 hv)
    rw [← norm_mul, e, norm_mul, h, mul_assoc]
  rw [e1, mul_pow, mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 2
  simp only [hermForm_add_left, hermForm_add_right, Complex.add_re, hermForm_swap_re hH z a]
  push_cast; ring

theorem cabs_gen_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ k k' (x : (U.X k).dom) (x' : (U.X k').dom) (t : Ix Dw → (CAt σ)ˣ), IsUnitFr (U.X k) x.1 → IsUnitFr (U.X k') x'.1 → FrBor t (U.un k x) (U.un k' x') → cabs (t none : CAt σ) = 1 := by
  intro E _ _ _ H Dw l Xo c σ r U _ hU k k' x x' t hx hx' hb
  obtain ⟨-, -, -, h4, -, g, e, F, ik, φ, -, hP⟩ := hU
  obtain ⟨γ, -, b, -, hk⟩ := (h4 k k' x x').1 ⟨t, hb⟩
  obtain rfl : k' = k := congrArg Sigma.fst hk
  clear hk h4
  obtain ⟨P, -, hp, hu, -, hA⟩ := hP k' x
  obtain ⟨P', -, hp', hu', -, hA'⟩ := hP k' x'
  obtain ⟨Hm, χ, fr, θ, Fd, hH, -, him, hd, hn, hc, h0, ha, hv, hF, hI⟩ := hA hx
  obtain ⟨Hm', χ', fr', θ', Fd', hH', -, him', hd', hn', hc', h0', ha', hv', hF', hI'⟩ := hA' hx'
  clear hA hA' hP
  obtain ⟨hxx, -, hbc⟩ := hb
  generalize ik k' = i at *
  obtain ⟨gam, hl, hg1, hg2, hg3, hg4⟩ := (F.fibre i P P' hp hp').1 (hu.symm.trans (hxx.symm.trans hu'))
  obtain ⟨h, hg⟩ : ∃ h : Matrix (Fin g) (Fin g) ℂ, ∀ a, P' (gam a) = h *ᵥ P a :=
    ⟨LinearMap.toMatrix' hl.toLinearMap, fun a => by rw [hg4, LinearMap.toMatrix'_mulVec]; rfl⟩
  obtain ⟨hdet, -, hex⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ g _ F i
    P P' gam h hp hp' hg1 hg2 hg3 hg
  have hspan : Submodule.span ℝ (P.range : Set (Fin g → ℂ)) = ⊤ := by
    rw [AddMonoidHom.coe_range]; exact hp.2.2.2.1
  have hHH : ∀ z w, hermForm Hm' (h *ᵥ z) (h *ᵥ w) = hermForm Hm z w :=
    hermForm_eq_of_im _ hspan Hm Hm' h (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← hg, ← hg, him, him', hg1])
  have hexp : ∀ a ∈ P.range, ∀ z, F.ex i P (z + a) = F.ex i P z := fun a ha z => by
    rw [F.ex_add i P hp, (F.ex_ker i P hp a).2 ha]
    exact @_root_.mul_one _ (CategoryTheory.Hom.monoid).toMulOneClass _
  have hcov : ∀ z, ∃ j, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun z =>
    GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB _
  have tr : ∀ j z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      ⊤ ≤ (F.ex i P' (h *ᵥ z)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun j z hz => by rw [hex]; exact hz
  have hm : ∀ j, ∀ a ∈ P.range, ∀ z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → ‖fr j z‖ =
      Real.exp (Real.pi * (hermForm Hm z a).re + Real.pi / 2 * (hermForm Hm a a).re) * ‖fr j (z + a)‖ := by
    rintro j _ ⟨a, rfl⟩ z hz
    exact norm_factor Hm _ _ _ _ _ (ha a j z).1 ((ha a j z).2 hz)
  have dl : Differentiable ℂ (fun z' : Fin g → ℂ => h *ᵥ z') :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin h)).differentiable
  have hfr : ∀ j z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr' j (h *ᵥ z) = fr j z :=
    frames_eq P.range hspan (fun j => {z | ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j})
      (fun j => GlobalTheory.FamilyUnif_isOpen_ex F i P hp _) hcov
      (fun j a ha z hz => by rw [Set.mem_setOf_eq, hexp a ha]; exact hz)
      fr (fun j z => fr' j (h *ᵥ z))
      (fun j j' z => valAt' (F.ex i P z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val)
      (fun a z => Real.exp (Real.pi * (hermForm Hm z a).re + Real.pi / 2 * (hermForm Hm a a).re))
      hd (fun j => (hd' j).comp dl.differentiableOn fun z hz => tr j z hz) hn
      (fun j j' z h1 h2 => hc j j' z ((top_le_preimage_inf _ _ _).2 ⟨h1, h2⟩))
      (fun j j' z h1 h2 => by
        have e2 := hc' j j' (h *ᵥ z) ((top_le_preimage_inf _ _ _).2 ⟨tr _ _ h1, tr _ _ h2⟩)
        rw [hex] at e2
        exact e2)
      (fun j hz => by
        have t0 := tr j 0 hz
        simp only [Matrix.mulVec_zero] at t0 ⊢
        rw [h0 j hz, h0' j t0, hxx])
      hm (by
        rintro j _ ⟨a, rfl⟩ z hz
        have := norm_factor Hm' _ _ _ _ _ (ha' (gam a) j (h *ᵥ z)).1 ((ha' (gam a) j (h *ᵥ z)).2 (tr j z hz))
        rw [hg, hHH, hHH, ← Matrix.mulVec_add] at this
        exact this)
  have hS : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hw0 : ∀ z, (F.ex i P z).left ≫ Xo.univ.t.G.hom = ((U.un k' x).x : Sp ℂ ⟶ Xo.X) := fun z =>
    (Over.w (F.ex i P z)).trans hu.symm
  have hid : spMap (RingHom.id ℂ) = 𝟙 _ := by simp [spMap]
  have hbc' : GlobalTheory.Frames.SecBC (RingHom.id ℂ) (Formalism.L2.PjFree.toC (t none : CAt σ)) (U.un k' x).x (U.un k' x').x
      (U.un k' x).s (U.un k' x').s := by
    obtain ⟨pm, p1, p2, p3⟩ := hbc
    exact ⟨pm, p1, by rw [hid]; exact p2.trans (Category.comp_id _).symm, p3⟩
  have hθ : ∀ z, θ' (h *ᵥ z) = Formalism.L2.PjFree.toC (t none : CAt σ) * θ z := fun z => by
    obtain ⟨j, hj⟩ := hcov z
    have hval := GlobalTheory.ThetaPtChg.val_of_secBC hS (Xo := Xo) _ _ hxx _ _ _ hbc'
      (Over.homMk (F.ex i P z).left (hw0 z)) j _ _
      (fun pt h1 h2 => hv j z pt h1 h2 hj)
      (fun pt h1 h2 => hv' j (h *ᵥ z) pt (h1.trans (hex z).symm) h2 (tr j z hj))
    rw [hfr j z hj, ← mul_assoc] at hval
    exact mul_right_cancel₀ (hn j z hj) hval
  have hθp : ∀ a ∈ P.range, ∀ z, ‖θ (z + a)‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm (z + a) (z + a)).re) =
      ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re) := fun a ha z => by
    obtain ⟨j, hj⟩ := hcov z
    have hj' : ⊤ ≤ (F.ex i P (z + a)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by rw [hexp a ha]; exact hj
    let p : Over.mk ((U.un k' x).x : Sp ℂ ⟶ Xo.X) ⟶ Xo.univ.t.G := Over.homMk (F.ex i P z).left (hw0 z)
    have e1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 _) p)
    have e2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 _) p)
    have v1 := hv j z _ e1 e2 hj
    have v2 := hv j (z + a) _ (by rw [hexp a ha]; exact e1) e2 hj'
    exact normSq_periodic hH _ _ _ _ z a (hn j _ hj') (v2.symm.trans v1) (hm j a ha z hj)
  haveI : Countable P.range := by
    haveI := hp.2.2.1
    exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hinj : Function.Injective (fun z : Fin g → ℂ => h *ᵥ z) :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det h).2 hdet)
  have key : ∀ z, ‖θ' (h *ᵥ z)‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm' (h *ᵥ z) (h *ᵥ z)).re) =
      ‖Formalism.L2.PjFree.toC (t none : CAt σ)‖ ^ 2 * (‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) :=
    fun z => by rw [hθ, hHH, norm_mul, mul_pow, mul_assoc]
  have hmean := mean_comp_eq P.range P'.range h hdet (fun z => ⟨?_, ?_⟩) Fd Fd' hF hF'
    (fun z => ‖θ' z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm' z z).re))
    (fun a ha z => by simp only [key, hθp a ha z])
  · simp only [key] at hmean
    rw [hI', integral_const_mul, mul_div_assoc, hI, mul_one] at hmean
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hmean
  · rintro ⟨a, ha⟩
    refine ⟨gam.symm a, hinj ?_⟩
    simp only
    rw [← hg, gam.apply_symm_apply, ha]
  · rintro ⟨a, rfl⟩
    exact ⟨gam a, hg a⟩

end GlobalTheory.UnitFrameGen
