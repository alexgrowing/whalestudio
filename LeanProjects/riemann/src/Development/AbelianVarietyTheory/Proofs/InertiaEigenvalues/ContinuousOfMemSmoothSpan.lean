import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumOneAddNormRpowNegLeEuclidean
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFundamentalDomainIUnion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
import GroundTheory.GlobalFields.TateThesis.GlobalZetaFinite

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.ThetaPoisson GroundTheory.Global
open scoped ComplexConjugate nonZeroDivisors

namespace GlobalTheory.RSTheta

section Row

variable {R : Type} [CommRing R] {a : ℕ}

def rowMat (ℓ : Fin a) (y : Fin a → R) : Matrix (Fin a) (Fin a) R := (1 : Matrix (Fin a) (Fin a) R).updateRow ℓ y

theorem det_rowMat (ℓ : Fin a) (y : Fin a → R) : (rowMat ℓ y).det = y ℓ := by
  have h := det_updateRow_sum (1 : Matrix (Fin a) (Fin a) R) ℓ y
  have e : ∑ k, y k • (1 : Matrix (Fin a) (Fin a) R) k = y := by
    funext j
    simp [Matrix.one_apply, Finset.sum_apply]
  rw [e] at h
  simpa [rowMat] using h

theorem isUnit_rowMat_iff {ℓ : Fin a} {y : Fin a → R} : IsUnit (rowMat ℓ y) ↔ IsUnit (y ℓ) := by
  rw [isUnit_iff_isUnit_det, det_rowMat]

open Classical in

def rowGL (ℓ : Fin a) (y : Fin a → R) : GL (Fin a) R :=
  if h : IsUnit (y ℓ) then (isUnit_rowMat_iff.2 h).unit else 1

theorem val_rowGL {ℓ : Fin a} {y : Fin a → R} (h : IsUnit (y ℓ)) : (rowGL ℓ y).val = rowMat ℓ y := by
  rw [rowGL, dif_pos h, IsUnit.unit_spec]

theorem single_vecMul_rowGL {ℓ : Fin a} {y : Fin a → R} (h : IsUnit (y ℓ)) :
    Pi.single ℓ 1 ᵥ* (rowGL ℓ y).val = y := by
  rw [val_rowGL h, single_one_vecMul]
  exact updateRow_self

theorem rowGL_single (ℓ : Fin a) : rowGL ℓ (Pi.single ℓ (1 : R)) = 1 := by
  refine Units.ext ((val_rowGL (by simp)).trans ?_)
  have : (Pi.single ℓ 1 : Fin a → R) = (1 : Matrix (Fin a) (Fin a) R) ℓ := by
    funext j
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [rowMat, this]
  exact updateRow_eq_self _ _

end Row

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [NumberField E] [IsTotallyComplex E] in
variable (E) in

def rowSet (ℓ : Fin a) : Set (Fin a → Cinf E) := {u | ∀ w, u ℓ w ≠ 0}

omit [NumberField E] [IsTotallyComplex E] in
theorem isUnit_of_mem_rowSet {ℓ : Fin a} {u : Fin a → Cinf E} (h : u ∈ rowSet E ℓ) : IsUnit (u ℓ) :=
  Pi.isUnit_iff.2 fun w => (h w).isUnit

omit [IsTotallyComplex E] in
theorem isOpen_rowSet (ℓ : Fin a) : IsOpen (rowSet E ℓ) := by
  rw [rowSet, Set.setOf_forall]
  exact isOpen_iInter_of_finite fun w => isOpen_ne_fun (by fun_prop) continuous_const

omit [IsTotallyComplex E] in

theorem continuousOn_rowGL (ℓ : Fin a) : ContinuousOn (rowGL ℓ) (rowSet E ℓ) := by
  refine GlobalTheory.CuspQuot.isOpenEmbedding_val.isInducing.continuousOn_iff.2 ?_
  have h : Continuous fun u : Fin a → Cinf E => rowMat ℓ u := continuous_const.matrix_updateRow ℓ continuous_id
  exact h.continuousOn.congr fun u hu => val_rowGL (isUnit_of_mem_rowSet hu)

def rsInf (ℓ : Fin a) (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (g : GA E a) (u : Fin a → Cinf E) : ℂ :=
  φ (g * (infGL E a (rowGL ℓ u))⁻¹) * conj (φ' (g * (infGL E a (rowGL ℓ u))⁻¹)) * Φ u

def rsPsi (ℓ : Fin a) (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) (g : GA E a) (y : Fin a → Ad E) : ℂ :=
  thetaFn (rsInf ℓ φ φ' Φ g) J η y

theorem rsPsi_ratGL_mul (ℓ : Fin a) {φ φ' : GA E a → ℂ} (h : ∀ γ g, φ (ratGL E a γ * g) = φ g)
    (h' : ∀ γ g, φ' (ratGL E a γ * g) = φ' g) (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) (γ : GL (Fin a) E) (g : GA E a) (y : Fin a → Ad E) :
    rsPsi ℓ φ φ' Φ J η (ratGL E a γ * g) y = rsPsi ℓ φ φ' Φ J η g y := by
  simp only [rsPsi, thetaFn, rsInf, mul_assoc, h, h']

theorem continuousOn_inv_rowGL (ℓ : Fin a) :
    ContinuousOn (fun u => (infGL E a (rowGL ℓ u))⁻¹) (rowSet E ℓ) :=
  (GlobalTheory.CuspQuot.continuous_infGL.comp_continuousOn (continuousOn_rowGL ℓ)).inv

theorem continuous_rsInf {ℓ : Fin a} {φ φ' : GA E a → ℂ} {Φ : (Fin a → Cinf E) → ℂ} (h : Continuous φ)
    (h' : Continuous φ') (hΦ : Continuous Φ) (hs : tsupport Φ ⊆ rowSet E ℓ) :
    Continuous fun p : GA E a × (Fin a → Cinf E) => rsInf ℓ φ φ' Φ p.1 p.2 := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  by_cases hp : p.2 ∈ tsupport Φ
  · have h1 : ContinuousAt (fun p : GA E a × (Fin a → Cinf E) => p.1 * (infGL E a (rowGL ℓ p.2))⁻¹) p :=
      continuousAt_fst.mul (ContinuousAt.comp (f := Prod.snd)
        ((continuousOn_inv_rowGL ℓ).continuousAt ((isOpen_rowSet ℓ).mem_nhds (hs hp))) continuousAt_snd)
    exact ((h.continuousAt.comp h1).mul ((Complex.continuous_conj.comp h').continuousAt.comp h1)).mul
      (hΦ.comp continuous_snd).continuousAt
  · refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [continuousAt_snd.eventually (notMem_tsupport_iff_eventuallyEq.1 hp)] with q hq
    simp [rsInf, hq]

omit [IsTotallyComplex E] in
theorem isOpen_latt (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : IsOpen (latt a J) := by
  rw [latt, Set.setOf_forall]
  exact isOpen_iInter_of_finite fun i => (isOpen_idealFiniteAdeles J).preimage (continuous_apply i)

omit [IsTotallyComplex E] in
theorem isCompact_latt (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : IsCompact (latt a J) :=
  isCompact_pi_infinite fun _ => isCompact_idealFiniteAdeles J

omit [IsTotallyComplex E] in
theorem isClosed_latt (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : IsClosed (latt a J) := by
  rw [latt, Set.setOf_forall]
  exact isClosed_iInter fun i =>
    (AddSubgroup.isClosed_of_isOpen _ (isOpen_idealFiniteAdeles J)).preimage (continuous_apply i)

theorem continuous_rsPsi {ℓ : Fin a} {φ φ' : GA E a → ℂ} {Φ : (Fin a → Cinf E) → ℂ} (h : Continuous φ)
    (h' : Continuous φ') (hΦ : Continuous Φ) (hs : tsupport Φ ⊆ rowSet E ℓ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) : Continuous fun p : GA E a × (Fin a → Ad E) => rsPsi ℓ φ φ' Φ J η p.1 p.2 := by
  have h1 : Continuous fun p : GA E a × (Fin a → Ad E) => (p.1, fun i => pInf E (p.2 i)) :=
    continuous_fst.prodMk (continuous_pi fun i =>
      GlobalTheory.ShortVecDecay.continuous_pInf.comp ((continuous_apply i).comp continuous_snd))
  have h2 : Continuous fun p : GA E a × (Fin a → Ad E) => (fun i => pFin E (p.2 i)) - η :=
    (continuous_pi fun i => (continuous_snd : Continuous (pFin E)).comp
      ((continuous_apply i).comp continuous_snd)).sub continuous_const
  have h3 : Continuous ((latt a J).indicator (1 : (Fin a → Af E) → ℂ)) :=
    (IsClopen.continuous_indicator ⟨isClosed_latt J, isOpen_latt J⟩ continuous_const)
  exact ((continuous_rsInf h h' hΦ hs).comp h1).mul (h3.comp h2)

theorem continuous_of_mem_smoothSpan {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ GlobalTheory.JSW.smoothSpan π) :
    Continuous F := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    have hS := GlobalTheory.ShortVecDecay.smoothSpan_le_Sm π (Submodule.subset_span hF)
    obtain ⟨f, φ, hf, hφ, rfl⟩ := hF
    refine ContAut.continuous_of_isOpen_stab E a ⟨_, hS⟩ (isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset
      ((π.cusp φ hφ).1.level.mem_nhds (by simp)) fun k hk => Subtype.ext (funext fun g => ?_)))
    have e : (fun x => φ.1 (x * finGL E a k)) = φ.1 := congrArg Subtype.val hk
    exact (GlobalTheory.JSW.smoothInf_rt_fin f φ.1 k g).symm.trans (by rw [e])
  | zero => exact continuous_const
  | add F G _ _ hF hG => exact hF.add hG
  | smul z F _ hF => exact hF.const_smul z

theorem continuous_of_mem_or {π : CuspSub E a} {φ : Sm E a} (h : φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.smoothSpan π) :
    Continuous φ.1 :=
  h.elim (fun h => ContAut.continuous_of_isOpen_stab E a φ (π.cusp φ h).1.level) continuous_of_mem_smoothSpan

end GlobalTheory.RSTheta

end
