import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdEmb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianTwistedRealReadingEntireAndInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockMonomialAtOriginGaussianEntireOrthonormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetsUnitVacuumEqScaledThetaJets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorPolIsHomogeneous

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormDictEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormDictEx.Jets

open Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.AdForm GlobalTheory.AdForm.VacRead GlobalTheory.FockCompare GlobalTheory.MixPer GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk

variable {D : D7}

theorem xiN_differentiable (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ)
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hgS : S.gram = 1) (hgT : T.gram = 1) (hδ : δ ≠ 0)
    (hsc : sc * ‖δ‖ ^ 2 = 2 * Formalism.L2.Pj.xiR D) (f : WO S T → ℂ) (hf1 : IsThetaFunO ψ S T f)
    (hf2 : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) f) :
    Differentiable ℂ (xiN θ S T rfl rfl δ sc f) := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨hF, hann⟩ := GlobalTheory.VacUnique.Ann.vacuum_annihilation D θ σ hσ ψ hψ S T (fun _ => 1) (fun _ => 1) f
    hf1 hf2
  set F : RW T S → ℂ := fun z => f (iotaW σ T S z) with hFdef
  set r : ℝ := sc / 2 with hr
  let L : RW T S →L[ℂ] RW T S := (-δ⁻¹) • ContinuousLinearMap.id ℂ (RW T S)
  have hL : ∀ Z τ i j, L Z τ i j = -(δ⁻¹ * Z τ i j) := fun Z τ i j => by simp [L]
  set E : RW T S → ℂ := fun Z => Complex.exp ((Real.pi * r * ∑ τ, ∑ i, ∑ j, ‖Z τ i j‖ ^ 2 : ℝ) : ℂ) with hE
  have hxi : xiN θ S T rfl rfl δ sc f = fun Z => F (L Z) * E Z := by
    funext Z
    unfold xiN
    have hp : realPt θ (fun τ => Matrix.of fun i j => -(δ⁻¹ * Z τ (Fin.cast rfl i) (Fin.cast rfl j))) =
        iotaW σ T S (L Z) := by
      refine realPt_eq hθ _ _ (by funext i j; exact hσ.fin _) fun τ => ?_
      funext i j
      show θ τ (infPart D (σ fun τ' => L Z τ' i j)) = _
      rw [hσ.comp]
      simp [hL]
    rw [hp, mul_comm]
    congr 2
    show (Real.pi : ℂ) / 2 * ((sc : ℂ) * ∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Z τ i j)) = _
    simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hr]; push_cast; ring
  rw [hxi]
  have hdG : ∀ Z Y, fderiv ℝ (fun Z => F (L Z)) Z Y = fderiv ℝ F (L Z) (L Y) := fun Z Y => by
    have h : HasFDerivAt (fun Z => F (L Z)) ((fderiv ℝ F (L Z)).comp (L.restrictScalars ℝ)) Z :=
      (hF (L Z)).hasFDerivAt.comp Z (L.restrictScalars ℝ).hasFDerivAt
    rw [h.fderiv]; rfl
  refine GlobalTheory.FockPos.differentiable_mul_of_cr (fun Z => F (L Z)) E
    (fun Z Y => (2 * Real.pi * r * ∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y τ i j) : ℂ))
    (hF.comp (L.restrictScalars ℝ).differentiable) (GlobalTheory.FockPos.gauss_cr r).1 (fun Z Y => ?_)
    (GlobalTheory.FockPos.gauss_cr r).2
  rw [hdG, hdG]
  have hj : GlobalTheory.VacUnique.jO S T (fun _ => 1) (fun _ => 1) (L Y) = L (Complex.I • Y) := by
    rw [L.map_smul]; funext τ; rw [GlobalTheory.VacUnique.jO_apply]
    change Complex.I • ((1 : Matrix (Fin T.rank) (Fin T.rank) ℂ) * Matrix.of (L Y τ) *
      (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ)) = _
    rw [Matrix.one_mul, Matrix.mul_one]; rfl
  have h := hann (L Z) (L Y)
  rw [hj] at h
  have hdd : δ⁻¹ * starRingEnd ℂ δ⁻¹ = (((‖δ‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_inv, Complex.normSq_eq_norm_sq]
  have hom : ∀ Y' : RW T S, GlobalTheory.VacUnique.omO S T (L Z) (L Y') =
      ∑ τ, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * (((‖δ‖ ^ 2)⁻¹ : ℝ) : ℂ) *
        ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y' τ i j)).re := by
    intro Y'
    rw [GlobalTheory.VacUnique.omO_apply]
    refine Finset.sum_congr rfl fun τ _ => ?_
    show 2 * (tauE D τ D.host.xi0 * GlobalTheory.VacUnique.hAt S T τ (L Z τ) (L Y' τ)).re = _
    rw [GlobalTheory.FockPos.xi_zero_eq_host τ]
    erw [hAt_one S T hgS hgT τ (L Z τ) (L Y' τ)]
    have hs : ∑ i, ∑ j, L Z τ i j * starRingEnd ℂ (L Y' τ i j) =
        (((‖δ‖ ^ 2)⁻¹ : ℝ) : ℂ) * ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y' τ i j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hL, hL, ← hdd]
      simp only [map_neg, map_mul]
      ring
    rw [hs]
    congr 2
    ring
  rw [hom, hom] at h
  have hs2 : ∀ τ, (∑ i, ∑ j, Z τ i j * starRingEnd ℂ ((Complex.I • Y) τ i j)) =
      -Complex.I * ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y τ i j) := fun τ => by
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [hs2] at h
  have key := key_sum (Formalism.L2.Pj.xiR D) ((‖δ‖ ^ 2)⁻¹) fun τ => ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y τ i j)
  have hrk : Formalism.L2.Pj.xiR D * (‖δ‖ ^ 2)⁻¹ = r :=
    scale_eq _ _ _ (pow_ne_zero 2 (norm_ne_zero_iff.2 hδ)) hsc
  rw [hrk] at key
  show _ = -((2 * Real.pi * r * ∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y τ i j) : ℂ) * F (L Z))
  linear_combination h + Real.pi * Complex.I * F (L Z) * key +
    2 * Real.pi * r * (∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y τ i j)) * F (L Z) * Complex.I_sq

theorem frAt_one {n : ℕ} : GlobalTheory.FockPos.frAt (1 : GL (Fin n) D.host.E) = fun _ => 1 := by
  funext τ
  simp [GlobalTheory.FockPos.frAt]

theorem eq_gauss_mul (θ : InfFam D) (hθ : IsInfFam θ) (S T : HSp D) (δ : ℂ) (sc : ℝ) (hδ : δ ≠ 0)
    (hsc : sc * ‖δ‖ ^ 2 = 2 * Formalism.L2.Pj.xiR D) (f : WO S T → ℂ) (w : WO S T) (hw : w.map (finPart D) = 0) :
    f w = GlobalTheory.FockPos.gaussO θ 1 1 w * xiN θ S T rfl rfl δ sc f ((-δ) • GlobalTheory.FockPos.zCo θ 1 1 w) := by
  have hz : ∀ τ, GlobalTheory.FockPos.zCo θ (1 : GL (Fin S.rank) D.host.E) (1 : GL (Fin T.rank) D.host.E) w τ = compAt θ τ w := by
    intro τ
    simp only [GlobalTheory.FockPos.zCo, frAt_one, inv_one, Matrix.one_mul, Matrix.mul_one]
    rfl
  set y := GlobalTheory.FockPos.zCo θ (1 : GL (Fin S.rank) D.host.E) (1 : GL (Fin T.rank) D.host.E) w with hy
  have hp : realPt θ (fun τ => Matrix.of fun i j => -(δ⁻¹ * ((-δ) • y) τ (Fin.cast rfl i) (Fin.cast rfl j))) = w := by
    refine realPt_eq hθ _ w hw fun τ => ?_
    funext i j
    rw [← hz τ]
    simp only [Matrix.of_apply, Fin.cast_eq_self, Pi.smul_apply, smul_eq_mul]
    field_simp
  unfold xiN
  rw [hp, GlobalTheory.FockPos.gaussO, ← hy, ← mul_assoc, ← Complex.exp_add]
  have hH : HV sc ((-δ) • y) ((-δ) • y) = (sc : ℂ) * (((‖δ‖ ^ 2 : ℝ) : ℂ) * ∑ τ, ∑ i, ∑ j, ((‖y τ i j‖ ^ 2 : ℝ) : ℂ)) := by
    show (sc : ℂ) * (∑ τ, ∑ i, ∑ j, ((-δ) • y) τ i j * starRingEnd ℂ (((-δ) • y) τ i j)) = _
    congr 1
    simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mul, norm_neg]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    push_cast; ring
  have hc : (sc : ℂ) * ((‖δ‖ ^ 2 : ℝ) : ℂ) = 2 * (Formalism.L2.Pj.xiR D : ℂ) := by exact_mod_cast hsc
  have h0 : -((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ i, ∑ j, ((‖y τ i j‖ ^ 2 : ℝ) : ℂ) +
      (Real.pi : ℂ) / 2 * HV sc ((-δ) • y) ((-δ) • y) = 0 := by
    rw [hH, ← mul_assoc (sc : ℂ), hc, Complex.ofReal_mul]
    ring
  rw [h0, Complex.exp_zero, one_mul]

theorem apply_minorPol {a d : ℕ} {n : D.what₂.Tau → ℕ} (U : Tup D a d n)
    (l : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ →ₗ[ℂ] ℂ) (p : ℂ) (G : Formalism.MainNotions.TaylorLogMetric.VC D a d → ℂ)
    (h : ∀ k : Formalism.MainNotions.GL3Theta.Idx D a d →₀ ℕ, l (MvPolynomial.monomial k 1) =
      p ^ (k.sum fun _ e => e) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) G) :
    l (minorPol D U) = p ^ (a * ∑ τ, n τ) * Formalism.MainNotions.GL3Theta.applyAt0 D (minorPol D U) G := by
  conv_lhs => rw [(minorPol D U).as_sum]
  rw [map_sum l, Formalism.MainNotions.GL3Theta.applyAt0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hk := GlobalTheory.RotJets.card_of_mem_support U hα
  rw [Finsupp.card_toMultiset] at hk
  have e : (MvPolynomial.monomial α ((minorPol D U).coeff α) : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ) =
      (minorPol D U).coeff α • MvPolynomial.monomial α 1 := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  have hk' : (α.sum fun _ e => e) = a * ∑ τ, n τ := hk
  rw [e, map_smul, h, GlobalTheory.FockPos.applyAt0_monomial', hk', smul_eq_mul]
  ring

theorem fock_minorPol_zero : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) {a d : ℕ} (hA : A.rank = a) (hB : B.rank = d) (n : D.what₂.Tau → ℕ) (s : ℂ) (sc : ℝ), IsStdChar D ψ (-1) → IsInfFam θ → A.gram = 1 → B.gram = 1 → s ≠ 0 → (∀ τ, sc * ‖s‖ ^ 2 = 2 * ‖tauE D τ D.host.xi0‖) → ∃ c₁ : ℂ, c₁ ≠ 0 ∧ ∀ f : WO A B → ℂ, IsThetaFunO ψ A B f → (∀ τ, IsFockVacAt (heisO ψ A B) θ τ (cplxO 1 1) f) → ∀ T : Tup D a d n, pureTensorL (aPlusAll (heisO ψ A B) θ (fun _ => cplxO 1 1) (fun _ => 1) (fun _ => 1)) f (MvPolynomial.rename (fun k : Formalism.MainNotions.GL3Theta.Idx D a d => ((k.1, Fin.cast hB.symm k.2.1, Fin.cast hA.symm k.2.2) : FVar D B.rank A.rank)) (minorPol D T)) 0 = c₁ * Formalism.MainNotions.GL3Theta.applyAt0 D (minorPol D T) (GlobalTheory.AdForm.xiN θ A B hA hB s sc f) := by
  intro D ψ θ A B a d hA hB n s sc hψ hθ hgA hgB hs hsc
  subst hA hB
  obtain ⟨τ₀⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  have hsc' : sc * ‖s‖ ^ 2 = 2 * Formalism.L2.Pj.xiR D := by
    rw [hsc τ₀, GlobalTheory.FockPos.norm_embedding_xi0_eq]
  have hx : 0 < Formalism.L2.Pj.xiR D := by
    unfold Formalism.L2.Pj.xiR
    exact norm_pos_iff.2 ((map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
  set p : ℂ := (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) * -s with hp
  have hp0 : p ≠ 0 := by
    refine mul_ne_zero (inv_ne_zero ?_) (neg_ne_zero.2 hs)
    exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne'
  have hon : ∀ {V : HSp D}, V.gram = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin V.rank) D.host.E).1 *
      V.gram * (1 : GL (Fin V.rank) D.host.E).1 = 1 := by
    intro V hV
    rw [hV]
    simp [Formalism.UG.cT]
  refine ⟨p ^ (A.rank * ∑ τ, n τ), pow_ne_zero _ hp0, fun f hf1 hf2 T => ?_⟩
  have hG := xiN_differentiable ψ θ A B s sc hψ hθ hgA hgB hs hsc' f hf1 hf2
  set G := xiN θ A B rfl rfl s sc f with hGdef
  have hΦ : Differentiable ℂ (fun z : Formalism.MainNotions.TaylorLogMetric.VC D A.rank B.rank => G ((-s) • z)) :=
    hG.comp (differentiable_id.const_smul (-s))
  have hid : (fun k : Formalism.MainNotions.GL3Theta.Idx D A.rank B.rank => ((k.1, Fin.cast (rfl : B.rank = B.rank).symm k.2.1,
      Fin.cast (rfl : A.rank = A.rank).symm k.2.2) : FVar D B.rank A.rank)) = id := by
    funext v; rfl
  rw [hid, MvPolynomial.rename_id, AlgHom.id_apply]
  refine apply_minorPol T ((LinearMap.proj (0 : WO A B)).comp
    (pureTensorO ψ θ A B (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f)) p G fun k => ?_
  have h := GlobalTheory.FockPos.fock_monomial_zero_of_on ψ θ A B 1 1 hψ hθ (hon hgA) (hon hgB) f _ hΦ
    (fun w hw => eq_gauss_mul θ hθ A B s sc hs hsc' f w hw) k
  rw [frAt_one, frAt_one, GlobalTheory.FockPos.applyAt0_monomial', GlobalTheory.FockPos.taylor_comp_smul' D _ hG] at h
  rw [GlobalTheory.FockPos.applyAt0_monomial']
  refine h.trans ?_
  rw [hp, mul_pow]
  ring

end GlobalTheory.NormDictEx.Jets
