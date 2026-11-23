import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.BridgeTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MvPolynomialClearDenominatorsEval
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexLevelSelfDualStabilizerEqProdLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPolynomialEqZeroOfVanishSkewHermitianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CayleyTransformSkewMemUnitaryGroupStatement
set_option autoImplicit false
noncomputable section
open NumberField Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatDenseEnd

theorem blockAct_univ {K : Type} [Field K] {ι : Type} {n : ℕ} (F : MvPolynomial (ι × Fin n × Fin n) K) :
    ∃ U : MvPolynomial (ι × Fin n × Fin n) (MvPolynomial (ι × Fin n × Fin n) K),
      ∀ g : ι → Matrix (Fin n) (Fin n) K,
        Formalism.GradedWeylDivisibility.blockAct K g F = MvPolynomial.map (MvPolynomial.eval (fun p => g p.1 p.2.1 p.2.2)) U := by
  induction F using MvPolynomial.induction_on with
  | C a => exact ⟨MvPolynomial.C (MvPolynomial.C a), fun g => by simp⟩
  | add p q hp hq =>
    obtain ⟨U, hU⟩ := hp
    obtain ⟨W, hW⟩ := hq
    exact ⟨U + W, fun g => by rw [map_add, map_add, hU, hW]⟩
  | mul_X p v hp =>
    obtain ⟨U, hU⟩ := hp
    refine ⟨U * ∑ b : Fin n, MvPolynomial.C (MvPolynomial.X (v.1, v.2.1, b)) * MvPolynomial.X (v.1, (b, v.2.2)),
      fun g => ?_⟩
    rw [map_mul, map_mul, hU]
    congr 1
    simp [Formalism.GradedWeylDivisibility.blockAct, MvPolynomial.aeval_X]

theorem lin_map_eval {K σ τ : Type} [Field K] (ℓ : MvPolynomial σ K →ₗ[K] K)
    (U : MvPolynomial σ (MvPolynomial τ K)) (p : τ → K) :
    ℓ (MvPolynomial.map (MvPolynomial.eval p) U) =
      MvPolynomial.eval p (∑ m ∈ U.support, U.coeff m * MvPolynomial.C (ℓ (MvPolynomial.monomial m 1))) := by
  conv_lhs => rw [U.as_sum]
  simp only [map_sum, MvPolynomial.map_monomial, map_mul, MvPolynomial.eval_C]
  refine Finset.sum_congr rfl fun m _ => ?_
  have e : ∀ c : K, MvPolynomial.monomial m c = c • MvPolynomial.monomial m (1 : K) := by
    intro c; rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul, smul_eq_mul]

theorem cayleyInv {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (hX : (1 + X).det ≠ 0) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, (1 - Y).det ≠ 0 ∧ (1 + Y) * (1 - Y)⁻¹ = X := by
  set A := 1 + X with hA
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hX
  have h1 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hu
  have h2 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hu
  have e1 : (1 : Matrix (Fin n) (Fin n) ℂ) - (X - 1) * A⁻¹ = (2 : ℂ) • A⁻¹ := by
    have : (1 : Matrix (Fin n) (Fin n) ℂ) - (X - 1) * A⁻¹ = (A - (X - 1)) * A⁻¹ := by conv_rhs => rw [Matrix.sub_mul, h1]
    rw [this, show A - (X - 1) = 1 + 1 by rw [hA]; abel, Matrix.add_mul, Matrix.one_mul, two_smul]
  have hdi : A⁻¹.det ≠ 0 := by
    exact (Matrix.isUnit_nonsing_inv_det A hu).ne_zero
  refine ⟨(X - 1) * A⁻¹, ?_, ?_⟩
  · rw [e1, Matrix.det_smul]; exact mul_ne_zero (pow_ne_zero _ two_ne_zero) hdi
  · have hinv : ((2 : ℂ) • A⁻¹)⁻¹ = (2 : ℂ)⁻¹ • A := by
      refine Matrix.inv_eq_left_inv ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h1, inv_mul_cancel₀ two_ne_zero, one_smul]
    rw [e1, hinv, Matrix.mul_smul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one, hA]
    rw [show (1 + X + (X - 1) : Matrix (Fin n) (Fin n) ℂ) = (2 : ℂ) • X by rw [two_smul]; abel, smul_smul,
      inv_mul_cancel₀ two_ne_zero, one_smul]

theorem ratOfUJ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (γE : GL (Fin V.rank) D.host.E)
    (h : γE ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram) : ∃ γ : GQ V, Bridge.IsRatMat V γ γE := by
  set ι := Formalism.L2.Theta.incA D with hι
  have key : ∀ x : D.host.E, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) D.sp.cm.sig (ι x) =
      ι (D.sp.cm.sig x) := fun x => by
    simp [hι, Formalism.L2.Theta.incA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Algebra.TensorProduct.map_tmul]
  have hc : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) D.sp.cm.sig)
      ((γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map ι) =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E)).map ι := by
    ext i j; simp [Formalism.UG.cT, key]
  have h' : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram *
      (γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = V.gram := h
  have hR : Formalism.UG.bc ι γE ∈
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) D.sp.cm.sig V.gram := by
    change Formalism.UG.cT _ ((γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map ι) * V.gram.map ι *
      (γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map ι = V.gram.map ι
    rw [hc, ← Matrix.map_mul, ← Matrix.map_mul, h']
  exact ⟨⟨⟨_, hR⟩, ⟨γE, h, rfl⟩⟩, rfl⟩

end GlobalTheory.RatDenseEnd

namespace GlobalTheory.RatDenseEnd

def pt {ι : Type} {n : ℕ} (Y : ι → Matrix (Fin n) (Fin n) ℂ) : ι × Fin n × Fin n → ℂ :=
  fun p => Y p.1 p.2.1 p.2.2

theorem map_inv_hom {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    (A⁻¹).map f = (A.map f)⁻¹ := by
  have h1 : A.adjugate.map f = (A.map f).adjugate := by
    have := RingHom.map_adjugate f A; simpa [RingHom.mapMatrix_apply] using this
  have h2 : (A.map f).det = f A.det := by
    have := RingHom.map_det f A; simpa [RingHom.mapMatrix_apply] using this.symm
  rw [Matrix.inv_def, Matrix.inv_def, Matrix.map_smul' _ _ _ (map_mul f), h1, h2, Ring.inverse_eq_inv',
    Ring.inverse_eq_inv', map_inv₀]

theorem sig_ne_id (D : D7) : D.sp.cm.sig ≠ AlgHom.id D.host.F D.host.E := by
  intro h
  have hall : ∀ a : D.host.E, a ∈ (algebraMap D.host.F D.host.E).range := fun a =>
    (D.sp.cm.fixed a).1 (by have := congrArg (fun φ => φ a) h; simpa [CMData.sig, starRingEnd_apply] using this)
  have hbot : (⊥ : Subalgebra D.host.F D.host.E) = ⊤ := by
    ext a
    simp only [Algebra.mem_top, iff_true, Algebra.mem_bot]
    obtain ⟨b, hb⟩ := hall a
    exact ⟨b, hb⟩
  have := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 hbot
  rw [D.sp.cm.deg2] at this
  norm_num at this

theorem ratDense (D : D7) (V : Formalism.BasicNotions.TH.HSp D)
    (Q : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin V.rank) ℂ)
    (hQ : ∀ γE : GL (Fin V.rank) D.host.E, γE ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram →
      MvPolynomial.eval (fun p => Formalism.BasicNotions.TH.tauE D p.1
        ((γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E) p.2.1 p.2.2)) Q = 0) :
    Q = 0 := by
  classical
  rcases isEmpty_or_nonempty D.what₂.Tau with hT | hT
  · apply MvPolynomial.funext
    intro x
    have h1 := hQ 1 (one_mem _)
    have hx : x = fun p => Formalism.BasicNotions.TH.tauE D p.1
        (((1 : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) p.2.1 p.2.2) :=
      funext fun p => isEmptyElim p.1
    rw [map_zero, hx]
    exact h1
  let Vv : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) (MvPolynomial (D.what₂.Tau × Fin V.rank × Fin V.rank) ℂ) :=
    fun σ => Matrix.of fun i j => MvPolynomial.X (σ, i, j)
  let P : D.what₂.Tau × Fin V.rank × Fin V.rank → MvPolynomial (D.what₂.Tau × Fin V.rank × Fin V.rank) ℂ :=
    fun p => ((1 + Vv p.1) * (1 - Vv p.1).adjugate) p.2.1 p.2.2
  let Dd : D.what₂.Tau × Fin V.rank × Fin V.rank → MvPolynomial (D.what₂.Tau × Fin V.rank × Fin V.rank) ℂ :=
    fun p => (1 - Vv p.1).det
  obtain ⟨G, M, hGM⟩ := GlobalTheory.clearDenominators Q P Dd
  have evV : ∀ (y : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) σ,
      (Vv σ).map (MvPolynomial.eval (pt y)) = y σ := by
    intro y σ; ext i j; simp [Vv, pt]
  have evDet : ∀ (y : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) σ,
      MvPolynomial.eval (pt y) ((1 - Vv σ).det) = (1 - y σ).det := by
    intro y σ
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_sub _ (map_sub _),
      Matrix.map_one _ (map_zero _) (map_one _), evV]
  have evDet' : ∀ (y : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) σ,
      MvPolynomial.eval (pt y) ((1 + Vv σ).det) = (1 + y σ).det := by
    intro y σ
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_add _ (map_add _),
      Matrix.map_one _ (map_zero _) (map_one _), evV]
  have evP : ∀ (y : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ σ, (1 - y σ).det ≠ 0) →
      (fun p => MvPolynomial.eval (pt y) (P p) / MvPolynomial.eval (pt y) (Dd p)) =
        pt (fun σ => (1 + y σ) * (1 - y σ)⁻¹) := by
    intro y hy
    funext p
    have hm : ((1 + Vv p.1) * (1 - Vv p.1).adjugate).map (MvPolynomial.eval (pt y)) =
        (1 + y p.1) * (1 - y p.1).adjugate := by
      rw [Matrix.map_mul, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, RingHom.map_adjugate,
        RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _),
        Matrix.map_one _ (map_zero _) (map_one _), evV]
    have hP : MvPolynomial.eval (pt y) (P p) = ((1 + y p.1) * (1 - y p.1).adjugate) p.2.1 p.2.2 := by
      rw [← hm]; rfl
    rw [hP, show MvPolynomial.eval (pt y) (Dd p) = (1 - y p.1).det from evDet y p.1]
    simp only [pt, Matrix.inv_def, Matrix.mul_smul, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
    rw [div_eq_inv_mul]
  have hQ' : G * ∏ σ, (1 - Vv σ).det = 0 := by
    refine GlobalTheory.T.mvPolynomial_eq_zero_of_vanish_skewHermitian D.host.F D.host.E D.sp.cm.sig (fun x => star_star x) (sig_ne_id D) D.sp.cm.deg2
      (Formalism.BasicNotions.TH.tauE D) ?_ V.rank V.gram (GlobalTheory.ParIndex.gram_herm D V) (GlobalTheory.ParIndex.gram_det_ne D V) _ ?_
    · intro τ τ' h
      exact (GlobalTheory.CMTypePlaces.places_bijective D).1 (by simp only at h ⊢; rw [h])
    intro S hS
    let y : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun τ => S.map (Formalism.BasicNotions.TH.tauE D τ)
    have hpt : (fun p : D.what₂.Tau × Fin V.rank × Fin V.rank => Formalism.BasicNotions.TH.tauE D p.1 (S p.2.1 p.2.2)) = pt y := rfl
    rw [hpt]
    have hdS : ∀ τ, (1 - y τ).det = Formalism.BasicNotions.TH.tauE D τ (1 - S).det := by
      intro τ
      rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_sub _ (map_sub _),
        Matrix.map_one _ (map_zero _) (map_one _)]
    rw [map_mul, map_prod]
    simp only [evDet, hdS]
    by_cases h0 : (1 - S).det = 0
    · obtain ⟨τ0⟩ := hT
      rw [Finset.prod_eq_zero (Finset.mem_univ τ0) (by rw [h0, map_zero]), mul_zero]
    · have hJ := GlobalTheory.ParIndex.gram_det_ne D V
      obtain ⟨γ, hγ, hγv⟩ : ∃ γ : GL (Fin V.rank) D.host.E,
          γ ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram ∧
            (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = (1 + S) * (1 - S)⁻¹ := by
        first
          | exact GlobalTheory.T.cayleyTransform_skew_mem_unitaryGroup (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram S hS h0
          | exact GlobalTheory.T.cayleyTransform_skew_mem_unitaryGroup (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram S hS hJ h0
          | exact GlobalTheory.T.cayleyTransform_skew_mem_unitaryGroup (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram S hJ hS h0
      have hne : ∀ τ, (1 - y τ).det ≠ 0 := fun τ => by
        rw [hdS]; exact (map_ne_zero _).2 h0
      have hDy : ∀ p, MvPolynomial.eval (pt y) (Dd p) ≠ 0 := fun p => by
        rw [show MvPolynomial.eval (pt y) (Dd p) = _ from evDet _ p.1]; exact hne p.1
      obtain ⟨-, hG⟩ := hGM _ hDy
      rw [hG, evP _ hne]
      have hc : pt (fun σ => (1 + y σ) * (1 - y σ)⁻¹) = fun p => Formalism.BasicNotions.TH.tauE D p.1
          ((γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) p.2.1 p.2.2) := by
        funext p
        have e : (1 + y p.1) * (1 - y p.1)⁻¹ = ((γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E)).map
            (Formalism.BasicNotions.TH.tauE D p.1) := by
          rw [hγv, Matrix.map_mul, map_inv_hom, Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _),
            Matrix.map_one _ (map_zero _) (map_one _)]
        simp only [pt, e, Matrix.map_apply]
      rw [hc, hQ γ hγ, mul_zero, zero_mul]
  have hprod : (∏ σ, (1 - Vv σ).det) ≠ 0 := by
    intro h
    have := congrArg (MvPolynomial.eval (pt (fun _ => (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ)))) h
    simp only [map_prod, evDet, sub_zero, Matrix.det_one, Finset.prod_const_one, map_zero] at this
    exact one_ne_zero this
  have hG0 : G = 0 := (mul_eq_zero.1 hQ').resolve_right hprod
  have hX : ∀ x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, (1 + x τ).det ≠ 0) →
      MvPolynomial.eval (pt x) Q = 0 := by
    intro x hx
    choose Y hYd hYX using fun τ => cayleyInv (x τ) (hx τ)
    have hDY : ∀ p, MvPolynomial.eval (pt Y) (Dd p) ≠ 0 := fun p => by
      rw [show MvPolynomial.eval (pt Y) (Dd p) = _ from evDet Y p.1]; exact hYd p.1
    obtain ⟨hM, hG⟩ := hGM _ hDY
    rw [hG0, map_zero, evP _ hYd, show (fun σ => (1 + Y σ) * (1 - Y σ)⁻¹) = x from funext hYX] at hG
    exact (mul_eq_zero.1 hG.symm).resolve_left hM
  have hprod2 : (∏ σ, (1 + Vv σ).det) ≠ 0 := by
    intro h
    have := congrArg (MvPolynomial.eval (pt (fun _ => (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ)))) h
    simp only [map_prod, evDet', add_zero, Matrix.det_one, Finset.prod_const_one, map_zero] at this
    exact one_ne_zero this
  have hz : Q * ∏ σ, (1 + Vv σ).det = 0 := by
    apply MvPolynomial.funext
    intro z
    let x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun τ => Matrix.of fun i j => z (τ, i, j)
    have hzx : z = pt x := rfl
    rw [map_zero, hzx, map_mul, map_prod]
    simp only [evDet']
    by_cases hx : ∀ τ, (1 + x τ).det ≠ 0
    · rw [hX x hx, zero_mul]
    · push_neg at hx
      obtain ⟨τ, hτ⟩ := hx
      rw [Finset.prod_eq_zero (Finset.mem_univ τ) hτ, mul_zero]
  exact (mul_eq_zero.1 hz).resolve_right hprod2

end GlobalTheory.RatDenseEnd

namespace GlobalTheory.RatDenseEnd

theorem comm_all : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (tauL : D.what₂.Tau → (D.host.E →+* D.what₂.LL)),
    (∀ τ, D.what₂.embLL.comp (tauL τ) = Formalism.BasicNotions.TH.tauE D τ) →
    ∀ (lam : D.what₂.Tau → DomWeight V.rank) (g : Module.End D.what₂.LL (VV D.what₂.LL lam)),
    (∀ (γ : GQ V) (γE : GL (Fin V.rank) D.host.E), Bridge.IsRatMat V γ γE →
      ∀ v, g (rhoVr tauL lam γE v) = rhoVr tauL lam γE (g v)) →
    ∀ (h : D.what₂.Tau → GL (Fin V.rank) D.what₂.LL) v, g (rhoK lam h v) = rhoK lam h (g v) := by
  intro D V tauL htau lam g hg h v
  classical
  obtain ⟨g', hg'⟩ := LinearMap.exists_extend g
  have hgv : ∀ w : VV D.what₂.LL lam, g w = g' (w : Pol D.what₂.LL D.what₂.Tau V.rank) := fun w => by
    rw [← hg']; rfl
  obtain ⟨Uv, hUv⟩ := blockAct_univ (v : Pol D.what₂.LL D.what₂.Tau V.rank)
  obtain ⟨Ug, hUg⟩ := blockAct_univ ((g v : VV D.what₂.LL lam) : Pol D.what₂.LL D.what₂.Tau V.rank)
  let ℓ : (D.what₂.Tau × Fin V.rank × Fin V.rank →₀ ℕ) → Pol D.what₂.LL D.what₂.Tau V.rank →ₗ[D.what₂.LL] D.what₂.LL :=
    fun μ => (MvPolynomial.lcoeff D.what₂.LL μ).comp ((VV D.what₂.LL lam).subtype.comp g')
  let R : (D.what₂.Tau × Fin V.rank × Fin V.rank →₀ ℕ) → MvPolynomial (D.what₂.Tau × Fin V.rank × Fin V.rank) D.what₂.LL :=
    fun μ => (∑ m ∈ Uv.support, Uv.coeff m * MvPolynomial.C (ℓ μ (MvPolynomial.monomial m 1))) - Ug.coeff μ
  have hR : ∀ μ (M : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) D.what₂.LL),
      MvPolynomial.eval (fun p => M p.1 p.2.1 p.2.2) (R μ) =
        ((g' (Formalism.GradedWeylDivisibility.blockAct D.what₂.LL M (v : Pol D.what₂.LL D.what₂.Tau V.rank)) : VV D.what₂.LL lam) :
          Pol D.what₂.LL D.what₂.Tau V.rank).coeff μ -
        (Formalism.GradedWeylDivisibility.blockAct D.what₂.LL M ((g v : VV D.what₂.LL lam) : Pol D.what₂.LL D.what₂.Tau V.rank)).coeff μ := by
    intro μ M
    simp only [R, map_sub]
    rw [← lin_map_eval, ← hUv M, hUg M, MvPolynomial.coeff_map]
    rfl
  have hrho : ∀ (k : D.what₂.Tau → GL (Fin V.rank) D.what₂.LL) (w : VV D.what₂.LL lam),
      ((rhoK lam k w : VV D.what₂.LL lam) : Pol D.what₂.LL D.what₂.Tau V.rank) =
        detTwK lam k • trAct k (w : Pol D.what₂.LL D.what₂.Tau V.rank) := fun k w => rfl
  have hgrho : ∀ k : D.what₂.Tau → GL (Fin V.rank) D.what₂.LL,
      ((g (rhoK lam k v) : VV D.what₂.LL lam) : Pol D.what₂.LL D.what₂.Tau V.rank) =
        detTwK lam k • ((g' (trAct k (v : Pol D.what₂.LL D.what₂.Tau V.rank)) : VV D.what₂.LL lam) :
          Pol D.what₂.LL D.what₂.Tau V.rank) := by
    intro k
    rw [hgv, hrho, map_smul]
    rfl
  have hdet : ∀ k : D.what₂.Tau → GL (Fin V.rank) D.what₂.LL, detTwK lam k ≠ 0 := by
    intro k
    simp only [detTwK, detPow]
    exact Finset.prod_ne_zero_iff.2 fun τ _ => Units.ne_zero _
  have hvan : ∀ μ, R μ = 0 := by
    intro μ
    apply MvPolynomial.map_injective D.what₂.embLL D.what₂.embLL.injective
    rw [map_zero]
    apply ratDense D V
    intro γE hγE
    obtain ⟨γ, hγ⟩ := ratOfUJ V γE⁻¹ (inv_mem hγE)
    have hc := hg γ γE⁻¹ hγ v
    set k := (invTrK (embGL tauL γE⁻¹) : D.what₂.Tau → GL (Fin V.rank) D.what₂.LL) with hkdef
    change g (rhoK lam k v) = rhoK lam k (g v) at hc
    have hk : ∀ τ, Matrix.transpose ((k τ : GL (Fin V.rank) D.what₂.LL) : Matrix (Fin V.rank) (Fin V.rank) D.what₂.LL) =
        (γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (tauL τ) := by
      intro τ
      show Matrix.transpose (Matrix.transpose (((Formalism.UG.bc (tauL τ) γE⁻¹)⁻¹ : GL (Fin V.rank) D.what₂.LL) : Matrix (Fin V.rank) (Fin V.rank) D.what₂.LL)) = _
      rw [Matrix.transpose_transpose, ← map_inv, inv_inv]
      rfl
    have h2 := congrArg (fun w : VV D.what₂.LL lam => (w : Pol D.what₂.LL D.what₂.Tau V.rank).coeff μ) hc
    simp only [hgrho, hrho, MvPolynomial.coeff_smul, smul_eq_mul] at h2
    have h3 := hR μ (fun τ => Matrix.transpose ((k τ : GL (Fin V.rank) D.what₂.LL) : Matrix (Fin V.rank) (Fin V.rank) D.what₂.LL))
    have ht : Formalism.GradedWeylDivisibility.blockAct D.what₂.LL
        (fun τ => Matrix.transpose ((k τ : GL (Fin V.rank) D.what₂.LL) : Matrix (Fin V.rank) (Fin V.rank) D.what₂.LL)) = trAct k := rfl
    rw [ht, mul_left_cancel₀ (hdet k) h2, sub_self] at h3
    have hp : (fun p : D.what₂.Tau × Fin V.rank × Fin V.rank =>
        Matrix.transpose ((k p.1 : GL (Fin V.rank) D.what₂.LL) : Matrix (Fin V.rank) (Fin V.rank) D.what₂.LL) p.2.1 p.2.2) =
        fun p => tauL p.1 ((γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E) p.2.1 p.2.2) := by
      funext p; rw [hk]; rfl
    rw [hp] at h3
    have hmap : (fun p : D.what₂.Tau × Fin V.rank × Fin V.rank =>
        Formalism.BasicNotions.TH.tauE D p.1 ((γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E) p.2.1 p.2.2)) =
        D.what₂.embLL ∘ fun p => tauL p.1 ((γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E) p.2.1 p.2.2) := by
      funext p; rw [← htau]; rfl
    rw [hmap, MvPolynomial.eval_map]
    have := MvPolynomial.eval₂_comp_left D.what₂.embLL (RingHom.id D.what₂.LL)
      (fun p : D.what₂.Tau × Fin V.rank × Fin V.rank => tauL p.1 ((γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E) p.2.1 p.2.2)) (R μ)
    rw [RingHom.comp_id] at this
    rw [← this]
    change D.what₂.embLL (MvPolynomial.eval _ (R μ)) = 0
    rw [h3, map_zero]
  apply Subtype.ext
  rw [hgrho, hrho]
  congr 1
  ext μ
  have := hR μ (fun τ => Matrix.transpose ((h τ : GL (Fin V.rank) D.what₂.LL) : Matrix (Fin V.rank) (Fin V.rank) D.what₂.LL))
  rw [hvan μ, map_zero] at this
  exact sub_eq_zero.1 this.symm

end GlobalTheory.RatDenseEnd
