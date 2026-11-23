import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnnihilationCreationPeriodCoordinates
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorOriginEqPolyDeriv
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermCColMulVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HxOfIsONFr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiHalfSymplecticOrthonormalFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CplxOfFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThAHeisEntireLinearInjective

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.Fock

open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open GlobalTheory.Ker (gaussR)

theorem norm_embedding_hostFormConstant_eq (D : D7) (τ : D.host.E →+* ℂ) : ‖τ D.host.xi0‖ = Formalism.L2.Pj.xiR D := by
  have hs : ∀ τ : D.host.E →+* ℂ, ‖τ D.host.sqrtMinusD‖ = Real.sqrt D.host.d := by
    intro τ
    have h0 : (τ D.host.sqrtMinusD) ^ 2 = -(D.host.d : ℂ) := by
      rw [← map_pow, Formalism.BasicNotions.Host.sqrtMinusD_sq D.host, map_neg, map_natCast]
    rw [← Real.sqrt_sq (norm_nonneg (τ D.host.sqrtMinusD)), ← norm_pow, h0, norm_neg, Complex.norm_natCast]
  unfold Formalism.L2.Pj.xiR Host.xi0
  simp only [map_div₀, map_neg, map_one, map_mul, map_natCast, norm_div, norm_neg, norm_one, norm_mul,
    Complex.norm_natCast, hs]

theorem aeval_scale {σ : Type} (c : ℂ) {P : MvPolynomial σ ℂ} {d : ℕ} (hP : P.IsHomogeneous d) :
    MvPolynomial.aeval (fun l => MvPolynomial.C c * MvPolynomial.X l : σ → MvPolynomial σ ℂ) P = c ^ d • P := by
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i ∈ m.support, m i = d := by
    have := hP (MvPolynomial.mem_support_iff.1 hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  rw [MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq, MvPolynomial.smul_eq_C_mul, ← hd]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    MvPolynomial.algebraMap_eq, map_pow]
  ring

variable {D : D7} {θ : InfFam D} {r g : ℕ}

theorem realM_lineAt (hθ : IsInfFam θ) {m n : ℕ} (ρ : D.what₂.Tau) (u : Matrix (Fin m) (Fin n) ℂ)
    (τ : D.host.E →+* ℂ) : realM θ (lineAt θ ρ u 1) τ = if τ = tauE D ρ then u else 0 := by
  have hL := (GlobalTheory.OrientedHeis.isLineAt_lineAt hθ ρ u).2.2 1
  unfold realM
  split_ifs with h1 h2 h2
  · rw [hL, if_pos (GlobalTheory.StdRat.tauE_injective D (h1.choose_spec.symm.trans h2))]
    simp
  · rw [hL, if_neg fun h => h2 (h1.choose_spec.trans (congrArg (tauE D) h))]
  · exact absurd ⟨ρ, h2⟩ h1
  · rfl

theorem perC_col {E : Type} [Field E] [NumberField E] [IsCMField E] (X : Data E r) {x : Frame X.Ψ r}
    (hx : IsONFr X x) (hd : x ∈ X.dom) (τ : X.Ψ) (c : Fin r) :
    perC X x (fun σ a => if σ = τ then x τ a c else 0) = Pi.single (τ, c) 1 := by
  funext ⟨σ, a⟩
  unfold perC
  dsimp only
  by_cases h : σ = τ
  · subst h
    simp only [if_true, Pi.single_apply, Prod.mk.injEq, true_and]
    by_cases ha : (a : ℕ) < X.p0
    · rw [if_pos ha]
      refine (congrFun (congrFun (hx σ) a) c).trans ?_
      simp [sgnM, Matrix.diagonal_apply, sgn, ha]
    · rw [if_neg ha]
      have := congrFun (congrFun (Matrix.nonsing_inv_mul (mat x σ) (isUnit_iff_ne_zero.2 (hd σ).1)) a) c
      rw [Matrix.one_apply] at this
      exact this
  · rw [Pi.single_eq_of_ne (fun e => h (congrArg Prod.fst e))]
    simp only [if_neg h]
    split_ifs
    · simp [hermC]
    · simp [Matrix.mulVec, dotProduct]

theorem perC_zero {E : Type} [Field E] [NumberField E] [IsCMField E] (X : Data E r) (x : Frame X.Ψ r) :
    perC X x (fun _ _ => 0) = 0 := by
  funext p
  unfold perC
  split_ifs
  · simp [hermC]
  · simp [Matrix.mulVec, dotProduct]

theorem zOf_unitMap (hθ : IsInfFam θ) {V W : HSp D} {hr : W.rank = r} {X : Data D.host.E r}
    (idx : Fin g ≃ X.Ψ × Fin r) {q0 : ℕ} {hq : X.p0 + q0 = r} {x : Frame X.Ψ r}
    {BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ}
    {vr : Harm.Var X.Ψ q0 X.p0 (Fin V.rank) ≃ FVar D W.rank V.rank}
    (hx : IsONFr X x) (hd : x ∈ X.dom) (hB : IsBasOf W hr X hq x BW) (hv : IsVarOf V W X q0 vr)
    (l : Harm.Var X.Ψ q0 X.p0 (Fin V.rank)) :
    zOf θ V W hr X idx x (lineAt θ (vr l).1 (unitMap 1 (BW (vr l).1) (vr l).2.1 (vr l).2.2) 1) =
      letterDir X hq idx l := by
  obtain ⟨h1, h2, h3⟩ := hv l
  funext b j
  have hU : ∀ a, unitMap 1 (BW (vr l).1) (vr l).2.1 (vr l).2.2 a b =
      if b = l.2.2 then x l.1 (Fin.cast hr a) (rowIdx hq l.2.1) else 0 := by
    intro a
    rw [← hB _ l.1 h1 l.2.1 (vr l).2.1 a h3, ← h2, unitMap, inv_one, Matrix.mul_one]
    split_ifs with h
    · rw [h]; simp
    · exact Matrix.mul_single_apply_of_ne _ _ _ _ _ h _
  unfold zOf letterDir
  simp only [realM_lineAt hθ, ← h1, Subtype.val_inj, Matrix.ite_apply, Matrix.zero_apply, hU, Fin.cast_cast, Fin.cast_eq_self]
  by_cases hb : b = l.2.2
  · subst hb
    simp only [if_true]
    rw [perC_col X hx hd, Pi.single_eq_same]
    simp only [Pi.single_apply, Equiv.eq_symm_apply, rowOf_apply]
  · simp only [if_neg hb, ite_self]
    rw [perC_zero, Pi.single_eq_of_ne hb]
    rfl

section Operators

variable {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {hr : W.rank = r} {X : Data D.host.E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {x : Frame X.Ψ r}

theorem dRho_eq (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hV : V.gram = 1) (hn : Even V.rank)
    (hM : IsMod W hr X) (hS : IsSympl X bas) (hx0 : IsONFr X x) (hd : x ∈ X.dom) (G : WO V W → ℂ)
    (Φ : (Fin V.rank → Fin g → ℂ) → ℂ) (hΦ : Differentiable ℝ Φ)
    (hG : ∀ w : WO V W, w.map (finPart D) = 0 →
      G w = gaussR X bas idx x (zOf θ V W hr X idx x w) * Φ (zOf θ V W hr X idx x w))
    (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (u : Fin V.rank → Fin g → ℂ)
    (hu : zOf θ V W hr X idx x (lineAt θ τ z 1) = u) (w : WO V W) (hw : w.map (finPart D) = 0) :
    Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z G w =
      gaussR X bas idx x (zOf θ V W hr X idx x w) *
        (-(Real.pi * ∑ k, hx X bas idx x (u k) (zOf θ V W hr X idx x w k)) * Φ (zOf θ V W hr X idx x w) +
          fderiv ℝ Φ (zOf θ V W hr X idx x w) u) := by
  obtain ⟨-, hadd, hline, -⟩ := GlobalTheory.AdTh.RealCoord.zOf_coordinates D ψ θ V W r g hr X bas idx hψ hθ hV hn hM hS x
  have hsym := GlobalTheory.T.psi_halfSymplectic_orthonormalFrame D ψ θ V W r g hr X bas idx hψ hθ hV hn hM hS x hx0
  have hs := (GlobalTheory.Dict.hx_laws _ _ X g bas idx V.rank hS hn _ hd).1
  rw [← (GlobalTheory.Ker.HeisDeriv.hasDerivAt_translate X bas idx x hs Φ hΦ (zOf θ V W hr X idx x w) u).deriv,
    Formalism.IndefR.Datum.dRho]
  congr 1
  funext t
  have hz : zOf θ V W hr X idx x (lineAt θ τ z t) = t • u := by
    rw [hline, hu]; rfl
  have hreal : (w + lineAt θ τ z t).map (finPart D) = 0 := by
    have h2 := (GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ z).2.1 t
    ext i j
    have a1 := congrFun (congrFun hw i) j
    have a2 := congrFun (congrFun h2 i) j
    simp only [Matrix.map_apply, Matrix.zero_apply] at a1 a2 ⊢
    rw [Matrix.add_apply, (finPart D).map_add, a1, a2, add_zero]
  rw [heisO, hsym w _ hw, hG _ hreal, hadd, hz, Complex.im_sum]

theorem crea_eq (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hV : V.gram = 1) (hn : Even V.rank)
    (hM : IsMod W hr X) (hS : IsSympl X bas) (hx0 : IsONFr X x) (hd : x ∈ X.dom)
    {s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ} (hs : IsInvOf W hr X x s) (G : WO V W → ℂ)
    (Φ : (Fin V.rank → Fin g → ℂ) → ℂ) (hΦ : Differentiable ℝ Φ)
    (hG : ∀ w : WO V W, w.map (finPart D) = 0 →
      G w = gaussR X bas idx x (zOf θ V W hr X idx x w) * Φ (zOf θ V W hr X idx x w))
    (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (u : Fin V.rank → Fin g → ℂ)
    (hu : zOf θ V W hr X idx x (lineAt θ τ z 1) = u) (w : WO V W) (hw : w.map (finPart D) = 0) :
    crea (heisO ψ V W) θ τ (cplxO 1 (s τ)) z G w =
      gaussR X bas idx x (zOf θ V W hr X idx x w) *
        (2 * ((-(Real.pi * ∑ k, hx X bas idx x (u k) (zOf θ V W hr X idx x w k))) * Φ (zOf θ V W hr X idx x w) +
          (1 / 2 : ℂ) * (fderiv ℝ Φ (zOf θ V W hr X idx x w) u -
            I * fderiv ℝ Φ (zOf θ V W hr X idx x w) (I • u)))) := by
  have hJ := (GlobalTheory.FrameCplx.cplx_of_frame D ψ θ V W r g hr X bas idx hψ hθ hV hn hM hS x s hx0 hs).2.2 τ z
  have h1 := dRho_eq hψ hθ hV hn hM hS hx0 hd G Φ hΦ hG τ z u hu w hw
  have h2 := dRho_eq hψ hθ hV hn hM hS hx0 hd G Φ hΦ hG τ (cplxO 1 (s τ) z) (I • u) (by rw [hJ, hu]) w hw
  have h3 : ∑ k, hx X bas idx x ((I • u) k) (zOf θ V W hr X idx x w k) =
      I * ∑ k, hx X bas idx x (u k) (zOf θ V W hr X idx x w k) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => GlobalTheory.Ker.HeisDeriv.hx_smul_left _ _ _ _ _ _ _
  rw [h3] at h2
  rw [crea, Pi.sub_apply, Pi.smul_apply, h1, h2, smul_eq_mul]
  linear_combination ((gaussR X bas idx x (zOf θ V W hr X idx x w)) * Real.pi *
    (∑ k, hx X bas idx x (u k) (zOf θ V W hr X idx x w k)) * Φ (zOf θ V W hr X idx x w)) * I_mul_I

end Operators

theorem pureTensorO_zero_eq_thP : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ (q0 : ℕ) (hq : X.p0 + q0 = r) (x : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (vr : Harm.Var X.Ψ q0 X.p0 (Fin V.rank) ≃ FVar D W.rank V.rank), IsONFr X x → IsInvOf W hr X x s → IsBasOf W hr X hq x BW → IsVarOf V W X q0 vr → ∀ (f : WO V W → ℂ) (φ : TF V.rank g), IsThetaFunO ψ V W f → Reads θ V W hr X bas idx f φ x → ∀ (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin V.rank)) (d : ℕ), P.IsHomogeneous d → pureTensorO ψ θ V W (fun _ => 1) s (fun _ => 1) BW f (MvPolynomial.rename vr P) 0 = ((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹ ^ d * thP X hq bas idx φ P x := by
  intro D ψ θ V W r g hr X bas idx hψ hθ hV hn hM hS q0 hq x s BW vr hx0 hs hB hv G φ _ hR P d hP
  have hd : x ∈ X.dom := (GlobalTheory.AdTh.hx_of_isONFr _ r g V.rank X bas idx hS hn x hx0).1
  have hΘ := (GlobalTheory.AdTh.thA_heis_entire_linear_injective _ r g V.rank X bas idx hS hn x hd φ hR.1).2.1
  set Θ := thA X bas idx φ x with hΘ0
  set c₀ : ℂ := ((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹ with hc₀
  let c : FVar D W.rank V.rank → ℂ := fun _ => c₀
  let u : FVar D W.rank V.rank → Fin V.rank → Fin g → ℂ := fun v => letterDir X hq idx (vr.symm v)
  have hdir : ∀ v : FVar D W.rank V.rank,
      zOf θ V W hr X idx x (lineAt θ v.1 (unitMap 1 (BW v.1) v.2.1 v.2.2) 1) = u v := by
    intro v
    obtain ⟨l, rfl⟩ := vr.surjective v
    rw [zOf_unitMap hθ idx hx0 hd hB hv l]
    simp only [u, Equiv.symm_apply_apply]
  let lam : FVar D W.rank V.rank → (Fin V.rank → Fin g → ℂ) → ℂ := fun v z =>
    -(Real.pi * ∑ k, hx X bas idx x (u v k) (z k))
  let Dl : FVar D W.rank V.rank → ((Fin V.rank → Fin g → ℂ) → ℂ) → (Fin V.rank → Fin g → ℂ) → ℂ :=
    fun l Φ z => lam l z * Φ z + (1 / 2 : ℂ) * (fderiv ℝ Φ z (u l) - I * fderiv ℝ Φ z (I • u l))
  have hlam : ∀ l, (∀ a b, lam l (a + b) = lam l a + lam l b) ∧
      ∀ (t : ℂ) a, lam l (t • a) = conj t * lam l a := by
    intro l
    refine ⟨fun a b => ?_, fun t a => ?_⟩
    · simp only [lam, GlobalTheory.Dict.hx, Pi.add_apply, mulVec_add, star_add, dotProduct_add,
        Finset.sum_add_distrib]
      ring
    · simp only [lam, GlobalTheory.Dict.hx, Pi.smul_apply, mulVec_smul, star_smul, dotProduct_smul,
        smul_eq_mul, ← Finset.mul_sum, RCLike.star_def]
      ring
  have hops := GlobalTheory.Ker.CreOp.foldr_creation_zero _ _ u lam Θ hlam hΘ Dl (fun _ _ _ => rfl)
  let A := aPlusAll (heisO ψ V W) θ (fun τ => cplxO 1 (s τ)) (fun _ => 1) BW
  have key : ∀ L : List (FVar D W.rank V.rank), ∀ w : WO V W, w.map (finPart D) = 0 →
      L.foldr (fun i g => A i g) G w = gaussR X bas idx x (zOf θ V W hr X idx x w) *
        ((L.map c).prod * L.foldr Dl Θ (zOf θ V W hr X idx x w)) := by
    intro L
    induction L with
    | nil =>
      intro w hw
      rw [List.foldr_nil, hR.2 w hw, gaussR, neg_mul]
      simp [hΘ0]
    | cons a L ih =>
      intro w hw
      have hdf : Differentiable ℝ (L.foldr Dl Θ) := (hops L).1.differentiable (by simp)
      have h := crea_eq hψ hθ hV hn hM hS hx0 hd hs _ (fun z => (L.map c).prod * L.foldr Dl Θ z)
        (hdf.const_mul _) ih a.1 (unitMap 1 (BW a.1) a.2.1 a.2.2) (u a) (hdir a) w hw
      rw [List.foldr_cons]
      change ((fockScale D a.1 : ℂ)⁻¹) * crea (heisO ψ V W) θ a.1 (cplxO 1 (s a.1))
        (unitMap 1 (BW a.1) a.2.1 a.2.2) (L.foldr (fun i g => A i g) G) w = _
      have hf : (fockScale D a.1 : ℂ)⁻¹ = c₀ / 2 := by
        rw [fockScale, norm_embedding_hostFormConstant_eq, hc₀, Complex.ofReal_mul, _root_.mul_inv_rev]
        norm_num [div_eq_mul_inv]
      rw [h, fderiv_const_mul (hdf _), hf]
      simp only [List.foldr_cons, List.map_cons, List.prod_cons, _root_.smul_apply, smul_eq_mul]
      simp only [Dl, lam, c]
      ring
  have h0 : zOf θ V W hr X idx x 0 = 0 := by
    have := (GlobalTheory.AdTh.RealCoord.zOf_coordinates D ψ θ V W r g hr X bas idx hψ hθ hV hn hM hS x).2.1 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  have hr0 : (0 : WO V W).map (finPart D) = 0 := by
    ext i j
    simp
  have hg0 : gaussR X bas idx x (0 : Fin V.rank → Fin g → ℂ) = 1 := by
    simp [gaussR, GlobalTheory.Dict.hx]
  have hsm := I2.contDiff_of_diff hΘ
  have main : ∀ Q : MvPolynomial (FVar D W.rank V.rank) ℂ,
      pureTensorO ψ θ V W (fun _ => 1) s (fun _ => 1) BW G Q 0 =
        polyDeriv (MvPolynomial.aeval (fun v => MvPolynomial.C (c v) * MvPolynomial.X (vr.symm v)) Q)
          (letterDir X hq idx) Θ 0 := by
    intro Q
    induction Q using MvPolynomial.induction_on' with
    | add P P' hP hP' =>
      rw [map_add, map_add, I2.polyDeriv_add, ← hP, ← hP']
      rfl
    | monomial m a =>
      have e : MvPolynomial.monomial m a = a • MvPolynomial.monomial m (1 : ℂ) := by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      rw [e, map_smul, map_smul, I2.polyDeriv_smul, Pi.smul_apply, smul_eq_mul]
      congr 1
      have h2 : pureTensorO ψ θ V W (fun _ => 1) s (fun _ => 1) BW G
          (MvPolynomial.monomial m (1 : ℂ)) = opPow A m G := by
        have := (MvPolynomial.basisMonomials (FVar D W.rank V.rank) ℂ).constr_basis ℂ
          (fun k => opPow A k G) m
        rwa [MvPolynomial.coe_basisMonomials] at this
      rw [h2, opPow, key _ 0 hr0, h0, hg0, one_mul, (hops _).2]
      refine Eq.trans ?_ (GlobalTheory.Ker.FockOrigin.polyDeriv_aeval_monomial c vr.symm _ hsm m 0).symm
      congr 1
      rw [I2.ct_iter_eq_itD_ofFn]
      congr 1
      exact List.ofFn_getElem_eq_map _ u
  rw [main, MvPolynomial.aeval_rename]
  have e : ((fun v => MvPolynomial.C (c v) * MvPolynomial.X (vr.symm v)) ∘ vr :
      _ → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin V.rank)) = fun l => MvPolynomial.C c₀ * MvPolynomial.X l := by
    funext l
    simp only [Function.comp_apply, c, Equiv.symm_apply_apply]
  rw [e, aeval_scale c₀ hP, I2.polyDeriv_smul]
  rfl

end GlobalTheory.AdTh.Fock
