import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutTrace
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutReal
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutEta
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutProd
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutGen
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutSubst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDistributionInvariantRationalTarget
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPointEqRealMulFiniteBothOrdersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormRealCoordinateMatrixHermitianDetNeZStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealCoordinateActionUnitaryPreservesHermitianForStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealChartAdeleTensorAdmissibleCMBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCMStatement

noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}

variable {η : (AEF F E)ˣ →* Circle} {ε : AEF F E} {of oi : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)}

variable (σ JS JT) in

def substF (p : GAF σ JS × GAF σ JT) : Module.End ℂ (WOF F E nS nT → ℂ) :=
  LinearMap.funLeft ℂ ℂ (actOF σ JS JT p.1⁻¹ p.2⁻¹)

theorem substF_apply (p : GAF σ JS × GAF σ JT) (f : WOF F E nS nT → ℂ) :
    substF σ JS JT p f = fun x => f (actOF σ JS JT p.1⁻¹ p.2⁻¹ x) := rfl

theorem substF_mul (p q : GAF σ JS × GAF σ JT) (f : WOF F E nS nT → ℂ) :
    substF σ JS JT (p * q) f = substF σ JS JT p (substF σ JS JT q f) := by
  funext x
  show f (actOF σ JS JT (p.1 * q.1)⁻¹ (p.2 * q.2)⁻¹ x) = f (actOF σ JS JT q.1⁻¹ q.2⁻¹ (actOF σ JS JT p.1⁻¹ p.2⁻¹ x))
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, actOF_mul]

theorem substF_one (f : WOF F E nS nT → ℂ) : substF σ JS JT 1 f = f := by
  funext x
  show f (actOF σ JS JT 1⁻¹ 1⁻¹ x) = f x
  rw [inv_one, inv_one, GlobalTheory.FinLatF.actOF_one]

variable (ξ₀ B of oi) in

def IsScalarF (p : GAF σ JS × GAF σ JT) (c : ℂ) : Prop :=
  ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → of p (oi p f) = c • substF σ JS JT p f

theorem exists_partsF (p : GAF σ JS × GAF σ JT) : ∃ a k : GAF σ JS × GAF σ JT, a.1 ∈ GinfCF σ JS ∧ a.2 ∈ GinfCF σ JT ∧
    k.1 ∈ GfCF σ JS ∧ k.2 ∈ GfCF σ JT ∧ p = a * k ∧ p = k * a := by
  obtain ⟨a, ha, k, hk, e1, e1'⟩ := GlobalTheory.T.unitaryAdelicPoint_eq_real_mul_finite_both_orders F E σ nS JS p.1
  obtain ⟨b, hb, l, hl, e2, e2'⟩ := GlobalTheory.T.unitaryAdelicPoint_eq_real_mul_finite_both_orders F E σ nT JT p.2
  exact ⟨(a, b), (k, l), ha, hb, hk, hl, Prod.ext e1 e2, Prod.ext e1' e2'⟩

theorem exists_isScalarF (C : Ctx σ B JS JT ξ₀ θ ι) {χS χT : (AEF F E)ˣ →* Circle}
    (hf : IsFinWeilF σ JS JT ξ₀ B.ψ χS χT of) (hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi)
    {p : GAF σ JS × GAF σ JT} (h1 : p.1 ∈ GQF σ JS) (h2 : p.2 ∈ GQF σ JT) : ∃ c : ℂ, ‖c‖ = 1 ∧ IsScalarF B ξ₀ of oi p c := by
  have R := fun f h => rat_subst C (inv_mem h1) (inv_mem h2) (f := f) h
  have R' := fun f h => rat_subst C h1 h2 (f := f) h
  obtain ⟨a, k, a1, a2, k1, k2, e1, e2⟩ := exists_partsF p
  have hoi : ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → oi p f = oi a f := fun f h => by
    rw [e1, map_mul, Module.End.mul_apply, hi.triv k.1 k1 k.2 k2 f h]
  have hof : ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → of p f = of k f := fun f h => by
    rw [e2, map_mul, Module.End.mul_apply, hf.triv a.1 a1 a.2 a2 f h]
  have hth := GlobalTheory.T.theta_function_heisenberg_invariant F E σ B C.good nS nT JS JT ξ₀
  obtain ⟨c, hc, h⟩ := schur_norm C (of p * oi p * substF σ JS JT p⁻¹)
    (fun f h => hf.pres _ _ (hi.pres _ _ (R f h).1))
    (fun u f h => by
      have t1 : IsThetaFunOF σ JS JT ξ₀ B.ψ (substF σ JS JT p⁻¹ f) := (R f h).1
      have t2 : substF σ JS JT p⁻¹ (heisOF σ JS JT ξ₀ B.ψ u f) =
        heisOF σ JS JT ξ₀ B.ψ (actOF σ JS JT p.1⁻¹ p.2⁻¹ u) (substF σ JS JT p⁻¹ f) := (R f h).2.1 u
      simp only [Module.End.mul_apply]
      rw [t2, hoi _ (hth _ _ t1), hi.Heisenberg₂ a.1 a1 a.2 a2 _ _ t1, hof _ (hth _ _ (hi.pres _ _ t1)),
        hf.Heisenberg₂ k.1 k1 k.2 k2 _ _ (hi.pres _ _ t1), ← actOF_mul, ← actOF_mul, ← hof _ (hi.pres _ _ t1), ← hoi _ t1,
        show k.1 * a.1 = p.1 from congrArg Prod.fst e2.symm, show k.2 * a.2 = p.2 from congrArg Prod.snd e2.symm,
        mul_inv_cancel, mul_inv_cancel, GlobalTheory.FinLatF.actOF_one])
    (fun μ 𝓕 hμ h𝓕 f h => by
      have t1 : IsThetaFunOF σ JS JT ξ₀ B.ψ (substF σ JS JT p⁻¹ f) := (R f h).1
      simp only [Module.End.mul_apply]
      rw [hf.unit μ 𝓕 hμ h𝓕 _ _ (hi.pres _ _ t1), hi.unit μ 𝓕 hμ h𝓕 _ _ t1]
      exact (R f h).2.2 μ 𝓕 hμ h𝓕)
  refine ⟨c, hc, fun f hf' => ?_⟩
  have := h (substF σ JS JT p f) (R' f hf').1
  simp only [Module.End.mul_apply] at this
  rwa [← substF_mul, inv_mul_cancel, substF_one] at this

theorem IsScalarF.mul (C : Ctx σ B JS JT ξ₀ θ ι) (hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi)
    (hcomm : ∀ p q f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → of p (oi q f) = oi q (of p f)) {p q : GAF σ JS × GAF σ JT} {c c' : ℂ}
    (h : IsScalarF B ξ₀ of oi p c) (h' : IsScalarF B ξ₀ of oi q c') (h1 : q.1 ∈ GQF σ JS) (h2 : q.2 ∈ GQF σ JT) :
    IsScalarF B ξ₀ of oi (p * q) (c * c') := fun f hf => by
  have t : IsThetaFunOF σ JS JT ξ₀ B.ψ (substF σ JS JT q f) := (rat_subst C h1 h2 hf).1
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hcomm q p _ (hi.pres _ _ hf), h' f hf, map_smul,
    map_smul, h _ t, smul_smul, mul_comm c', substF_mul]

theorem comm_inv {G M : Type} [Group G] [Monoid M] (m : G →* M) {x : M} {p : G} (h : x * m p = m p * x) :
    x * m p⁻¹ = m p⁻¹ * x := by
  calc x * m p⁻¹ = m p⁻¹ * (m p * x) * m p⁻¹ := by rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
    _ = m p⁻¹ * x := by rw [← h, mul_assoc, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

theorem IsRatF.det_ne {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) {g : GAF σ J} {a} (h : IsRatF σ J g a) :
    a.det ≠ 0 := fun h0 => by
  have := congrArg Matrix.det h.unitary
  rw [Matrix.det_mul, h0, mul_zero] at this
  exact hJ.2 this.symm

def cutRat (x : AEF F E) (h : x * x = x) : Eˣ →* (AEF F E)ˣ :=
  (Units.map (GlobalTheory.SplitDetCharF.cut x h)).comp (Units.map (incAF F E).toMonoidHom)

theorem cutRat_val (x : AEF F E) (h : x * x = x) (u : Eˣ) : (cutRat x h u : AEF F E) = (1 - x) + x * incAF F E u := rfl

theorem cAF_incAF' (x : E) : cAF σ (incAF F E x) = incAF F E (σ x) := GlobalTheory.HeisLineF.cAF_incAF σ x

theorem half_add (hB : B.IsGood σ) (hε : IsHalfF σ ε) : (ε + cAF σ ε) * (ε + cAF σ ε) = ε + cAF σ ε := by
  have h3 : cAF σ ε * cAF σ ε = cAF σ ε := by rw [← map_mul, hε.idem]
  linear_combination hε.idem + h3 + 2 * hε.orth

theorem eta_cut (hB : B.IsGood σ) (h2 : ResEtaF η 1) (hε : IsHalfF σ ε) (u : Eˣ) :
    η (cutRat _ (half_add hB hε) u) * η (cutRat ε hε.idem (Units.map (σ : E →* E) u)) = η (cutRat ε hε.idem u) := by
  have h3 : cAF σ ε * cAF σ ε = cAF σ ε := by rw [← map_mul, hε.idem]
  have e1 : cutRat _ (half_add hB hε) u = cutRat ε hε.idem u * cutRat _ h3 u := Units.ext (by
    rw [Units.val_mul, cutRat_val, cutRat_val, cutRat_val]
    linear_combination (-(incAF F E u - 1) ^ 2) * hε.orth)
  have e2 := GlobalTheory.SplitDetCharF.char_norm hB.cm h2 (cutRat _ h3 u) (cutRat ε hε.idem (Units.map (σ : E →* E) u)) (by
    rw [cutRat_val, cutRat_val, map_add, map_sub, map_mul, map_one,
      GlobalTheory.HeisLineF.cAF_cAF σ (GlobalTheory.SplitDetCharF.sig_invol hB.cm), cAF_incAF']
    rfl)
  rw [e1, map_mul, mul_assoc, e2, mul_one]

theorem cutDet_rat {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) {g : GAF σ J} {a} (h : IsRatF σ J g a)
    (x : AEF F E) (hx : x * x = x) : GlobalTheory.SplitDetCharF.cutDet σ J x hx g = cutRat x hx (Units.mk0 _ (h.det_ne hJ)) :=
  Units.ext (by
    rw [GlobalTheory.SplitDetCharF.cutDet_val, cutRat_val, show mtF σ J g = _ from h, Units.val_mk0, RingHom.map_det]
    rfl)

structure Parts (C : Ctx σ B JS JT ξ₀ θ ι) (hc : HeisClosedF σ JS JT ξ₀ B.ψ) (lam : ℕ →* ℂ)
    (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)) (η : (AEF F E)ˣ →* Circle) (ε : AEF F E)
    (of oi : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)) : Prop where
  res : ResEtaF η 1
  half : IsHalfF σ ε
  prod : ∀ (x : E) (k : ℕ), x ≠ 0 → (k : ℚ) = |Algebra.norm ℚ x| → ∀ y : (AEF F E)ˣ,
      (y : AEF F E) = (ε + cAF σ ε) * incAF F E x + (1 - (ε + cAF σ ε)) →
        ∃ r : ℝ, 0 < r ∧ (η y : ℂ) * lam k * ∏ v, tauB B v x = r
  hf : IsFinWeilF σ JS JT ξ₀ B.ψ (η ^ nS) (η ^ nT) of
  hof : ∀ p (f : thetaSubF σ JS JT ξ₀ B.ψ), of p f = (zF σ JS JT η ε half.idem p : ℂ) • (Om p f : WOF F E nS nT → ℂ)
  hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi
  vac : ∀ s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ, s * s = 1 → (HMF JS JT ξ₀ (tauB B) * s).PosDef → ∀ p,
      s * mMF σ JS JT θ p = mMF σ JS JT θ p * s → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsVacF σ JS JT ξ₀ B.ψ ι s f →
        oi p f = GlobalTheory.RealWeil.dP s (mMF σ JS JT θ p) • f

theorem real_data (C : Ctx σ B JS JT ξ₀ θ ι) (hs : CartF σ JS JT ξ₀ B θ s) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) (hcm : s * mMF σ JS JT θ (g, h) = mMF σ JS JT θ (g, h) * s)
    (hd : (b ⊗ₖ aᵀ - 1).det ≠ 0) :
    Integrable (gaussV (HMF JS JT ξ₀ (tauB B)) s (mMF σ JS JT θ (g⁻¹, h⁻¹))) volume ∧
      GlobalTheory.RealWeil.dP s (mMF σ JS JT θ (g, h)) ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧
      (∫ v, gaussV (HMF JS JT ξ₀ (tauB B)) s (mMF σ JS JT θ (g⁻¹, h⁻¹)) v) * ∏ v, tauB B v (b ⊗ₖ aᵀ - 1).det =
        r * (-s).det * ((∏ v, tauB B v (b ⊗ₖ aᵀ).det) * GlobalTheory.RealWeil.dP s (mMF σ JS JT θ (g, h))) := by
  obtain ⟨q1, q2⟩ := det_mMF C ha hb
  have hH := GlobalTheory.T.hermitianFormRealCoordinateMatrix_hermitian_det_ne_zero F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ
  have hU := GlobalTheory.T.realCoordinateAction_unitary_preserves_hermitianForm F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ θ C.inf ι C.chart (g⁻¹, h⁻¹)
  have c1 : s * mMF σ JS JT θ (g⁻¹, h⁻¹) = mMF σ JS JT θ (g⁻¹, h⁻¹) * s := by
    have := comm_inv (mMF σ JS JT θ) hcm
    rwa [Prod.inv_mk] at this
  have c2 : mMF σ JS JT θ (g⁻¹, h⁻¹) * mMF σ JS JT θ (g, h) = 1 := by
    rw [← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one]
  have c3 : (mMF σ JS JT θ (g⁻¹, h⁻¹) - 1).det ≠ 0 := by
    rw [q2]
    exact Finset.prod_ne_zero_iff.2 fun v _ => (map_ne_zero _).2 hd
  rw [← q1, ← q2]
  exact integral_gaussV hH.1 hs.sq hs.pos hU c1 c2 c3

theorem zF_rat (C : Ctx σ B JS JT ξ₀ θ ι) (hε : ε * ε = ε) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) (hΔ : (b ⊗ₖ aᵀ).det ≠ 0) :
    zF σ JS JT η ε hε (g, h) * η (cutRat ε hε (Units.mk0 _ hΔ)) = 1 := by
  have da := ha.det_ne C.hS
  have db := hb.det_ne C.hT
  have e1 := cutDet_rat C.hT hb ε hε
  rw [map_inv, inv_eq_iff_eq_inv] at e1
  have e2 := cutDet_rat C.hS ha ε hε
  have u0 : Units.mk0 _ hΔ = Units.mk0 _ db ^ nS * Units.mk0 _ da ^ nT := Units.ext (by
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_mk0, Units.val_mk0,
      Matrix.det_kronecker, Matrix.det_transpose, Fintype.card_fin, Fintype.card_fin])
  unfold zF
  rw [u0, e1, e2]
  simp only [MonoidHom.pow_apply, map_mul, map_pow, map_inv]
  generalize η (cutRat ε hε (Units.mk0 _ da)) = x
  generalize η (cutRat ε hε (Units.mk0 _ db)) = y
  rw [mul_comm (y ^ nS), mul_mul_mul_comm, inv_mul_cancel, inv_mul_cancel, one_mul]

theorem phase_rat (C : Ctx σ B JS JT ξ₀ θ ι) (h2 : ResEtaF η 1) (hε : IsHalfF σ ε) {Δ d N : E} (hΔ : Δ ≠ 0) (hd : d ≠ 0)
    (hN : N ≠ 0) {m : ℕ} (d1 : Δ * σ Δ = 1) (d2 : Δ * σ d = (-1) ^ m * d) {z : Circle}
    (v0 : z * η (cutRat ε hε.idem (Units.mk0 _ hΔ)) = 1) :
    (z : ℂ) * η (cutRat _ (half_add C.good hε) (Units.mk0 _ hN * Units.mk0 _ hΔ)) =
      η (cutRat ε hε.idem ((-1) ^ m)) * η (cutRat _ (half_add C.good hε) (Units.mk0 _ hN * Units.mk0 _ hd)) := by
  rw [← Circle.coe_mul, ← Circle.coe_mul]
  have u1 : Units.mk0 _ hΔ * Units.map (σ : E →* E) (Units.mk0 _ hΔ) = 1 := Units.ext d1
  have u2 : Units.mk0 _ hΔ * Units.map (σ : E →* E) (Units.mk0 _ hd) = (-1) ^ m * Units.mk0 _ hd :=
    Units.ext (by simpa using d2)
  exact congrArg _ (GlobalTheory.RatAut.phase_identity (η.comp (cutRat ε hε.idem)) (η.comp (cutRat _ (half_add C.good hε)))
    (Units.map (σ : E →* E)) (eta_cut C.good h2 hε) v0 u1 u2)

theorem Parts.prod' {C : Ctx σ B JS JT ξ₀ θ ι} (P : Parts C hc lam Om η ε of oi) {N x : E} (hN : N ≠ 0) (hx : x ≠ 0)
    {c n : ℕ} (h : ((c * n : ℕ) : ℚ) = |Algebra.norm ℚ (N * x)|) : ∃ r : ℝ, 0 < r ∧
      (η (cutRat _ (half_add C.good P.half) (Units.mk0 _ hN * Units.mk0 _ hx)) : ℂ) * (lam c * lam n) *
        ((∏ v, tauB B v N) * ∏ v, tauB B v x) = r := by
  obtain ⟨r, p, e⟩ := P.prod _ _ (mul_ne_zero hN hx) h (cutRat _ (half_add C.good P.half) (Units.mk0 _ hN * Units.mk0 _ hx))
    (by rw [cutRat_val, add_comm, Units.val_mul, Units.val_mk0, Units.val_mk0])
  refine ⟨r, p, ?_⟩
  rw [← e, map_mul lam, ← Finset.prod_mul_distrib]
  simp only [map_mul]

theorem Parts.kappa {C : Ctx σ B JS JT ξ₀ θ ι} (P : Parts C hc lam Om η ε of oi)
    (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om) (hs : CartF σ JS JT ξ₀ B θ s) {g : GAF σ JS} {h : GAF σ JT}
    (hcm : s * mMF σ JS JT θ (g, h) = mMF σ JS JT θ (g, h) * s) {c : ℂ} (hc0 : c ≠ 0) (H : IsScalarF B ξ₀ of oi (g, h) c)
    (f : thetaSubF σ JS JT ξ₀ B.ψ) (f1 : Fixes (opFF hc w) (latF F E nS nT Λ) f) (f2 : IsVacF σ JS JT ξ₀ B.ψ ι s f)
    (x : WOF F E nS nT) :
    (f : WOF F E nS nT → ℂ) (actOF σ JS JT g⁻¹ h⁻¹ x) = (c⁻¹ * GlobalTheory.RealWeil.dP s (mMF σ JS JT θ (g, h)) *
      zF σ JS JT η ε P.half.idem (g, h) *
      (lam (idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h)))))⁻¹) *
      ((sumOp (opFF hc w) (latF F E nS nT Λ)
        ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))) f : thetaSubF σ JS JT ξ₀ B.ψ) : WOF F E nS nT → ℂ) x := by
  have e1 := congrFun (H f f.2) x
  rw [P.vac s hs.sq hs.pos (g, h) hcm f f.2 f2, map_smul, P.hof, hO.vac _ f f1, normOp, Submodule.coe_smul] at e1
  simp only [Pi.smul_apply, smul_eq_mul, substF_apply] at e1
  rw [← one_mul (f.1 _), ← inv_mul_cancel₀ hc0, mul_assoc, ← e1]
  ring

theorem scalar_const (C : Ctx σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om) (P : Parts C hc lam Om η ε of oi) (hs : CartF σ JS JT ξ₀ B θ s) :
    ∃ e s₀ : ℂ, s₀ ≠ 0 ∧ ∀ g h a b, IsRatF σ JS g a → IsRatF σ JT h⁻¹ b →
      s * mMF σ JS JT θ (g, h) = mMF σ JS JT θ (g, h) * s → (b ⊗ₖ aᵀ - 1).det ≠ 0 →
      ∀ c : ℂ, c ≠ 0 → IsScalarF B ξ₀ of oi (g, h) c → ∃ r : ℝ, 0 < r ∧ c * e = r * s₀ := by
  refine ⟨(-s).det, η (cutRat ε P.half.idem ((-1) ^ Fintype.card (Fin nT × Fin nS))), Circle.coe_ne_zero _,
    fun g h a b ha hb hcm hd c hc0 H => ?_⟩
  obtain ⟨d1, d2⟩ := det_kron C ha hb
  have hΔ := left_ne_zero_of_mul_eq_one d1
  obtain ⟨hbij, n, t, c₀, N, M, hn, hc₀, hN, t1, t2, g1, g2, i1, i2⟩ := finite_data C hG hR hO ha hb hΔ hd
  obtain ⟨hI, hδ0, r₂, p₂, h2⟩ := real_data C hs ha hb hcm hd
  obtain ⟨r₁, p₁, h1⟩ := gauss_mul_integral C hG hR hO hs ha hb hbij hI _ (P.kappa hO hs hcm hc0 H) n t t1 t2
  rw [g1] at h1
  have hN' : (N : E) ^ M ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hN)
  obtain ⟨r₃, p₃, h3⟩ := P.prod' hN' hd i1
  obtain ⟨r₄, p₄, h4⟩ := P.prod' hN' hΔ i2
  exact GlobalTheory.RatAut.final_algebra p₁ p₂ p₃ p₄ hn hc0 hδ0 (Circle.coe_ne_zero _) h1 h2 h3 h4 g2
    (phase_rat C P.res P.half hΔ hd hN' d1 d2 (zF_rat C P.half.idem ha hb hΔ))

set_option maxHeartbeats 1000000 in

theorem isScalar_one_of_comm (C : Ctx σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om) (P : Parts C hc lam Om η ε of oi) (hs : CartF σ JS JT ξ₀ B θ s)
    {g : GAF σ JS} {h : GAF σ JT} (hg : g ∈ GQF σ JS) (hh : h ∈ GQF σ JT)
    (hcm : s * mMF σ JS JT θ (g, h) = mMF σ JS JT θ (g, h) * s) : IsScalarF B ξ₀ of oi (g, h) 1 := by
  obtain ⟨a, ha⟩ := exists_isRatF hg
  obtain ⟨b, hb⟩ := exists_isRatF (inv_mem hh)
  obtain ⟨e, s₀, hs₀, H⟩ := scalar_const C hG hR hO P hs
  obtain ⟨t, ht, ht'⟩ := (infinite_norm_one C).exists_notMem_finite
    ((GlobalTheory.RatAut.finite_det_smul_sub_one (b ⊗ₖ aᵀ)).union (GlobalTheory.RatAut.finite_det_smul_sub_one
      ((1 : Matrix (Fin nT) (Fin nT) E) ⊗ₖ (1 : Matrix (Fin nS) (Fin nS) E)ᵀ)))
  rw [Set.mem_union, not_or] at ht'
  obtain ⟨k, rk⟩ := exists_of_unitary (σ := σ) C.hT (a := t • 1) (by
    have e : ((t • (1 : Matrix (Fin nT) (Fin nT) E)).map σ)ᵀ = σ t • 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]
    rw [e, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, show t * σ t = 1 from ht, one_smul])
  have hk := rk.mem
  have hcomm := fin_inf_comm C hO (fun p => ⟨_, P.hof p⟩) P.hi
  have ck : s * mMF σ JS JT θ (1, k⁻¹) = mMF σ JS JT θ (1, k⁻¹) * s := by
    have := comm_inv (mMF σ JS JT θ) (hs.cen k t rk)
    rwa [Prod.inv_mk, inv_one] at this
  obtain ⟨c, hc1, sc⟩ := exists_isScalarF (p := (g, h)) C P.hf P.hi hg hh
  obtain ⟨c', hc', sc'⟩ := exists_isScalarF (p := (1, k⁻¹)) C P.hf P.hi (one_mem _) (inv_mem hk)
  have hc0 : c ≠ 0 := norm_ne_zero_iff.1 (hc1 ▸ one_ne_zero)
  have hc0' : c' ≠ 0 := norm_ne_zero_iff.1 (hc' ▸ one_ne_zero)
  obtain ⟨r', p', e'⟩ := H 1 k⁻¹ 1 (t • 1) (isRatF_one JS) (by rwa [inv_inv]) ck
    (by rw [Matrix.smul_kronecker]; exact ht'.2) c' hc0' sc'
  obtain ⟨r, p, e''⟩ := H (g * 1) (h * k⁻¹) a (t • b) (by rwa [mul_one])
    (by
      have := rk.mul hb
      rwa [Matrix.smul_mul, Matrix.one_mul, ← inv_inv k, ← _root_.mul_inv_rev] at this)
    (by rw [← Prod.mk_mul_mk, map_mul, ← mul_assoc, hcm, mul_assoc, ck, mul_assoc])
    (by rw [Matrix.smul_kronecker]; exact ht'.1) (c * c') (mul_ne_zero hc0 hc0')
    (sc.mul C P.hi hcomm sc' (one_mem _) (inv_mem hk))
  have q' : (r' : ℂ) ≠ 0 := by exact_mod_cast p'.ne'
  have e1 : c = ((r / r' : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, eq_div_iff q']
    refine mul_right_cancel₀ hs₀ ?_
    rw [← e'', mul_assoc, ← e', mul_assoc]
  have e2 : r / r' = 1 := by
    rw [e1, Complex.norm_real, Real.norm_of_nonneg (div_pos p p').le] at hc1
    exact hc1
  rwa [e1, e2, Complex.ofReal_one] at sc

theorem datumEta : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E), GoodLat Λ → RatSD σ JS JT ξ₀ Λ →
      ∀ (hc : HeisClosedF σ JS JT ξ₀ B.ψ) (w : 𝓞 E) (lam : ℕ →* ℂ)
        (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)), IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om →
      ∀ η : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF η → ResEtaF η 1 → HasExp B.emb η (fun _ => 1) → UnramInert σ η →
        ∃ ω, IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ (η ^ nS) (η ^ nT) ω := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ h0 hξ Λ hG hR hc w lam Om hO η h1 h2 h3 h4
  obtain ⟨θ, hθ⟩ := (GlobalTheory.T.standardTraceAddChar_isStandardChar_of_admissibleCMBase F E σ B hB).2.1
  obtain ⟨ι, hι⟩ := GlobalTheory.T.exists_realChart_adeleTensor_admissibleCMBase F E σ B hB θ hθ
  have C : Ctx σ B JS JT ξ₀ θ ι := ⟨hB, hS, hT, h0, hξ, hθ, hι⟩
  obtain ⟨ε, hε, hprod⟩ := eta_prod hB h1 h2 h3 h4 hO.good hO.sqrt
  obtain ⟨of, hf, hof⟩ := exists_fin C hO h1 h2 hε
  obtain ⟨oi, hi, hvac⟩ := exists_inf C
  have P : Parts C hc lam Om η ε of oi := ⟨h2, hε, hprod, hf, hof, hi, hvac⟩
  have hcomm := fin_inf_comm C hO (fun p => ⟨_, hof p⟩) hi
  refine datum_of_aut C hG hO h1 h2 hf (fun p => ⟨_, hof p⟩) hi fun γ hγ γ' hγ' f hf' => ?_
  have := rat_gen C (fun p => IsScalarF B ξ₀ of oi p 1)
    (fun p q _ _ q1 q2 a b => mul_one (1 : ℂ) ▸ a.mul C hi hcomm b q1 q2)
    (fun p s p1 p2 hs hcm => isScalar_one_of_comm C hG hR hO P hs p1 p2 hcm) (γ, γ') hγ hγ' f hf'
  rw [this, one_smul]
  show f (actOF σ JS JT γ⁻¹ γ'⁻¹ 0) = f 0
  rw [actOF, Matrix.mul_zero, Matrix.zero_mul]

end PositivityTheory.ThKW

end
