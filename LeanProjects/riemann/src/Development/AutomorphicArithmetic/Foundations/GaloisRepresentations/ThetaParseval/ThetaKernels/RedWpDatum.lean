import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.IsScalarOneOfComm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutDef
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutSubst
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaFunctionHeisenbergTranslate
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutReal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.HermitianFormMatrixSelfadjoint
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ArchimedeanChartGaussianVector

set_option synthInstance.maxHeartbeats 200000

section
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
theorem exists_isScalarF_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) {χS χT : (AEF F E)ˣ →* Circle}
    (hf : IsFinWeilF σ JS JT ξ₀ B.ψ χS χT of) (hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi)
    {p : GAF σ JS × GAF σ JT} (h1 : p.1 ∈ GQF σ JS) (h2 : p.2 ∈ GQF σ JT) : ∃ c : ℂ, ‖c‖ = 1 ∧ IsScalarF B ξ₀ of oi p c := by
  have R := fun f h => _root_.PositivityTheory.ThKW.rat_subst_k C (inv_mem h1) (inv_mem h2) (f := f) h
  have R' := fun f h => _root_.PositivityTheory.ThKW.rat_subst_k C h1 h2 (f := f) h
  obtain ⟨a, k, a1, a2, k1, k2, e1, e2⟩ := exists_partsF p
  have hoi : ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → oi p f = oi a f := fun f h => by
    rw [e1, map_mul, Module.End.mul_apply, hi.triv k.1 k1 k.2 k2 f h]
  have hof : ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → of p f = of k f := fun f h => by
    rw [e2, map_mul, Module.End.mul_apply, hf.triv a.1 a1 a.2 a2 f h]
  have hth := _root_.GlobalTheory.T.theta_function_heisenberg_translate F E σ B C.good nS nT JS JT ξ₀
  obtain ⟨c, hc, h⟩ := _root_.PositivityTheory.ThKW.schur_norm_k C (of p * oi p * substF σ JS JT p⁻¹)
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
theorem IsScalarF.mul_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi)
    (hcomm : ∀ p q f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → of p (oi q f) = oi q (of p f)) {p q : GAF σ JS × GAF σ JT} {c c' : ℂ}
    (h : IsScalarF B ξ₀ of oi p c) (h' : IsScalarF B ξ₀ of oi q c') (h1 : q.1 ∈ GQF σ JS) (h2 : q.2 ∈ GQF σ JT) :
    IsScalarF B ξ₀ of oi (p * q) (c * c') := fun f hf => by
  have t : IsThetaFunOF σ JS JT ξ₀ B.ψ (substF σ JS JT q f) := (_root_.PositivityTheory.ThKW.rat_subst_k C h1 h2 hf).1
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hcomm q p _ (hi.pres _ _ hf), h' f hf, map_smul,
    map_smul, h _ t, smul_smul, mul_comm c', substF_mul]
theorem half_add_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hε : IsHalfF σ ε) : (ε + cAF σ ε) * (ε + cAF σ ε) = ε + cAF σ ε := by
  have h3 : cAF σ ε * cAF σ ε = cAF σ ε := by rw [← map_mul, hε.idem]
  linear_combination hε.idem + h3 + 2 * hε.orth
theorem eta_cut_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (h2 : ResEtaF η 1) (hε : IsHalfF σ ε) (u : Eˣ) :
    η (cutRat _ (_root_.PositivityTheory.ThKW.half_add_k hB hε) u) * η (cutRat ε hε.idem (Units.map (σ : E →* E) u)) = η (cutRat ε hε.idem u) := by
  have h3 : cAF σ ε * cAF σ ε = cAF σ ε := by rw [← map_mul, hε.idem]
  have e1 : cutRat _ (_root_.PositivityTheory.ThKW.half_add_k hB hε) u = cutRat ε hε.idem u * cutRat _ h3 u := Units.ext (by
    rw [Units.val_mul, cutRat_val, cutRat_val, cutRat_val]
    linear_combination (-(incAF F E u - 1) ^ 2) * hε.orth)
  have e2 := GlobalTheory.SplitDetCharF.char_norm hB.cm h2 (cutRat _ h3 u) (cutRat ε hε.idem (Units.map (σ : E →* E) u)) (by
    rw [cutRat_val, cutRat_val, map_add, map_sub, map_mul, map_one,
      GlobalTheory.HeisLineF.cAF_cAF σ (GlobalTheory.SplitDetCharF.sig_invol hB.cm), cAF_incAF']
    rfl)
  rw [e1, map_mul, mul_assoc, e2, mul_one]
theorem real_data_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hs : CartF σ JS JT ξ₀ B θ s) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) (hcm : s * mMF σ JS JT θ (g, h) = mMF σ JS JT θ (g, h) * s)
    (hd : (b ⊗ₖ aᵀ - 1).det ≠ 0) :
    Integrable (gaussV (HMF JS JT ξ₀ (tauB B)) s (mMF σ JS JT θ (g⁻¹, h⁻¹))) volume ∧
      GlobalTheory.RealWeil.dP s (mMF σ JS JT θ (g, h)) ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧
      (∫ v, gaussV (HMF JS JT ξ₀ (tauB B)) s (mMF σ JS JT θ (g⁻¹, h⁻¹)) v) * ∏ v, tauB B v (b ⊗ₖ aᵀ - 1).det =
        r * (-s).det * ((∏ v, tauB B v (b ⊗ₖ aᵀ).det) * GlobalTheory.RealWeil.dP s (mMF σ JS JT θ (g, h))) := by
  obtain ⟨q1, q2⟩ := _root_.PositivityTheory.ThKW.det_mMF_k C ha hb
  have hH := _root_.GlobalTheory.T.hermitian_form_matrix_selfadjoint F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ
  have hU := _root_.GlobalTheory.T.archimedean_chart_gaussian_vector F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ θ C.inf ι C.chart (g⁻¹, h⁻¹)
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
theorem zF_rat_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hε : ε * ε = ε) {g : GAF σ JS} {h : GAF σ JT} {a b}
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
theorem phase_rat_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (h2 : ResEtaF η 1) (hε : IsHalfF σ ε) {Δ d N : E} (hΔ : Δ ≠ 0) (hd : d ≠ 0)
    (hN : N ≠ 0) {m : ℕ} (d1 : Δ * σ Δ = 1) (d2 : Δ * σ d = (-1) ^ m * d) {z : Circle}
    (v0 : z * η (cutRat ε hε.idem (Units.mk0 _ hΔ)) = 1) :
    (z : ℂ) * η (cutRat _ (_root_.PositivityTheory.ThKW.half_add_k C.good hε) (Units.mk0 _ hN * Units.mk0 _ hΔ)) =
      η (cutRat ε hε.idem ((-1) ^ m)) * η (cutRat _ (_root_.PositivityTheory.ThKW.half_add_k C.good hε) (Units.mk0 _ hN * Units.mk0 _ hd)) := by
  rw [← Circle.coe_mul, ← Circle.coe_mul]
  have u1 : Units.mk0 _ hΔ * Units.map (σ : E →* E) (Units.mk0 _ hΔ) = 1 := Units.ext d1
  have u2 : Units.mk0 _ hΔ * Units.map (σ : E →* E) (Units.mk0 _ hd) = (-1) ^ m * Units.mk0 _ hd :=
    Units.ext (by simpa using d2)
  exact congrArg _ (GlobalTheory.RatAut.phase_identity (η.comp (cutRat ε hε.idem)) (η.comp (cutRat _ (_root_.PositivityTheory.ThKW.half_add_k C.good hε)))
    (Units.map (σ : E →* E)) (_root_.PositivityTheory.ThKW.eta_cut_k C.good h2 hε) v0 u1 u2)
end PositivityTheory.ThKW
end
end
