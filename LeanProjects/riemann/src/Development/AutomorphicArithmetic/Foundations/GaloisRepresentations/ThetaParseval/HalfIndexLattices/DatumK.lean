import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab

noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA

namespace UpperTheory.TP.W

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}
variable {η κ χS χT : (AEF F E)ˣ →* Circle} {ε : AEF F E} {of oi : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)}

theorem resEta_mul (h2 : ResEtaF η 1) (hκ : IsKap σ lam κ) : ResEtaF (η * κ) 1 :=
  ⟨h2.1, fun e he a => by rw [MonoidHom.mul_apply, hκ.base a, mul_one]; exact h2.2 e he a⟩

structure PartsK (C : Ctx σ B JS JT ξ₀ θ ι) (hc : HeisClosedF σ JS JT ξ₀ B.ψ) (lam : ℕ →* ℂ)
    (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)) (η χS χT : (AEF F E)ˣ →* Circle) (ε : AEF F E)
    (of oi : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)) : Prop where
  res : ResEtaF η 1
  half : IsHalfF σ ε
  prod : ∀ (x : E) (k : ℕ), x ≠ 0 → (k : ℚ) = |Algebra.norm ℚ x| → ∀ y : (AEF F E)ˣ,
      (y : AEF F E) = (ε + cAF σ ε) * incAF F E x + (1 - (ε + cAF σ ε)) →
        ∃ r : ℝ, 0 < r ∧ (η y : ℂ) * lam k * ∏ v, tauB B v x = r
  hf : IsFinWeilF σ JS JT ξ₀ B.ψ χS χT of
  hof : ∀ p (f : thetaSubF σ JS JT ξ₀ B.ψ), of p f = (zF σ JS JT η ε half.idem p : ℂ) • (Om p f : WOF F E nS nT → ℂ)
  hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi
  vac : ∀ s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ, s * s = 1 → (HMF JS JT ξ₀ (tauB B) * s).PosDef → ∀ p,
      s * mMF σ JS JT θ p = mMF σ JS JT θ p * s → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsVacF σ JS JT ξ₀ B.ψ ι s f →
        oi p f = GlobalTheory.RealWeil.dP s (mMF σ JS JT θ p) • f

theorem PartsK.prod' {C : Ctx σ B JS JT ξ₀ θ ι} (P : PartsK C hc lam Om η χS χT ε of oi) {N x : E} (hN : N ≠ 0) (hx : x ≠ 0)
    {c n : ℕ} (h : ((c * n : ℕ) : ℚ) = |Algebra.norm ℚ (N * x)|) : ∃ r : ℝ, 0 < r ∧
      (η (cutRat _ (half_add C.good P.half) (Units.mk0 _ hN * Units.mk0 _ hx)) : ℂ) * (lam c * lam n) *
        ((∏ v, tauB B v N) * ∏ v, tauB B v x) = r := by
  obtain ⟨r, p, e⟩ := P.prod _ _ (mul_ne_zero hN hx) h (cutRat _ (half_add C.good P.half) (Units.mk0 _ hN * Units.mk0 _ hx))
    (by rw [cutRat_val, add_comm, Units.val_mul, Units.val_mk0, Units.val_mk0])
  refine ⟨r, p, ?_⟩
  rw [← e, map_mul lam, ← Finset.prod_mul_distrib]
  simp only [map_mul]

theorem PartsK.kappa {C : Ctx σ B JS JT ξ₀ θ ι} (P : PartsK C hc lam Om η χS χT ε of oi)
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

end UpperTheory.TP.W

end
