import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GramDetNeZeroLocalBasisCofiniteStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GramDeterminantLogDifferentStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsTransitionMatrixGramStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicNormTransitionDetOneStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocalBasisGramDetLogNormStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PureTypeLatticesOrthogonalStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveZNeZeroStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackPureFrameOpenStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackPureNormStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCmPeriodEmbeddingStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.ExistsExtensionEmbeddingAlgClosedStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem flatGen_finNorm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ) (k : IntermediateField ℚ ℂ) [NumberField k] (hc : c.F ≤ k) (hM : ∀ b, (Z b).M ≤ k) (r : k) (ℓ : Nat.Primes), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → (∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P → y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U) → IsLineFn U τ φ → LinearIndependent (𝓞 E) e → IsConstMul U τ φ FU i e ρ → r ≠ 0 → (r : ℂ) * (Z true).z ^ D.p = ρ * (Z false).z ^ D.q → ∃ t : E, (∀ j : E →+* ℂ_[ℓ], Real.log ‖j t‖ + Real.log ‖j (IsCMField.complexConj E t)‖ + Real.log ‖j (gramE (FU.Di i) e).det‖ = -((D.p : ℝ) + D.q) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) ∧ (IsLocBasis (𝓞 E) ℓ e → ∀ j : E →+* ℂ_[ℓ], Real.log ‖j t‖ = 0) ∧ ∀ (j : k →+* ℂ_[ℓ]) (t₀ : ℝ), HasFinNorm U τ φ ℓ (j.comp (IntermediateField.inclusion hc).toRingHom) t₀ → t₀ = Real.log ‖j r‖ - Real.log ‖j ((((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) t)‖ - D.q * logIdeal ((j.comp (((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ))).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) + ((D.q : ℝ) - D.p) * (logIdeal ((j.comp (((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ))).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j ((((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) (H.rt : E))‖) := by
  intro E _ _ _ H D l Xo c g ty FU i Z U τ φ e ρ k _ hc hM r ℓ hty hrt hmem hline he hconst hr hz
  obtain ⟨P, hP, x, hx, X, v, w, hkK, hxl, hfr⟩ :=
    GlobalTheory.T.exists_cm_period_embedding E H D l Xo c g ty FU i Z τ ℓ k inferInstance hty hrt
  have hcard : Fintype.card (Fin D.p ⊕ Fin D.q) = (FU.Di i).p + (FU.Di i).q := by
    simp [(FU.sig i).1, (FU.sig i).2]
  obtain ⟨T, hT, hgram, hdet, -⟩ := GlobalTheory.T.exists_transition_matrix_gram E H (FU.Di i) (Fin D.p ⊕ Fin D.q) x e hcard he
  have hT0 : T.det ≠ 0 := hdet hxl.1
  have hge : (gramE (FU.Di i) e).det ≠ 0 := (GlobalTheory.T.gram_det_ne_zero_local_basis_cofinite E H (FU.Di i) _ e hcard he).1
  have hconj : (T.map (IsCMField.complexConj E)).det = IsCMField.complexConj E T.det :=
    (AlgEquiv.map_det (IsCMField.complexConj E) T).symm
  have hgdet : (gramE (FU.Di i) x).det
      = T.det * (gramE (FU.Di i) e).det * IsCMField.complexConj E T.det := by
    rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hconj]
  refine ⟨T.det, ?_, ?_, ?_⟩
  · intro j
    have h1 := GlobalTheory.T.gram_determinant_log_different E H (FU.Di i) _ x ℓ hxl j
    have n1 : ‖j T.det‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero j).2 hT0)
    have n2 : ‖j (gramE (FU.Di i) e).det‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero j).2 hge)
    have n3 : ‖j (IsCMField.complexConj E T.det)‖ ≠ 0 :=
      norm_ne_zero_iff.2 ((map_ne_zero j).2 (by simpa using hT0))
    rw [hgdet, map_mul, map_mul, norm_mul, norm_mul, Real.log_mul (mul_ne_zero n1 n2) n3,
      Real.log_mul n1 n2] at h1
    have hc2 : ((Fintype.card (Fin D.p ⊕ Fin D.q) : ℕ) : ℝ) = (D.p : ℝ) + D.q := by simp
    rw [hc2] at h1
    linarith
  · intro hel j
    rw [GlobalTheory.T.padic_norm_transition_det_one E H (FU.Di i) _ x e T ℓ hxl hel hT j, Real.log_one]
  · intro j t₀ hN
    obtain ⟨j', hj'⟩ := GlobalTheory.T.exists_extension_embedding_alg_closed k X.K ℂ_[ℓ] (IntermediateField.inclusion hkK).toRingHom j
    obtain ⟨V, hV, hVf, Tm, m'', δ, δ', v', w', hval, hδ, hδ', hlogδ, hlogδ', hA, hB, hfr', hiv, hiw⟩ :=
      GlobalTheory.T.cm_pack_pure_norm E H D l Xo c g ty FU i Z P hP X x hx τ ℓ j' v w hty hrt hxl hfr
    obtain ⟨hF, hφ⟩ := GlobalTheory.T.cm_pack_pure_frame_open E H D l Xo c g ty FU i Z P hP X x hx U τ φ e ρ T v w hty hrt
      hmem hline he hconst hxl.1 hT hfr
    have hF' : IsFramed U τ X.β X.y v' w' := ⟨hfr'.1, hF.2.1, hfr'.2.2⟩
    have hβ : j'.comp X.β = j.comp (IntermediateField.inclusion hc).toRingHom := by
      rw [← hj']; ext a; rfl
    haveI := hV
    haveI := hVf
    have hfin := hN V X.K j' X.β X.y v' w' Tm X.t X.m m'' hval hβ hF' hiv hiw
    have hchg := hline.chg X.K X.β X.y v w v' w' (δ • (1 : Matrix (Fin D.p) (Fin D.p) X.K))
      (δ' • (1 : Matrix (Fin D.q) (Fin D.q) X.K)) hF hF' hA hB
    simp only [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hchg
    have hφ0 := hline.ne X.K X.β X.y v w hF
    have hφ'0 := hline.ne X.K X.β X.y v' w' hF'
    have horth : ∀ a b, sesq (FU.Di i) (x (.inl a)) (x (.inr b)) = 0 := fun a b =>
      (GlobalTheory.T.pure_type_lattices_orthogonal E H (FU.Di i) g ty P hP _ _ (hx.1 a) (hx.2 b)).1
    obtain ⟨hG0, hGlog⟩ := GlobalTheory.T.local_basis_gram_det_log_norm E H (FU.Di i) D.p D.q x ℓ hxl horth
    have hzt : (Z true).z ^ D.p ≠ 0 := pow_ne_zero _ (GlobalTheory.T.curve_z_ne_zero E H _ (Z true))
    have hC : ((φ X.K X.y v w : X.K) : ℂ) * τ T.det = (r : ℂ) * τ (gramE (FU.Di i) (x ∘ Sum.inr)).det := by
      apply mul_right_cancel₀ hzt
      rw [hφ, ← hz]
      ring
    have hK : φ X.K X.y v w * X.β (tauE c τ T.det)
        = (IntermediateField.inclusion hkK).toRingHom r * X.β (tauE c τ (gramE (FU.Di i) (x ∘ Sum.inr)).det) :=
      Subtype.ext hC
    have hjE : j'.comp (X.β.comp (tauE c τ))
        = j.comp (((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) := by
      rw [← RingHom.comp_assoc, hβ, RingHom.comp_assoc]
    have happ : ∀ a : E, j' (X.β (tauE c τ a))
        = j ((((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) a) := fun a =>
      congrArg (fun f : E →+* ℂ_[ℓ] => f a) hjE
    have hjr : j' ((IntermediateField.inclusion hkK).toRingHom r) = j r := by
      rw [← hj']; rfl
    have nφ : ‖j' (φ X.K X.y v w)‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero j').2 hφ0)
    have nφ' : ‖j' (φ X.K X.y v' w')‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero j').2 hφ'0)
    have nδ : ‖j' δ‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero j').2 hδ)
    have nδ' : ‖j' δ'‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero j').2 hδ')
    have nr : ‖j r‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero j).2 (by simpa using hr))
    have nt : ‖j' (X.β (tauE c τ T.det))‖ ≠ 0 :=
      norm_ne_zero_iff.2 ((map_ne_zero j').2 ((map_ne_zero _).2 ((map_ne_zero _).2 hT0)))
    have nG : ‖j' (X.β (tauE c τ (gramE (FU.Di i) (x ∘ Sum.inr)).det))‖ ≠ 0 :=
      norm_ne_zero_iff.2 ((map_ne_zero j').2 ((map_ne_zero _).2 ((map_ne_zero _).2 hG0)))
    have hn : ‖j' (φ X.K X.y v w)‖ * ‖j' (X.β (tauE c τ T.det))‖
        = ‖j r‖ * ‖j' (X.β (tauE c τ (gramE (FU.Di i) (x ∘ Sum.inr)).det))‖ := by
      have h := congrArg (fun a => ‖j' a‖) hK
      simpa only [map_mul, norm_mul, hjr] using h
    have hl : Real.log ‖j' (φ X.K X.y v w)‖ + Real.log ‖j' (X.β (tauE c τ T.det))‖
        = Real.log ‖j r‖ + Real.log ‖j' (X.β (tauE c τ (gramE (FU.Di i) (x ∘ Sum.inr)).det))‖ := by
      rw [← Real.log_mul nφ nt, ← Real.log_mul nr nG, hn]
    have hm : ‖j' (φ X.K X.y v' w')‖ * ‖j' δ‖ ^ D.p = ‖j' (φ X.K X.y v w)‖ * ‖j' δ'‖ ^ D.q := by
      have h := congrArg (fun a => ‖j' a‖) hchg
      simp only [map_mul, map_pow, map_one, norm_mul, norm_pow, norm_one] at h
      linear_combination h
    have hlog : Real.log ‖j' (φ X.K X.y v' w')‖ + D.p * Real.log ‖j' δ‖
        = Real.log ‖j' (φ X.K X.y v w)‖ + D.q * Real.log ‖j' δ'‖ := by
      rw [← Real.log_pow, ← Real.log_pow, ← Real.log_mul nφ' (pow_ne_zero _ nδ),
        ← Real.log_mul nφ (pow_ne_zero _ nδ'), hm]
    have hGl := hGlog (j.comp (((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)))
    rw [RingHom.comp_apply, ← happ] at hGl
    rw [hjE, happ] at hlogδ
    rw [← happ]
    linear_combination -hfin + hlog + hl + hGl + (D.q : ℝ) * hlogδ' + ((D.q : ℝ) - D.p) * hlogδ

end GlobalTheory.CompanionTheory.Ar.Fl
