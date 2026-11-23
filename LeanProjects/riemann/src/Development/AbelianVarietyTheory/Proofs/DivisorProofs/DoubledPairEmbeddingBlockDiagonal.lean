import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxSymplecticDoubledHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewDeterminantNeZeroFirstSpace
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer
open GlobalTheory.DblDatum

noncomputable section

namespace GlobalTheory.DblDiagValue

theorem absE_det {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (hJ : J.det ≠ 0) (h : UA σ J) :
    absE F E (Matrix.GeneralLinearGroup.det h.1) = 1 := by
  have hG : IsUnit (incM F J).det := by
    have e : (incM F J).det = inclR (F := F) (AF F) J.det := by
      rw [incM, RingHom.map_det]; rfl
    rw [e]
    exact (Ne.isUnit hJ).map _
  have hd := congrArg Matrix.det (show (h.1.1)ᵀ * incM F J * (h.1.1).map (cA σ) = incM F J from h.2)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    show (h.1.1.map (cA σ)).det = cA σ h.1.1.det from ((cA σ).toRingHom.map_det _).symm] at hd
  have key : cA σ h.1.1.det * h.1.1.det = 1 := hG.mul_left_cancel (by linear_combination hd)
  have hu : conjUnit σ (Matrix.GeneralLinearGroup.det h.1) * Matrix.GeneralLinearGroup.det h.1 = 1 := by
    ext
    exact key
  have h2 := congrArg (absE F E) hu
  rw [map_mul, absE_conjUnit, map_one, ← sq] at h2
  exact (pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).1 h2

theorem apply_zero_diag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (Xs : Spc F E n) (W : Spc F E d) (M : Model σ Xs W) (χX χW : Chr F E) (om : Rep σ Xs W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ →
    ∀ W₂ : Spc F E (d + d), W₂.J = dblGram finSumFinEquiv W.J →
    ∀ i : UA σ W.J × UA σ W.J →* UA σ W₂.J, (∀ h h', mat (i (h, h')) = blkMat finSumFinEquiv (mat h) (mat h')) →
    ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F Xs.J) (incM F W₂.J)) (Fin n × Fin (d + d)),
      (∀ x : Matrix (Fin n) (Fin (d + d)) E, ∃ y z : Fin n × Fin (d + d) → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      (∀ u, (∀ i, u i ∈ diagSub (AE F E) finSumFinEquiv) → (co.e u).1 = 0) →
      (∀ u, (∀ i, u i ∈ antiSub (AE F E) finSumFinEquiv) → (co.e u).2 = 0) →
    ∀ om₂ : Rep σ Xs W₂, IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F Xs.J) (incM F W₂.J) co χX 1 om₂ →
    ∀ h : UA σ W.J, ∀ Φ ∈ schA F (Fin n × Fin (d + d)),
      om₂ (1, i (h, h)) Φ 0 = ((χX (Matrix.GeneralLinearGroup.det h.1) : Circle) : ℂ) * Φ 0 := by
  intro F E _ _ _ _ _ σ B n d Xs W M χX χW om r s' r₁ s₁ hP W₂ hW₂ i hi co _ hΔ _ om₂ hom h Φ hΦ
  obtain ⟨⟨-, dd, omd, hdc, ⟨-, hus, hSR⟩, hbox⟩, -, -⟩ := hom
  have hJB : incM F W₂.J = blkMat finSumFinEquiv (incM F W.J) (-(incM F W.J)) := by
    rw [hW₂, dblGram, incM, incM, blkMat_map _ _ (map_zero _), Matrix.map_neg _ (map_neg _)]
  have hev := GlobalTheory.DblEvalLaw.proj_mem_adm F (Fin n × Fin (d + d) ⊕ Fin n × Fin (d + d)) 0
  have hm : (i (h, h)).1.1 = blkMat finSumFinEquiv (mat h) (mat h) := hi h h
  have hp : ((i (h, h)).1 : GL (Fin (d + d)) (AE F E)) ∈ Formalism.UG.stabGL (diagSub (AE F E) finSumFinEquiv) := by
    rw [mem_stabGL_diagSub, hm, keepsDiag_blkMat]
  have hk := GlobalTheory.DblEvalLaw.apply_zero_of_keepsDiag finSumFinEquiv hJB hdc hus.toIsSplitting hSR hbox hΔ hev
      (fun φ₁ h₁ φ₂ h₂ => GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ₁ h₁ φ₂ h₂)
      (GlobalTheory.SchANonzero.exists_mem_schA_ne_zero F _) (i (h, h)) hp Φ hΦ
  have hl : leviGL finSumFinEquiv ⟨(i (h, h)).1, hp⟩ = h.1 := by
    refine Units.ext ?_
    rw [val_leviGL]
    show leviMat finSumFinEquiv (i (h, h)).1.1 = _
    rw [hm, leviMat_blkMat]; rfl
  rw [MonoidHom.comp_apply, MonoidHom.inr_apply, hl, GlobalTheory.ModuAdele.modu_norm_eq_absE,
    absE_det (GlobalTheory.SkewGram.det_ne_zero F E σ B d W r₁ s₁ hP.skew) h] at hk
  simpa using hk

end GlobalTheory.DblDiagValue
