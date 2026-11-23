import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopCMulBlk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingPairLatticeMeasure
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer
open GlobalTheory.DblDatum

noncomputable section

namespace GlobalTheory.DblWeilSecond

theorem assemble {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Xs : Spc F E n} {W : Spc F E d} {W₂ : Spc F E (d + d)} {χX : Chr F E}
    (om : Rep σ Xs W) (om₂ : Rep σ Xs W₂) (i : UA σ W.J × UA σ W.J →* UA σ W₂.J)
    (e : (((Fin n × Fin d ⊕ Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] ((Fin n × Fin (d + d) → AF F) → ℂ))
    (hpres : ∀ h, ∀ Φ ∈ schA F (Fin n × Fin d), om (1, h) Φ ∈ schA F (Fin n × Fin d))
    (hdiag : ∀ h : UA σ W.J, ∀ Φ₁ ∈ schA F (Fin n × Fin d), ∀ Φ₂ ∈ schA F (Fin n × Fin d),
      om₂ (1, i (h, h)) (e (boxC Φ₁ Φ₂)) =
        ((χX (Matrix.GeneralLinearGroup.det h.1) : Circle) : ℂ) • e (boxC (om (1, h) Φ₁) (om (1, h) Φ₂)))
    (hfirst : ∀ h : UA σ W.J, ∀ Φ₁ ∈ schA F (Fin n × Fin d), ∀ Φ₂ ∈ schA F (Fin n × Fin d),
      om₂ (1, i (h, 1)) (e (boxC Φ₁ Φ₂)) = e (boxC (om (1, h) Φ₁) Φ₂))
    (h' : UA σ W.J) (Φ₁ : _) (hΦ₁ : Φ₁ ∈ schA F (Fin n × Fin d)) (Φ₂ : _) (hΦ₂ : Φ₂ ∈ schA F (Fin n × Fin d)) :
    om₂ (1, i (1, h')) (e (boxC Φ₁ Φ₂)) =
      ((χX (Matrix.GeneralLinearGroup.det h'.1) : Circle) : ℂ) • e (boxC Φ₁ (om (1, h') Φ₂)) := by
  have hi : i (1, h') = i (h'⁻¹, 1) * i (h', h') := by
    rw [← map_mul]; congr 1; ext <;> simp
  have h1 : ((1 : UA σ Xs.J), i (1, h')) = (1, i (h'⁻¹, 1)) * (1, i (h', h')) := by
    rw [hi]; ext <;> simp
  have h2 : om (1, h'⁻¹) (om (1, h') Φ₁) = Φ₁ := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, inv_mul_cancel, Prod.mk_one_one, map_one,
      Module.End.one_apply]
  rw [h1, map_mul, Module.End.mul_apply, hdiag h' Φ₁ hΦ₁ Φ₂ hΦ₂, map_smul,
    hfirst h'⁻¹ _ (hpres h' Φ₁ hΦ₁) _ (hpres h' Φ₂ hΦ₂), h2]

theorem om₂_right_boxC : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (Xs : Spc F E n) (W : Spc F E d) (M : Model σ Xs W) (χX χW : Chr F E) (om : Rep σ Xs W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ →
    ∀ W₂ : Spc F E (d + d), W₂.J = dblGram finSumFinEquiv W.J → W₂.L = sumLat finSumFinEquiv W.L W.L →
    (∀ w, W₂.θ w = blkMat finSumFinEquiv (W.θ w) (-W.θ w)) →
    ∀ i : UA σ W.J × UA σ W.J →* UA σ W₂.J, (∀ h h', mat (i (h, h')) = blkMat finSumFinEquiv (mat h) (mat h')) →
    ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F Xs.J) (incM F W₂.J)) (Fin n × Fin (d + d)),
      (∀ x : Matrix (Fin n) (Fin (d + d)) E, ∃ y z : Fin n × Fin (d + d) → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      (∀ u, (∀ i, u i ∈ diagSub (AE F E) finSumFinEquiv) → (co.e u).1 = 0) →
      (∀ u, (∀ i, u i ∈ antiSub (AE F E) finSumFinEquiv) → (co.e u).2 = 0) →
    ∀ om₂ : Rep σ Xs W₂, IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F Xs.J) (incM F W₂.J) co χX 1 om₂ →
    ∀ e : (((Fin n × Fin d ⊕ Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] ((Fin n × Fin (d + d) → AF F) → ℂ),
      Set.BijOn e (schA F (Fin n × Fin d ⊕ Fin n × Fin d) : Set _) (schA F (Fin n × Fin (d + d)) : Set _) →
      (∀ l ∈ (adeleClass F).adm (Fin n × Fin (d + d)), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d)) →
      (∀ u, ∀ Ψ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), e (schr B.ψ (dblE M.co u) Ψ) = co.rho B.ψ u (e Ψ)) →
    ∀ h' : UA σ W.J, ∀ Φ₁ ∈ schA F (Fin n × Fin d), ∀ Φ₂ ∈ schA F (Fin n × Fin d),
      om₂ (1, i (1, h')) (e (boxC Φ₁ Φ₂)) = ((χX (Matrix.GeneralLinearGroup.det h'.1) : Circle) : ℂ) • e (boxC Φ₁ (om (1, h') Φ₂)) := by
  intro F E _ _ _ _ _ σ B n d Xs W M χX χW om r s' r₁ s₁ hP W₂ hJ hL hθ i hi co hrat hΔ hN om₂ hom₂ e he1 he2 he3
    h' Φ₁ hΦ₁ Φ₂ hΦ₂
  exact assemble om om₂ i e (fun h Φ hΦ => hP.weil.isUSplitting.pres (1, h) Φ hΦ)
    (fun h Ψ₁ hΨ₁ Ψ₂ hΨ₂ => diag_box σ B n d Xs W M χX χW om r s' r₁ s₁ hP W₂ hJ i hi co hrat hΔ hN om₂ hom₂ e he1 he2
      he3 h Ψ₁ hΨ₁ Ψ₂ hΨ₂)
    (fun h Ψ₁ hΨ₁ Ψ₂ hΨ₂ => GlobalTheory.DblWeilBox.om₂_left_boxC F E σ B n d Xs W M χX χW om r s' r₁ s₁ hP W₂ hJ hL hθ i hi co
      hrat hΔ hN om₂ hom₂ e he1 he2 he3 h Ψ₁ hΨ₁ Ψ₂ hΨ₂)
    h' Φ₁ hΦ₁ Φ₂ hΦ₂

end GlobalTheory.DblWeilSecond

end
