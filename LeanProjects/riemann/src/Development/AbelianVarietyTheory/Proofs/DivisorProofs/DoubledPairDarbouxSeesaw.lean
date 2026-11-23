import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantAdmissibleFormEqMulDiagonalIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPreservesInnerProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicWeilRepSchrodingerModelUnique
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer
open GlobalTheory.DblDatum

noncomputable section

namespace GlobalTheory.DblPairInv

theorem fromCols_blocks {A : Type} {n d : ℕ} (z z' : Matrix (Fin n) (Fin d) A) :
    ((Matrix.fromCols z z').submatrix id finSumFinEquiv.symm).submatrix id (finSumFinEquiv ∘ Sum.inl) = z ∧
      ((Matrix.fromCols z z').submatrix id finSumFinEquiv.symm).submatrix id (finSumFinEquiv ∘ Sum.inr) = z' := by
  constructor <;> ext i j <;>
    simp only [Matrix.submatrix_apply, Function.comp_apply, Equiv.symm_apply_apply, id, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr]

theorem pairing_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (Xs : Spc F E n) (W : Spc F E d) (M : Model σ Xs W) (χX χW : Chr F E) (om : Rep σ Xs W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ →
    ∀ W₂ : Spc F E (d + d), W₂.J = dblGram finSumFinEquiv W.J →
    ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F Xs.J) (incM F W₂.J)) (Fin n × Fin (d + d)),
      (∀ x : Matrix (Fin n) (Fin (d + d)) E, ∃ y z : Fin n × Fin (d + d) → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      (∀ u, (∀ i, u i ∈ diagSub (AE F E) finSumFinEquiv) → (co.e u).1 = 0) →
      (∀ u, (∀ i, u i ∈ antiSub (AE F E) finSumFinEquiv) → (co.e u).2 = 0) →
    ∀ e : (((Fin n × Fin d ⊕ Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] ((Fin n × Fin (d + d) → AF F) → ℂ),
      Set.BijOn e (schA F (Fin n × Fin d ⊕ Fin n × Fin d) : Set _) (schA F (Fin n × Fin (d + d)) : Set _) →
      (∀ l ∈ (adeleClass F).adm (Fin n × Fin (d + d)), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d)) →
      (∀ u, ∀ Ψ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), e (schr B.ψ (dblE M.co u) Ψ) = co.rho B.ψ u (e Ψ)) →
    ∀ h : UA σ W.J, ∀ Φ₁ ∈ schA F (Fin n × Fin d), ∀ Φ₂ ∈ schA F (Fin n × Fin d),
      e (boxC (om (1, h) Φ₁) (om (1, h) Φ₂)) 0 = e (boxC Φ₁ Φ₂) 0 := by
  intro F E _ _ _ _ _ σ B n d Xs W M χX χW om r s' r₁ s₁ hP W₂ _ co _ hΔ _ e _ hadm hint h Φ₁ hΦ₁ Φ₂ hΦ₂
  have hS := IsUWeilPair.isUSplitting hP.weil
  letI : MeasurableSpace (Fin n × Fin d → AF F) := borel _
  haveI : BorelSpace (Fin n × Fin d → AF F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  have hμ : (Measure.addHaar : Measure (Fin n × Fin d → AF F)).IsAddHaarMeasure := inferInstance
  obtain ⟨c, hc⟩ := GlobalTheory.DiagUniq.eq_mul_diagInt F B.ψ hP.base.std (Fin n × Fin d) _
    (hadm _ (GlobalTheory.WeilSchUnique.evalZero_mem_adelicSchwartzAdmittedForms _)) (fun x y Φ hΦ => by
      let z := M.co.e.symm (x, y)
      let u : Matrix (Fin n) (Fin (d + d)) (AE F E) := (Matrix.fromCols z z).submatrix id finSumFinEquiv.symm
      have ht : topC u = z := (fromCols_blocks z z).1
      have hb : botC u = z := (fromCols_blocks z z).2
      have hu : dblE M.co u = (Sum.elim x x, Sum.elim y (-y)) := by simp [dblE, ht, hb, z]
      have h0 : (co.e u).1 = 0 := hΔ u fun i => by
        rw [diagSub, LinearMap.mem_eqLocus]
        funext j
        exact (congrFun (congrFun ht i) j).trans (congrFun (congrFun hb i) j).symm
      simp only [LinearMap.comp_apply, LinearMap.proj_apply]
      rw [← hu, hint u Φ hΦ]
      simp [Darboux.rho, schr, h0]) Measure.addHaar hμ
  simp only [LinearMap.comp_apply, LinearMap.proj_apply] at hc
  have hbox : ∀ φ₁ ∈ schA F (Fin n × Fin d), ∀ φ₂ ∈ schA F (Fin n × Fin d),
      e (boxC φ₁ φ₂) 0 = c * ∫ x, φ₁ x * starRingEnd ℂ (φ₂ x) ∂Measure.addHaar := fun φ₁ h₁ φ₂ h₂ =>
    hc _ (GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ₁ h₁ _ (GlobalTheory.SchAConj.star_mem_schA F _ φ₂ h₂))
  rw [hbox _ (hS.pres _ _ hΦ₁) _ (hS.pres _ _ hΦ₂), hbox _ hΦ₁ _ hΦ₂,
    GlobalTheory.L2PairingPolar.pairing_eq F _ (om (1, h)) (hS.pres _) (fun μ hμ => hS.unit μ hμ _) _ hμ Φ₁ hΦ₁ Φ₂ hΦ₂]

end GlobalTheory.DblPairInv

end
