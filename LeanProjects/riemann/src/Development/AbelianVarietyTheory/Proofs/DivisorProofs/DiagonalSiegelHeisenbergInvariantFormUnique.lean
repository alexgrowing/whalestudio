import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUgReindex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalLagrangianInvariantFormUniqueStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGoodPlace

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

noncomputable section

namespace GlobalTheory.DiagSiegelUniq

open GlobalTheory.WeilM

theorem diagMat_eq_mul {A : Type} [CommRing A] {m n : ℕ} (w : Matrix (Fin m) (Fin n) A) :
    GlobalTheory.DiagSiegel.diagMat w =
      w * ((diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) A).submatrix finSumFinEquiv.symm id)ᵀ := by
  ext i j
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases j with j | j <;>
    simp only [GlobalTheory.DiagSiegel.diagMat, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, id] <;>
    simp [diagCols, Matrix.one_apply]

theorem transpose_transport (D : D7) (S T : HSp D) (ν : Measure (Formalism.IndefR.Datum.WO T S))
    (𝓕 : Set (Formalism.IndefR.Datum.WO T S)) (h : Formalism.IndefR.Datum.IsCovolOne (ratL S T) ν 𝓕) :
    ∃ (ν' : Measure (Formalism.IndefR.DatumF.WOF D.host.F D.host.E S.rank T.rank))
      (𝓕' : Set (Formalism.IndefR.DatumF.WOF D.host.F D.host.E S.rank T.rank)),
      ν'.IsAddHaarMeasure ∧ IsAddFundamentalDomain (Formalism.IndefR.DatumF.ratLF D.host.F D.host.E S.rank T.rank) 𝓕' ν' ∧
      ∀ f : Matrix (Fin T.rank) (Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E) → ℂ,
        ∫ u in 𝓕', f u ∂ν' = ∫ w in 𝓕, f wᵀ ∂ν := by
  classical
  haveI : BorelSpace (Formalism.IndefR.Datum.WO T S) := ⟨rfl⟩
  haveI : BorelSpace (Formalism.IndefR.DatumF.WOF D.host.F D.host.E S.rank T.rank) := ⟨rfl⟩
  obtain ⟨hH, hF, -⟩ := h
  let e : Formalism.IndefR.Datum.WO T S ≃+ Formalism.IndefR.DatumF.WOF D.host.F D.host.E S.rank T.rank :=
    Matrix.transposeAddEquiv _ _ _
  have hc : Continuous e := Continuous.matrix_transpose continuous_id
  have hcs : Continuous e.symm := Continuous.matrix_transpose continuous_id
  let E' : Formalism.IndefR.Datum.WO T S ≃ᵐ Formalism.IndefR.DatumF.WOF D.host.F D.host.E S.rank T.rank :=
    (Homeomorph.mk e.toEquiv hc hcs).toMeasurableEquiv
  have hE' : ∀ w, E' w = wᵀ := fun _ => rfl
  let eG : Formalism.IndefR.DatumF.ratLF D.host.F D.host.E S.rank T.rank ≃ ratL S T :=
    { toFun := fun g => ⟨(g : Matrix (Fin T.rank) (Fin S.rank) _)ᵀ, by
        obtain ⟨γ, hγ⟩ := g.2
        exact ⟨γᵀ, by rw [← hγ]; rfl⟩⟩
      invFun := fun g => ⟨(g : Matrix (Fin S.rank) (Fin T.rank) _)ᵀ, by
        obtain ⟨γ, hγ⟩ := g.2
        exact ⟨γᵀ, by rw [← hγ]; rfl⟩⟩
      left_inv := fun g => Subtype.ext (Matrix.transpose_transpose _)
      right_inv := fun g => Subtype.ext (Matrix.transpose_transpose _) }
  refine ⟨ν.map E', E' '' 𝓕, ?_, ?_, fun f => ?_⟩
  · exact AddEquiv.isAddHaarMeasure_map ν e hc hcs
  · refine hF.image_of_equiv E'.toEquiv (E'.quasiMeasurePreserving_symm ν) eG fun g x => ?_
    show (((eG g : ratL S T) : Matrix (Fin S.rank) (Fin T.rank) _) + x)ᵀ = (g : Matrix (Fin T.rank) (Fin S.rank) _) + xᵀ
    rw [Matrix.transpose_add]
    exact congrArg (· + xᵀ) (Matrix.transpose_transpose _)
  · rw [E'.restrict_map, E'.preimage_image, MeasureTheory.integral_map_equiv]
    rfl

theorem lubinTateSeries_eq_of_coeff_one_eq (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E)
    (hξ : ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹)) (κ : Type) [Fintype κ]
    (J' : Matrix (Fin (T.rank + T.rank)) (Fin (T.rank + T.rank)) (AF D.host.F ⊗[D.host.F] D.host.E))
    (hJ : incM D.host.F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG T.gram)ᵀ = J')
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ J' (incM D.host.F JB)) κ)
    (hrat : ∀ x : Matrix (Fin (T.rank + T.rank)) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
      co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i),
        fun i => algebraMap D.host.F (AF D.host.F) (z i)))
    (ν' : Measure (Formalism.IndefR.DatumF.WOF D.host.F D.host.E S.rank T.rank))
    (𝓕' : Set (Formalism.IndefR.DatumF.WOF D.host.F D.host.E S.rank T.rank)) (hν' : ν'.IsAddHaarMeasure)
    (h𝓕' : IsAddFundamentalDomain (Formalism.IndefR.DatumF.ratLF D.host.F D.host.E S.rank T.rank) 𝓕' ν')
    (l : ((κ → AF D.host.F) → ℂ) →ₗ[ℂ] ℂ) (hl : l ∈ (GlobalTheory.WeilM.adeleClass D.host.F).adm κ)
    (hinv : ∀ z : Matrix (Fin S.rank) (Fin T.rank) (AF D.host.F ⊗[D.host.F] D.host.E),
      ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
        l ((GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co).rho ψ
          (GlobalTheory.DiagSiegel.diagMat z) Φ) = l Φ) :
    ∃ c : ℂ, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, l Φ = c * GlobalTheory.LagrTheta.lagrInt ν' 𝓕'
      ((diagCols (Fin T.rank) : Matrix (Fin T.rank ⊕ Fin T.rank) (Fin T.rank)
        (AF D.host.F ⊗[D.host.F] D.host.E)).submatrix finSumFinEquiv.symm id)
      (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) := by
  subst hJ
  classical
  obtain ⟨v₁, -, -, ⟨τ₁⟩⟩ := GlobalTheory.TripleDarboux.exists_good_place D ∅
  let B : Base D.host.F D.host.E :=
    { ψ := ψ, emb := fun _ => Classical.arbitrary _, mα := 0, mβ := 0, P := ∅,
      τ := fun v => absurd v.2 (Finset.notMem_empty _), v₁ := v₁, τ₁ := τ₁ }
  have hB : B.IsGood D.sp.cm.sig :=
    GlobalTheory.TripleDarboux.base_isGood B hψ fun v hv => absurd hv (Finset.notMem_empty _)
  exact GlobalTheory.T.diagonalLagrangian_invariantForm_unique D.host.F D.host.E D.sp.cm.sig B hB S.rank T.rank S.gram T.gram
    (GlobalTheory.Doubling.isHermND_gram S) (GlobalTheory.Doubling.isHermND_gram T) D.host.xi0 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
    (Formalism.L2.Pj.conj_xi0_alt D) JB ξ hξ κ co hrat ν' 𝓕' hν' h𝓕' l hl fun z Φ hΦ => by
      rw [← diagMat_eq_mul]
      exact hinv z Φ hΦ

theorem uniq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E),
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ
            (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin (GlobalTheory.Doubling.dblSp T).rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i),
              fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ (ν : MeasureTheory.Measure (Formalism.IndefR.Datum.WO T S)) (𝓕 : Set (Formalism.IndefR.Datum.WO T S)),
            Formalism.IndefR.Datum.IsCovolOne (ratL S T) ν 𝓕 →
          ∀ l : ((κ → AF D.host.F) → ℂ) →ₗ[ℂ] ℂ, l ∈ (GlobalTheory.WeilM.adeleClass D.host.F).adm κ →
            (∀ z : Matrix (Fin S.rank) (Fin T.rank) (AF D.host.F ⊗[D.host.F] D.host.E),
              ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
                l ((GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co).rho ψ
                  (GlobalTheory.DiagSiegel.diagMat z) Φ) = l Φ) →
            ∃ c : ℂ, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, l Φ = c * GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕
              (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co) ψ Φ) := by
  intro D ψ hψ S T JB ξ hξ κ _ co hrat ν 𝓕 hcov l hl hinv
  obtain ⟨ν', 𝓕', hν', h𝓕', hint⟩ := transpose_transport D S T ν 𝓕 hcov
  have hJ : incM D.host.F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG T.gram)ᵀ =
      incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ) := by
    rw [← GlobalTheory.WeilSchrodinger.DblTargetF.reindex_dbl_incM (F := D.host.F) (J := T.gram) rfl,
      GlobalTheory.WeilSchrodinger.DblTarget.reindex_dbl_incM T rfl]
  obtain ⟨c, hc⟩ := lubinTateSeries_eq_of_coeff_one_eq D ψ hψ S T JB ξ hξ κ _ hJ co hrat ν' 𝓕' hν' h𝓕' l hl hinv
  refine ⟨c, fun Φ hΦ => ?_⟩
  rw [hc Φ hΦ, GlobalTheory.LagrTheta.lagrInt, hint, GlobalTheory.DiagSiegel.thetaDiagInt]
  congr 2
  funext w
  simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilSchrodinger.transD_rho, diagMat_eq_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose]

end GlobalTheory.DiagSiegelUniq

end
