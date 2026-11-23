import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUgReindex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt

import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionDegeneratePrincipalSeriesLaw
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelFormulasWittTarget
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusOfNormEqAbs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunctionThetaTransformRationalDarboux

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Datum GlobalTheory.Doubling

noncomputable section

namespace GlobalTheory.DblTargetTheta

open MeasureTheory Formalism.IndefR.Datum GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw

variable {D : D7}

theorem exists_GA_of_UG (V : HSp D)
    (p : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F V.gramᵀ)) :
    ∃ h : GA D V, mt V h = p.1.1 := by
  have h : p.1.1ᵀ * incM D.host.F V.gramᵀ * p.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = incM D.host.F V.gramᵀ := p.2
  have h2 := congrArg Matrix.transpose h
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at h2
  exact ⟨ofMat V p.1.1 h2, rfl⟩

theorem thetaDiag_transD (S T : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AE D) (κ : Type) [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ
      (incM D.host.F ((dblSp T).gramᵀ)) (incM D.host.F JB)) κ)
    (ψ : AddChar (AF D.host.F) ℂ) (ν : Measure (WO T S)) (𝓕 : Set (WO T S)) (Ψ : (κ → AF D.host.F) → ℂ) :
    GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 (GlobalTheory.WeilSchrodinger.thetaTr D.host.F
                 (GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co) ψ Ψ) =
      ∫ w in 𝓕, GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Ψ (GlobalTheory.DiagSiegel.diagMat w)ᵀ ∂ν := by
  unfold GlobalTheory.DiagSiegel.thetaDiagInt
  congr 1

theorem isCovolOne_map {m n m' n' : ℕ} {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)} (h : IsCovolOne (ratMx D m n) μ 𝓕)
    (e : Mx D m n ≃+ Mx D m' n') (he : Continuous e) (he' : Continuous e.symm)
    (hr : ∀ x ∈ ratMx D m n, e x ∈ ratMx D m' n') (hr' : ∀ x ∈ ratMx D m' n', e.symm x ∈ ratMx D m n) :
    IsCovolOne (ratMx D m' n') (μ.map e) (e '' 𝓕) ∧ MeasurableEmbedding e := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D m n
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := lattice_Mx D m' n'
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI : BorelSpace (Mx D m' n') := ⟨rfl⟩
  haveI := h.1
  let f : Mx D m n ≃ₜ Mx D m' n' := { e.toEquiv with continuous_toFun := he, continuous_invFun := he' }
  have hemb : MeasurableEmbedding e := f.measurableEmbedding
  refine ⟨⟨e.isAddHaarMeasure_map μ he he', ?_, ?_⟩, hemb⟩
  · let g : ratMx D m' n' ≃ ratMx D m n :=
      { toFun := fun γ => ⟨e.symm γ, hr' _ γ.2⟩
        invFun := fun γ => ⟨e γ, hr _ γ.2⟩
        left_inv := fun γ => Subtype.ext (e.apply_symm_apply _)
        right_inv := fun γ => Subtype.ext (e.symm_apply_apply _) }
    refine h.2.1.image_of_equiv e.toEquiv ?_ g fun γ x => ?_
    · refine ⟨he'.measurable, ?_⟩
      have : (μ.map e).map e.symm = μ := by
        rw [Measure.map_map he'.measurable he.measurable]
        have : (e.symm ∘ e : Mx D m n → Mx D m n) = id := funext e.symm_apply_apply
        rw [this, Measure.map_id]
      exact this.absolutelyContinuous
    · change e (e.symm γ + x) = γ + e x
      rw [map_add, e.apply_symm_apply]
  · rw [hemb.map_apply, Set.preimage_image_eq _ e.injective]
    exact h.2.2

def gramT (T : HSp D) (n : ℕ) : Mx D n T.rank ≃+ Mx D T.rank n where
  toFun w := gA T ⬝ wᵀ
  invFun a := (giA T ⬝ a)ᵀ
  left_inv w := by simp only [giA_gA_cancel, Matrix.transpose_transpose]
  right_inv a := by simp only [Matrix.transpose_transpose, gA_giA_cancel]
  map_add' w w' := by simp only [Matrix.transpose_add, Matrix.mul_add]

theorem ratMx_transpose {m n : ℕ} {x : Mx D m n} (hx : x ∈ ratMx D m n) : xᵀ ∈ ratMx D n m := by
  obtain ⟨a, rfl⟩ := mem_ratMx.1 hx
  exact ⟨aᵀ, rfl⟩

theorem incX_gramT (S T : HSp D) (w : Mx D S.rank T.rank) :
    (dblDec T).incX S (gramT T S.rank w) = (GlobalTheory.DiagSiegel.diagMat w)ᵀ := by
  have hj : (dblDec T).jX = (Matrix.fromRows (giA T) (giA T)).submatrix finSumFinEquiv.symm id := by
    ext i j
    obtain ⟨s | s, rfl⟩ := finSumFinEquiv.surjective i <;>
      simp only [HypDec.jX, dblDec, stackRows, rat, giA, Matrix.map_apply, Matrix.submatrix_apply, id,
        Equiv.symm_apply_apply, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr]
  rw [HypDec.incX_apply, hj]
  ext i j
  have h : giA T ⬝ gramT T S.rank w = wᵀ := giA_gA_cancel T wᵀ
  obtain ⟨s | s, rfl⟩ := finSumFinEquiv.surjective i
  · simpa only [GlobalTheory.DiagSiegel.diagMat, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id,
      Equiv.symm_apply_apply, Matrix.fromRows_apply_inl, Matrix.fromCols_apply_inl] using congrFun (congrFun h s) j
  · simpa only [GlobalTheory.DiagSiegel.diagMat, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id,
      Equiv.symm_apply_apply, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inr] using congrFun (congrFun h s) j

theorem diag_eq_mixT (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ν : Measure (WO T S)) (𝓕 : Set (WO T S))
    (hν : IsCovolOne (ratL S T) ν 𝓕) :
    ∃ (μ : Measure (Mx D T.rank S.rank)) (𝓕' : Set (Mx D T.rank S.rank)), IsCovolOne (ratMx D T.rank S.rank) μ 𝓕' ∧
      ∀ f : WO S (dblSp T) → ℂ,
        (∫ w in 𝓕, f (GlobalTheory.DiagSiegel.diagMat w)ᵀ ∂ν) = (dblDec T).mixT S ψ μ 𝓕' f 0 0 := by
  have hν' : IsCovolOne (ratMx D S.rank T.rank) ν 𝓕 := hν
  obtain ⟨hc, hemb⟩ := isCovolOne_map hν' (gramT T S.rank)
    (continuous_const.matrix_mul continuous_id.matrix_transpose)
    (continuous_const.matrix_mul continuous_id).matrix_transpose
    (fun x hx => ratMx_mul (rat_mem _) (ratMx_transpose hx))
    (fun x hx => ratMx_transpose (ratMx_mul (rat_mem _) hx))
  refine ⟨_, _, hc, fun f => ?_⟩
  simp only [HypDec.mixT, HypDec.integrandT_eq]
  simp only [map_zero, add_zero, symplOH_zero_right, AddChar.map_zero_eq_one, one_mul]
  rw [hemb.setIntegral_map, Set.preimage_image_eq _ (gramT T S.rank).injective]
  simp only [incX_gramT]

theorem keepsDiag_of_diagCols {A : Type} [CommRing A] {n : ℕ} {M : Matrix (Fin (n + n)) (Fin (n + n)) A}
    {t : Matrix (Fin n) (Fin n) A}
    (h : ∀ i j, ∑ k, M i k * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) A) 1).submatrix finSumFinEquiv.symm id k j =
      ∑ k, (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) A) 1).submatrix finSumFinEquiv.symm id i k * t k j) :
    KeepsDiag finSumFinEquiv M ∧ leviMat finSumFinEquiv M = t := by
  have key : ∀ (s : Fin n ⊕ Fin n) (j : Fin n), M (finSumFinEquiv s) (finSumFinEquiv (.inl j)) +
      M (finSumFinEquiv s) (finSumFinEquiv (.inr j)) = t (s.elim id id) j := by
    intro s j
    have h1 := h (finSumFinEquiv s) j
    rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type] at h1
    rcases s with s | s <;>
      simpa only [Matrix.submatrix_apply, id, Equiv.symm_apply_apply, Matrix.fromRows_apply_inl,
        Matrix.fromRows_apply_inr, Matrix.one_apply, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul,
        Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Sum.elim_inl, Sum.elim_inr] using h1
  refine ⟨(keepsDiag_iff _).2 fun i j => (key (.inr i) j).trans (key (.inl i) j).symm, ?_⟩
  ext i j
  exact key (.inl i) j

theorem siegel_of_diag (T : HSp D) (h : GA D (dblSp T))
    (p : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)))
    (hh : mt (dblSp T) h = p.1.1) (t : GL (Fin T.rank) (AF D.host.F ⊗[D.host.F] D.host.E))
    (ht : p.1.1 * (GlobalTheory.WeilM.diagCols (Fin T.rank) : Matrix (Fin T.rank ⊕ Fin T.rank) (Fin T.rank) (AE D)).submatrix
                finSumFinEquiv.symm id =
              (GlobalTheory.WeilM.diagCols (Fin T.rank) : Matrix (Fin T.rank ⊕ Fin T.rank) (Fin T.rank) (AE D)).submatrix
                finSumFinEquiv.symm id * t.1) :
    h ∈ siegel T ∧ ∀ hs : h ∈ siegel T, aP T ⟨h, hs⟩ = Matrix.GeneralLinearGroup.det t := by
  have hk := keepsDiag_of_diagCols (n := T.rank) (M := p.1.1) (t := t.1) fun i j => congrFun (congrFun ht i) j
  have hk1 : KeepsDiag finSumFinEquiv (mt (dblSp T) h) := hh ▸ hk.1
  have hk2 : leviMat finSumFinEquiv (mt (dblSp T) h) = t.1 := hh ▸ hk.2
  exact ⟨mem_siegelOf.2 hk1, fun hs => Units.ext (congrArg Matrix.det hk2)⟩

theorem ruleFac_absE {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (χ : (AF F ⊗[F] E)ˣ →* Circle) (n : ℕ) {ρ : ℕ} (t : GL (Fin ρ) (AF F ⊗[F] E)) :
    GlobalTheory.DiagSiegel.ruleFac (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.WeilM.adeleClass F) χ n t =
      ((χ (Matrix.GeneralLinearGroup.det t) : Circle) : ℂ) *
        ((((absE F E (Matrix.GeneralLinearGroup.det t) : NNReal) : ℝ) ^ ((n : ℝ) / 2) : ℝ) : ℂ) := by
  rw [← GlobalTheory.ModuAdele.modu_norm_eq_absE]
  rfl

theorem ruleFac_eq (χ : (AE D)ˣ →* Circle) (n : ℕ) {ρ : ℕ} (a : GL (Fin ρ) (AE D)) (t : GL (Fin ρ) (AF D.host.F ⊗[D.host.F] D.host.E))
    (h : Matrix.GeneralLinearGroup.det a = Matrix.GeneralLinearGroup.det t) :
    ((χ (Matrix.GeneralLinearGroup.det a) : Circle) : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod n a : ℂ) =
      GlobalTheory.DiagSiegel.ruleFac (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.adeleClass D.host.F) χ
        (Fintype.card (Fin n)) t := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod, h, Fintype.card_fin]
  exact (ruleFac_absE D.sp.cm.sig χ n t).symm

theorem mixT_law (hP : GlobalTheory.Published.WeilRepresentationUnitaryPair) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)
    (χS : (AE D)ˣ →* Circle) (ωd : GA D S × GA D (dblSp T) →* Module.End ℂ (WO S (dblSp T) → ℂ))
    (hW : IsWeilDatumO ψ S (dblSp T) χS 1 ωd) (μ : Measure (Mx D T.rank S.rank)) (𝓕 : Set (Mx D T.rank S.rank))
    (hμ : IsCovolOne (ratMx D T.rank S.rank) μ 𝓕) (f : WO S (dblSp T) → ℂ) (hf : IsThetaFunO ψ S (dblSp T) f)
    (h : GA D (dblSp T)) (hs : h ∈ siegel T) (t : GL (Fin T.rank) (AF D.host.F ⊗[D.host.F] D.host.E))
    (ht : aP T ⟨h, hs⟩ = Matrix.GeneralLinearGroup.det t) :
    (dblDec T).mixT S ψ μ 𝓕 (ωd (1, h) f) 0 0 =
      GlobalTheory.DiagSiegel.ruleFac (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.adeleClass D.host.F) χS
        (Fintype.card (Fin S.rank)) t * (dblDec T).mixT S ψ μ 𝓕 f 0 0 := by
  obtain ⟨om₀, h₀⟩ : ∃ om₀ : GA D S × GA D (zeroSp D) →* Module.End ℂ (WO S (zeroSp D) → ℂ),
      IsWeilDatumO ψ S (zeroSp D) χS 1 om₀ := by
    refine hP D ψ S (zeroSp D) χS 1 hW.std hW.hecS hW.hecT hW.resS ?_
    exact ⟨hW.resS.1, fun η _ a => by rw [show (zeroSp D).rank = 0 from rfl, pow_zero]; rfl⟩
  obtain ⟨a, c, hp⟩ := siegel_decomp T ⟨h, hs⟩
  have haP := aP_decomp T ⟨h, hs⟩ a c hp
  replace hp : h = (dblDec T).levi a * (dblDec T).nC c := hp
  have hF' := hW.om_pres (1, (dblDec T).nC c) f hf
  have hM := GlobalTheory.MixTargetProof.mixedTarget D ψ S (dblSp T) (zeroSp D) T.rank (dblDec T) χS 1 ωd om₀ hW h₀ μ 𝓕 hμ
  have h1 := (hM _ hF').levi a 0
  have h2 := (hM f hf).centre c 0
  have e1 : ωd (1, h) f = ωd (1, (dblDec T).levi a) (ωd (1, (dblDec T).nC c) f) := by
    rw [hp, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  have hq : (dblDec T).qT S c 0 = 0 := by rw [HypDec.qT, map_zero, symplOH_zero_left]
  rw [e1, h1, Matrix.zero_mul, h2, hq, AddChar.map_zero_eq_one, one_smul, Pi.smul_apply, smul_eq_mul,
    ruleFac_eq χS S.rank a t (haP.symm.trans ht)]

end GlobalTheory.DblTargetTheta

end

open GlobalTheory.DblTargetTheta in

theorem GlobalTheory.DblTargetTheta.thetaDiag_rule : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
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
          ∀ (χS : (AE D)ˣ →* Circle), IsHeckeChar D χS → ResEta D χS S.rank →
          ∀ ωd : GA D S × GA D (GlobalTheory.Doubling.dblSp T) →* Module.End ℂ (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S (GlobalTheory.Doubling.dblSp T) χS 1 ωd →
          ∀ omp : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →*
                Module.End ℂ ((κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ co ωd omp →
          ∀ (p : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)))
            (t : GL (Fin T.rank) (AF D.host.F ⊗[D.host.F] D.host.E)),
            p.1.1 * (GlobalTheory.WeilM.diagCols (Fin T.rank) : Matrix (Fin T.rank ⊕ Fin T.rank) (Fin T.rank) (AE D)).submatrix
                finSumFinEquiv.symm id =
              (GlobalTheory.WeilM.diagCols (Fin T.rank) : Matrix (Fin T.rank ⊕ Fin T.rank) (Fin T.rank) (AE D)).submatrix
                finSumFinEquiv.symm id * t.1 →
          ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
            omp (p, 1) Φ ∈ GlobalTheory.WeilM.schA D.host.F κ ∧
            GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 (GlobalTheory.WeilSchrodinger.thetaTr D.host.F
                         (GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co) ψ (omp (p, 1) Φ)) =
              GlobalTheory.DiagSiegel.ruleFac (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.adeleClass D.host.F) χS
                (Fintype.card (Fin S.rank)) t *
              GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 (GlobalTheory.WeilSchrodinger.thetaTr D.host.F
                (GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co) ψ Φ) := by
  intro D ψ hψ S T JB ξ hξ κ _ co hco ν 𝓕 hν χS hχ hη ωd hW omp homp p t hpt Φ hΦ
  obtain ⟨h, hh⟩ := exists_GA_of_UG (dblSp T) p
  have hT := homp p 1 1 h hh (by simp) Φ hΦ
  refine ⟨hT.1, ?_⟩
  have hf := GlobalTheory.ThetaTransformTheta.isThetaFunO_thetaTr D ψ hψ S (dblSp T) _ JB ξ rfl hξ κ co hco Φ hΦ
  obtain ⟨μ, 𝓕', hμ, hI⟩ := diag_eq_mixT ψ S T ν 𝓕 hν
  have key := siegel_of_diag T h p hh t hpt
  have hL := mixT_law GlobalTheory.weilRepresentationUnitaryPair ψ S T χS ωd hW μ 𝓕' hμ _ hf h key.1 t (key.2 key.1)
  have e2 : (∫ w in 𝓕, GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (omp (p, 1) Φ) (GlobalTheory.DiagSiegel.diagMat w)ᵀ ∂ν) = ∫ w in 𝓕, ωd (1, h) (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) (GlobalTheory.DiagSiegel.diagMat w)ᵀ ∂ν := by rw [hT.2]
  refine (thetaDiag_transD S T JB ξ κ co ψ ν 𝓕 (omp (p, 1) Φ)).trans ?_
  refine e2.trans ?_
  refine (hI _).trans ?_
  refine hL.trans ?_
  exact congrArg (_ * ·) ((hI _).symm.trans (thetaDiag_transD S T JB ξ κ co ψ ν 𝓕 Φ).symm)
