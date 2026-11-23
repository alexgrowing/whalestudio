import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoMeanProd

variable {D : D7}

local infixl:70 " ⬝ " => HMul.hMul

theorem symplOH_iso_mid {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B)
    (q₀ : Matrix (Fin W.rank) (Fin r) D.host.E) (a : Mx D W.rank r) (x : WO V' W) :
    symplOH V W (isoPart V W C (q₀.map (incA D))) (isoPart V W C a + midPart V V' W B x) = 0 := by
  set P : Mx D r V.rank := GlobalTheory.MixModel.rat (adj D C * V.gram) with hP
  set Q : Mx D V'.rank V.rank := GlobalTheory.MixModel.rat (V'.gram⁻¹ * adj D B * V.gram) with hQ
  have hG := GlobalTheory.MixModel.gram_conjTranspose V
  have hG' := GlobalTheory.MixModel.gramInv_conjTranspose V'
  have hU := GlobalTheory.MixModel.gram_isUnit_det V
  have hC0 : adj D C * V.gram * C = 0 := hs.frame.2.2
  have hO : adj D C * V.gram * B = 0 := hs.orth
  have k1 : P ⬝ GlobalTheory.MixModel.giA V ⬝ GlobalTheory.MixModel.adj P = 0 := by
    rw [hP, ← GlobalTheory.MixModel.rat_conjTranspose, GlobalTheory.MixModel.giA, ← GlobalTheory.MixModel.rat_mul, ← GlobalTheory.MixModel.rat_mul]
    have : adj D C * V.gram * V.gram⁻¹ * (adj D C * V.gram)ᴴ = 0 := by
      change Cᴴ * V.gram * V.gram⁻¹ * (Cᴴ * V.gram)ᴴ = 0
      change Cᴴ * V.gram * C = 0 at hC0
      rw [Matrix.conjTranspose_mul, hG, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc (Cᴴ * V.gram),
        ← Matrix.mul_assoc V.gram⁻¹, Matrix.nonsing_inv_mul _ hU, Matrix.one_mul, hC0]
    rw [this, GlobalTheory.MixModel.rat_zero]
  have k2 : P ⬝ GlobalTheory.MixModel.giA V ⬝ GlobalTheory.MixModel.adj Q = 0 := by
    rw [hP, hQ, ← GlobalTheory.MixModel.rat_conjTranspose, GlobalTheory.MixModel.giA, ← GlobalTheory.MixModel.rat_mul, ← GlobalTheory.MixModel.rat_mul]
    have : adj D C * V.gram * V.gram⁻¹ * (V'.gram⁻¹ * adj D B * V.gram)ᴴ = 0 := by
      change Cᴴ * V.gram * V.gram⁻¹ * (V'.gram⁻¹ * Bᴴ * V.gram)ᴴ = 0
      change Cᴴ * V.gram * B = 0 at hO
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hG, hG', Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc (Cᴴ * V.gram), ← Matrix.mul_assoc V.gram⁻¹,
        Matrix.nonsing_inv_mul _ hU, Matrix.one_mul, ← Matrix.mul_assoc, hO, Matrix.zero_mul]
    rw [this, GlobalTheory.MixModel.rat_zero]
  have e1 : isoPart V W C (q₀.map (incA D)) = GlobalTheory.MixModel.rat q₀ ⬝ P := rfl
  have e2 : isoPart V W C a + midPart V V' W B x = a ⬝ P + x ⬝ Q := rfl
  have k3 : P ⬝ GlobalTheory.MixModel.giA V ⬝ GlobalTheory.MixModel.adj (a ⬝ P + x ⬝ Q) = 0 := by
    rw [GlobalTheory.MixModel.adj_add, GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_mul, Matrix.mul_add,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, k1, k2, Matrix.zero_mul, Matrix.zero_mul, add_zero]
  rw [GlobalTheory.MixModel.symplOH_eq, GlobalTheory.MixModel.hO_eq_trace, e1, e2]
  have e3 : GlobalTheory.MixModel.giA V ⬝ (GlobalTheory.MixModel.adj (a ⬝ P + x ⬝ Q) ⬝ (GlobalTheory.MixModel.gA W ⬝ (GlobalTheory.MixModel.rat q₀ ⬝ P))) =
      (GlobalTheory.MixModel.giA V ⬝ GlobalTheory.MixModel.adj (a ⬝ P + x ⬝ Q) ⬝ GlobalTheory.MixModel.gA W ⬝ GlobalTheory.MixModel.rat q₀) ⬝ P := by
    simp only [Matrix.mul_assoc]
  rw [e3, Matrix.trace_mul_comm]
  have e4 : P ⬝ (GlobalTheory.MixModel.giA V ⬝ GlobalTheory.MixModel.adj (a ⬝ P + x ⬝ Q) ⬝ GlobalTheory.MixModel.gA W ⬝ GlobalTheory.MixModel.rat q₀) =
      (P ⬝ GlobalTheory.MixModel.giA V ⬝ GlobalTheory.MixModel.adj (a ⬝ P + x ⬝ Q)) ⬝ (GlobalTheory.MixModel.gA W ⬝ GlobalTheory.MixModel.rat q₀) := by
    simp only [Matrix.mul_assoc]
  rw [e4, k3, Matrix.zero_mul, Matrix.trace_zero, map_zero]

theorem iso_periodic {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B) {ψ : AddChar (AF D.host.F) ℂ}
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (x : WO V' W) :
    ∀ γ ∈ GlobalTheory.MixModel.ratMx D W.rank r, ∀ a,
      f (isoPart V W C (γ + a) + midPart V V' W B x) = f (isoPart V W C a + midPart V V' W B x) := by
  rintro _ ⟨q₀, rfl⟩ a
  have e3 : (incA D).toAddMonoidHom.mapMatrix q₀ = q₀.map (incA D) := rfl
  have hadd : isoPart V W C (q₀.map (incA D) + a) = isoPart V W C (q₀.map (incA D)) + isoPart V W C a :=
    Matrix.add_mul _ _ _
  have hrat : ratW W V (q₀ * (adj D C * V.gram)) = isoPart V W C (q₀.map (incA D)) := Matrix.map_mul
  rw [e3, hadd, add_assoc, ← hrat, hf.quasi, hrat, symplOH_iso_mid hs, neg_zero, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.IsoMeanProd

namespace GlobalTheory.IsoMeanProd

theorem mean_iso_mul_star : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ F G, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G → ∫ y in 𝓨, ∫ y' in 𝓨, ∫ x in 𝓕', F (isoPart V W C (y + y') + midPart V V' W B x) * star (G (isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ ∂μ = ∫ x in 𝓕', res V V' W C B μ 𝓨 F x * star (res V V' W C B μ 𝓨 G x) ∂μ' := by
  intro D V V' W r C B hs ψ hψ μ 𝓨 hμ μ' 𝓕' hμ' h𝓕' F G hF hG
  have hμ1 : IsCovolOne (GlobalTheory.MixModel.ratMx D W.rank r) μ 𝓨 := hμ
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank r
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V'.rank
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI : BorelSpace (WO V' W) := ⟨rfl⟩
  haveI hfin1 : IsFiniteMeasure (μ.restrict 𝓨) :=
    ⟨by rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure (μ'.restrict 𝓕') :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 (GlobalTheory.Size.measure_dom hμ' h𝓕').2⟩
  haveI hsf1 : SigmaFinite (μ.restrict 𝓨) := @IsFiniteMeasure.toSigmaFinite _ _ _ hfin1
  haveI : SFinite (μ.restrict 𝓨) := @instSFiniteOfSigmaFinite _ _ _ hsf1
  haveI : SigmaFinite (μ'.restrict 𝓕') := inferInstance
  haveI : SFinite (μ'.restrict 𝓕') := inferInstance
  obtain ⟨cF, hcF⟩ := GlobalTheory.WeilVacMove.exists_bound hψ hF
  obtain ⟨cG, hcG⟩ := GlobalTheory.WeilVacMove.exists_bound hψ hG
  have ciso : Continuous (fun y : Mx D W.rank r => isoPart V W C y) := continuous_id.matrix_mul continuous_const
  have cmid : Continuous (fun x : WO V' W => midPart V V' W B x) := continuous_id.matrix_mul continuous_const
  obtain ⟨H, hH⟩ : ∃ H : Mx D W.rank r → Mx D W.rank r → WO V' W → ℂ, H = fun y y' x =>
      F (isoPart V W C (y + y') + midPart V V' W B x) * star (G (isoPart V W C y' + midPart V V' W B x)) := ⟨_, rfl⟩
  have hHb : ∀ y y' x, ‖H y y' x‖ ≤ cF * cG := by
    intro y y' x
    rw [hH, norm_mul, norm_star]
    exact mul_le_mul (hcF _) (hcG _) (norm_nonneg _) ((norm_nonneg _).trans (hcF 0))
  have hHc : Continuous fun p : Mx D W.rank r × Mx D W.rank r × WO V' W => H p.1 p.2.1 p.2.2 := by
    rw [hH]
    exact (hF.cont.comp ((ciso.comp (continuous_fst.add continuous_snd.fst)).add (cmid.comp continuous_snd.snd))).mul
      (continuous_star.comp (hG.cont.comp ((ciso.comp continuous_snd.fst).add (cmid.comp continuous_snd.snd))))
  have hint : ∀ {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] (ν : Measure X)
      [IsFiniteMeasure ν] (g : X → ℂ), Continuous g → (∀ z, ‖g z‖ ≤ cF * cG) → Integrable g ν :=
    fun ν _ g hg hb => Integrable.of_bound hg.aestronglyMeasurable _ (Filter.Eventually.of_forall hb)
  have hI1 : ∀ y, Integrable (Function.uncurry fun y' x => H y y' x) ((μ.restrict 𝓨).prod (μ'.restrict 𝓕')) :=
    fun y => hint _ _ (hHc.comp (continuous_const.prodMk continuous_id)) fun z => hHb _ _ _
  have hI3 : Integrable (fun q : (Mx D W.rank r × WO V' W) × Mx D W.rank r => H q.1.1 q.2 q.1.2)
      (((μ.restrict 𝓨).prod (μ'.restrict 𝓕')).prod (μ.restrict 𝓨)) :=
    hint _ _ (hHc.comp (continuous_fst.fst.prodMk (continuous_snd.prodMk continuous_fst.snd))) fun z => hHb _ _ _
  have hI2 : Integrable (Function.uncurry fun y x => ∫ y', H y y' x ∂(μ.restrict 𝓨))
      ((μ.restrict 𝓨).prod (μ'.restrict 𝓕')) := hI3.integral_prod_left
  have hI4 : ∀ x, Integrable (Function.uncurry fun y y' => H y y' x) ((μ.restrict 𝓨).prod (μ.restrict 𝓨)) :=
    fun x => hint _ _ (hHc.comp (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))) fun z => hHb _ _ _
  have step4 : ∀ x y', ∫ y in 𝓨, H y y' x ∂μ =
      res V V' W C B μ 𝓨 F x * star (G (isoPart V W C y' + midPart V V' W B x)) := by
    intro x y'
    rw [hH]
    simp only
    rw [integral_mul_const]
    congr 1
    exact GlobalTheory.MixModel.covolOne_integral_add hμ1 (fun a => F (isoPart V W C a + midPart V V' W B x))
      (iso_periodic hs hF x) y'
  have step5 : ∀ x, ∫ y' in 𝓨, res V V' W C B μ 𝓨 F x * star (G (isoPart V W C y' + midPart V V' W B x)) ∂μ =
      res V V' W C B μ 𝓨 F x * star (res V V' W C B μ 𝓨 G x) := by
    intro x
    rw [integral_const_mul]
    congr 1
    exact integral_conj
  have e0 : ∀ y y' x, F (isoPart V W C (y + y') + midPart V V' W B x) * star (G (isoPart V W C y' + midPart V V' W B x)) = H y y' x := by
    intro y y' x; rw [hH]
  simp only [e0]
  calc ∫ y in 𝓨, ∫ y' in 𝓨, ∫ x in 𝓕', H y y' x ∂μ' ∂μ ∂μ
      = ∫ y in 𝓨, ∫ x in 𝓕', ∫ y' in 𝓨, H y y' x ∂μ ∂μ' ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun y => integral_integral_swap (hI1 y))
    _ = ∫ x in 𝓕', ∫ y in 𝓨, ∫ y' in 𝓨, H y y' x ∂μ ∂μ ∂μ' := integral_integral_swap hI2
    _ = ∫ x in 𝓕', ∫ y' in 𝓨, ∫ y in 𝓨, H y y' x ∂μ ∂μ ∂μ' :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => integral_integral_swap (hI4 x))
    _ = ∫ x in 𝓕', ∫ y' in 𝓨, res V V' W C B μ 𝓨 F x * star (G (isoPart V W C y' + midPart V V' W B x)) ∂μ ∂μ' :=
        integral_congr_ae (Filter.Eventually.of_forall fun x =>
          integral_congr_ae (Filter.Eventually.of_forall fun y' => step4 x y'))
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun x => step5 x)

end GlobalTheory.IsoMeanProd
