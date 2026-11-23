import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOOneOne
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)
open Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasMat GlobalTheory.SplitWeil.matrixMeasurableSpace

noncomputable section

namespace GlobalTheory.DblBoxHaar

open MeasureTheory Pointwise

section Generic

variable {G H : Type} [AddCommGroup G] [AddCommGroup H] [MeasurableSpace G] [MeasurableSpace H]

theorem isAddFundamentalDomain_blocks (e : G ≃ᵐ H × H) (he : ∀ x y, e (x + y) = e x + e y)
    (Γ : AddSubgroup G) (Λ : AddSubgroup H) (h1 : ∀ g ∈ Γ, (e g).1 ∈ Λ) (h2 : ∀ g ∈ Γ, (e g).2 ∈ Λ)
    (h3 : ∀ a ∈ Λ, ∀ b ∈ Λ, e.symm (a, b) ∈ Γ) (μ₁ : Measure H) [SigmaFinite μ₁] (𝓕₁ : Set H)
    (h : IsAddFundamentalDomain Λ 𝓕₁ μ₁) :
    IsAddFundamentalDomain Γ (e ⁻¹' (𝓕₁ ×ˢ 𝓕₁)) ((μ₁.prod μ₁).map e.symm) := by
  let eA : G →+ H × H := AddMonoidHom.mk' e he
  have hneg : ∀ g, e (-g) = -e g := fun g => eA.map_neg g
  have hqmp : Measure.QuasiMeasurePreserving e ((μ₁.prod μ₁).map e.symm) (μ₁.prod μ₁) :=
    ⟨e.measurable, by rw [MeasurableEquiv.map_map_symm]⟩
  have hvadd : ∀ (g : Γ) (x : G), e (g +ᵥ x) = e g + e x := fun g x => he _ _
  refine ⟨(h.nullMeasurableSet.prod h.nullMeasurableSet).preimage hqmp, ?_, ?_⟩
  · rw [e.symm.measurableEmbedding.ae_map_iff]
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae h.ae_covers,
      Measure.quasiMeasurePreserving_snd.ae h.ae_covers] with p ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨⟨e.symm (a, b), h3 _ a.2 _ b.2⟩, ?_⟩
    simp only [Set.mem_preimage, hvadd, MeasurableEquiv.apply_symm_apply]
    exact ⟨ha, hb⟩
  · intro g g' hgg'
    have hset : ∀ g : Γ, g +ᵥ e ⁻¹' (𝓕₁ ×ˢ 𝓕₁) = e ⁻¹' (((⟨(e g).1, h1 _ g.2⟩ : Λ) +ᵥ 𝓕₁) ×ˢ ((⟨(e g).2, h2 _ g.2⟩ : Λ) +ᵥ 𝓕₁)) := by
      intro g
      ext x
      simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_preimage, Set.mem_prod, hvadd]
      simp only [AddSubgroup.vadd_def, NegMemClass.coe_neg, hneg, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, vadd_eq_add]
    show ((μ₁.prod μ₁).map e.symm) ((g +ᵥ e ⁻¹' (𝓕₁ ×ˢ 𝓕₁)) ∩ (g' +ᵥ e ⁻¹' (𝓕₁ ×ˢ 𝓕₁))) = 0
    rw [hset, hset, ← Set.preimage_inter, Set.prod_inter_prod, MeasurableEquiv.map_apply,
      MeasurableEquiv.symm_preimage_preimage, Measure.prod_prod]
    by_cases hfst : (e g).1 = (e g').1
    · have hsnd : (e g).2 ≠ (e g').2 := fun hs => hgg' (Subtype.ext (e.injective (Prod.ext hfst hs)))
      have := h.aedisjoint (i := ⟨(e g).2, h2 _ g.2⟩) (j := ⟨(e g').2, h2 _ g'.2⟩) (fun hh => hsnd (congrArg Subtype.val hh))
      rw [show μ₁ _ = 0 from this, mul_zero]
    · have := h.aedisjoint (i := ⟨(e g).1, h1 _ g.2⟩) (j := ⟨(e g').1, h1 _ g'.2⟩) (fun hh => hfst (congrArg Subtype.val hh))
      rw [show μ₁ _ = 0 from this, zero_mul]

theorem setIntegral_blocks (e : G ≃ᵐ H × H) (μ₁ : Measure H) [SigmaFinite μ₁] (𝓕₁ : Set H) (f g : H → ℂ) :
    ∫ w in e ⁻¹' (𝓕₁ ×ˢ 𝓕₁), f (e w).1 * star (g (e w).2) ∂((μ₁.prod μ₁).map e.symm) =
      (∫ u in 𝓕₁, f u ∂μ₁) * star (∫ u in 𝓕₁, g u ∂μ₁) := by
  rw [MeasurableEquiv.restrict_map, MeasurableEquiv.symm_preimage_preimage,
    e.symm.measurableEmbedding.integral_map, ← Measure.prod_restrict]
  simp only [MeasurableEquiv.apply_symm_apply, Complex.star_def]
  rw [integral_prod_mul (f := f) (g := fun v => starRingEnd ℂ (g v)), integral_conj]

end Generic

end GlobalTheory.DblBoxHaar

namespace GlobalTheory.DblBoxHaar

open MeasureTheory GlobalTheory.DblBox

variable {D : D7} {S T : HSp D}

theorem continuous_join : Continuous fun p : WO S T × WO S T => join p.1 p.2 := by
  have : Continuous fun p : WO S T × WO S T => Matrix.fromRows p.1 p.2 :=
    continuous_pi fun i => match i with
      | Sum.inl k => (continuous_apply k).comp continuous_fst
      | Sum.inr k => (continuous_apply k).comp continuous_snd
  exact this.matrix_submatrix _ _

def blocks (S T : HSp D) : WO S (GlobalTheory.Doubling.dblSp T) ≃ₜ+ WO S T × WO S T where
  toFun w := (top w, bot w)
  invFun p := join p.1 p.2
  left_inv := join_top_bot
  right_inv p := by simp
  map_add' x y := by simp
  continuous_toFun := (continuous_id.matrix_submatrix _ _).prodMk (continuous_id.matrix_submatrix _ _)
  continuous_invFun := continuous_join

theorem top_mem {g : WO S (GlobalTheory.Doubling.dblSp T)} (hg : g ∈ ratL (GlobalTheory.Doubling.dblSp T) S) : top g ∈ ratL T S := by
  obtain ⟨γ, rfl⟩ := hg
  exact ⟨γ.submatrix (finSumFinEquiv ∘ Sum.inl) id, by ext i j; rfl⟩

theorem bot_mem {g : WO S (GlobalTheory.Doubling.dblSp T)} (hg : g ∈ ratL (GlobalTheory.Doubling.dblSp T) S) : bot g ∈ ratL T S := by
  obtain ⟨γ, rfl⟩ := hg
  exact ⟨γ.submatrix (finSumFinEquiv ∘ Sum.inr) id, by ext i j; rfl⟩

theorem join_mem {u v : WO S T} (hu : u ∈ ratL T S) (hv : v ∈ ratL T S) : join u v ∈ ratL (GlobalTheory.Doubling.dblSp T) S := by
  obtain ⟨γ, rfl⟩ := hu
  obtain ⟨δ, rfl⟩ := hv
  refine ⟨(Matrix.fromRows γ δ).submatrix finSumFinEquiv.symm id, ?_⟩
  ext i j
  simp only [join, Matrix.submatrix_apply, AddMonoidHom.mapMatrix_apply, Matrix.map_apply, id]
  generalize finSumFinEquiv.symm i = s
  rcases s with k | k <;> rfl

end GlobalTheory.DblBoxHaar

open MeasureTheory in

theorem GlobalTheory.DblBoxHaar.box_integral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D),
    ∃ (μ : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T))) (𝓕 : Set (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T)))
      (μ₁ : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕₁ : Set (Formalism.IndefR.Datum.WO S T)),
      μ.IsAddHaarMeasure ∧ MeasureTheory.IsAddFundamentalDomain (Formalism.L2.Theta.ratL (GlobalTheory.Doubling.dblSp T) S) 𝓕 μ ∧
      μ₁.IsAddHaarMeasure ∧ MeasureTheory.IsAddFundamentalDomain (Formalism.L2.Theta.ratL T S) 𝓕₁ μ₁ ∧
      ∀ a a' b b' : Formalism.IndefR.Datum.WO S T → ℂ, Formalism.IndefR.Datum.IsThetaFunO ψ S T a → Formalism.IndefR.Datum.IsThetaFunO ψ S T a' →
        Formalism.IndefR.Datum.IsThetaFunO ψ S T b → Formalism.IndefR.Datum.IsThetaFunO ψ S T b' →
        ∫ w in 𝓕, GlobalTheory.DblBox.box a b w * star (GlobalTheory.DblBox.box a' b' w) ∂μ =
          (∫ u in 𝓕₁, a u * star (a' u) ∂μ₁) * star (∫ u in 𝓕₁, b u * star (b' u) ∂μ₁) := by
  intro D ψ hψ S T
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  obtain ⟨j1, j2, j3, j4, -, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D (GlobalTheory.Doubling.dblSp T) S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : BorelSpace (WO S (GlobalTheory.Doubling.dblSp T)) := ⟨rfl⟩
  obtain ⟨μ₁, 𝓕₁, hμ₁, h𝓕₁, -⟩ :=
    (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hKc).1
  haveI := hμ₁
  let e := GlobalTheory.DblBoxHaar.blocks S T
  let eM : WO S (GlobalTheory.Doubling.dblSp T) ≃ᵐ WO S T × WO S T := e.toHomeomorph.toMeasurableEquiv
  refine ⟨(μ₁.prod μ₁).map eM.symm, eM ⁻¹' (𝓕₁ ×ˢ 𝓕₁), μ₁, 𝓕₁, ?_, ?_, hμ₁, h𝓕₁, ?_⟩
  · exact ContinuousAddEquiv.isAddHaarMeasure_map (μ₁.prod μ₁) e.symm
  · exact GlobalTheory.DblBoxHaar.isAddFundamentalDomain_blocks eM (fun x y => e.map_add x y) _ _
      (fun g hg => GlobalTheory.DblBoxHaar.top_mem hg) (fun g hg => GlobalTheory.DblBoxHaar.bot_mem hg)
      (fun a ha b hb => GlobalTheory.DblBoxHaar.join_mem ha hb) μ₁ 𝓕₁ h𝓕₁
  · intro a a' b b' _ _ _ _
    rw [← GlobalTheory.DblBoxHaar.setIntegral_blocks eM μ₁ 𝓕₁ (fun u => a u * star (a' u)) (fun v => b v * star (b' v))]
    congr 1
    funext w
    simp only [GlobalTheory.DblBox.box, star_mul', star_star]
    show _ = a (GlobalTheory.DblBox.top w) * star (a' (GlobalTheory.DblBox.top w)) * (star (b (GlobalTheory.DblBox.bot w)) * b' (GlobalTheory.DblBox.bot w))
    ring
