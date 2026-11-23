import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd

noncomputable section

open MeasureTheory Measure Set
open scoped Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.CompanionTheory.ThTot

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot.ProdMeasPf

section Abstract

variable {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

theorem isAddFundamentalDomain_join (J : X × Y ≃ᵐ Z) (hJ : ∀ a b, J (a + b) = J a + J b)
    (Γ : AddSubgroup X) (Δ : AddSubgroup Y) (Λ : AddSubgroup Z)
    (hΛ : ∀ z, z ∈ Λ ↔ (J.symm z).1 ∈ Γ ∧ (J.symm z).2 ∈ Δ)
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (F : Set X) (G : Set Y)
    (hF : IsAddFundamentalDomain Γ F μ) (hG : IsAddFundamentalDomain Δ G ν) :
    IsAddFundamentalDomain Λ (J '' (F ×ˢ G)) ((μ.prod ν).map J) := by
  have hm : ∀ R : Set (X × Y), (μ.prod ν).map J (J '' R) = μ.prod ν R := fun R => by
    rw [J.map_apply, Set.preimage_image_eq _ J.injective]
  have htr : ∀ (l : Z) (w : X × Y), l + J w = J (J.symm l + w) := fun l w => by
    rw [hJ, J.apply_symm_apply]
  have himg : ∀ l : Λ, (l +ᵥ (J '' (F ×ˢ G)) : Set Z) =
      J '' ((((⟨(J.symm l.1).1, ((hΛ _).1 l.2).1⟩ : Γ) +ᵥ F : Set X)) ×ˢ
        (((⟨(J.symm l.1).2, ((hΛ _).1 l.2).2⟩ : Δ) +ᵥ G : Set Y))) := by
    intro l
    ext z
    constructor
    · rintro ⟨_, ⟨w, ⟨h1, h2⟩, rfl⟩, rfl⟩
      refine ⟨J.symm l.1 + w, ⟨⟨w.1, h1, rfl⟩, ⟨w.2, h2, rfl⟩⟩, ?_⟩
      exact (htr l.1 w).symm
    · rintro ⟨w, ⟨⟨a, ha, h1⟩, ⟨b, hb, h2⟩⟩, rfl⟩
      refine ⟨J (a, b), ⟨(a, b), ⟨ha, hb⟩, rfl⟩, ?_⟩
      have : J.symm l.1 + (a, b) = w := Prod.ext h1 h2
      change l.1 + J (a, b) = J w
      rw [htr, this]
  refine ⟨?_, ?_, ?_⟩
  · have hq : QuasiMeasurePreserving J.symm ((μ.prod ν).map J) (μ.prod ν) := by
      refine ⟨J.symm.measurable, ?_⟩
      rw [Measure.map_map J.symm.measurable J.measurable]
      simp only [MeasurableEquiv.symm_comp_self, Measure.map_id]
      exact Measure.AbsolutelyContinuous.rfl
    rw [J.image_eq_preimage_symm]
    exact (hF.nullMeasurableSet.prod hG.nullMeasurableSet).preimage hq
  · rw [J.measurableEmbedding.ae_map_iff]
    have h1 := (quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hF.ae_covers
    have h2 := (quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae hG.ae_covers
    filter_upwards [h1, h2] with w hw1 hw2
    obtain ⟨g, hg⟩ := hw1
    obtain ⟨d, hd⟩ := hw2
    refine ⟨⟨J (g.1, d.1), (hΛ _).2 (by simp)⟩, (g.1 + w.1, d.1 + w.2), ⟨hg, hd⟩, ?_⟩
    change J (g.1 + w.1, d.1 + w.2) = J (g.1, d.1) + J w
    rw [← hJ]
    rfl
  · intro l l' hll
    change (μ.prod ν).map J ((l +ᵥ (J '' (F ×ˢ G)) : Set Z) ∩ (l' +ᵥ (J '' (F ×ˢ G)) : Set Z)) = 0
    rw [himg, himg, ← Set.image_inter J.injective, hm, Set.prod_inter_prod, Measure.prod_prod]
    have hne : (⟨(J.symm l.1).1, ((hΛ _).1 l.2).1⟩ : Γ) ≠ ⟨(J.symm l'.1).1, ((hΛ _).1 l'.2).1⟩ ∨
        (⟨(J.symm l.1).2, ((hΛ _).1 l.2).2⟩ : Δ) ≠ ⟨(J.symm l'.1).2, ((hΛ _).1 l'.2).2⟩ := by
      by_contra hcon
      push_neg at hcon
      apply hll
      apply Subtype.ext
      apply J.symm.injective
      exact Prod.ext (congrArg Subtype.val hcon.1) (congrArg Subtype.val hcon.2)
    rcases hne with h | h
    · have := hF.aedisjoint h
      rw [show μ _ = 0 from this, zero_mul]
    · have := hG.aedisjoint h
      rw [show ν _ = 0 from this, mul_zero]

end Abstract

variable {D : D7} {r s p : ℕ}

theorem rowT_rowJ (x : Mx D r p) (z : Mx D s p) : rowT (rowJ x z) = x := by
  funext i j; simp [rowT, rowJ]

theorem rowB_rowJ (x : Mx D r p) (z : Mx D s p) : rowB (rowJ x z) = z := by
  funext i j; simp [rowB, rowJ]

theorem rowJ_rowT_rowB (y : Mx D (r + s) p) : rowJ (rowT y) (rowB y) = y := by
  funext i j
  induction i using Fin.addCases with
  | left a => simp [rowT, rowJ]
  | right b => simp [rowB, rowJ]

theorem rowJ_add (x x' : Mx D r p) (z z' : Mx D s p) : rowJ (x + x') (z + z') = rowJ x z + rowJ x' z' := by
  funext i j
  induction i using Fin.addCases with
  | left a => simp [rowJ]
  | right b => simp [rowJ]

theorem continuous_rowT : Continuous (rowT : Mx D (r + s) p → Mx D r p) :=
  continuous_matrix fun i j => continuous_id.matrix_elem _ _

theorem continuous_rowB : Continuous (rowB : Mx D (r + s) p → Mx D s p) :=
  continuous_matrix fun i j => continuous_id.matrix_elem _ _

theorem continuous_rowJ : Continuous (fun z : Mx D r p × Mx D s p => rowJ z.1 z.2) := by
  refine continuous_matrix fun i j => ?_
  induction i using Fin.addCases with
  | left a =>
    simpa [rowJ] using (continuous_fst.matrix_elem a j)
  | right b =>
    simpa [rowJ] using (continuous_snd.matrix_elem b j)

def rowH : Mx D r p × Mx D s p ≃ₜ Mx D (r + s) p where
  toFun z := rowJ z.1 z.2
  invFun y := (rowT y, rowB y)
  left_inv z := Prod.ext (rowT_rowJ _ _) (rowB_rowJ _ _)
  right_inv := rowJ_rowT_rowB
  continuous_toFun := continuous_rowJ
  continuous_invFun := continuous_rowT.prodMk continuous_rowB

theorem mem_ratMx_iff (y : Mx D (r + s) p) :
    y ∈ ratMx D (r + s) p ↔ rowT y ∈ ratMx D r p ∧ rowB y ∈ ratMx D s p := by
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨⟨fun i j => γ (Fin.castAdd s i) j, rfl⟩, ⟨fun i j => γ (Fin.natAdd r i) j, rfl⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    replace ha : rat a = rowT y := ha
    replace hb : rat b = rowB y := hb
    refine ⟨fun i j => Fin.addCases (motive := fun _ => D.host.E) (fun u => a u j) (fun v => b v j) i, ?_⟩
    change rat _ = y
    funext i j
    induction i using Fin.addCases with
    | left u =>
      refine Eq.trans ?_ (congrFun (congrFun ha u) j)
      change incA D (Fin.addCases (motive := fun _ => D.host.E) (fun u => a u j) (fun v => b v j) (Fin.castAdd s u)) =
        incA D (a u j)
      rw [Fin.addCases_left]
    | right v =>
      refine Eq.trans ?_ (congrFun (congrFun hb v) j)
      change incA D (Fin.addCases (motive := fun _ => D.host.E) (fun u => a u j) (fun v => b v j) (Fin.natAdd r v)) =
        incA D (b v j)
      rw [Fin.addCases_right]

theorem prodMeas : ProdMeas := by
  intro D r s p μr 𝓕r μs 𝓕s μ 𝓕 hr hs h
  obtain ⟨a1, a2, a3, a4, -⟩ := lattice_Mx D r p
  obtain ⟨b1, b2, b3, b4, -⟩ := lattice_Mx D s p
  obtain ⟨c1, c2, c3, c4, -⟩ := lattice_Mx D (r + s) p
  haveI : BorelSpace (Mx D r p) := ⟨rfl⟩
  haveI : BorelSpace (Mx D s p) := ⟨rfl⟩
  haveI : BorelSpace (Mx D (r + s) p) := ⟨rfl⟩
  haveI := hr.1
  haveI := hs.1
  let J : Mx D r p × Mx D s p ≃ᵐ Mx D (r + s) p := (rowH (D := D) (r := r) (s := s) (p := p)).toMeasurableEquiv
  have hJ : ∀ a b, J (a + b) = J a + J b := fun a b => rowJ_add a.1 b.1 a.2 b.2
  have hJf : (J : Mx D r p × Mx D s p → Mx D (r + s) p) = fun z => rowJ z.1 z.2 := rfl
  let e : Mx D r p × Mx D s p ≃+ Mx D (r + s) p :=
    { (rowH (D := D) (r := r) (s := s) (p := p)).toEquiv with map_add' := hJ }
  have hH : ((μr.prod μs).map e).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map (μr.prod μs) e continuous_rowJ (continuous_rowT.prodMk continuous_rowB)
  have hF : IsAddFundamentalDomain (ratMx D (r + s) p) (J '' (𝓕r ×ˢ 𝓕s)) ((μr.prod μs).map J) :=
    isAddFundamentalDomain_join J hJ (ratMx D r p) (ratMx D s p) (ratMx D (r + s) p)
      (fun z => mem_ratMx_iff z) μr μs 𝓕r 𝓕s hr.2.1 hs.2.1
  have h1 : (μr.prod μs).map J (J '' (𝓕r ×ˢ 𝓕s)) = 1 := by
    rw [J.map_apply, Set.preimage_image_eq _ J.injective, Measure.prod_prod, hr.2.2, hs.2.2, one_mul]
  have hcov : IsCovolOne (ratMx D (r + s) p) ((μr.prod μs).map J) (J '' (𝓕r ×ˢ 𝓕s)) := ⟨hH, hF, h1⟩
  exact covolOne_measure_eq hcov h

end GlobalTheory.CompanionTheory.ThTot.ProdMeasPf
