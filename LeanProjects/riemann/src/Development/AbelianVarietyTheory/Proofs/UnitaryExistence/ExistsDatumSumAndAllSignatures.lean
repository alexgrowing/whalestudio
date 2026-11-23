import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HermitianDatumDirectPower
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.DatumSum

noncomputable section

def blockEnd {U V W : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] [AddCommGroup W]
    [Module ℝ W] (e : U ≃ₗ[ℝ] V × W) (f : V →ₗ[ℝ] V) (g : W →ₗ[ℝ] W) : U →ₗ[ℝ] U :=
  e.symm.toLinearMap ∘ₗ (f.prodMap g) ∘ₗ e.toLinearMap

theorem blockEnd_apply {U V W : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] [AddCommGroup W]
    [Module ℝ W] (e : U ≃ₗ[ℝ] V × W) (f : V →ₗ[ℝ] V) (g : W →ₗ[ℝ] W) (x : U) :
    e (blockEnd e f g x) = (f (e x).1, g (e x).2) := by
  simp [blockEnd, Prod.map]

theorem blockEnd_comp {U V W : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] [AddCommGroup W]
    [Module ℝ W] (e : U ≃ₗ[ℝ] V × W) (f f' : V →ₗ[ℝ] V) (g g' : W →ₗ[ℝ] W) :
    blockEnd e f g ∘ₗ blockEnd e f' g' = blockEnd e (f ∘ₗ f') (g ∘ₗ g') := by
  ext x
  apply e.injective
  simp [blockEnd_apply]

theorem trace_blockEnd {U V W : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] [AddCommGroup W]
    [Module ℝ W] [Module.Finite ℝ V] [Module.Finite ℝ W] (e : U ≃ₗ[ℝ] V × W) (f : V →ₗ[ℝ] V) (g : W →ₗ[ℝ] W) :
    LinearMap.trace ℝ U (blockEnd e f g) = LinearMap.trace ℝ V f + LinearMap.trace ℝ W g := by
  have h1 : blockEnd e f g = e.symm.conj (f.prodMap g) := by
    ext x; simp [blockEnd, LinearEquiv.conj_apply]
  rw [h1, LinearMap.trace_conj', LinearMap.trace_prodMap']

def sumForm {L M : Type} [AddCommGroup L] [AddCommGroup M] (B : LinearMap.BilinForm ℤ L)
    (C : LinearMap.BilinForm ℤ M) : LinearMap.BilinForm ℤ (L × M) :=
  B.compl₁₂ (LinearMap.fst ℤ L M) (LinearMap.fst ℤ L M) + C.compl₁₂ (LinearMap.snd ℤ L M) (LinearMap.snd ℤ L M)

theorem sumForm_apply {L M : Type} [AddCommGroup L] [AddCommGroup M] (B : LinearMap.BilinForm ℤ L)
    (C : LinearMap.BilinForm ℤ M) (x y : L × M) : sumForm B C x y = B x.1 y.1 + C x.2 y.2 := by
  simp [sumForm]

theorem sumForm_bijective {L M : Type} [AddCommGroup L] [AddCommGroup M] (B : LinearMap.BilinForm ℤ L)
    (C : LinearMap.BilinForm ℤ M) (hB : Function.Bijective B) (hC : Function.Bijective C) :
    Function.Bijective (sumForm B C) := by
  constructor
  · intro x y h
    refine Prod.ext (hB.1 ?_) (hC.1 ?_)
    · ext z
      have := LinearMap.congr_fun h (z, 0)
      simpa [sumForm_apply] using this
    · ext z
      have := LinearMap.congr_fun h (0, z)
      simpa [sumForm_apply] using this
  · intro φ
    obtain ⟨x, hx⟩ := hB.2 (φ ∘ₗ LinearMap.inl ℤ L M)
    obtain ⟨y, hy⟩ := hC.2 (φ ∘ₗ LinearMap.inr ℤ L M)
    refine ⟨(x, y), LinearMap.ext fun z => ?_⟩
    rw [sumForm_apply, hx, hy]
    simp [← map_add]

theorem sumForm_baseChange {L M : Type} [AddCommGroup L] [AddCommGroup M] (B : LinearMap.BilinForm ℤ L)
    (C : LinearMap.BilinForm ℤ M) (x y : ℝ ⊗[ℤ] (L × M)) :
    (sumForm B C).baseChange ℝ x y =
      B.baseChange ℝ (TensorProduct.prodRight ℤ ℝ ℝ L M x).1 (TensorProduct.prodRight ℤ ℝ ℝ L M y).1 +
      C.baseChange ℝ (TensorProduct.prodRight ℤ ℝ ℝ L M x).2 (TensorProduct.prodRight ℤ ℝ ℝ L M y).2 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, Prod.fst_add, Prod.snd_add, ha, hb]; ring
  | tmul r u =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, Prod.fst_add, Prod.snd_add, ha, hb]; ring
    | tmul s v => simp [sumForm_apply, add_smul, add_mul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def sumDatum (D D' : Datum H) : Datum H where
  La := D.La × D'.La
  fin := by haveI := D.fin; haveI := D'.fin; infer_instance
  proj := by haveI := D.proj; haveI := D'.proj; infer_instance
  EF := sumForm D.EF D'.EF
  alt := fun x => by simp [sumForm_apply, D.alt, D'.alt]
  unimod := sumForm_bijective D.EF D'.EF D.unimod D'.unimod
  adj := fun a x y => by simp [sumForm_apply, D.adj, D'.adj]
  p := D.p + D'.p
  q := D.q + D'.q
  rank := by
    haveI := D.fin
    haveI := D.proj
    haveI := D'.fin
    haveI := D'.proj
    have h1 := (TensorProduct.isBaseChange (𝓞 E) (D.La × D'.La) E).finrank_eq
    have h2 := (TensorProduct.isBaseChange (𝓞 E) D.La E).finrank_eq
    have h2' := (TensorProduct.isBaseChange (𝓞 E) D'.La E).finrank_eq
    have h3 := (TensorProduct.prodRight (𝓞 E) E E D.La D'.La).finrank_eq
    rw [← h1, h3, Module.finrank_prod, h2, h2', D.rank, D'.rank]
    ring
  dom := by
    haveI := D.fin
    haveI := D'.fin
    haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
    haveI : Module.Finite ℤ D'.La := Module.Finite.trans (𝓞 E) D'.La
    obtain ⟨J, h1, h2, h3, h4⟩ := D.dom
    obtain ⟨J', h1', h2', h3', h4'⟩ := D'.dom
    set e := TensorProduct.prodRight ℤ ℝ ℝ D.La D'.La with he
    refine ⟨blockEnd e J J', ?_, ?_, ?_, ?_⟩
    · intro x
      apply e.injective
      simp [blockEnd_apply, h1, h1', Prod.ext_iff]
    · intro x y
      simp only [sumForm_baseChange, ← he, blockEnd_apply, h2, h2']
    · intro x hx
      simp only [sumForm_baseChange, ← he, blockEnd_apply]
      have hne : e x ≠ 0 := fun hc => hx (e.injective (by rw [map_zero]; exact hc))
      by_cases ha : (e x).1 = 0
      · have hb : (e x).2 ≠ 0 := fun hb => hne (Prod.ext ha hb)
        simpa [ha] using h3' _ hb
      · by_cases hb : (e x).2 = 0
        · simpa [hb] using h3 _ ha
        · exact add_pos (h3 _ ha) (h3' _ hb)
    · intro a A t hA ht
      let A0 : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La :=
        ((DistribMulAction.toAddMonoidHom D.La a).toIntLinearMap).baseChange ℝ
      let A1 : ℝ ⊗[ℤ] D'.La →ₗ[ℝ] ℝ ⊗[ℤ] D'.La :=
        ((DistribMulAction.toAddMonoidHom D'.La a).toIntLinearMap).baseChange ℝ
      obtain ⟨k1, k2, k3⟩ := h4 a A0 _ (fun x => by simp [A0]) rfl
      obtain ⟨k1', k2', k3'⟩ := h4' a A1 _ (fun x => by simp [A1]) rfl
      have hAA : A = blockEnd e A0 A1 := by
        apply LinearMap.ext
        intro x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | add a b ha hb => simp only [map_add, ha, hb]
        | tmul r u =>
          have : r ⊗ₜ[ℤ] u = r • ((1 : ℝ) ⊗ₜ[ℤ] u) := by simp [TensorProduct.smul_tmul']
          rw [this, map_smul, map_smul, hA]
          congr 1
          apply e.injective
          rw [blockEnd_apply]
          simp [he, A0, A1]
      have ht' : t = ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0),
          ((D.p : ℂ) * τ (a : E) + (D.q : ℂ) * starRingEnd ℂ (τ (a : E))) +
          ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0),
          ((D'.p : ℂ) * τ (a : E) + (D'.q : ℂ) * starRingEnd ℂ (τ (a : E))) := by
        rw [ht, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun τ _ => ?_
        push_cast; ring
      rw [hAA, blockEnd_comp, blockEnd_comp, trace_blockEnd, trace_blockEnd, k1, ← k1, k1', ← k1', k2, k3, k2', k3',
        ht']
      refine ⟨rfl, ?_, ?_⟩
      · rw [Complex.add_re]; ring
      · rw [Complex.add_im]; ring

theorem finrank_cyclotomic_twenty_eight : Module.finrank ℚ CM.CyclotomicTwentyEight.CyclotomicFieldTwentyEight = 12 := by
  rw [IsCyclotomicExtension.finrank (n := 28) CM.CyclotomicTwentyEight.CyclotomicFieldTwentyEight (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
  decide

end

end GlobalTheory.DatumSum

namespace GlobalTheory

theorem exists_datum_sum_and_all_signatures :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D D' : Datum H), ∃ (D'' : Datum H) (e : D''.La ≃ₗ[𝓞 E] D.La × D'.La), D''.p = D.p + D'.p ∧ D''.q = D.q + D'.q ∧ ∀ x y, D''.EF x y = D.EF (e x).1 (e y).1 + D'.EF (e x).2 (e y).2) ∧ ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (H : Host E), 2 < Module.finrank ℚ E ∧ ∀ p q : ℕ, ∃ D : Datum H, D.p = p ∧ D.q = q := by
  refine ⟨fun E _ _ _ H D D' => ⟨DatumSum.sumDatum D D', LinearEquiv.refl (𝓞 E) (D.La × D'.La), rfl, rfl,
    fun x y => DatumSum.sumForm_apply D.EF D'.EF x y⟩, ?_⟩
  refine ⟨CM.CyclotomicTwentyEight.CyclotomicFieldTwentyEight, inferInstance, inferInstance, inferInstance, CM.CyclotomicTwentyEight.host, ?_, fun p q => ?_⟩
  · rw [DatumSum.finrank_cyclotomic_twenty_eight]; norm_num
  · obtain ⟨D, hp, hq⟩ := CM.CyclotomicTwentyEight.exists_datum
    refine ⟨DatumSum.sumDatum (powDatum D p) (powDatum (CM.oppDatum D) q), ?_, ?_⟩
    · change p * D.p + q * D.q = p
      simp [hp, hq]
    · change p * D.q + q * D.p = q
      simp [hp, hq]

end GlobalTheory
