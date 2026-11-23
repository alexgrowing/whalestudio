import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.HcToIdele

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published GroundTheory.LocalField

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.CharacterPositivity

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem pow_eq_one_of_fin {ω : HChar F} (h : IsOfFinOrder ω) :
    ∃ n : ℕ, 0 < n ∧ ∀ x, (ω.1 x) ^ n = 1 := by
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  refine ⟨n, hn, fun x => ?_⟩
  have h1 : (ω ^ n).1 x = 1 := by rw [hpow]; rfl
  rw [← MonoidHom.pow_apply, ← Subgroup.coe_pow, h1]

theorem omega_inf_pos (ω : HChar F) (h : IsOfFinOrder ω) (z : (InfiniteAdeleRing F)ˣ)
    (hz : ∀ w : InfinitePlace F, 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal
      (IsTotallyReal.isReal w) ((z : InfiniteAdeleRing F) w)) :
    ω.1 (ofInfinite z) = 1 := by
  obtain ⟨n, hn, hpow⟩ := pow_eq_one_of_fin h
  rw [ofInfinite_eq_prod, map_prod]
  refine Finset.prod_eq_one fun w _ => ?_
  have hw := IsTotallyReal.isReal w
  set u := infiniteComponent w z
  set x : ℝˣ := Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw : w.Completion →+* ℝ).toMonoidHom u
  have hu : realUnitsHom hw x = u := realUnitsHom_surjective hw u
  have hx : 0 < (x : ℝ) := by
    show 0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw ((z : InfiniteAdeleRing F) w)
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
    exact hz w
  have hr : 0 < (x : ℝ) ^ (n⁻¹ : ℝ) := Real.rpow_pos_of_pos hx _
  have hy : Units.mk0 _ hr.ne' ^ n = x := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Real.rpow_inv_natCast_pow hx.le hn.ne'])
  rw [← hu, ← hy]
  simp only [map_pow]
  exact hpow _

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.CharacterPositivity

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open L4 CharacterPositivity

theorem character_positive_holds : OmegaPos := by
  intro F _ _ _ ω c H ξ hξ
  have hdiag : ω.1 (diagonal F ξ) = 1 := ω.2.2 ξ
  have hsplit := ofFinite_mul_ofInfinite (diagonal F ξ)
  have hfin : toFinite F (diagonal F ξ) = xiF ξ := Units.ext rfl
  rw [← hsplit, map_mul, hfin, omega_inf_pos ω H.fin _ ?_, mul_one] at hdiag
  · unfold ωF
    rw [hdiag, Units.val_one]
  · intro w
    have h1 : ((toInfinite F (diagonal F ξ) : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w =
        algebraMap F w.Completion (ξ : F) := rfl
    rw [h1]
    have h2 := hξ w
    unfold reAt at h2
    rw [← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal w), Complex.ofReal_re] at h2
    convert h2 using 1
    exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe (IsTotallyReal.isReal w) _

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
