import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipB
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.NarrowCls

theorem exists_finset_mod_sq {G : Type} [CommGroup G] [Group.FG G] :
    ∃ E : Finset G, ∀ g : G, ∃ e ∈ E, ∃ h : G, g = e * h ^ 2 := by
  classical
  let H : Subgroup G := (powMonoidHom 2 : G →* G).range
  have hfin : Finite (G ⧸ H) := by
    apply CommGroup.finite_of_fg_torsion
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    refine (isOfFinOrder_iff_pow_eq_one).2 ⟨2, by norm_num, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨g, rfl⟩
  haveI := Fintype.ofFinite (G ⧸ H)
  refine ⟨Finset.univ.image (fun q : G ⧸ H => q.out), fun g => ?_⟩
  refine ⟨(g : G ⧸ H).out, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
  have h1 : ((g : G ⧸ H).out : G ⧸ H) = (g : G ⧸ H) := Quotient.out_eq' _
  rw [QuotientGroup.eq] at h1
  obtain ⟨h, hh⟩ := h1
  refine ⟨h, ?_⟩
  simp only [powMonoidHom_apply] at hh
  rw [hh, mul_inv_cancel_left]

variable {F : Type} [Field F] [NumberField F]

def finIdele : (Af F)ˣ →* Ideles F :=
  Units.map
    { toFun := fun x => (((1 : InfiniteAdeleRing F), x) : AdeleRing (𝓞 F) F)
      map_one' := rfl
      map_mul' := fun x y => Prod.ext (mul_one 1).symm rfl }

def finClass : (Af F)ˣ →* ClassGroup (𝓞 F) := (ReciprocityTheory.Neutral.Bridge.HCFR.classOf F).comp finIdele

theorem eq_of_finClass_eq_one (z : (Af F)ˣ) (hz : finClass z = 1) :
    ∃ (k : Fˣ) (u : (Af F)ˣ), (∀ w, Valued.v (pLoc F w (u : Af F)) = 1) ∧
      z = Units.map (algebraMap F (Af F)).toMonoidHom k * u := by
  obtain ⟨k, u', hu', he⟩ := (ReciprocityTheory.Neutral.Bridge.HCFR.classOf_eq_one_iff F (finIdele z)).1 hz
  have hsnd := congrArg (ReciprocityTheory.Neutral.Bridge.HCFR.sndU F) he
  rw [map_mul] at hsnd
  have hinv : ReciprocityTheory.Neutral.Bridge.HCFR.sndU F u' * ReciprocityTheory.Neutral.Bridge.HCFR.sndU F u'⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hinv' : ReciprocityTheory.Neutral.Bridge.HCFR.sndU F u'⁻¹ * ReciprocityTheory.Neutral.Bridge.HCFR.sndU F u' = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  refine ⟨k, ⟨_, _, hinv, hinv'⟩, ?_, ?_⟩
  · intro w
    exact (ReciprocityTheory.Neutral.Bridge.HCFR.rayUnits_top_iff F u').1 hu' w
  · ext1
    exact hsnd

variable [IsTotallyReal F]

theorem reAt_eq (v : InfinitePlace F) (x : F) :
    reAt v x = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x := by
  rw [reAt, ← InfinitePlace.embedding_of_isReal_apply]
  exact Complex.ofReal_re _

open Classical in

def sgn (k : Fˣ) : InfinitePlace F → Bool := fun v => decide (0 < reAt v (k : F))

theorem tp_of_sgn_eq (k σ : Fˣ) (h : sgn k = sgn σ) : TP ((k * σ⁻¹ : Fˣ) : F) := by
  intro v
  have hv := congrFun h v
  simp only [sgn, decide_eq_decide] at hv
  rw [reAt_eq] at hv ⊢
  set e := InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v)
  have hk : e (k : F) ≠ 0 := (map_ne_zero e).2 k.ne_zero
  have hs : e (σ : F) ≠ 0 := (map_ne_zero e).2 σ.ne_zero
  rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
  rcases lt_or_gt_of_ne hs with h1 | h1
  · have h2 : e (k : F) < 0 := by
      rcases lt_or_gt_of_ne hk with h3 | h3
      · exact h3
      · exact absurd (hv.1 h3) (not_lt.2 h1.le)
    exact mul_pos_of_neg_of_neg h2 (inv_lt_zero.2 h1)
  · exact mul_pos (hv.2 h1) (inv_pos.2 h1)

theorem narrowClass_unitsSq_finite : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F],
    (∃ Y : Finset (Af F)ˣ, ∀ z : (Af F)ˣ, ∃ y ∈ Y, ∃ (ξ : Fˣ) (u : (Af F)ˣ), TP (ξ : F) ∧
      (∀ w, Valued.v (pLoc F w (u : Af F)) = 1) ∧ z = Units.map (algebraMap F (Af F)).toMonoidHom ξ * y * u) ∧
    ∃ E : Finset (𝓞 F)ˣ, ∀ ε : (𝓞 F)ˣ, ∃ e ∈ E, ∃ η : (𝓞 F)ˣ, ε = e * η ^ 2 := by
  intro F _ _ _
  classical
  refine ⟨?_, ?_⟩
  · let Y0 : Finset (Af F)ˣ := Finset.univ.image
      (fun c : ClassGroup (𝓞 F) => if h : ∃ y, finClass y = c then h.choose else 1)
    let S : Finset Fˣ := Finset.univ.image
      (fun b : InfinitePlace F → Bool => if h : ∃ σ : Fˣ, sgn σ = b then h.choose else 1)
    let ι := Units.map (algebraMap F (Af F)).toMonoidHom
    refine ⟨(S ×ˢ Y0).image (fun p => ι p.1 * p.2), fun z => ?_⟩
    have hc : ∃ y, finClass y = finClass z := ⟨z, rfl⟩
    set y0 := hc.choose with hy0
    have hy0c : finClass y0 = finClass z := hc.choose_spec
    have hy0m : y0 ∈ Y0 := by
      refine Finset.mem_image.2 ⟨finClass z, Finset.mem_univ _, ?_⟩
      rw [dif_pos hc]
    obtain ⟨k, u, hu, hk⟩ := eq_of_finClass_eq_one (z * y0⁻¹) (by rw [map_mul, map_inv, hy0c, mul_inv_cancel])
    have hs : ∃ σ : Fˣ, sgn σ = sgn k := ⟨k, rfl⟩
    set σ := hs.choose with hσ
    have hσs : sgn σ = sgn k := hs.choose_spec
    have hσm : σ ∈ S := by
      refine Finset.mem_image.2 ⟨sgn k, Finset.mem_univ _, ?_⟩
      rw [dif_pos hs]
    refine ⟨ι σ * y0, Finset.mem_image.2 ⟨(σ, y0), Finset.mem_product.2 ⟨hσm, hy0m⟩, rfl⟩,
      k * σ⁻¹, u, tp_of_sgn_eq k σ hσs.symm, hu, ?_⟩
    have hz : z = ι k * u * y0 := by rw [← hk, inv_mul_cancel_right]
    show z = ι (k * σ⁻¹) * (ι σ * y0) * u
    rw [← mul_assoc, ← map_mul, inv_mul_cancel_right, mul_right_comm]
    exact hz
  · haveI : Group.FG (𝓞 F)ˣ := Group.fg_iff_monoid_fg.2 inferInstance
    exact exists_finset_mod_sq

end GlobalTheory.HilbertThetaSeries.NarrowCls

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_narrowIdeleClasses_and_units_mod_squares : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], (∃ Y : Finset (Af F)ˣ, ∀ z : (Af F)ˣ, ∃ y ∈ Y, ∃ (ξ : Fˣ) (u : (Af F)ˣ), TP (ξ : F) ∧ (∀ w, Valued.v (pLoc F w (u : Af F)) = 1) ∧ z = Units.map (algebraMap F (Af F)).toMonoidHom ξ * y * u) ∧ ∃ E : Finset (𝓞 F)ˣ, ∀ ε : (𝓞 F)ˣ, ∃ e ∈ E, ∃ η : (𝓞 F)ˣ, ε = e * η ^ 2 := by
  first | exact @GlobalTheory.HilbertThetaSeries.NarrowCls.narrowClass_unitsSq_finite | exact GlobalTheory.HilbertThetaSeries.NarrowCls.narrowClass_unitsSq_finite | (intros; apply GlobalTheory.HilbertThetaSeries.NarrowCls.narrowClass_unitsSq_finite <;> assumption)
