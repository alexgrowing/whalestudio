import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GluingMassOfGluingFacts
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence.LatticeLiftIndependence

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section LinAlg

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

theorem finrank_orth_add_finrank (U : Submodule E S.V) : finrank E (orth S U) + finrank E U = finrank E S.V := by
  classical
  let b := Module.finBasis E U
  let ℓ : Fin (finrank E U) → Module.Dual E S.V := fun a => S.hT (b a : S.V)
  have hind : LinearIndependent E (fun a => (b a : S.V)) :=
    b.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
  have hspan : Submodule.span E (Set.range fun a => (b a : S.V)) = U := by
    have : (Set.range fun a => (b a : S.V)) = U.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have hℓ : LinearIndependent E ℓ := by
    rw [Fintype.linearIndependent_iff]
    intro c hc a
    have h1 : S.hT (∑ a, star (c a) • (b a : S.V)) = 0 := by
      rw [map_sum, ← hc]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [map_smulₛₗ, starRingEnd_apply, star_star]
    have h2 : ∑ a, star (c a) • (b a : S.V) = 0 := S.nondeg.1 _ (fun y => by rw [h1]; rfl)
    have h3 := Fintype.linearIndependent_iff.1 hind _ h2 a
    simpa using h3
  have hΦ : finrank E (Submodule.span E (Set.range ℓ)) = finrank E U := by
    rw [finrank_span_eq_card hℓ]; simp
  have hco : (Submodule.span E (Set.range ℓ)).dualCoannihilator = orth S U := by
    ext v
    rw [Submodule.mem_dualCoannihilator, Formalism.MainNotions.mem_orth_iff]
    constructor
    · intro h
      have hle : U ≤ LinearMap.ker (S.hT.flip v) := by
        rw [← hspan]
        refine Submodule.span_le.2 ?_
        rintro _ ⟨a, rfl⟩
        have := h (ℓ a) (Submodule.subset_span ⟨_, rfl⟩)
        simpa [ℓ] using this
      intro x hx
      simpa using hle hx
    · intro h φ hφ
      refine Submodule.span_induction (p := fun φ _ => φ v = 0) ?_ ?_ ?_ ?_ hφ
      · rintro _ ⟨a, rfl⟩
        exact h _ (b a).2
      · simp
      · intro x y _ _ hx hy
        simp [hx, hy]
      · intro c x _ hx
        simp [hx]
  have := Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.span E (Set.range ℓ))
  rw [hΦ, hco] at this
  omega

theorem isCompl_orth_of_nondegenerate (U : Submodule E S.V) (hU : U ⊓ orth S U = ⊥) : IsCompl U (orth S U) := by
  have hd : Disjoint U (orth S U) := disjoint_iff.2 hU
  refine ⟨hd, codisjoint_iff.2 (Submodule.eq_top_of_disjoint U (orth S U) ?_ hd)⟩
  have := finrank_orth_add_finrank S U
  omega

end LinAlg

section Ext

variable (D : D7)

theorem embedding_isometry_W (x y : (D.sp.X 0).V) : (VS D).hT (D.sp.iXY 0 x) (D.sp.iXY 0 y) = (D.sp.X 0).hT x y :=
  D.sp.iXY_isom 0 (lt_of_lt_of_le (by norm_num) D.R.two_le_m) x y

theorem embedding_W_injective : Function.Injective (D.sp.iXY 0) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  refine (Submodule.mem_bot _).2 ((D.sp.X 0).nondeg.2 x (fun y => ?_))
  rw [← embedding_isometry_W D y x, hx, map_zero]

theorem isCompl_range_orth_range : IsCompl (LinearMap.range (D.sp.iXY 0)) (orth (hS D) (LinearMap.range (D.sp.iXY 0))) := by
  refine isCompl_orth_of_nondegenerate _ _ ?_
  rw [eq_bot_iff]
  rintro _ ⟨⟨x, rfl⟩, hx⟩
  have hx' := (Formalism.MainNotions.mem_orth_iff _ _).1 hx
  have h0 : x = 0 := (D.sp.X 0).nondeg.2 x (fun y => by rw [← embedding_isometry_W D y x]; exact hx' _ ⟨y, rfl⟩)
  rw [h0, map_zero]
  exact Submodule.zero_mem _

def conjEquivOnEmbeddingRange (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) :
    LinearMap.range (D.sp.iXY 0) ≃ₗ[D.host.E] LinearMap.range (D.sp.iXY 0) :=
  (LinearEquiv.ofInjective (D.sp.iXY 0) (embedding_W_injective D)).symm ≪≫ₗ γ ≪≫ₗ LinearEquiv.ofInjective (D.sp.iXY 0) (embedding_W_injective D)

def extendByIdentity (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) : (VS D).V ≃ₗ[D.host.E] (VS D).V :=
  (Submodule.prodEquivOfIsCompl _ _ (isCompl_range_orth_range D)).symm ≪≫ₗ
    ((conjEquivOnEmbeddingRange D γ).prodCongr (LinearEquiv.refl _ _)) ≪≫ₗ Submodule.prodEquivOfIsCompl _ _ (isCompl_range_orth_range D)

theorem extendByIdentity_apply (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) (w : (D.sp.X 0).V) (b : (VS D).V)
    (hb : b ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0))) :
    extendByIdentity D γ (D.sp.iXY 0 w + b) = D.sp.iXY 0 (γ w) + b := by
  have e : D.sp.iXY 0 w + b = Submodule.prodEquivOfIsCompl _ _ (isCompl_range_orth_range D)
      (LinearEquiv.ofInjective (D.sp.iXY 0) (embedding_W_injective D) w, ⟨b, hb⟩) := by
    rw [Submodule.coe_prodEquivOfIsCompl']
    rfl
  rw [e]
  unfold extendByIdentity
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    Submodule.coe_prodEquivOfIsCompl']
  unfold conjEquivOnEmbeddingRange
  simp only [LinearEquiv.prodCongr_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.refl_apply]
  rfl

theorem exists_decomp_range_orth (x : (VS D).V) : ∃ (w : (D.sp.X 0).V) (b : (VS D).V),
    b ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0)) ∧ x = D.sp.iXY 0 w + b := by
  obtain ⟨⟨a, b⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl _ _ (isCompl_range_orth_range D)).surjective x
  obtain ⟨w, hw⟩ := a.2
  exact ⟨w, b.1, b.2, by rw [Submodule.coe_prodEquivOfIsCompl', hw]⟩

theorem inner_decomp_orth_range (w w' : (D.sp.X 0).V) (b b' : (VS D).V)
    (hb : b ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0))) (hb' : b' ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0))) :
    (VS D).hT (D.sp.iXY 0 w + b) (D.sp.iXY 0 w' + b') = (D.sp.X 0).hT w w' + (VS D).hT b b' := by
  have h1 : (VS D).hT (D.sp.iXY 0 w) b' = 0 := (Formalism.MainNotions.mem_orth_iff _ _).1 hb' _ ⟨w, rfl⟩
  have h2 : (VS D).hT b (D.sp.iXY 0 w') = 0 := Formalism.MainNotions.hT_swap_zero ((Formalism.MainNotions.mem_orth_iff _ _).1 hb _ ⟨w', rfl⟩)
  simp only [map_add, LinearMap.add_apply]
  rw [embedding_isometry_W, h1, h2]
  ring

theorem extendByIdentity_mem_isom (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) (hγ : γ ∈ isom (D.sp.X 0).hT) :
    extendByIdentity D γ ∈ isom (VS D).hT := by
  intro x y
  obtain ⟨w, b, hb, rfl⟩ := exists_decomp_range_orth D x
  obtain ⟨w', b', hb', rfl⟩ := exists_decomp_range_orth D y
  rw [extendByIdentity_apply D γ w b hb, extendByIdentity_apply D γ w' b' hb', inner_decomp_orth_range D _ _ _ _ hb hb',
    inner_decomp_orth_range D _ _ _ _ hb hb', hγ w w']

theorem extendByIdentity_symm_apply (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) (w : (D.sp.X 0).V) (b : (VS D).V)
    (hb : b ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0))) :
    (extendByIdentity D γ).symm (D.sp.iXY 0 w + b) = D.sp.iXY 0 (γ.symm w) + b := by
  rw [LinearEquiv.symm_apply_eq, extendByIdentity_apply D γ _ b hb, LinearEquiv.apply_symm_apply]

theorem extendByIdentity_symm_fix_orth (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) (b : (VS D).V)
    (hb : b ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0))) : (extendByIdentity D γ).symm b = b := by
  have := extendByIdentity_symm_apply D γ 0 b hb
  simpa using this

end Ext

end Formalism.MainNotions.BridgeLemma₂

end
