import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueRealLinearOfEventuallyAddModDiscrete

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.UnifPoint

open Topology Filter

theorem t2Space_ptsOver_of_isSeparated {X S : Scheme.{0}} (p : X ⟶ S) [IsSeparated p] (s : Sp ℂ ⟶ S) :
    T2Space (Points.PtsOver p s) := by
  rw [t2_iff_isClosed_diagonal]
  let h := Points.PtsOver.prodHomeomorph (IsPullback.of_hasPullback p p) s
  have hd : pullback.diagonal p ≫ pullback.fst p p ≫ p = p := by simp
  have hc := (h.isClosedEmbedding.comp
    (Points.PtsOver.isClosedEmbedding_map (pullback.diagonal p) hd s)).isClosed_range
  convert hc using 1
  have key : ∀ x, h (Points.PtsOver.map (pullback.diagonal p) hd s x) = (x, x) := fun x =>
    Prod.ext (Subtype.ext (by simp [h])) (Subtype.ext (by simp [h]))
  ext ⟨a, b⟩
  constructor
  · intro hab
    obtain rfl : a = b := hab
    exact ⟨a, key a⟩
  · rintro ⟨x, hx⟩
    rw [Function.comp_apply, key] at hx
    rw [← hx]
    rfl

theorem exists_realLinear_lift {V W Q T : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
    [NormedSpace ℝ W] [FiniteDimensional ℝ W] [Group Q] [TopologicalSpace T] [T2Space T] (j : Q → T)
    (hj : Function.Injective j) (e : W → Q) (e₀ : V → Q) (he : ∀ z w, e (z + w) = e z * e w)
    (he₀ : ∀ z w, e₀ (z + w) = e₀ z * e₀ w) (hs : Function.Surjective e) (Λ : Submodule ℤ W) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hk : ∀ z, e z = 1 ↔ z ∈ Λ) (hc : Continuous (j ∘ e)) (hc₀ : Continuous (j ∘ e₀)) :
    ∃ L : V →L[ℝ] W, ∀ z, e (L z) = e₀ z := by
  have heq : ∀ z w, e z = e w ↔ z - w ∈ Λ := fun z w => by
    rw [← hk, ← mul_left_inj (e w) (b := e (z - w)), ← he, sub_add_cancel, _root_.one_mul]
  have : CompactSpace (W ⧸ Λ) := by
    refine ⟨?_⟩
    rw [← (Submodule.mkQ_surjective Λ).range_eq]
    refine IsZLattice.isCompact_range_of_periodic Λ _ Λ.isOpenQuotientMap_mkQ.continuous fun z w hw => ?_
    rw [map_add, Submodule.mkQ_apply _ w, (Submodule.Quotient.mk_eq_zero Λ).2 hw, add_zero]
  let ē : W ⧸ Λ → T := Quotient.lift (j ∘ e) fun a b hab =>
    congrArg j ((heq a b).2 ((Submodule.quotientRel_def Λ).1 hab))
  have hē : ∀ w, ē (Λ.mkQ w) = j (e w) := fun _ => rfl
  have hemb : IsClosedEmbedding ē := by
    refine (hc.quotient_lift _).isClosedEmbedding fun a b hab => ?_
    obtain ⟨a, rfl⟩ := Λ.mkQ_surjective a
    obtain ⟨b, rfl⟩ := Λ.mkQ_surjective b
    exact (Submodule.Quotient.eq Λ).2 ((heq a b).1 (hj hab))
  choose σ hσ using hs
  let φ : V →+ W ⧸ Λ := AddMonoidHom.mk' (fun z => Λ.mkQ (σ (e₀ z))) fun a b => by
    rw [← map_add]
    exact (Submodule.Quotient.eq Λ).2 ((heq _ _).1 (by rw [he, hσ, hσ, hσ, he₀]))
  have hφ : Continuous φ := hemb.isEmbedding.continuous_iff.2 (hc₀.congr fun z => by
    show j (e₀ z) = j (e (σ (e₀ z)))
    rw [hσ])
  obtain ⟨L, hL, -⟩ := existsUnique_realLinear_lift (ex := φ) (isDiscrete_ker_mkQ Λ)
    (Λ.isOpenMap_mkQ.nhds_le 0) hφ.continuousAt
  exact ⟨L, fun z => ((heq _ _).2 ((Submodule.Quotient.eq Λ).1 (hL z))).trans (hσ _)⟩

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S}

def IsExp {g : ℕ} (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) : Prop :=
  (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧
    (∀ w, ∃! v : epsPt y ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
    (∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)

theorem continuous_of_isHolTo {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}
    {a : V → (Sp ℂ ⟶ X)} (h : IsHolTo Set.univ a) : Continuous a :=
  Points.continuous_of_differentiableOn fun U f => by simpa using h U f

theorem differentiableAt_of_isHolTo {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}
    {a : V → (Sp ℂ ⟶ X)} (h : IsHolTo Set.univ a) (U : X.Opens) (f : Γ(X, U)) {z : V} (hz : ⊤ ≤ a z ⁻¹ᵁ U) :
    DifferentiableAt ℂ (fun b => valAt' (a b) U f) z :=
  (h U f).2.differentiableAt ((h U f).1.mem_nhds ⟨trivial, hz⟩)

theorem IsExp.eq_of_fderiv {g : ℕ} {e : (Fin g → ℂ) → (Over.mk y ⟶ G)} (he : IsExp e) {w w' : Fin g → ℂ}
    (h : ∀ (U : G.left.Opens) (f : Γ(G.left, U)), ⊤ ≤ (e 0).left ⁻¹ᵁ U →
      fderiv ℂ (fun z => valAt' (e z).left U f) 0 w = fderiv ℂ (fun z => valAt' (e z).left U f) 0 w') : w = w' := by
  obtain ⟨v, hv, -⟩ := he.2.2.2.1 w
  refine (he.2.2.2.2 v hv.1).unique hv ⟨hv.1, fun U hU f => (hv.2 U hU f).trans (h U f ?_)⟩
  have h1 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left := hv.1
  rw [← h1]
  exact Points.le_preimage_comp _ _ hU (Points.le_preimage_top _)

theorem map_zero_of_add {V Q : Type*} [AddGroup V] [Group Q] {e : V → Q} (he : ∀ z w, e (z + w) = e z * e w) :
    e 0 = 1 := by
  have := he 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

theorem eq_iff_sub_of_add {V Q : Type*} [AddGroup V] [Group Q] {e : V → Q} (he : ∀ z w, e (z + w) = e z * e w)
    (z w : V) : e z = e w ↔ e (z - w) = 1 := by
  rw [← mul_left_inj (e w) (b := e (z - w)), ← he, sub_add_cancel, _root_.one_mul]

theorem IsExp.exists_linearEquiv [IsSeparated G.hom] {g g₀ : ℕ} {e : (Fin g → ℂ) → (Over.mk y ⟶ G)} (he : IsExp e)
    (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hk : ∀ z, e z = 1 ↔ z ∈ Λ)
    {e₀ : (Fin g₀ → ℂ) → (Over.mk y ⟶ G)} (ha : ∀ z w, e₀ (z + w) = e₀ z * e₀ w) (hs : Function.Surjective e₀)
    (hh : IsHolTo Set.univ (fun z => (e₀ z).left)) (hc : {z | e₀ z = 1}.Countable) :
    ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e (h z) = e₀ z := by
  have := t2Space_ptsOver_of_isSeparated G.hom y
  obtain ⟨L, hL⟩ := exists_realLinear_lift (T := Points.PtsOver G.hom y) (fun x : Over.mk y ⟶ G => ⟨x.left, Over.w x⟩)
    (fun a b hab => Over.OverMorphism.ext (congrArg Subtype.val hab)) e e₀ he.1 ha he.2.1 Λ hk
    ((continuous_of_isHolTo he.2.2.1).subtype_mk _) ((continuous_of_isHolTo hh).subtype_mk _)
  have hsm : ∀ (c : ℂ) z, L (c • z) = c • L z := fun c z => he.eq_of_fderiv fun U f hU => by
    have h0 : (e₀ 0).left = (e 0).left := by rw [map_zero_of_add ha, map_zero_of_add he.1]
    have d := (differentiableAt_of_isHolTo he.2.2.1 U f hU).hasFDerivAt.restrictScalars ℝ
    have d₀ := (differentiableAt_of_isHolTo hh U f (z := 0) (by simpa only [h0] using hU)).hasFDerivAt.restrictScalars ℝ
    rw [← L.map_zero] at d
    have d₁ := d.comp 0 L.hasFDerivAt
    rw [L.map_zero] at d₁
    have e₁ : (fun b => valAt' (e b).left U f) ∘ L = fun b => valAt' (e₀ b).left U f := by
      funext b
      simp only [Function.comp_apply, hL]
    rw [e₁] at d₁
    have k := fun x => DFunLike.congr_fun (d₁.unique d₀) x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars'] at k
    rw [k, map_smul, map_smul, k]
  have hi : Function.Injective L := realLinear_injective_of_countable_ker L.toLinearMap
    (hc.mono fun x (hx : L x = 0) => by
      show e₀ x = 1
      rw [← hL, hx, map_zero_of_add he.1])
  have hsu : Function.Surjective L := realLinear_surjective_of_mod_countable L.toLinearMap (Γ := Λ)
    (Set.countable_coe_iff.1 (inferInstanceAs (Countable Λ))) fun w => by
      obtain ⟨x, hx⟩ := hs (e w)
      exact ⟨x, (hk _).1 ((eq_iff_sub_of_add he.1 _ _).1 (hx.symm.trans (hL x).symm))⟩
  exact ⟨LinearEquiv.ofBijective ⟨⟨L, L.map_add⟩, hsm⟩ ⟨hi, hsu⟩, hL⟩

end GlobalTheory.UnifPoint
