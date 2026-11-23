import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSubfieldOfForallRingEquivFixedOfIsAlgClosedAlStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShimuraObjectPullbackCompCancelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsObjMapFixingDescendedPointsSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledLowerObjectGroupIdentificationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledLowerObjectDescendsWithPointsSubfieldStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.BaseDescent

theorem ratHom_mem_of_isAlgClosed : ∀ (K : Type) [Field K] (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (F : IntermediateField ℚ ℂ), FiniteDimensional ℚ F → ∀ (g : F →+* K) (x : F), g x ∈ k₀ := by
  intro K _ k₀ hk₀ F hF g x
  haveI : CharZero K := (RingHom.charZero_iff g.injective).mp inferInstance
  haveI : CharZero k₀ := (RingHom.charZero_iff k₀.subtype.injective).mpr inferInstance
  have h1 : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
  have h2 : IsAlgebraic ℚ (g x) := by
    have := h1.algHom g.toRatAlgHom
    simpa using this
  have h3 : IsIntegral k₀ (g x) := (h2.extendScalars (algebraMap ℚ k₀).injective).isIntegral
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible k₀ (minpoly.irreducible h3)
  obtain ⟨y, hy⟩ := minpoly.mem_range_of_degree_eq_one k₀ (g x) hdeg
  rw [← hy]
  exact y.2

theorem pulledObj_descends : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X), DivFrom L Q oQ iw s ε e → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (ev : V →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (o' : LowObj D' c ((ev.comp iw).comp L.b)) (m₁ : ObjMap o' L.o (spMap (ev.comp iw))), (∃ (B₀ : Over (Sp k₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (Sp k₀ ⟶ B₀.left)) (B' : Over (Sp K)) (_ : GrpObj B') (π₁ : B'.left ⟶ Q.P.A.left) (π₀ : B'.left ⟶ B₀.left) (w : LB.Iso (Q.P.L.pull π₁) (M₀.pull π₀)) (c' : Q.X → (Sp K ⟶ B'.left)), IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback B' Q.P.A (spMap ev) π₁ ∧ IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ ∧ w.IsGen ∧ ∀ a, c' a ≫ B'.hom = 𝟙 _ ∧ c' a ≫ π₁ = spMap ev ≫ (Q.c a).left ∧ c' a ≫ π₀ = spMap k₀.subtype ≫ c₀ a) → ∃ (B₀ : Over (Sp k₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (π : o'.t.G.left ⟶ B₀.left), IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback o'.t.G B₀ (spMap k₀.subtype) π ∧ LBIso o'.t.PP.L (M₀.pull π) ∧ ∀ y : L.D.X, ∃ x : Sp K ⟶ o'.t.G.left, x ≫ o'.t.G.hom = 𝟙 _ ∧ x ≫ m₁.toSABMap.φ ≫ L.φB = spMap (ev.comp iw) ≫ (L.D.c y).left ∧ ∃ x₀ : Sp k₀ ⟶ B₀.left, x ≫ π = spMap k₀.subtype ≫ x₀ := by
  intro E _ _ _ H D' l c L V _ _ Q _ oQ iw I _ s ε e hDiv K _ _ _ ev k₀ hk₀ o' m₁ hB
  obtain ⟨B₀, _, _, M₀, c₀, B', _, π₁, π₀, w, c', hab, hM, h1, h0, hw, hc⟩ := hB
  obtain ⟨θ, hθ, hLθ, hrel⟩ := GlobalTheory.T.pulledLowerObject_group_identification L Q oQ iw s ε e hDiv K ev o' m₁ B' π₁ h1
  obtain ⟨hpb, hL, hpts⟩ := GlobalTheory.T.pulledLowerObject_descends_with_points_subfield L Q oQ iw s ε e hDiv K ev k₀ hk₀ o' m₁ B₀ M₀ c₀ B' π₁ π₀ w c' θ hab hM h1 h0 hw hc hθ hLθ hrel
  exact ⟨B₀, inferInstance, inferInstance, M₀, θ ≫ π₀, hab, hM, hpb, hL, fun y => by
    obtain ⟨x, hx1, hx2, x₀, hx₀⟩ := hpts y
    exact ⟨x, hx1, hx2, x₀, by rw [← Category.assoc] at hx₀ ⊢; simpa using hx₀⟩⟩

end GlobalTheory.UCanon.BaseDescent

theorem GlobalTheory.UCanon.base_value_mem_of_descended_point : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X), DivFrom L Q oQ iw s ε e → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∃ (B₀ : Over (Sp k₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (Sp k₀ ⟶ B₀.left)) (B' : Over (Sp K)) (_ : GrpObj B') (π₁ : B'.left ⟶ Q.P.A.left) (π₀ : B'.left ⟶ B₀.left) (w : LB.Iso (Q.P.L.pull π₁) (M₀.pull π₀)) (c' : Q.X → (Sp K ⟶ B'.left)), IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback B' Q.P.A (spMap ev) π₁ ∧ IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ ∧ w.IsGen ∧ ∀ a, c' a ≫ B'.hom = 𝟙 _ ∧ c' a ≫ π₁ = spMap ev ≫ (Q.c a).left ∧ c' a ≫ π₀ = spMap k₀.subtype ≫ c₀ a) → ∀ a, ev (iw a) ∈ k₀ := by
  intro E _ _ _ H D' l c L V _ _ Q _ oQ iw I _ s ε e hDiv K _ _ ev k₀ hk₀ hB a
  let f : L.W →+* K := ev.comp iw
  have hF : ∀ x : c.F, (f.comp L.b) x ∈ k₀ := GlobalTheory.UCanon.BaseDescent.ratHom_mem_of_isAlgClosed K k₀ hk₀ c.F c.fin (f.comp L.b)
  haveI : CharZero K := (RingHom.charZero_iff (f.comp L.b).injective).mp inferInstance
  obtain ⟨o', ⟨m₁⟩⟩ := (GlobalTheory.T.shimuraObject_pullback_comp_cancel (D := D') (l := GlobalTheory.LowDat.lowLevel l)).1 (lowMap c L.b) L.o (spMap f)
    (lowMap c (f.comp L.b)) (by simp only [lowMap, spMap, ← Spec.map_comp]; rfl)
  obtain ⟨B₀, _, _, M₀, π, hab, hM, hpb, hL, hpts⟩ := GlobalTheory.UCanon.BaseDescent.pulledObj_descends L Q oQ iw s ε e hDiv K ev k₀ hk₀ o' m₁ hB
  choose x hx1 hx2 hx3 using hpts
  apply GlobalTheory.T.mem_subfield_of_forall_ringEquiv_fixed_of_isAlgClosed' K k₀ hk₀
  intro σ hσ
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_objMap_fixing_descended_points_subfield K k₀ hk₀ o' B₀ M₀ π hab hM hpb hL σ hσ
  have hcomp : ∀ g' : Sp K ⟶ Sp L.W, g' = spMap (σ : K →+* K) ≫ spMap f →
      ∃ k : ObjMap o' L.o g', k.toSABMap.φ = n.toSABMap.φ ≫ m₁.toSABMap.φ := by
    rintro g' rfl
    exact ((GlobalTheory.T.shimuraObject_pullback_comp_cancel (D := D') (l := GlobalTheory.LowDat.lowLevel l)).2 _ _ _ L.o o' o' (spMap f) (spMap (σ : K →+* K)) m₁).1 n
  obtain ⟨m₂, hm₂⟩ := hcomp (spMap ((σ : K →+* K).comp f)) (by simp only [spMap, ← Spec.map_comp]; rfl)
  have key := L.fineRed K f ((σ : K →+* K).comp f)
    (by ext y; simp only [RingHom.comp_apply]; exact (hσ _ (hF y)).symm) o' m₁ m₂ x hx2
    (fun y => by
      rw [hm₂, Category.assoc, ← Category.assoc (x y), hn (x y) (hx1 y) (hx3 y), Category.assoc, hx2 y]
      simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, f]) hx1
  have := congrArg (fun g : L.W →+* K => g a) key
  simpa [f] using this.symm
