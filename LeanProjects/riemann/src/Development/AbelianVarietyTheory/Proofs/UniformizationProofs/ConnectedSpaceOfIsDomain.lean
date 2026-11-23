import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConnDvr

theorem connectedSpace_of_isDomain (X : Scheme.{0}) [IsDomain Γ(X, ⊤)] : ConnectedSpace X := by
  have hne : Nonempty X := by
    by_contra h
    have hT : (⊤ : X.Opens) = ⊥ := by
      ext x
      exact (h ⟨x⟩).elim
    have : Subsingleton Γ(X, ⊤) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hT)
    exact false_of_nontrivial_of_subsingleton Γ(X, ⊤)
  refine { toNonempty := hne, isPreconnected_univ := ?_ }
  intro U W hU hW hc ⟨u, _, hu⟩ ⟨w, _, hw⟩
  by_contra hd
  let U' : X.Opens := ⟨U, hU⟩
  let W' : X.Opens := ⟨W, hW⟩
  have h0 : U' ⊓ W' = ⊥ := le_bot_iff.1 fun y hy => hd ⟨y, trivial, hy⟩
  have h1 : U' ⊔ W' = ⊤ := top_unique fun y _ => hc (Set.mem_univ y)
  have : Nonempty U' := ⟨⟨u, hu⟩⟩
  have : Nonempty W' := ⟨⟨w, hw⟩⟩
  have hdom : IsDomain Γ(X, U' ⊔ W') := by rw [h1]; infer_instance
  let e : Γ(X, U' ⊔ W') ≅ CommRingCat.of _ :=
    (X.sheaf.isProductOfDisjoint U' W' h0).conePointUniqueUpToIso
      (CommRingCat.prodFanIsLimit _ _)
  have : IsDomain (Γ(X, U') × Γ(X, W')) :=
    e.symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  exact false_of_nontrivial_of_product_domain Γ(X, U') Γ(X, W')

theorem injective_or_le_ker {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] (φ : V →+* K) :
    Function.Injective φ ∨ IsLocalRing.maximalIdeal V ≤ RingHom.ker φ := by
  by_cases h : RingHom.ker φ = ⊥
  · exact Or.inl ((RingHom.injective_iff_ker_eq_bot φ).2 h)
  · have hp : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
    have hm : (RingHom.ker φ).IsMaximal := Ring.DimensionLEOne.maximalOfPrime h hp
    exact Or.inr (IsLocalRing.eq_maximalIdeal hm).ge

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (B : Over (Spec (CommRingCat.of V))) [IsProper B.hom], Function.Bijective B.hom.appTop.hom → GeometricallyConnected (thickObj V (IsLocalRing.maximalIdeal V) 0 B).hom → GeometricallyConnected B.hom := by
  intro V _ _ _ B _ hb hc
  refine ⟨geometrically_iff_of_commRing.2 ?_⟩
  intro K _ _ Y p q H
  rcases injective_or_le_ker (algebraMap V K) with h | h
  · have : FaithfulSMul V K := (faithfulSMul_iff_algebraMap_injective V K).2 h
    have hf : Module.Flat V K := inferInstance
    have : Flat (Spec.map (CommRingCat.ofHom (algebraMap V K))) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact RingHom.flat_algebraMap_iff.2 hf
    have : IsIso B.hom.appTop := (ConcreteCategory.isIso_iff_bijective _).2 hb
    have : IsIso q.appTop := GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback H
    have : IsDomain Γ(Y, ⊤) :=
      (asIso q.appTop).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
    exact connectedSpace_of_isDomain Y
  · have h' : ∀ a ∈ IsLocalRing.maximalIdeal V ^ (0 + 1), algebraMap V K a = 0 := fun a ha => by
      rw [zero_add, pow_one] at ha
      exact h ha
    let y : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1))) :=
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _ (algebraMap V K) h'))
    have hy : y ≫ thick V (IsLocalRing.maximalIdeal V) 0 =
        Spec.map (CommRingCat.ofHom (algebraMap V K)) := by
      simp only [y, thick, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl
    rw [← hy] at H
    let r : Y ⟶ pullback B.hom (thick V (IsLocalRing.maximalIdeal V) 0) :=
      pullback.lift p (q ≫ y) (by rw [H.w, Category.assoc])
    have H' : IsPullback r q (pullback.snd B.hom (thick V (IsLocalRing.maximalIdeal V) 0)) y := by
      refine IsPullback.of_right (h₁₂ := pullback.fst _ _) (v₁₃ := B.hom) (h₂₂ := thick V _ 0) ?_ ?_
        (IsPullback.of_hasPullback _ _)
      · rw [pullback.lift_fst]; exact H
      · exact pullback.lift_snd _ _ _
    exact hc.geometrically_connectedSpace y r q H'

end GlobalTheory.ConnDvr
