import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldOneVariableTranscendentalFiniteAndEStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldFiniteSupportSumOrderEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalSectionAtRingPointSpMapCompRestrictStalkStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFunctionFieldOfOneVariableOfGenericPointOfCurvStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalSectionAtRingPointGenericInjectiveFractionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueCentreFunctionFieldPlaceCurveStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem evAt_congr' {R : Type} [CommRing R] {X : Scheme.{0}} {ξ ξ' : Sp R ⟶ X} (e : ξ = ξ') {U : X.Opens}
    (h : ⊤ ≤ ξ ⁻¹ᵁ U) (h' : ⊤ ≤ ξ' ⁻¹ᵁ U) (f : Γ(X, U)) : evAt ξ h f = evAt ξ' h' f := by
  subst e; rfl

theorem top_le_preimage_comp' {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ g ⁻¹ᵁ U) :
    ⊤ ≤ (f ≫ g) ⁻¹ᵁ U := by
  intro z _
  exact h (Set.mem_univ (f z))

theorem finite_centre_not_mem (k K E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] [Field E]
    [Algebra k E] [Algebra K E] [IsScalarTower k K E] [FiniteDimensional K E] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)]
    (x : Sp K ⟶ C) (hx : IsGenOver k x) (V : C.Opens) (hV : (V : Set C).Nonempty) :
    {p : Place k E | ∃ b : Sp p.O ⟶ C, spMap p.O.subtype ≫ b = spMap (algebraMap K E) ≫ x ∧ ¬ ⊤ ≤ b ⁻¹ᵁ V}.Finite := by
  have hC := hx.1
  haveI : IsIntegral C := GlobalTheory.LieSemineg.isIntegral_curve hC.1 hC.2.2
  obtain ⟨z, hz⟩ := hV
  obtain ⟨V', hV'a, hzV', hV'V⟩ := Opens.isBasis_iff_nbhd.1 C.isBasis_affineOpens hz
  have hV'a : IsAffineOpen V' := hV'a
  obtain ⟨hxV', -, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_generic_injective_fraction K C x hx.2.1 V' ⟨z, hzV'⟩
  obtain ⟨ev1, ev2, -, -, ev5, ev6, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk
  let f : Γ(C, V') →+* E := (algebraMap K E).comp (evAt x hxV')
  haveI := hC.1
  haveI : Smooth (strHom k C) := SmoothOfRelativeDimension.smooth 1 _
  have eV : V' ≤ strHom k C ⁻¹ᵁ ⊤ := fun _ _ => trivial
  let ψ := ((strHom k C).appLE ⊤ V' eV).hom
  have hft : ψ.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) (strHom k C) inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨V', hV'a⟩ eV
  letI := ψ.toAlgebra
  obtain ⟨s, hs⟩ := hft.out

  have hconst : ∀ (p : Place k E) (c : Γ(Sp k, ⊤)), p.1 (f (ψ c)) ≤ 1 := by
    intro p c
    have hxs : ⊤ ≤ (x ≫ strHom k C) ⁻¹ᵁ (⊤ : (Sp k).Opens) := top_le_preimage_comp' x (strHom k C) ⊤ (fun _ _ => trivial)
    have htop : ⊤ ≤ (𝟙 (Sp k)) ⁻¹ᵁ (⊤ : (Sp k).Opens) := fun _ _ => trivial
    have h1 : evAt x hxV' (ψ c) = evAt (x ≫ strHom k C) hxs c :=
      (ev2 K C (Sp k) x (strHom k C) V' ⊤ hxV' _ eV c).symm
    have h2 : evAt (x ≫ strHom k C) hxs c =
        evAt (spMap (algebraMap k K) ≫ 𝟙 (Sp k)) (top_le_preimage_comp' _ _ _ htop) c :=
      evAt_congr' (by rw [Category.comp_id]; exact hx.2.2) _ _ c
    have h3 := ev1 k K (Sp k) (algebraMap k K) (𝟙 (Sp k)) ⊤ htop (top_le_preimage_comp' _ _ _ htop) c
    have hf : f (ψ c) = algebraMap k E (evAt (𝟙 (Sp k)) htop c) := by
      simp only [f, RingHom.comp_apply]
      rw [h1, h2, h3, ← IsScalarTower.algebraMap_apply]
    rw [hf]
    by_cases hd : evAt (𝟙 (Sp k)) htop c = 0
    · rw [hd, map_zero, map_zero]; exact zero_le'
    · exact (p.2.2 _ hd).le
  have key : ∀ p : Place k E, (∀ a ∈ s, p.1 (f a) ≤ 1) → ∀ g, p.1 (f g) ≤ 1 := by
    intro p hp g
    have hg : g ∈ Algebra.adjoin Γ(Sp k, ⊤) (s : Set Γ(C, V')) := by rw [hs]; trivial
    induction hg using Algebra.adjoin_induction with
    | mem a ha => exact hp a ha
    | algebraMap c => exact hconst p c
    | add a b _ _ ha hb => rw [map_add]; exact (p.1.map_add _ _).trans (max_le ha hb)
    | mul a b _ _ ha hb => rw [map_mul, map_mul]; exact mul_le_one' ha hb
  have hE : IsFF k E := (GlobalTheory.T.functionFieldOneVariable_transcendental_finite_and_ext k K (GlobalTheory.T.isFunctionFieldOfOneVariable_of_genericPointOfCurve k K C x hx)).2 E
  refine ((s.finite_toSet.biUnion fun a _ => (?_ : {p : Place k E | ¬ p.1 (f a) ≤ 1}.Finite))).subset ?_
  · by_cases h0 : f a = 0
    · convert Set.finite_empty
      ext p; simp [h0]
    · exact (GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k E hE (f a) h0).1.subset fun p hp h1 => hp h1.le
  · rintro p ⟨b, hb1, hb2⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    by_contra hno
    push_neg at hno
    have hall := key p fun a ha => hno a ha
    have hmem : ∀ g, f g ∈ p.O := fun g => (Valuation.mem_valuationSubring_iff _ _).2 (hall g)
    let φ : Γ(C, V') →+* p.O := f.codRestrict p.O hmem
    obtain ⟨b', hb', hev⟩ := ev6 p.O C V' hV'a φ
    have hc := top_le_preimage_comp' (spMap p.O.subtype) b' V' hb'
    have hd := top_le_preimage_comp' (spMap (algebraMap K E)) x V' hxV'
    have hcd : spMap p.O.subtype ≫ b' = spMap (algebraMap K E) ≫ x := by
      refine ev5 E C _ _ V' hV'a hc hd ?_
      ext g
      rw [ev1 p.O E C p.O.subtype b' V' hb' hc g, ev1 K E C (algebraMap K E) x V' hxV' hd g, hev]
      rfl
    have hbb := (GlobalTheory.T.existsUnique_centre_functionFieldPlace_curve k K E C x hx p).unique hb1 hcd
    subst hbb
    exact hb2 fun w hw => hV'V (hb' hw)

end GlobalTheory.Nef
