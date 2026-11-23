import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueExtensionOfForallNormLeOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))

namespace GlobalTheory

namespace BoundedRegular

theorem valF_spMap_comp_eq {F F' : Type} [Field F] [Field F'] (f : F →+* F') {X : Scheme.{0}}
    (t : Sp F ⟶ X) (U : X.Opens) (ht : ⊤ ≤ t ⁻¹ᵁ U) (φ : Γ(X, U)) :
    valF (spMap f ≫ t) U φ =
      f ((Scheme.ΓSpecIso (CommRingCat.of F)).hom (t.appLE U ⊤ ht φ)) := by
  have h' : ⊤ ≤ (spMap f ≫ t) ⁻¹ᵁ U := fun q _ => ht (Set.mem_univ (spMap f q))
  rw [valF, dif_pos h']
  have e : (spMap f ≫ t).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of F')).hom =
      t.appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom ≫ CommRingCat.ofHom f := by
    rw [← Scheme.ΓSpecIso_naturality, ← Scheme.Hom.appLE_comp_appLE (spMap f) t U ⊤ ⊤ ht le_rfl,
      Category.assoc]
    rfl
  exact congrArg (fun g => g.hom φ) e

theorem valF_mul_valF_eq_one {F : Type} [Field F] {X : Scheme.{0}} (t : Sp F ⟶ X) (U : X.Opens)
    (ht : Set.range t ⊆ U) {φ φ' : Γ(X, U)} (h : φ * φ' = 1) :
    valF t U φ * valF t U φ' = 1 := by
  have h' : ⊤ ≤ t ⁻¹ᵁ U := fun q _ => ht ⟨q, rfl⟩
  rw [valF, valF, dif_pos h', dif_pos h', ← map_mul, ← map_mul, h, map_one, map_one]

theorem exists_point_norm_valF_eq {X : Scheme.{0}} {p : ℕ} [Fact p.Prime]
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (y : Spec (.of (integralClosure ℤ_[p] K)) ⟶ X) (U : X.Opens)
    (hy : ⊤ ≤ (Spec.map (CommRingCat.ofHom (algebraMap (integralClosure ℤ_[p] K) K)) ≫ y) ⁻¹ᵁ U)
    (φ : Γ(X, U)) :
    ∃ y' : Sp (OO p) ⟶ X, y' (cPt p) = y (IsLocalRing.closedPoint (integralClosure ℤ_[p] K)) ∧
      Set.range (gPt p ≫ y') ⊆ U ∧
      valF (gPt p ≫ y') U φ = (((Scheme.ΓSpecIso (.of K)).hom
        ((Spec.map (CommRingCat.ofHom (algebraMap (integralClosure ℤ_[p] K) K)) ≫ y).appLE
          U ⊤ hy φ) : K) : PadicAlgCl p) := by
  haveI := isLocalHom_integralClosureToPadicAlgClIntegers K
  have e : gPt p ≫ spMap (integralClosureToPadicAlgClIntegers K) ≫ y =
      spMap K.val.toRingHom ≫
        Spec.map (CommRingCat.ofHom (algebraMap (integralClosure ℤ_[p] K) K)) ≫ y := by
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  refine ⟨spMap (integralClosureToPadicAlgClIntegers K) ≫ y, ?_, ?_, ?_⟩
  · refine (Scheme.Hom.comp_apply _ _ _).trans (congrArg y ?_)
    exact IsLocalRing.comap_closedPoint (integralClosureToPadicAlgClIntegers K)
  · rw [e]
    rintro _ ⟨q, rfl⟩
    exact hy (Set.mem_univ (spMap K.val.toRingHom q))
  · rw [e, valF_spMap_comp_eq _ _ U hy]
    rfl

theorem existsUnique_resG_eq {X : Scheme.{0}} [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π]
    [LocallyOfFiniteType π] (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) {U W : X.Opens}
    (h : U ≤ W) (φ : Γ(X, U)) (hU : (U : Set X).Nonempty)
    (H : ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ X), y (cPt p) ∈ W →
      Set.range (gPt p ≫ y) ⊆ U → ‖valF (gPt p ≫ y) U φ‖ ≤ 1) :
    ∃! ψ : Γ(X, W), resG X h ψ = φ := by
  haveI : Nonempty U := hU.to_subtype
  haveI : Nonempty W := (hU.mono h).to_subtype
  obtain ⟨ψ, hψ⟩ := exists_germToFunctionField_eq_of_frequently_norm_le_one π U W
    (fun x _ _ _ => (hX x).2) (φ := φ) fun p _ K hK => ⟨K, hK, le_rfl, fun y hy hW _ _ => by
      obtain ⟨y', h1, h2, h3⟩ := exists_point_norm_valF_eq K y U hy φ
      rw [← h3]
      exact H p y' (h1 ▸ hW) h2⟩
  have e : resG X h ψ = φ :=
    X.germToFunctionField_injective U ((X.presheaf.germ_res_apply (homOfLE h) _ _ ψ).trans hψ)
  exact ⟨ψ, e, fun ψ' h' => map_injective_of_isIntegral X (homOfLE h) (h'.trans e.symm)⟩

end BoundedRegular

open BoundedRegular in

theorem regular_of_bounded_at_padicAlgCl_points :
    (∀ (X : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π] (x : X),
      IsClosed ({x} : Set X) → IsIntegrallyClosed (X.presheaf.stalk x) →
      ∀ (U : X.Opens) (φ : Γ(X, U)), (U : Set X).Nonempty →
      (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ X), y (cPt p) = x →
        Set.range (gPt p ≫ y) ⊆ U → ‖valF (gPt p ≫ y) U φ‖ ≤ 1) →
      ∃ (W : X.Opens) (ψ : Γ(X, W)), x ∈ W ∧
        resG X (inf_le_left : W ⊓ U ≤ W) ψ = resG X (inf_le_right : W ⊓ U ≤ U) φ) ∧
    (∀ (X : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π],
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ (U W : X.Opens) (h : U ≤ W) (φ : Γ(X, U)),
      (U : Set X).Nonempty →
      ((∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ X), y (cPt p) ∈ W →
        Set.range (gPt p ≫ y) ⊆ U → ‖valF (gPt p ≫ y) U φ‖ ≤ 1) →
          ∃! ψ : Γ(X, W), resG X h ψ = φ) ∧
      (IsUnit φ → (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ X), y (cPt p) ∈ W →
        Set.range (gPt p ≫ y) ⊆ U → ‖valF (gPt p ≫ y) U φ‖ = 1) →
          ∃ ψ : Γ(X, W), IsUnit ψ ∧ resG X h ψ = φ)) := by
  refine ⟨fun X _ π _ _ x hx hn U φ hU H => ?_, fun X _ π _ _ hX U W h φ hU =>
    ⟨existsUnique_resG_eq π hX h φ hU, fun hφ H => ?_⟩⟩
  · haveI : Nonempty U := hU.to_subtype
    obtain ⟨p, hp, hpx⟩ := exists_prime_residueField_eq_zero π hx
    haveI : Fact p.Prime := ⟨hp⟩
    have hm := mem_range_stalk_of_forall_norm_le_one π hx hpx (φ := φ) fun K _ y hy hyx => by
      obtain ⟨y', h1, h2, h3⟩ := exists_point_norm_valF_eq K y U hy φ
      rw [← h3]
      exact H p y' (h1.trans hyx) h2
    obtain ⟨V, hV, s, hxV, -, hs⟩ :=
      exists_germToFunctionField_eq_of_mem_range_stalk hm (W := ⊤) trivial
    have hg : ∀ (W : X.Opens) [Nonempty W], genericPoint X ∈ W := fun W h =>
      ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr (by simpa using h)
    haveI : Nonempty (V ⊓ U : X.Opens) := ⟨⟨_, hg V, hg U⟩⟩
    refine ⟨V, s, hxV, X.germToFunctionField_injective (V ⊓ U) ?_⟩
    exact (X.presheaf.germ_res_apply (homOfLE inf_le_left) _ _ s).trans
      (hs.trans (X.presheaf.germ_res_apply (homOfLE inf_le_right) _ _ φ).symm)
  · haveI : Nonempty U := hU.to_subtype
    obtain ⟨φ', hφ'⟩ := hφ.exists_right_inv
    obtain ⟨ψ, hψ, -⟩ := existsUnique_resG_eq π hX h φ hU fun p _ y h1 h2 => (H p y h1 h2).le
    obtain ⟨ψ', hψ', -⟩ := existsUnique_resG_eq π hX h φ' hU fun p _ y h1 h2 => by
      have e := congrArg norm (valF_mul_valF_eq_one _ U h2 hφ')
      rw [norm_mul, H p y h1 h2, _root_.one_mul, norm_one] at e
      exact e.le
    refine ⟨ψ, IsUnit.of_mul_eq_one ψ' (map_injective_of_isIntegral X (homOfLE h) ?_), hψ⟩
    change resG X h (ψ * ψ') = resG X h 1
    rw [map_mul, hψ, hψ', hφ', map_one]

end GlobalTheory
