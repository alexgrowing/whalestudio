import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCocycleFirstChernClassTateTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC
open ClsSpec

theorem one_eq_of_ev (q : ℕ) [NeZero q] (E : Spc) (hE : Inv q E)
    (α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0)
    (hα : ∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ) :
    CohomologyClass.mk α = one q E := by
  obtain ⟨β, hβ, hβv⟩ := one_spec q E hE
  rw [← hβ]
  congr 1
  refine Cocycle.ext ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1 _ _ fun p s h U x => ?_)
  cases p with
  | zero =>
    obtain rfl : s = 0 := by simpa using h.symm
    refine ClsSpec.sep (ClsSpec.loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).1 (hE U ⟨x⟩)) fun V g hz => ?_)
    obtain ⟨ζ⟩ := hz
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 α.1, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 β.1, hα _ _ ζ, hβv _ _ ζ]
  | succ p =>
    have hs : s < 0 := by omega
    haveI := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness (ZMod q) (tw q 0) U).2.2.2 s hs
    exact Subsingleton.elim _ _

theorem pull_one (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') (hE' : Inv q E') :
    pull _ f _ _ (one q E') = one q E := by
  have hE : Inv q E := fun U ⟨x⟩ => hE' U ⟨x.map f⟩
  obtain ⟨β, hβ, hβv⟩ := one_spec q E' hE'
  rw [← hβ]
  refine one_eq_of_ev q E hE _ fun U x ζ => ?_
  exact ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.1 f β.1 0 0 _ U x).trans (hβv U (x.map f) ζ)

theorem rootClass_eq_secClass {q : ℕ} (i : ℤ) {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) :
    rootClass i ζ = secClass (tw q i) (twGen i ζ) := by
  unfold rootClass secClass
  congr 1
  funext c
  apply propext
  constructor
  · rintro ⟨α, hα, h⟩
    exact ⟨α, hα, (h X (𝟙 X)).trans (ClsSpec.res_id _)⟩
  · rintro ⟨α, hα, h⟩
    refine ⟨α, hα, fun U x => ?_⟩
    have e := (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 α.1 0 0 (by simp) U X x (𝟙 X)
    rw [h] at e
    refine e.symm.trans ?_
    congr 1

theorem one_root_spec : ∀ (q : ℕ) [NeZero q], (∀ E : Spc, Inv q E → ∃ α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0, CohomologyClass.mk α = one q E ∧ ∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ) ∧ (∀ E : Spc, Inv q E → ∀ α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0, (∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ) → CohomologyClass.mk α = one q E) ∧ (∀ {E E' : Spc} (f : E ⟶ E'), Inv q E' → pull _ f _ _ (one q E') = one q E) ∧ ∀ (i : ℤ) (X : Scheme.{0}) (ζ : Prim q Γ(X, ⊤)), rootClass i ζ = secClass (tw q i) (twGen i ζ) :=
  fun q _ => ⟨fun E hE => one_spec q E hE, fun E hE α hα => one_eq_of_ev q E hE α hα,
    fun f hE' => pull_one q f hE', fun i _ ζ => rootClass_eq_secClass i ζ⟩

end GlobalTheory.EtC

end
