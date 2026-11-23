import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfUnitOnEtalePoints
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonHypercohomologyOfLocallyExactOnSuppoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleEqChainMapShiftCompatClassesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBiproductChainMapOfInjectiveFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeIsKInjectiveBijectiveHypercohomologyIStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsComplexExactEtaleLocallyOfNoClassesStatement

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.DiscSupp

theorem assemble : ∀ (R : Type) [CommRing R] {ι : Type} [Fintype ι] (L : ι → Cx R) (C : Cx R) (d : ι → ℤ) (ψ : ∀ j, Cocycle (L j) C (d j)) (m₀ : ℤ), (∀ j, (L j).IsStrictlyGE m₀) → (∀ j n, CategoryTheory.Injective ((L j).X n)) → ∃ (D : Cx R) (f : D ⟶ C) (m : ℤ), D.IsStrictlyGE m ∧ (∀ n, CategoryTheory.Injective (D.X n)) ∧ ∀ (K : Cx R) (n : ℤ), ∃ e : (∀ j, CohomologyClass K (L j) (n - d j)) ≃ CohomologyClass K D n, ∀ a, cpush K f n (e a) = ∑ j, cpost K (ψ j) (n - d j) n (by omega) (a j) := by
  intro R _ ι _ L C d ψ m₀ hL hLi
  choose L' g hb hi he using fun j => GlobalTheory.T.cocycle_eq_chainMap_shift_compat_classes R (L j) C (d j) (ψ j)
  choose e he using he
  have hm : ∀ j, (L' j).IsStrictlyGE (m₀ - ∑ k, |d k|) := fun j => by
    haveI := hb j m₀ (hL j)
    refine isStrictlyGE_of_ge (L' j) _ (m₀ + d j) ?_
    have h1 : |d j| ≤ ∑ k, |d k| := Finset.single_le_sum (f := fun k => |d k|) (fun k _ => abs_nonneg (d k)) (Finset.mem_univ j)
    have h2 := neg_abs_le (d j)
    omega
  obtain ⟨D, f, hD, hDi, hs⟩ := GlobalTheory.T.exists_biproduct_chainMap_of_injective_family R L' C g (m₀ - ∑ k, |d k|) hm (fun j => hi j (hLi j))
  refine ⟨D, f, _, hD, hDi, fun K n => ?_⟩
  obtain ⟨e', he'⟩ := hs K n
  refine ⟨(Equiv.piCongrRight fun j => e j K n).trans e', fun a => ?_⟩
  simp only [Equiv.trans_apply, Equiv.piCongrRight_apply, he']
  exact Finset.sum_congr rfl fun j _ => he j K n (a j)

theorem bijective_disc : ∀ (q : ℕ) [NeZero q] {ι : Type} [Fintype ι] (L : ι → Cx (ZMod q)) (C : Cx (ZMod q)) (d : ι → ℤ) (ψ : ∀ j, Cocycle (L j) C (d j)) (m₀ : ℤ), (∀ j, (L j).IsStrictlyGE m₀) → C.IsStrictlyGE m₀ → (∀ j n, CategoryTheory.Injective ((L j).X n)) → (∀ n, CategoryTheory.Injective (C.X n)) → (∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → ∀ n : ℤ, Function.Bijective fun a : ∀ j, CohomologyClass ((chains (ZMod q)).obj (sch.obj U)) (L j) (n - d j) => ∑ j, cpost _ (ψ j) (n - d j) n (by omega) (a j)) → ∀ F : PSh, Inv q (disc.obj F) → ∀ n : ℤ, Function.Bijective fun a : ∀ j, CohomologyClass ((chains (ZMod q)).obj (disc.obj F)) (L j) (n - d j) => ∑ j, cpost _ (ψ j) (n - d j) n (by omega) (a j) := by
  intro q _ ι _ L C d ψ m₀ hL hC hLi hCi hU F hF
  obtain ⟨D, f, m, hD, hDi, he⟩ := assemble (ZMod q) L C d ψ m₀ hL hLi
  have hD' : D.IsStrictlyGE (min m m₀) := isStrictlyGE_of_ge D _ _ (min_le_left _ _)
  have hC' : C.IsStrictlyGE (min m m₀) := isStrictlyGE_of_ge C _ _ (min_le_right _ _)
  obtain ⟨hKI, hcone⟩ := GlobalTheory.T.mappingCone_isKInjective_bijective_hypercohomology_iff (ZMod q) f (min m m₀) hD' hC' hDi hCi
  have key : ∀ K : Cx (ZMod q), (∀ n : ℤ, Function.Bijective fun a : ∀ j, CohomologyClass K (L j) (n - d j) =>
      ∑ j, cpost K (ψ j) (n - d j) n (by omega) (a j)) ↔ ∀ n, Subsingleton (CohomologyClass K (mappingCone f) n) := by
    intro K
    rw [← hcone K]
    refine forall_congr' fun n => ?_
    obtain ⟨e, he'⟩ := he K n
    have : (fun a : ∀ j, CohomologyClass K (L j) (n - d j) => ∑ j, cpost K (ψ j) (n - d j) n (by omega) (a j)) =
        (cpush K f n) ∘ e := funext fun a => (he' a).symm
    rw [this]
    exact Function.Bijective.of_comp_iff _ e.bijective
  refine (key _).mpr ?_
  exact GlobalTheory.T.subsingleton_hypercohomology_of_locallyExact_on_support (ZMod q) (disc.obj F) (mappingCone f) (fun U hU' n b hb =>
    GlobalTheory.T.sectionsComplex_exact_etaleLocally_of_no_classes (ZMod q) (mappingCone f) U ((key _).mp (hU U (hF U hU'))) n b hb)

end GlobalTheory.EtC.DiscSupp

end
