import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
open CategoryTheory AlgebraicGeometry GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.SecPowLoc

theorem fnOf_map {X : Scheme.{0}} [IsIntegral X] {U V : X.Opens} (i : V ⟶ U)
    (h : genericPoint X ∈ V) (a : Γ(X, U)) :
    fnOf V h (X.presheaf.map i.op a) = fnOf U (i.le h) a :=
  X.presheaf.germ_res_apply i _ h a

theorem exists_pow_regularAt_on {X : Scheme.{0}} [IsIntegral X] (D : CartierDiv X)
    (f : X.functionField) (t : Γ(X, ⊤)) (hf : ∀ z ∈ X.basicOpen t, D.RegularAt z f)
    (W : X.Opens) (hW : IsAffineOpen W) (g : X.functionFieldˣ) (hg : ∀ z ∈ W, D.IsEqn z g)
    {y : X} (hy : y ∈ W) (ht : genericPoint X ∈ X.basicOpen t) :
    ∃ n : ℕ, ∀ z ∈ W, D.RegularAt z (t ^ n • f) := by
  set t' : Γ(X, W) := X.presheaf.map (homOfLE le_top).op t
  have hB : X.basicOpen t' = W ⊓ X.basicOpen t := X.basicOpen_res t _
  have hgen : genericPoint X ∈ X.basicOpen t' := hB ▸ memInf (gen_mem hy) ht
  obtain ⟨b, hb⟩ := exists_fnOf_eq (f := f * (g : X.functionField)) hgen fun z hz => by
    rw [hB] at hz
    exact (hg z hz.1).regularAt_iff.1 (hf z hz.2)
  obtain ⟨n, a, ha⟩ := exists_eq_pow_mul_of_isAffineOpen X W hW t' b
  have key : fnOf W (gen_mem hy) a = fnOf ⊤ trivial t ^ n * (f * (g : X.functionField)) := by
    have e := congrArg (fnOf _ hgen) ha
    rw [map_mul, map_pow, hb] at e
    erw [fnOf_map, fnOf_map, fnOf_map] at e
    exact e
  refine ⟨n, fun z hz => (hg z hz).regularAt_iff.2 ?_⟩
  rw [Algebra.smul_def, algebraMap_top, map_pow, mul_assoc, ← key]
  exact regAt_fnOf hz _ a

end GlobalTheory.Cartier.SecPowLoc

namespace GlobalTheory.Cartier

open SecPowLoc in

theorem exists_smul_mem_sections_of_regAt : ∀ (X : Scheme.{0}) [IsIntegral X] [IsAffine X] (D : CartierDiv X)
    (x : X) (g : X.functionFieldˣ), D.IsEqn x g → ∀ f : X.functionField, RegAt x (f * g) →
    ∃ s : Γ(X, ⊤), x ∈ X.basicOpen s ∧ s • f ∈ D.sections := by
  intro X _ _ D x g hg f hf
  obtain ⟨U, hxU, hU⟩ := hg.exists_nhds
  obtain ⟨U', hxU', a, ha⟩ := hf.exists_fnOf
  obtain ⟨_, ⟨t, rfl⟩, hxt, htle⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.1 (isBasis_basicOpen X) (show x ∈ U ⊓ U' from ⟨hxU, hxU'⟩)
  have hft : ∀ z ∈ X.basicOpen t, D.RegularAt z f := fun z hz => by
    have h1 := regAt_fnOf (htle hz).2 (gen_mem hxU') a
    rw [ha] at h1
    exact (hU z (htle hz).1).regularAt_iff.2 h1
  have hgt : genericPoint X ∈ X.basicOpen t := gen_mem hxt
  have loc : ∀ y : X, ∃ W : X.Opens, y ∈ W ∧ ∃ n : ℕ, ∀ z ∈ W, D.RegularAt z (t ^ n • f) := by
    intro y
    obtain ⟨V, hyV, g', hg'⟩ := D.exists_isEqn_nhds y
    obtain ⟨W, hW, hyW, hWV⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hyV
    exact ⟨W, hyW, exists_pow_regularAt_on D f t hft W hW g' (fun z hz => hg' z (hWV hz)) hyW hgt⟩
  choose W hyW n hn using loc
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun y => (W y : Set X))
    (fun y => (W y).isOpen) (fun y _ => Set.mem_iUnion.2 ⟨y, hyW y⟩)
  refine ⟨t ^ (T.sup n + 1), ?_, mem_sections.2 fun z => ?_⟩
  · rw [X.basicOpen_pow t (Nat.succ_pos _)]
    exact hxt
  · obtain ⟨y, hyT, hz⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ z))
    have hle : n y ≤ T.sup n + 1 := (Finset.le_sup hyT).trans (Nat.le_succ _)
    rw [← Nat.sub_add_cancel hle, pow_add, mul_smul]
    have h2 := (hn y z hz).regAt_mul (regAt_fnOf (U := ⊤) trivial trivial (t ^ (T.sup n + 1 - n y)))
    rwa [← algebraMap_top, ← Algebra.smul_def] at h2

end GlobalTheory.Cartier
