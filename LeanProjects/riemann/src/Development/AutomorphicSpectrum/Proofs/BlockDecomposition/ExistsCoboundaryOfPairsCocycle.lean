import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHomLocBijectiveGrSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfMem
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHomogeneousFamilySaturating
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexGradedModuleExactAtOfLargeDegree
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsGradedMapGlueD
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
open GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

theorem cube_res_injective_of_eq {ι : Type} {A : Type} [CommRing A] (C : Cube.{0} ι A)
    {s t : Finset ι} (e : s = t) (h : s ⊆ t) : Function.Injective (Cube.res C h) := by
  subst e
  intro x y hxy
  rwa [GlobalTheory.Cube.res_self, GlobalTheory.Cube.res_self] at hxy

theorem cube_pairs_diag {ι : Type} [LinearOrder ι] {A : Type} [CommRing A] (C : Cube.{0} ι A)
    (c : ∀ i j : ι, C.obj {i, j})
    (hc : ∀ i j k, Cube.res C (sub_triple_ij i j k) (c i j) +
      Cube.res C (sub_triple_jk i j k) (c j k) = Cube.res C (sub_triple_ik i j k) (c i k))
    (i : ι) : c i i = 0 := by
  have hx := hc i i i
  rw [add_eq_left] at hx
  apply GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.cube_res_injective_of_eq C (s := {i, i}) (t := {i, i, i}) (by ext; simp)
    (GlobalTheory.CompanionTheory.FormalAlg.Lift.sub_triple_ij i i i)
  rw [map_zero]
  exact hx

theorem exists_coboundary_of_pairs_cocycle : ∀ (ι : Type) [LinearOrder ι] (A : Type) [CommRing A] (C : Cube.{0} ι A), Function.Exact (Cube.d C 1) (Cube.d C 2) → ∀ c : ∀ i j : ι, C.obj {i, j}, (∀ i j k, Cube.res C (sub_triple_ij i j k) (c i j) + Cube.res C (sub_triple_jk i j k) (c j k) = Cube.res C (sub_triple_ik i j k) (c i k)) → ∃ b : ∀ i : ι, C.obj {i}, ∀ i j, c i j = Cube.res C (sub_pair_left i j) (b i) - Cube.res C (sub_pair_right i j) (b j) := by
  intro ι _ A _ C hex c hc
  have hne : ∀ s : Finset ι, s.card = 2 → s.Nonempty := fun s hs => Finset.card_pos.1 (by omega)
  have hmm : ∀ (s : Finset ι) (hs : s.card = 2), ({s.min' (hne s hs), s.max' (hne s hs)} : Finset ι) ⊆ s :=
    fun s hs => Finset.insert_subset (Finset.min'_mem _ _)
      (Finset.singleton_subset_iff.2 (Finset.max'_mem _ _))
  have htr : ∀ {a b a' b' : ι} (ha : a = a') (hb : b = b') (h : ({a, b} : Finset ι) ⊆ {a', b'}),
      GlobalTheory.Cube.res C h (c a b) = c a' b' := by
    intro a b a' b' ha hb h
    subst ha hb
    exact GlobalTheory.Cube.res_self C h _
  let y : GlobalTheory.Cube.Term C 2 := fun s =>
    -GlobalTheory.Cube.res C (hmm s.1 s.2) (c (s.1.min' (hne s.1 s.2)) (s.1.max' (hne s.1 s.2)))
  have hy : ∀ {i j : ι} (hij : i < j) (hs : ({i, j} : Finset ι).card = 2), y ⟨{i, j}, hs⟩ = -c i j := by
    intro i j hij hs
    have hmin : ({i, j} : Finset ι).min' (hne _ hs) = i :=
      le_antisymm (Finset.min'_le _ _ (by simp)) (Finset.le_min' _ _ _ (by simp [hij.le]))
    have hmax : ({i, j} : Finset ι).max' (hne _ hs) = j :=
      le_antisymm (Finset.max'_le _ _ _ (by simp [hij.le])) (Finset.le_max' _ _ (by simp))
    exact congrArg Neg.neg (htr hmin hmax _)
  have hy0 : GlobalTheory.Cube.d C 2 y = 0 := by
    funext ⟨t, ht⟩
    show _ = 0
    obtain ⟨i, j, k, hij, hjk, rfl⟩ := GlobalTheory.AbLaw.CechOne.exists_triple (t := t) ht
    rw [GlobalTheory.AbLaw.CechOne.d_two_apply_triple C y hij hjk ht, hy hij, hy hjk, hy (hij.trans hjk)]
    simp only [map_neg]
    rw [← hc i j k]
    abel
  obtain ⟨x, hx⟩ := (hex y).1 hy0
  have hlt : ∀ i j, i < j → c i j =
      GlobalTheory.Cube.res C (GlobalTheory.CompanionTheory.FormalAlg.Lift.sub_pair_left i j) (x ⟨{i}, Finset.card_singleton i⟩) -
        GlobalTheory.Cube.res C (GlobalTheory.CompanionTheory.FormalAlg.Lift.sub_pair_right i j) (x ⟨{j}, Finset.card_singleton j⟩) := by
    intro i j hij
    have h1 := GlobalTheory.Cube.d_one_apply_pair C x hij
    rw [hx, hy hij] at h1
    rw [← neg_sub, ← h1, neg_neg]
  refine ⟨fun i => x ⟨{i}, Finset.card_singleton i⟩, fun i j => ?_⟩
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact hlt i j hij
  · rw [GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.cube_pairs_diag C c hc i, sub_self]
  · apply GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.cube_res_injective_of_eq C (s := {i, j}) (t := {i, j, i})
      (by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
      (GlobalTheory.CompanionTheory.FormalAlg.Lift.sub_triple_ij i j i)
    have h := hc i j i
    rw [GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.cube_pairs_diag C c hc i, map_zero] at h
    rw [eq_neg_of_add_eq_zero_left h, hlt j i hji]
    simp only [map_sub, neg_sub, GlobalTheory.Cube.res_res]

end GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue
