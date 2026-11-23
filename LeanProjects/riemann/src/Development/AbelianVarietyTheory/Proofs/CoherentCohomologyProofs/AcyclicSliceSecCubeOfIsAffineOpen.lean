import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SecOnBasicOpenLocalization

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.AbLaw

variable {Y : Scheme.{0}} (M : LB Y)

def SecOnLE {V W : Y.Opens} (_h : W ≤ V) : Type := SecOn M W

namespace SecOnLE

variable {V W W' : Y.Opens}

instance (h : W ≤ V) : AddCommGroup (SecOnLE M h) := inferInstanceAs (AddCommGroup (SecOn M W))

instance (h : W ≤ V) : Module Γ(Y, V) (SecOnLE M h) := Module.compHom (SecOn M W) (rs Y h)

def restrict (h : W ≤ V) (h' : W' ≤ V) (e : W' ≤ W) : SecOnLE M h →ₗ[Γ(Y, V)] SecOnLE M h' where
  toFun s := SecOn.restrict M e s
  map_add' s t := (SecOn.restrict M e).map_add s t
  map_smul' a s := ((SecOn.restrict M e).map_smulₛₗ (rs Y h a) s).trans
    (congrArg (· • SecOn.restrict M e s) (rs_rs _ _ a))

end SecOnLE

def secCubeLE {κ : Type} (V : Finset κ → Y.Opens) (hV : Antitone V) : Cube.{0} κ Γ(Y, V ∅) :=
  Cube.mk (fun s => ModuleCat.of _ (SecOnLE M (hV (Finset.empty_subset s))))
    (fun h => SecOnLE.restrict M _ _ (hV h))
    (fun _ x => SecOn.restrict_self le_rfl x) (fun h h' x => SecOn.restrict_restrict (hV h) (hV h') x)

variable {M}

theorem restrict_torsion (hM : M.IsLB) {V W W' : Y.Opens} (hW : IsAffineOpen W)
    (hW' : IsAffineOpen W') (h : W ≤ V) (e : W' ≤ W) (a : Γ(Y, V))
    (ha : W ⊓ Y.basicOpen a ≤ W') :
    (∀ y : SecOn M W, SecOn.restrict M e y = 0 → ∃ n : ℕ, rs Y h (a ^ n) • y = 0) ∧
      ∀ z : SecOn M W', ∃ (n : ℕ) (y : SecOn M W),
        SecOn.restrict M e y = rs Y (e.trans h) (a ^ n) • z := by
  have e₁ : W ⊓ Y.basicOpen a = Y.basicOpen (rs Y h a) := (Y.basicOpen_res a (homOfLE h).op).symm
  have e₂ : W ⊓ Y.basicOpen a = Y.basicOpen (rs Y (e.trans h) a) :=
    (le_antisymm (le_inf ha inf_le_right) (inf_le_inf_right _ e)).trans
      (Y.basicOpen_res a (homOfLE (e.trans h)).op).symm
  obtain ⟨k₁, c₁⟩ := secOn_basicOpen_localization Y M W _ _ inf_le_left hM hW.isCompact
    hW.isQuasiSeparated e₁
  obtain ⟨k₂, -⟩ := secOn_basicOpen_localization Y M W' _ _ ha hM hW'.isCompact
    hW'.isQuasiSeparated e₂
  refine ⟨fun y hy => ?_, fun z => ?_⟩
  · simp only [map_pow]
    refine k₁ y ?_
    rw [← SecOn.restrict_restrict e ha, hy, map_zero]
  · obtain ⟨n, x, hx⟩ := c₁ (SecOn.restrict M ha z)
    obtain ⟨m, hm⟩ := k₂ (SecOn.restrict M e x - rs Y (e.trans h) a ^ n • z) (by
      rw [map_sub, SecOn.restrict_restrict, hx, map_smulₛₗ, map_pow, rs_rs, rs_rs, sub_self])
    refine ⟨m + n, rs Y h a ^ m • x, ?_⟩
    rw [smul_sub, sub_eq_zero] at hm
    rw [map_smulₛₗ, map_pow, rs_rs, hm, map_pow, pow_add, mul_smul]

theorem secCubeLE_exactAt (hM : M.IsLB) {κ : Type} [LinearOrder κ] [Finite κ]
    (V : Finset κ → Y.Opens) (hV : Antitone V) (ha : ∀ s, IsAffineOpen (V s)) (U : κ → Y.Opens)
    (hU : V ∅ ≤ ⨆ k, U k) (hVU : ∀ k s, V s ⊓ U k ≤ V (insert k s)) (p : ℕ) :
    (cubeComplex (secCubeLE M V hV)).ExactAt p := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton]
  refine subsingleton_of_forall_eq 0 fun x => ?_
  let S : Set Γ(Y, V ∅) := {a | ∃ k, Y.basicOpen a ≤ U k}
  have hS : Ideal.span S = ⊤ := by
    rw [← (ha ∅).self_le_iSup_basicOpen_iff]
    intro y hy
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (hU hy)
    obtain ⟨a, h₁, h₂⟩ := (ha ∅).exists_basicOpen_le (V := U k) ⟨y, hk⟩ hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, k, h₁⟩, h₂⟩
  refine (Submodule.mem_bot _).1 (Submodule.mem_of_span_eq_top_of_smul_pow_mem ⊥ _ hS x ?_)
  rintro ⟨a, k, hk⟩
  have key (s : Finset κ) := restrict_torsion hM (ha s) (ha (insert k s))
    (hV (Finset.empty_subset s)) (hV (Finset.subset_insert k s)) a
    ((inf_le_inf_left _ hk).trans (hVU k s))
  obtain ⟨_, ⟨n, rfl⟩, h⟩ := cubeComplex_exists_smul_homology_eq_zero (secCubeLE M V hV)
    (.powers a) k
    (fun s _ y hy => by
      obtain ⟨n, hn⟩ := (key s).1 y hy
      exact ⟨_, ⟨n, rfl⟩, hn⟩)
    (fun s _ z => by
      obtain ⟨n, y, hn⟩ := (key s).2 z
      exact ⟨_, ⟨n, rfl⟩, y, hn⟩) p x
  exact ⟨n, h⟩

theorem acyclic_slice_secCube_of_isAffineOpen :
    ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) (μ κ : Type) [LinearOrder μ] [LinearOrder κ] [Fintype κ] (D : μ → Y.Opens) (e : κ ↪o μ) (s₀ : Finset μ), M.IsLB → (⨅ i ∈ s₀, D i) ≤ ⨆ k, D (e k) → (∀ t : Finset κ, IsAffineOpen (⨅ i ∈ s₀ ∪ t.map e.toEmbedding, D i)) → (cubeComplex (Cube.slice e s₀ (secCube f M D))).Acyclic := by
  intro R _ Y f M μ κ _ _ _ D e s₀ hM hc ha p
  let V : Finset κ → Y.Opens := fun t => ⨅ i ∈ s₀ ∪ t.map e.toEmbedding, D i
  have hV : Antitone V := fun _ _ h => iInf_le_iInf_of_subset D (Cube.monotone_union_map e s₀ h)
  have H := secCubeLE_exactAt hM V hV ha (fun k => D (e k))
    ((iInf_le_iInf_of_subset D Finset.subset_union_left).trans hc) (fun k s => by
      simp only [V, Finset.map_insert, Finset.union_insert, Finset.iInf_insert]
      exact le_inf inf_le_right inf_le_left)
  have hd (q : ℕ) (x : Cube.Term (Cube.slice e s₀ (secCube f M D)) q) :
      Cube.d (Cube.slice e s₀ (secCube f M D)) q x = Cube.d (secCubeLE M V hV) q x :=
    funext fun t => (Cube.d_apply _ q x t).trans (Cube.d_apply (secCubeLE M V hV) q x t).symm
  cases p with
  | zero =>
    rw [cubeComplex_exactAt_zero_iff']
    exact fun x y h => (cubeComplex_exactAt_zero_iff' _).1 (H 0) ((hd 0 x).symm.trans (h.trans (hd 0 y)))
  | succ p =>
    rw [cubeComplex_exactAt_succ_iff]
    intro x
    refine ⟨fun hx => ?_, by rintro ⟨y, rfl⟩; exact Cube.d_d _ p y⟩
    obtain ⟨y, hy⟩ := ((cubeComplex_exactAt_succ_iff _ p).1 (H (p + 1)) x).1 ((hd _ x).symm.trans hx)
    exact ⟨y, (hd p y).trans hy⟩

end GlobalTheory.AbLaw
