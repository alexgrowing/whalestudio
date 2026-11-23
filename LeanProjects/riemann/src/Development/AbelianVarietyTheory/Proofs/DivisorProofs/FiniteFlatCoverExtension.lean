import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportPullbackEqPreimageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuleLengthDisjointSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatQuasicoherentLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatAffineAvoidingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMapClosedFibreStatement
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.Twist

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ProjBase

theorem chiLen_eq_length_sections {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] (R : Type) [CommRing R]
    [Algebra R Γ(X, ⊤)] (F : X.Modules) [IsFiniteQC F] (h : suppDim F ≤ 0) :
    chiLen R F = (Module.length R (sectionsOn F ⊤)).toNat := by
  rw [chiLen_eq_sum_range R 1 fun n hn => subsingleton_coh_of_suppDim_le_zero h (by omega)]
  simp [(cohOn.zeroEquiv R F ⊤).length_eq]

theorem topDim_le_zero_of_finite_closed {T : Type} [TopologicalSpace T] {s : Set T} (hs : s.Finite)
    (hc : ∀ x ∈ s, IsClosed ({x} : Set T)) : topologicalKrullDim s ≤ 0 := by
  have : Finite s := hs.to_subtype
  have : T1Space s := ⟨fun x => by
    simpa [← Set.image_singleton, Set.preimage_image_eq _ Subtype.val_injective] using
      (hc x.1 x.2).preimage (continuous_subtype_val (p := (· ∈ s)))⟩
  exact topologicalKrullDim_zero_of_discreteTopology s

theorem chiLen_pullback_eq_mul : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B) (U : B.X.Opens) (n : ℕ), (∀ x ∈ U, ∃ V : B.X.Opens, x ∈ V ∧ V ≤ U ∧ IsAffineOpen V ∧ IsAffineOpen (f.f ⁻¹ᵁ V) ∧ (letI := (f.f.app V).hom.toAlgebra; Module.Free Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V) ∧ Module.Finite Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V) ∧ Module.finrank Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V) = n)) → ∀ (G : B.X.Modules) [IsFiniteQC G], B.IsVertical G → suppDim G ≤ 0 → support G ⊆ (U : Set B.X) → chiLen O ((Scheme.Modules.pullback f.f).obj G) = n * chiLen O G := by
  intro O _ _ _ B B' f U n hU G _ _ hdim hsub
  classical
  have hfin : (support G).Finite := finite_support_of_suppDim_le_zero hdim
  have hcl : ∀ x ∈ support G, IsClosed ({x} : Set B.X) := fun x hx =>
    isClosed_singleton_of_suppDim_le_zero hdim hx
  have key : ∀ x : support G, ∃ W : B.X.Opens, x.1 ∈ W ∧ (∀ y ∈ support G \ {x.1}, y ∉ W) ∧
      IsAffineOpen W ∧ IsAffineOpen (f.f ⁻¹ᵁ W) ∧
      (letI := (f.f.app W).hom.toAlgebra; Module.Free Γ(B.X, W) Γ(B'.X, f.f ⁻¹ᵁ W) ∧
        Module.Finite Γ(B.X, W) Γ(B'.X, f.f ⁻¹ᵁ W) ∧ Module.finrank Γ(B.X, W) Γ(B'.X, f.f ⁻¹ᵁ W) = n) := by
    intro x
    obtain ⟨V, hxV, -, hVa, hV'a, hfree⟩ := hU x.1 (hsub x.2)
    obtain ⟨W, hxW, -, hWT, hWa, hW'a, hWfree⟩ := GlobalTheory.T.finite_flat_affine_avoiding f.f n V hVa hV'a hfree x.1 hxV
      (support G \ {x.1}) (hfin.subset Set.diff_subset) (fun y hy => hcl y hy.1) (by simp)
    exact ⟨W, hxW, hWT, hWa, hW'a, hWfree⟩
  choose W hxW hWS hWa hW'a hWfree using key
  letI : Fintype (support G) := hfin.fintype
  have hsupp' : support ((Scheme.Modules.pullback f.f).obj G) = f.f.base ⁻¹' support G :=
    GlobalTheory.T.support_pullback_eq_preimage f.f G
  have hmem : ∀ x : support G, ∀ y ∈ support G, y ∈ W x → y = x.1 := fun x y hy hyW => by
    by_contra h; exact hWS x y ⟨hy, h⟩ hyW
  have hpts : ∀ y ∈ support ((Scheme.Modules.pullback f.f).obj G), IsClosed ({y} : Set B'.X) := by
    intro y hy
    rw [hsupp'] at hy
    exact (GlobalTheory.T.finite_map_closed_fibre f.f (W ⟨_, hy⟩) (hWa _) (hW'a _) (hWfree _).2.1 _ (hxW _) (hcl _ hy)).2 y rfl
  have hfin' : (support ((Scheme.Modules.pullback f.f).obj G)).Finite := by
    rw [hsupp']
    refine (Set.Finite.biUnion (t := fun x => f.f.base ⁻¹' {x}) hfin fun x hx => (GlobalTheory.T.finite_map_closed_fibre f.f (W ⟨x, hx⟩) (hWa _) (hW'a _)
      (hWfree _).2.1 _ (hxW _) (hcl _ hx)).1).subset fun y hy => ?_
    exact Set.mem_biUnion hy rfl
  have hdim' : suppDim ((Scheme.Modules.pullback f.f).obj G) ≤ 0 :=
    topDim_le_zero_of_finite_closed hfin' hpts
  have hO : ∀ r : O, f.f.appTop (algebraMap O Γ(B.X, ⊤) r) = algebraMap O Γ(B'.X, ⊤) r :=
    GlobalTheory.Vert.Model.appTop_const f.comp_str
  rw [chiLen_eq_length_sections O _ hdim, chiLen_eq_length_sections O _ hdim',
    GlobalTheory.T.module_length_disjoint_support G O W (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxW _⟩)
      (fun i j hij y hy hyi hyj => hij (Subtype.ext ((hmem i y hy hyi).symm.trans (hmem j y hy hyj)))),
    GlobalTheory.T.module_length_disjoint_support _ O (fun x => f.f ⁻¹ᵁ W x) ?_ ?_]
  · simp_rw [GlobalTheory.T.finite_flat_quasicoherent_local O f.f hO _ n (hWa _) (hW'a _) (hWfree _) G]
    rw [← Finset.mul_sum, ENat.toNat_mul]
    simp
  · intro y hy
    rw [hsupp'] at hy
    exact Set.mem_iUnion.2 ⟨⟨_, hy⟩, hxW _⟩
  · intro i j hij y hy hyi hyj
    rw [hsupp'] at hy
    exact hij (Subtype.ext ((hmem i _ hy hyi).symm.trans (hmem j _ hy hyj)))

end GlobalTheory.ProjBase
