import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPullbackEqZeroIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorRelationLatticeNonzerodivisorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleSectionsFiniteProjectiveStatement
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.GroupBplus (AffOp)
open GlobalTheory.RingChain (RChain mv baseOf Qt IsFrobLin)
open GlobalTheory.ChainPts.PullHT (pullA)
open GlobalTheory.PerfdLat (piMap)
open scoped TensorProduct Pointwise
open GlobalTheory.ChainPts
open GlobalTheory.ChainDesc

set_option autoImplicit false

namespace GlobalTheory.ChainDesc.KerJ

theorem piMap_mem_baseOf {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R) {h : ℕ} {π : A} {x : Fin h → A}
    (hx : x ∈ baseOf π h) : piMap φ (Fin h) x ∈ baseOf (φ π) h := by
  obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
  refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨piMap φ (Fin h) y, trivial, ?_⟩
  rw [LinearMap.map_smulₛₗ]

theorem span_eq_baseOf {A R P : Type} [CommRing A] [CommRing R] (φ : A →+* R) {h : ℕ} {π : A} (κ : P → (Fin h → A))
    (S : P → Prop) (hS : ∀ x, S x ↔ κ x ∈ baseOf π h) (hκ : ∀ y ∈ baseOf π h, ∃ x, κ x = y) :
    Submodule.span R {z | ∃ x₀ : P, S x₀ ∧ z = piMap φ (Fin h) (κ x₀)} = baseOf (φ π) h := by
  classical
  refine le_antisymm (Submodule.span_le.2 ?_) fun z hz => ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact piMap_mem_baseOf φ ((hS x).1 hx)
  · obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hz
    rw [pi_eq_sum_univ' y, Finset.smul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [smul_comm]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    have hm : π • (fun j => if j = i then (1 : A) else 0) ∈ baseOf π h :=
      (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨_, trivial, rfl⟩
    obtain ⟨x, hx⟩ := hκ _ hm
    refine ⟨x, (hS x).2 (hx ▸ hm), ?_⟩
    rw [hx, LinearMap.map_smulₛₗ]
    congr 1
    funext j
    change _ = φ (if j = i then (1 : A) else 0)
    split_ifs with hj <;> simp [hj]

theorem mem_kerJ_iff {A R : Type} [CommRing A] [CommRing R] {p h o : ℕ} {π : A} {γ : ℕ → A} {Lie Om : Type}
    [AddCommGroup Lie] [Module A Lie] [AddCommGroup Om] [Module A Om] (C : RChain p A h o π γ Lie Om) (φ : A →+* R) {r : ℕ}
    (y : Fin r → Lie) (x : Fin r → C.L 0) (hx : ∀ l, C.j (y l) = Submodule.Quotient.mk (x l)) (c : Fin r → R) :
    c ∈ C.kerJ φ y ↔ ∑ l, c l • piMap φ _ (x l).1 ∈ baseOf (φ π) h := by
  refine ⟨fun ⟨x', hx', hc⟩ => ?_, fun hc => ⟨x, hx, hc⟩⟩
  have hd : ∑ l, c l • piMap φ _ (x l).1 - ∑ l, c l • piMap φ _ (x' l).1 ∈ baseOf (φ π) h := by
    rw [← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun l _ => ?_
    rw [← smul_sub, ← map_sub]
    exact Submodule.smul_mem _ _ (piMap_mem_baseOf φ
      ((Submodule.Quotient.eq ((baseOf π h).comap (C.L 0).subtype)).1 ((hx l).symm.trans (hx' l))))
  simpa using Submodule.add_mem _ hd hc

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) (B B' : GlobalTheory.Vert.Model O) (Λ : Type) [CommRing Λ] (h o : ℕ) (Lie Om : AM B Λ) (π : Γ(B.X, ⊤)) (γ : ℕ → Γ(B.X, ⊤)) (M : Λ →+* Matrix (Fin h) (Fin h) ℤ) (C : ChainsBp p h o Lie Om π γ) (f : GlobalTheory.Vert.Model.Hom B' B) (g : ∀ U : AffOp B.X, Γ(B'.X, f.f ⁻¹ᵁ U.1) →+* U.Bp) (E : ℕ → B'.X.Modules) (ι : ∀ n, E n ⟶ freeModule B'.X (Fin h)) (Q : AM B' Λ) (t : E 0 ⟶ Q.V) (j : (pullA f.f).obj Lie ⟶ Q) (k : IsCov f g), IsLatOf C f g ι → IsQuot M (ι 0) (baseOn h (f.f.appTop π)) Q t → ∀ U : AffOp B.X, JUp C f g U (ι 0) t j.hom → ∀ (R : Type) [CommRing R] (φ : U.Bp →+* R), φ (cstBp U π) ∈ nonZeroDivisors R → ∀ (hw : ⊤ ≤ (spMap (φ.comp (g U)) ≫ (k.isAffineOpen U).fromSpec) ⁻¹ᵁ f.f ⁻¹ᵁ U.1) (r : ℕ) (e : Fin r → Γ(Lie.V, U.1)), kerAt (spMap (φ.comp (g U)) ≫ (k.isAffineOpen U).fromSpec) j.hom hw (fun l => pullbackSections f.f Lie.V le_rfl (e l)) = (C U).kerJ φ fun l => 1 ⊗ₜ e l := by
  intro O _ _ _ p B B' Λ _ h o Lie Om π γ M C f g E ι Q t j k hL hQ U hJ R _ φ hπ hw r e
  haveI := hQ.1
  haveI := (hL 0).2.1
  have hV := k.isAffineOpen U
  letI : Algebra Γ(B'.X, f.f ⁻¹ᵁ U.1) R := (φ.comp (g U)).toAlgebra
  haveI := (GlobalTheory.T.vector_bundle_sections_finite_projective _ _ _ (hL 0).1 _ hV).2
  obtain ⟨h1, h2, -⟩ := hQ.2 _ hV
  choose x y hy hj ht using fun l => hJ (e l)
  have hb : baseOf (resG B'.X le_top (f.f.appTop π)) h ≤ LinearMap.range (crd (ι 0) (f.f ⁻¹ᵁ U.1)) := fun z hz => by
    have h3 := piMap_mem_baseOf (g U) hz
    rw [k.map_cst] at h3
    have h4 : z ∈ latOf (ι 0) (f.f ⁻¹ᵁ U.1) := by
      rw [((hL 0).2.2 U).1]
      exact (C U).base_le _ h3
    exact h4
  have hc : algebraMap Γ(B'.X, f.f ⁻¹ᵁ U.1) R (resG B'.X le_top (f.f.appTop π)) = φ (cstBp U π) :=
    congrArg φ (k.map_cst U π)
  ext c
  refine ((KerTens.main B'.X R _ Q.V j.hom _ r _ c).1 (k.isAffineOpen U) hw).trans ?_
  rw [mem_kerJ_iff (C U) φ _ y hj]
  have key := GlobalTheory.T.tensor_relation_lattice_nonzerodivisor _ R h _ _ (crd (ι 0) (f.f ⁻¹ᵁ U.1)) (appLinear t _) _ (crd_injective _ _) hb (hc ▸ hπ) h1 r x c
  rw [span_eq_baseOf _ (crd (ι 0) (f.f ⁻¹ᵁ U.1)) (fun x => appLinear t (f.f ⁻¹ᵁ U.1) x = 0) h2 hb, hc] at key
  refine Iff.trans (Iff.of_eq ?_) (key.trans (Iff.of_eq ?_))
  · congr 1
    exact Finset.sum_congr rfl fun l _ => congrArg _ (ht l)
  · congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hy l]
    rfl

end GlobalTheory.ChainDesc.KerJ
