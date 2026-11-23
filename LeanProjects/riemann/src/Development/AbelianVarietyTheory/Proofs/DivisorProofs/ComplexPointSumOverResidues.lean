import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory

noncomputable def cxPtsFibreEquiv (X : Scheme.{0}) (x : X) :
    {y : Sp ℂ ⟶ X // y (IsLocalRing.closedPoint ℂ) = x} ≃ (X.residueField x →+* ℂ) :=
  ((Equiv.subtypeEquiv (Scheme.SpecToEquivOfField ℂ X) fun _ => Iff.rfl).trans
    (Equiv.sigmaSubtype (β := fun z : X => X.residueField z ⟶ CommRingCat.of ℂ) x)).trans
    ⟨fun f => f.hom, fun f => CommRingCat.ofHom f, fun _ => rfl, fun _ => rfl⟩

theorem charZero_residueField_pt (X : Scheme.{0}) (y : Sp ℂ ⟶ X) :
    CharZero (X.residueField (y (IsLocalRing.closedPoint ℂ))) :=
  RingHom.charZero ((Scheme.SpecToEquivOfField ℂ X y).2.hom)

theorem finsum_cxPts_eq_sum_card (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    [Finite (k →+* ℂ)] (S : Finset X) (m : X → ℝ)
    (hS : ∀ x ∈ S, Finite (X.residueField x →+* ℂ))
    (hm : ∀ x : X, CharZero (X.residueField x) → m x ≠ 0 → x ∈ S) :
    ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts p σ, m y.pt =
      ∑ x ∈ S, m x * (Nat.card (X.residueField x →+* ℂ) : ℝ) := by
  classical
  let pt : (Sp ℂ ⟶ X) → X := fun y => y (IsLocalRing.closedPoint ℂ)
  let g : (Sp ℂ ⟶ X) → ℝ := fun y => m (pt y)
  let F : X → Set (Sp ℂ ⟶ X) := fun x => {y | pt y = x}
  let A : (k →+* ℂ) → Set (Sp ℂ ⟶ X) := fun σ => {y | y ≫ p = spMap σ}
  have hF : ∀ x ∈ S, (F x).Finite := fun x hx => by
    have := hS x hx
    have : Finite (F x) := Finite.of_equiv _ (cxPtsFibreEquiv X x).symm
    exact Set.toFinite _
  have hsupp : Function.support g ⊆ ⋃ x ∈ (S : Set X), F x := fun y hy =>
    Set.mem_biUnion (hm _ (charZero_residueField_pt X y) hy) rfl
  have hsf : (Function.support g).Finite :=
    (S.finite_toSet.biUnion fun x hx => hF x hx).subset hsupp
  have hdisj : (S : Set X).PairwiseDisjoint F := fun a _ b _ hab =>
    Set.disjoint_left.2 fun y h1 h2 => hab (h1.symm.trans h2)
  have h1 : ∑ᶠ y, g y = ∑ x ∈ S, m x * (Nat.card (X.residueField x →+* ℂ) : ℝ) := by
    rw [← finsum_mem_support, ← Set.inter_eq_right.2 hsupp, finsum_mem_inter_support,
      finsum_mem_biUnion hdisj S.finite_toSet hF, finsum_mem_coe_finset]
    refine Finset.sum_congr rfl fun x hx => ?_
    have e : ∑ᶠ y ∈ F x, g y = ∑ᶠ y ∈ F x, m x := finsum_mem_congr rfl fun y hy => congrArg m hy
    have hc : Nat.card (F x) = Nat.card (X.residueField x →+* ℂ) := Nat.card_congr (cxPtsFibreEquiv X x)
    rw [e, finsum_mem_eq_finite_toFinset_sum _ (hF x hx), Finset.sum_const, nsmul_eq_mul, mul_comm,
      ← Set.ncard_eq_toFinset_card _ (hF x hx), ← Nat.card_coe_set_eq, hc]
  have h2 : ∀ σ : k →+* ℂ, ∑ᶠ y : CxPts p σ, m y.pt = ∑ᶠ y ∈ A σ ∩ Function.support g, g y :=
    fun σ => (finsum_set_coe_eq_finsum_mem (f := g) (A σ)).trans (finsum_mem_inter_support g (A σ)).symm
  have hdisjA : Pairwise (Function.onFun Disjoint fun σ => A σ ∩ Function.support g) := fun σ τ hστ =>
    Set.disjoint_left.2 fun y h1 h2 => hστ (by
      have e : spMap σ = spMap τ := h1.1.symm.trans h2.1
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective e))
  have hU : ⋃ σ, A σ ∩ Function.support g = Function.support g := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    refine ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨(Spec.preimage (y ≫ p)).hom, ?_, h⟩⟩
    show y ≫ p = Spec.map (CommRingCat.ofHom _)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  rw [finsum_congr h2, ← finsum_mem_iUnion hdisjA fun σ => hsf.subset Set.inter_subset_right, hU,
    finsum_mem_support, h1]

end GlobalTheory
