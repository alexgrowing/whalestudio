import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.UnitLocus

theorem mem_basicOpen_iff {X : Scheme.{0}} {k : Type} [Field k] (g : Sp k ⟶ X) (s : Γ(X, ⊤)) :
    g (default : PrimeSpectrum k) ∈ X.basicOpen s ↔ IsUnit (g.appTop.hom s) := by
  have p : g ⁻¹ᵁ X.basicOpen s = (Sp k).basicOpen (g.appTop.hom s) := Scheme.preimage_basicOpen g s
  constructor
  · intro H
    refine RingedSpace.isUnit_of_isUnit_germ (Sp k).toRingedSpace ⊤ _ fun y hy => ?_
    have : y ∈ (Sp k).basicOpen (g.appTop.hom s) := by
      rw [← p]
      have e : y = (default : PrimeSpectrum k) := Subsingleton.elim (α := PrimeSpectrum k) _ _
      rw [e]
      exact H
    exact ((Sp k).mem_basicOpen _ y hy).1 this
  · intro H
    have : (default : PrimeSpectrum k) ∈ g ⁻¹ᵁ X.basicOpen s := by
      rw [p, Scheme.basicOpen_of_isUnit _ H]; trivial
    exact this

theorem exists_geometricPoint {X : Scheme.{0}} (x : X) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (g : Sp k ⟶ X), g (default : PrimeSpectrum k) = x := by
  refine ⟨AlgebraicClosure (X.residueField x), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) (AlgebraicClosure (X.residueField x)))) ≫
      X.fromSpecResidueField x, ?_⟩
  exact Scheme.fromSpecResidueField_apply x _

theorem avg_cases {R : Type} [CommRing R] [IsDomain R] {n : ℕ} {m w : R} (hm : m * n = 1) (hw : w ^ n = 1) :
    (w = 1 → m * ∑ i ∈ Finset.range n, w ^ i = 1) ∧ (w ≠ 1 → m * ∑ i ∈ Finset.range n, w ^ i = 0) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa [h] using hm
  · have h₀ : (∑ i ∈ Finset.range n, w ^ i) * (w - 1) = 0 := by rw [geom_sum_mul, hw, sub_self]
    rw [(mul_eq_zero.1 h₀).resolve_right (sub_ne_zero.2 h), mul_zero]

end GlobalTheory.UnitLocus

namespace GlobalTheory

open UnitLocus in

theorem loc_units_eq :
    ∀ (X : Scheme.{0}) (N : ℕ) (c₀ u : Γ(X, ⊤)ˣ), IsUnit (N : Γ(X, ⊤)) → c₀ ^ N = 1 → (∀ (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ X), Units.map g.appTop.hom.toMonoidHom u ^ N = 1) → GlobalTheory.HkClopen.Loc (S := X) (fun (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ X) => Units.map g.appTop.hom.toMonoidHom c₀ = Units.map g.appTop.hom.toMonoidHom u) := by
  intro X N c₀ u hN hc hu
  obtain ⟨m, hm⟩ := hN.exists_left_inv
  let w : Γ(X, ⊤) := (c₀ * u⁻¹).val
  let e : Γ(X, ⊤) := m * ∑ i ∈ Finset.range N, w ^ i
  have key : ∀ (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ X),
      (g (default : PrimeSpectrum k) ∈ X.basicOpen e ↔
        Units.map g.appTop.hom.toMonoidHom c₀ = Units.map g.appTop.hom.toMonoidHom u) ∧
      (g (default : PrimeSpectrum k) ∈ X.basicOpen (1 - e) ↔
        ¬ Units.map g.appTop.hom.toMonoidHom c₀ = Units.map g.appTop.hom.toMonoidHom u) := by
    intro k _ _ g
    have : IsDomain Γ(Sp k, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain k
    have hval : g.appTop.hom w =
        (Units.map g.appTop.hom.toMonoidHom c₀ * (Units.map g.appTop.hom.toMonoidHom u)⁻¹).val := by
      rw [← map_inv, ← map_mul]; rfl
    have h1 : Units.map g.appTop.hom.toMonoidHom c₀ = Units.map g.appTop.hom.toMonoidHom u ↔
        g.appTop.hom w = 1 := by
      rw [hval, Units.val_eq_one, mul_inv_eq_one]
    have hw : g.appTop.hom w ^ N = 1 := by
      rw [hval, ← Units.val_pow_eq_pow_val, mul_pow, inv_pow, hu, ← map_pow, hc, map_one, inv_one,
        _root_.mul_one, Units.val_one]
    have hm' : g.appTop.hom m * N = 1 := by
      have := congrArg g.appTop.hom hm
      rwa [map_mul, map_natCast, map_one] at this
    have he : g.appTop.hom e = g.appTop.hom m * ∑ i ∈ Finset.range N, g.appTop.hom w ^ i := by
      simp only [e, map_mul, map_sum, map_pow]
    obtain ⟨a, b⟩ := avg_cases hm' hw
    rw [mem_basicOpen_iff, mem_basicOpen_iff, h1, map_sub, map_one, he]
    by_cases h : g.appTop.hom w = 1
    · rw [a h]; simp [h]
    · rw [b h]; simp [h]
  refine ⟨X.basicOpen e, ⟨?_, (X.basicOpen e).isOpen⟩, fun k _ _ g => (key k g).1⟩
  have : (X.basicOpen e : Set X) = (X.basicOpen (1 - e) : Set X)ᶜ := by
    ext x
    obtain ⟨k, _, _, g, rfl⟩ := exists_geometricPoint x
    exact (key k g).1.trans (not_not.symm.trans (not_congr (key k g).2.symm))
  rw [this]
  exact (X.basicOpen (1 - e)).isOpen.isClosed_compl

end GlobalTheory
