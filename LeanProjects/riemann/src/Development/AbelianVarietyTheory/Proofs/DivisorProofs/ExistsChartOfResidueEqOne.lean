import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff.MemLoc

section Gen

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {N : ℕ}

theorem torsMap_comp {B C D : Type} [CommRing B] [Algebra R B] [CommRing C] [Algebra R C] [CommRing D]
    [Algebra R D] (φ : B →ₐ[R] C) (ψ : C →ₐ[R] D) (z : Tors G N B) :
    torsMap ψ (torsMap φ z) = torsMap (ψ.comp φ) z := by
  apply Subtype.ext
  show spOver ψ ≫ (spOver φ ≫ z.1) = spOver (ψ.comp φ) ≫ z.1
  rw [← Category.assoc, spOver_comp]

theorem torsMap_mul {B C : Type} [CommRing B] [Algebra R B] [CommRing C] [Algebra R C] (φ : B →ₐ[R] C)
    (x y : Tors G N B) : torsMap φ (x * y) = torsMap φ x * torsMap φ y :=
  Subtype.ext (MonObj.comp_mul _ _ _)

theorem torsMap_one {B C : Type} [CommRing B] [Algebra R B] [CommRing C] [Algebra R C] (φ : B →ₐ[R] C) :
    torsMap φ (1 : Tors G N B) = 1 :=
  Subtype.ext (MonObj.comp_one _)

theorem torsMap_inv {B C : Type} [CommRing B] [Algebra R B] [CommRing C] [Algebra R C] (φ : B →ₐ[R] C)
    (x : Tors G N B) : torsMap φ x⁻¹ = (torsMap φ x)⁻¹ :=
  map_inv ({ toFun := torsMap φ, map_one' := torsMap_one φ, map_mul' := torsMap_mul φ } :
    Tors G N B →* Tors G N C) x

theorem range_subset_of_residue (W : G.left.Opens) (A : Type) [CommRing A] [IsLocalRing A] [Algebra R A]
    (z : Tors G N A)
    (h : Set.range (torsMap (IsScalarTower.toAlgHom R A (IsLocalRing.ResidueField A)) z).1.left ⊆ W) :
    Set.range z.1.left ⊆ W := by
  rintro _ ⟨x, rfl⟩
  have hx : (x : PrimeSpectrum A) ⤳ IsLocalRing.closedPoint A := IsLocalRing.specializes_closedPoint x
  refine (hx.map z.1.left.continuous).mem_open W.isOpen ?_
  have hm := h ⟨IsLocalRing.closedPoint (IsLocalRing.ResidueField A), rfl⟩
  rw [torsMap_val, Over.comp_left, spOver_left] at hm
  have e : (spMap (IsLocalRing.residue A)).base (IsLocalRing.closedPoint (IsLocalRing.ResidueField A)) =
      IsLocalRing.closedPoint A :=
    IsLocalRing.comap_closedPoint (IsLocalRing.residue A)
  have hm' : z.1.left ((spMap (IsLocalRing.residue A)).base
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField A))) ∈ W := hm
  rwa [e] at hm'

end Gen

end GlobalTheory.GroupBplus.Aff.MemLoc

namespace GlobalTheory.GroupBplus.Aff.MemLoc

section Chart

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {N : ℕ}

theorem exists_chart_of_residue_eq_one {q : PrimeSpectrum R} (c : PreChart G N q) (hc : c.IsGrp)
    (A : Type) [CommRing A] [IsLocalRing A] [Algebra R A] (hr : IsUnit (algebraMap R A c.r)) (z : Tors G N A)
    (hz : torsMap (IsScalarTower.toAlgHom R A (IsLocalRing.ResidueField A)) z = 1) :
    ∃ ψ₀ : c.C →ₐ[R] A, torsMap ψ₀ c.j = z := by
  obtain ⟨⟨ψ, hψ⟩, -⟩ := hc
  have hrκ : IsUnit (algebraMap R (IsLocalRing.ResidueField A) c.r) := by
    rw [IsScalarTower.algebraMap_apply R A (IsLocalRing.ResidueField A)]; exact hr.map _
  let φ : Localization.Away c.r →ₐ[R] IsLocalRing.ResidueField A :=
    IsLocalization.liftAlgHom (M := Submonoid.powers c.r) (f := Algebra.ofId R (IsLocalRing.ResidueField A))
      (by rintro ⟨_, n, rfl⟩; simpa using hrκ.pow n)
  have h1 : Set.range (torsMap (φ.comp ψ) c.j).1.left ⊆ c.W := (c.bij _).mapsTo (Set.mem_univ (φ.comp ψ))
  rw [← torsMap_comp, hψ, torsMap_one, ← hz] at h1
  have h2 : z ∈ {z : Tors G N A | Set.range z.1.left ⊆ c.W} := range_subset_of_residue c.W A z h1
  obtain ⟨ψ₀, -, h⟩ := (c.bij A).surjOn h2
  exact ⟨ψ₀, h⟩

end Chart

theorem exists_localElem_of_lift {R K : Type} [CommRing R] [Field K] [Algebra R K] (G : Over (Sp R)) [GrpObj G]
    [IsCommMonObj G] (N : ℕ)
    (hlift : ∀ (k : Type) [Field k] [Algebra R k] (z : Tors G N k), ∃ (r : R) (ψ : Localization.Away r →ₐ[R] k)
      (z' : Tors G N (Localization.Away r)), torsMap ψ z' = z)
    (q : PrimeSpectrum R) (c : PreChart G N q) (hc : c.IsGrp) (f : Tors G N K → K)
    (hf : ∀ s : Tors G N K, ∃ a : c.C, ∀ ψ : c.C →ₐ[R] K, ψ a = f (s * torsMap ψ c.j))
    (q' : PrimeSpectrum R) (c' : PreChart G N q') (s : Tors G N K) (P : Ideal c'.C) [P.IsPrime]
    (hP : algebraMap R c'.C c.r ∉ P) :
    ∃ b : Localization.AtPrime P, ∀ ψ : Localization.AtPrime P →ₐ[R] K,
      ψ b = f (s * torsMap (ψ.comp (IsScalarTower.toAlgHom R c'.C (Localization.AtPrime P))) c'.j) := by
  classical
  let incl := IsScalarTower.toAlgHom R c'.C (Localization.AtPrime P)
  let u : Tors G N (Localization.AtPrime P) := torsMap incl c'.j
  let ρ := IsScalarTower.toAlgHom R (Localization.AtPrime P) (IsLocalRing.ResidueField (Localization.AtPrime P))
  obtain ⟨r', ψ, z', hz'⟩ := hlift (IsLocalRing.ResidueField (Localization.AtPrime P)) (torsMap ρ u)
  have hu' : IsUnit (algebraMap R (Localization.AtPrime P) r') := by
    by_contra hn
    have h0 : algebraMap R (IsLocalRing.ResidueField (Localization.AtPrime P)) r' = 0 := by
      rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime P)]
      exact (IsLocalRing.residue_eq_zero_iff _).2 hn
    have h2 : IsUnit (ψ (algebraMap R _ r')) := (IsLocalization.Away.algebraMap_isUnit r').map ψ
    rw [ψ.commutes, h0] at h2
    exact not_isUnit_zero h2
  let lam : Localization.Away r' →ₐ[R] Localization.AtPrime P :=
    IsLocalization.liftAlgHom (M := Submonoid.powers r') (f := Algebra.ofId R _)
      (by rintro ⟨_, n, rfl⟩; simpa using hu'.pow n)
  let t : Tors G N (Localization.AtPrime P) := torsMap lam z'
  have ht : torsMap ρ (u * t⁻¹) = 1 := by
    rw [torsMap_mul, torsMap_inv, torsMap_comp lam ρ,
      (IsLocalization.algHom_subsingleton (Submonoid.powers r')).elim (ρ.comp lam) ψ, hz', mul_inv_cancel]
  have hrA : IsUnit (algebraMap R (Localization.AtPrime P) c.r) := by
    rw [IsScalarTower.algebraMap_apply R c'.C (Localization.AtPrime P)]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff _ P _).2 hP
  obtain ⟨ψ₀, hψ₀⟩ := exists_chart_of_residue_eq_one c hc (Localization.AtPrime P) hrA (u * t⁻¹) ht
  by_cases hK : Nonempty (Localization.AtPrime P →ₐ[R] K)
  · obtain ⟨ψK⟩ := hK
    let tK : Tors G N K := torsMap (ψK.comp lam) z'
    obtain ⟨a, ha⟩ := hf (s * tK)
    refine ⟨ψ₀ a, fun χ => ?_⟩
    have e1 : χ (ψ₀ a) = (χ.comp ψ₀) a := rfl
    have e2 : torsMap χ t = tK := by
      rw [torsMap_comp lam χ, (IsLocalization.algHom_subsingleton (Submonoid.powers r')).elim (χ.comp lam) (ψK.comp lam)]
    rw [e1, ha, ← torsMap_comp ψ₀ χ, hψ₀, torsMap_mul, torsMap_inv, e2, ← torsMap_comp incl χ]
    congr 1
    rw [_root_.mul_comm (torsMap χ u), _root_.mul_assoc, _root_.mul_inv_cancel_left]
  · exact ⟨0, fun χ => (hK ⟨χ⟩).elim⟩

end GlobalTheory.GroupBplus.Aff.MemLoc
