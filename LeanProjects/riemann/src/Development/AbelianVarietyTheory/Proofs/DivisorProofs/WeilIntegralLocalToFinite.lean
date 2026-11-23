import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosure
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteAlgebrasOverHenselianAndComplete
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingHenselianAndSmoothPointsLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowEqScaleAndExistsUniqueTorsion

open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WeilIntegral

theorem exists_factor_pi {O B : Type} [CommRing O] [IsDomain O] [CommRing B] [Algebra O B]
    {J : Type} [Finite J] {T : J → Type} [∀ i, CommRing (T i)] [∀ i, Algebra O (T i)]
    (e : B ≃ₐ[O] Π i, T i) (ψ : B →ₐ[O] O) :
    ∃ (i : J) (φ : T i →ₐ[O] O), ψ = φ.comp ((Pi.evalAlgHom O T i).comp e.toAlgHom) := by
  classical
  haveI := Fintype.ofFinite J
  set χ : (Π i, T i) →ₐ[O] O := ψ.comp e.symm.toAlgHom with hχ
  have hsum : ∑ i, χ (Pi.single i 1) = 1 := by
    rw [← map_sum, show (∑ i, Pi.single i 1 : Π i, T i) = 1 from Finset.univ_sum_single (1 : Π i, T i), map_one]
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hsum.trans_ne one_ne_zero)
  have hidem : IsIdempotentElem (χ (Pi.single i 1)) := by
    have : IsIdempotentElem (Pi.single i (1 : T i) : Π j, T j) := by
      unfold IsIdempotentElem
      rw [← Pi.single_mul, _root_.one_mul]
    exact this.map χ
  have h1 : χ (Pi.single i 1) = 1 := (IsIdempotentElem.iff_eq_zero_or_one.1 hidem).resolve_left hi
  have hmul : ∀ y : Π j, T j, y * Pi.single i 1 = Pi.single i (y i) := by
    intro y
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  let φ : T i →ₐ[O] O :=
    { toFun := fun t => χ (Pi.single i t)
      map_one' := h1
      map_mul' := fun a b => by rw [Pi.single_mul, map_mul]
      map_zero' := by simp only [Pi.single_zero, map_zero]
      map_add' := fun a b => by simp only [Pi.single_add, map_add]
      commutes' := fun r => by
        change χ (Pi.single i (algebraMap O (T i) r)) = _
        rw [Algebra.algebraMap_eq_smul_one, Pi.single_smul, map_smul, h1, smul_eq_mul, _root_.mul_one]
        rfl }
  refine ⟨i, φ, AlgHom.ext fun b => ?_⟩
  have hb : ψ b = χ (e b) := by simp [hχ]
  rw [hb]
  change χ (e b) = χ (Pi.single i (e b i))
  rw [← hmul, map_mul, h1, _root_.mul_one]

end GlobalTheory.WeilIntegral

open GlobalTheory.TangentPow in

theorem GlobalTheory.WeilIntegral.weilIntegralFinite_of_local : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), WeilIntegralLocal P → WeilIntegralFinite P := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P hloc B _ _ _ _ N hN x y hx hy
  classical
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  haveI : ValuationRing O := ValuationRing.of_integers v P.integers
  haveI : IsFractionRing O C := P.integers.isFractionRing
  haveI : HenselianLocalRing O := henselianLocalRing_of_valuationRing_of_isAlgClosed O C
  obtain ⟨J, hJ, T, _, _, e, hT⟩ := ((finite_algebras_over_henselian O).1 B).1
  let π : ∀ i, B →ₐ[O] T i := fun i => (Pi.evalAlgHom O T i).comp e.toAlgHom
  have hflat : ∀ i, Module.Flat O (T i) := fun i =>
    Module.Flat.of_retract (e.symm.toLinearMap ∘ₗ LinearMap.single O T i)
      (LinearMap.proj i ∘ₗ e.toLinearMap) (LinearMap.ext fun t => by simp)
  have key : ∀ i, ∃ u : T i, ∀ φ : T i →ₐ[O] O, algebraMap O C (φ u) =
      (weil P.A N (P.toA (ptMap φ ≫ ptMap (π i) ≫ x)) (P.toA (ptMap φ ≫ ptMap (π i) ≫ y)) : C) := by
    intro i
    haveI := (hT i).1
    haveI := (hT i).2
    haveI := hflat i
    exact hloc (T i) N hN (ptMap (π i) ≫ x) (ptMap (π i) ≫ y)
      (by rw [← MonObj.comp_pow, hx, MonObj.comp_one])
      (by rw [← MonObj.comp_pow, hy, MonObj.comp_one])
  choose u hu using key
  refine ⟨e.symm u, fun ψ => ?_⟩
  obtain ⟨i, φ, rfl⟩ := GlobalTheory.WeilIntegral.exists_factor_pi e ψ
  rw [← ptMap_comp_ptMap, Category.assoc, Category.assoc, ← hu i φ]
  exact congrArg (fun t => algebraMap O C (φ t)) (congrFun (e.apply_symm_apply u) i)
