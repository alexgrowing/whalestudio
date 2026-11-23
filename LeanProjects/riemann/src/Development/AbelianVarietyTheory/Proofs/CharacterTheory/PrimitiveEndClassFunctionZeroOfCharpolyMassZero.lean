import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.AdditiveEqPolynomialVonMangoldtConvolutionOne
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ConjOfPrimaryFinrankKerPowEq
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyLinearEqui
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.AdditiveEqPolynomialVonMangoldtConvolutionOneStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ConjOfPrimaryFinrankKerPowEqStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyLinearEquiStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EndomorphismMassMobiusInverseMonicEqStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EqZeroOfNotPrimaryStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.PrimitiveEndClassFunctionEqZeroOfPrimaryStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsPrimitiveEndClassFunctionInvariantSubspaceMobiStatement

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem finsum_mem_lin_comb_of_finite {α : Type} [Finite α] (S : Set α) (a b : ℂ) (u v : α → ℂ) :
    ∑ᶠ x ∈ S, (a * u x - b * v x) = a * (∑ᶠ x ∈ S, u x) - b * ∑ᶠ x ∈ S, v x := by
  have hS : S.Finite := Set.toFinite S
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, finsum_mem_eq_finite_toFinset_sum _ hS,
    finsum_mem_eq_finite_toFinset_sum _ hS, Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]

theorem eq_zero_of_mass_charpoly_eq_zero (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (φ : Module.End F V → ℂ) (hc : IsClassFn φ) (hp : IsPrimitive φ)
    (g : Module.End F V) (hm : mass φ (LinearMap.charpoly g) = 0) : φ g = 0 := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Module.End F V) := Finite.of_injective (fun h : Module.End F V => (h : V → V))
    DFunLike.coe_injective
  rcases Nat.eq_zero_or_pos (Module.finrank F V) with h0 | hpos
  · haveI : Subsingleton V := Module.finrank_zero_iff.mp h0
    have hset : {g' : Module.End F V | LinearMap.charpoly g' = LinearMap.charpoly g} = {g} := by
      ext g'
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      have : g' = g := Subsingleton.elim _ _
      simp [this]
    rw [mass, hset, finsum_mem_singleton] at hm
    exact hm
  by_cases hprim : ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ LinearMap.charpoly g = f ^ m
  swap
  · exact GlobalTheory.T.classFn_eq_zero_of_charpoly_not_irreducible_pow F V φ hc hp hpos g hprim
  obtain ⟨f, m, hfm, hf, hm0, hg⟩ := hprim
  set s : F[X] → ℂ := fun P => (P.natDegree : ℂ) with hs
  have hsa : IsAdditive s := isAdditive_natDegree
  have hπc : IsClassFn (psi s V) := fun e x => GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj F s V V e x
  have hπp : IsPrimitive (psi s V) := GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse F V s hsa
  have hdeg : (LinearMap.charpoly g).natDegree = Module.finrank F V := LinearMap.charpoly_natDegree g
  have hmass : mass (psi s V) (LinearMap.charpoly g) ≠ 0 := by
    rw [GlobalTheory.T.endomorphismMass_mobiusInverse_monic_eq F V s hsa _ (LinearMap.charpoly_monic g) hdeg, hdeg, hg,
      (GlobalTheory.T.additive_eq_polynomialVonMangoldt_convolution_one F s hsa).2.1 f m hfm hf hm0]
    have h1 : glCard F (Module.finrank F V) ≠ 0 := by
      rw [glCard]
      exact_mod_cast (Nat.card_pos (α := GL (Fin (Module.finrank F V)) F)).ne'
    have h2 : s f ≠ 0 := by
      simp only [hs]
      exact_mod_cast hf.natDegree_pos.ne'
    have h3 : (Nat.card F : ℂ) ^ Module.finrank F V - 1 ≠ 0 := by
      have hq : 1 < Nat.card F := Finite.one_lt_card
      have : 1 < Nat.card F ^ Module.finrank F V := Nat.one_lt_pow hpos.ne' hq
      rw [sub_ne_zero]
      exact_mod_cast this.ne'
    exact div_ne_zero (mul_ne_zero h1 h2) h3
  have hex : ∃ g₀ : Module.End F V, LinearMap.charpoly g₀ = f ^ m ∧ aeval g₀ f = 0 ∧ psi s V g₀ ≠ 0 := by
    by_contra hne
    push_neg at hne
    apply hmass
    rw [mass]
    refine finsum_mem_eq_zero_of_forall_eq_zero fun x hx => ?_
    exact GlobalTheory.T.primitiveEndClassFunction_eq_zero_of_primary F V _ hπc hπp f m hf hne x (hg ▸ hx)
  obtain ⟨g₀, hg₀, hfg₀, hπ₀⟩ := hex
  have hconj : ∀ g₁ : Module.End F V, aeval g₁ f = 0 → ∃ e : V ≃ₗ[F] V, e.conj g₀ = g₁ := by
    intro g₁ h₁
    refine GlobalTheory.T.conj_of_primary_finrank_ker_pow_eq F V g₀ g₁ f 1 hf (by simpa using hfg₀) (by simpa using h₁) fun j => ?_
    rw [map_pow, map_pow, hfg₀, h₁]
  set φ' : Module.End F V → ℂ := fun x => psi s V g₀ * φ x - φ g₀ * psi s V x with hφ'
  have hc' : IsClassFn φ' := fun e x => by simp only [hφ', hc e x, hπc e x]
  have hp' : IsPrimitive φ' := fun A h1 h2 x hx => by
    simp only [hφ']
    rw [finsum_mem_lin_comb_of_finite _ _ _ (fun h => φ (x + h)) (fun h => psi s V (x + h)),
      hp A h1 h2 x hx, hπp A h1 h2 x hx]
    simp
  have hz : ∀ x : Module.End F V, LinearMap.charpoly x = f ^ m → φ' x = 0 := by
    refine GlobalTheory.T.primitiveEndClassFunction_eq_zero_of_primary F V φ' hc' hp' f m hf fun x _ hx => ?_
    obtain ⟨e, rfl⟩ := hconj x hx
    simp only [hφ', hc e g₀, hπc e g₀]
    ring
  have hm' : mass φ' (LinearMap.charpoly g) = 0 := by
    rw [mass]
    exact finsum_mem_eq_zero_of_forall_eq_zero fun x hx => hz x (hg ▸ hx)
  have hlin : mass φ' (LinearMap.charpoly g) = psi s V g₀ * mass φ (LinearMap.charpoly g) -
      φ g₀ * mass (psi s V) (LinearMap.charpoly g) :=
    finsum_mem_lin_comb_of_finite _ _ _ _ _
  rw [hm', hm, mul_zero, zero_sub, eq_comm, neg_eq_zero] at hlin
  have h0 : φ g₀ = 0 := (mul_eq_zero.mp hlin).resolve_right hmass
  have := hz g hg
  simp only [hφ', h0, zero_mul, sub_zero] at this
  exact (mul_eq_zero.mp this).resolve_left hπ₀

end GlobalTheory.CuspGL
