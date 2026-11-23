import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.SuppBCOfMix
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.PrimitiveClassFunctionExpansionRootSumsStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvertibleEndInnerProductRootPowerSumMobiusStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootPowerSumCharacterAdditiveAndXSubOnePowStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyLinearEquiStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsPrimitiveEndClassFunctionInvariantSubspaceMobiStatement

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open GlobalTheory.CuspGL GlobalTheory.BI
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem pow_mod_modEq (q m : ℕ) (hq : 0 < q) (hm : 0 < m) (e : ℕ) :
    q ^ e ≡ q ^ (e % m) [MOD q ^ m - 1] := by
  have h1 : q ^ m ≡ 1 [MOD q ^ m - 1] := Nat.modEq_sub (Nat.one_le_pow _ _ hq)
  conv_lhs => rw [← Nat.div_add_mod e m, pow_add, pow_mul]
  calc (q ^ m) ^ (e / m) * q ^ (e % m) ≡ 1 ^ (e / m) * q ^ (e % m) [MOD q ^ m - 1] :=
        (h1.pow _).mul_right _
    _ = q ^ (e % m) := by rw [one_pow, one_mul]

private theorem count_le (q m c c' i k : ℕ) (hq : 0 < q) (hm : 0 < m)
    (h : c' ≡ c * q ^ i [MOD q ^ m - 1]) :
    ((Finset.range m).filter fun j => c' * q ^ j ≡ k [MOD q ^ m - 1]).card ≤
      ((Finset.range m).filter fun j => c * q ^ j ≡ k [MOD q ^ m - 1]).card := by
  apply Finset.card_le_card_of_injOn (fun j => (j + i) % m)
  · intro j hj
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hj ⊢
    refine ⟨Nat.mod_lt _ hm, ?_⟩
    calc c * q ^ ((j + i) % m) ≡ c * q ^ (j + i) [MOD q ^ m - 1] :=
          ((pow_mod_modEq q m hq hm (j + i)).symm).mul_left _
      _ = c * q ^ i * q ^ j := by ring
      _ ≡ c' * q ^ j [MOD q ^ m - 1] := h.symm.mul_right _
      _ ≡ k [MOD q ^ m - 1] := hj.2
  · intro a ha b hb hab
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at ha hb
    have h' : a ≡ b [MOD m] := Nat.ModEq.add_right_cancel' i hab
    unfold Nat.ModEq at h'
    rwa [Nat.mod_eq_of_lt ha.1, Nat.mod_eq_of_lt hb.1] at h'

private theorem count_eq (q m c c' i k : ℕ) (hq : 0 < q) (hm : 0 < m)
    (h : c' ≡ c * q ^ i [MOD q ^ m - 1]) :
    ((Finset.range m).filter fun j => c' * q ^ j ≡ k [MOD q ^ m - 1]).card =
      ((Finset.range m).filter fun j => c * q ^ j ≡ k [MOD q ^ m - 1]).card := by
  apply le_antisymm (count_le q m c c' i k hq hm h)
  apply count_le q m c' c (m - i % m) k hq hm
  have hr : i % m < m := Nat.mod_lt _ hm
  have hd : m * (i / m) + i % m = i := Nat.div_add_mod i m
  have hs : i + (m - i % m) = m * (i / m + 1) := by
    rw [mul_add, mul_one]
    omega
  calc c = c * q ^ ((i + (m - i % m)) % m) := by rw [hs, Nat.mul_mod_right, pow_zero, mul_one]
    _ ≡ c * q ^ (i + (m - i % m)) [MOD q ^ m - 1] :=
        ((pow_mod_modEq q m hq hm _).symm).mul_left _
    _ = c * q ^ i * q ^ (m - i % m) := by ring
    _ ≡ c' * q ^ (m - i % m) [MOD q ^ m - 1] := h.symm.mul_right _

private theorem psi_eq (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y)
    (hn : 0 < Module.finrank F V) (c c' i : ℕ)
    (h : c' ≡ c * Nat.card F ^ i [MOD Nat.card F ^ Module.finrank F V - 1])
    (g : Module.End F V) (hg : IsUnit g) :
    psi (rootSum θ c') V g = psi (rootSum θ c) V g := by
  have hcl : ∀ s : F[X] → ℂ, IsAdditive s →
      IsClassFn (psi s V) ∧ GlobalTheory.CuspGL.IsPrimitive (psi s V) := fun s hs =>
    ⟨fun e x => GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj F s V V e x, GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse F V s hs⟩
  have hc := hcl _ (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow F θ c).1
  have hc' := hcl _ (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow F θ c').1
  have e1 := GlobalTheory.T.primitiveClassFunction_expansion_rootSums F V θ hθ _ hc'.1 hc'.2 hn g hg
  have e2 := GlobalTheory.T.primitiveClassFunction_expansion_rootSums F V θ hθ _ hc.1 hc.2 hn g hg
  have hsum : (∑ k ∈ Finset.range (Nat.card F ^ Module.finrank F V - 1),
      (ipGL (psi (rootSum θ c') V) fun x ↦ rootSum θ k (LinearMap.charpoly x)) *
        psi (rootSum θ k) V g) =
      ∑ k ∈ Finset.range (Nat.card F ^ Module.finrank F V - 1),
      (ipGL (psi (rootSum θ c) V) fun x ↦ rootSum θ k (LinearMap.charpoly x)) *
        psi (rootSum θ k) V g := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [GlobalTheory.T.invertibleEndInnerProduct_rootPowerSum_mobius F V θ hθ hn, GlobalTheory.T.invertibleEndInnerProduct_rootPowerSum_mobius F V θ hθ hn,
      count_eq (Nat.card F) (Module.finrank F V) c c' i k Nat.card_pos hn h]
  have hne : glCard F (Module.finrank F V) * (Module.finrank F V : ℂ) ≠ 0 := by
    refine mul_ne_zero ?_ (Nat.cast_ne_zero.mpr hn.ne')
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  exact mul_left_cancel₀ hne (e1.trans (hsum.trans e2.symm))

theorem UpperTheory.Gal.InertialTypesAlt.cuspFrob :
    CuspFrob := by
  intro F _ _ θ hθ m c c' i hm h
  funext x
  simp only [GlobalTheory.Shin.cusp, GlobalTheory.Shin.psiG]
  congr 1
  have hr : Module.finrank F (Fin m → F) = m := Module.finrank_fin_fun F
  refine psi_eq F (Fin m → F) θ hθ (by rw [hr]; exact hm) c c' i (by rw [hr]; exact h) _ ?_
  exact x.isUnit.map
    (Matrix.toLinAlgEquiv' : Matrix (Fin m) (Fin m) F ≃ₐ[F] Module.End F (Fin m → F))
