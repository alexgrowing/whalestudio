import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenRegularCharacters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GreenCuspidalCharIsCuspidalOfMinpolyOfParam
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsTeichmullerMapAlgebraicClosureFiniteFieldStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseOneProdIcoStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyOfIrreduciStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsPrimitiveEndClassFunctionInvariantSubspaceMobiStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyLinearEquiStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootPowerSumCharacterAdditiveAndXSubOnePowStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvertibleEndInnerProductRootPowerSumMobiusStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.PrimitiveClassFunctionExpansionRootSumsStatement

open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial GlobalTheory.CuspGL
open scoped Classical

noncomputable section

namespace GlobalTheory.GreenRegular

theorem pow_modEq_pow_mod {g : ℕ} (d : ℕ) (hg : 0 < g) (m : ℕ) : g ^ m ≡ g ^ (m % d) [MOD g ^ d - 1] := by
  have h1 : g ^ d ≡ 1 [MOD g ^ d - 1] := Nat.modEq_sub (Nat.one_le_pow _ _ hg)
  conv_lhs => rw [← Nat.div_add_mod m d, pow_add, pow_mul]
  calc (g ^ d) ^ (m / d) * g ^ (m % d) ≡ 1 ^ (m / d) * g ^ (m % d) [MOD g ^ d - 1] :=
        (h1.pow _).mul_right _
    _ = g ^ (m % d) := by rw [one_pow, one_mul]

theorem filter_modEq_congr {g d a b l : ℕ} (h : a ≡ b [MOD g ^ d - 1]) :
    ((Finset.range d).filter fun i => a * g ^ i ≡ l [MOD g ^ d - 1]) =
      (Finset.range d).filter fun i => b * g ^ i ≡ l [MOD g ^ d - 1] :=
  Finset.filter_congr fun i _ =>
    ⟨fun h' => ((h.symm.mul_right _).trans h'), fun h' => ((h.mul_right _).trans h')⟩

theorem card_filter_le_shift {g d : ℕ} (hg : 0 < g) (hd : 0 < d) (a c l : ℕ) :
    ((Finset.range d).filter fun i => a * g ^ c * g ^ i ≡ l [MOD g ^ d - 1]).card ≤
      ((Finset.range d).filter fun i => a * g ^ i ≡ l [MOD g ^ d - 1]).card := by
  refine Finset.card_le_card_of_injOn (fun i => (i + c) % d) ?_ ?_
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi ⊢
    refine ⟨Nat.mod_lt _ hd, ?_⟩
    refine ((pow_modEq_pow_mod d hg (i + c)).symm.mul_left a).trans ?_
    rw [pow_add, mul_comm (g ^ i), ← mul_assoc]
    exact hi.2
  · intro i hi j hj hij
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi hj
    have h1 : i + c ≡ j + c [MOD d] := hij
    have h2 := Nat.ModEq.add_right_cancel' c h1
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hi.1, Nat.mod_eq_of_lt hj.1] at h2

theorem card_filter_shift {g d : ℕ} (hg : 0 < g) (hd : 0 < d) (a c l : ℕ) (hc : c ≤ d) :
    ((Finset.range d).filter fun i => a * g ^ c * g ^ i ≡ l [MOD g ^ d - 1]).card =
      ((Finset.range d).filter fun i => a * g ^ i ≡ l [MOD g ^ d - 1]).card := by
  refine le_antisymm (card_filter_le_shift hg hd a c l) ?_
  have e : a ≡ a * g ^ c * g ^ (d - c) [MOD g ^ d - 1] := by
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hc]
    calc a = a * 1 := (mul_one a).symm
      _ ≡ a * g ^ d [MOD g ^ d - 1] := (Nat.modEq_sub (Nat.one_le_pow _ _ hg)).symm.mul_left a
  rw [filter_modEq_congr e]
  exact card_filter_le_shift hg hd (a * g ^ c) (d - c) l

end GlobalTheory.GreenRegular

namespace GlobalTheory.GreenRegular

theorem exists_cusp_of_regular : ∀ (g : ℕ) [Fact g.Prime] (d : ℕ), 0 < d → ∀ (K : Type) [Field K] [Algebra (ZMod g) K],
    Module.finrank (ZMod g) K = d → ∃ τ : (Kˣ →* ℂˣ) → Gn g d → ℂ,
      (∀ θ, IsRegularChar g d θ → IsCusp (τ θ) ∧ τ θ 1 = ∏ i ∈ Finset.Ico 1 d, ((g : ℂ) ^ i - 1) ∧
        ∀ y : Gn g d, Irreducible (y : Mt g d).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g d).charpoly = 0 →
          τ θ y = (-1) ^ (d - 1) * ∑ i ∈ Finset.range d, ((θ (z ^ g ^ i) : ℂˣ) : ℂ)) ∧
      (∀ θ θ', IsRegularChar g d θ → IsRegularChar g d θ' → (τ θ = τ θ' ↔ ∃ i < d, θ' = θ ^ g ^ i)) := by
  intro g _ d hd K _ _ hK
  have hgp : g.Prime := Fact.out
  have hg : 0 < g := hgp.pos
  have hcF : Nat.card (ZMod g) = g := Nat.card_zmod g
  haveI : FiniteDimensional (ZMod g) K := Module.finite_of_finrank_pos (by rw [hK]; exact hd)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  letI : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = g ^ d := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, hK]
  have hcardU : Nat.card Kˣ = g ^ d - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, hcardK]
  have hN0 : 0 < g ^ d - 1 := by
    have := Nat.one_lt_pow hd.ne' hgp.one_lt
    omega
  obtain ⟨θ₀, hθ₀⟩ := GlobalTheory.T.exists_teichmuller_map_algebraicClosure_finiteField (ZMod g)
  let ι : K →ₐ[ZMod g] AlgebraicClosure (ZMod g) := IsAlgClosed.lift
  let lam : Kˣ →* ℂˣ := (Units.map θ₀).comp (Units.map (ι : K →* AlgebraicClosure (ZMod g)))
  have hlam : ∀ u : Kˣ, ((lam u : ℂˣ) : ℂ) = θ₀ (ι (u : K)) := fun u => rfl
  have hlam_inj : Function.Injective lam := by
    intro u v h
    have h' := congrArg Units.val h
    rw [hlam, hlam] at h'
    exact Units.ext (ι.injective (hθ₀ _ _ ((map_ne_zero ι).2 u.ne_zero) ((map_ne_zero ι).2 v.ne_zero) h'))
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hprim : IsPrimitiveRoot (lam γ) (g ^ d - 1) := by
    rw [← hcardU, ← orderOf_eq_card_of_forall_mem_zpowers hγ, ← orderOf_injective lam hlam_inj γ]
    exact IsPrimitiveRoot.orderOf _
  have hmod : ∀ u : Kˣ, u ^ (g ^ d - 1) = 1 := fun u => by
    rw [← hcardU]; exact pow_card_eq_one'
  have hpow_eq : ∀ a b : ℕ, lam ^ a = lam ^ b ↔ a ≡ b [MOD g ^ d - 1] := by
    intro a b
    constructor
    · intro h
      have h1 := congrArg (fun f : Kˣ →* ℂˣ => f γ) h
      simp only [MonoidHom.pow_apply] at h1
      rwa [pow_eq_pow_iff_modEq, ← hprim.eq_orderOf] at h1
    · intro h
      refine MonoidHom.ext fun u => ?_
      rw [MonoidHom.pow_apply, MonoidHom.pow_apply, pow_eq_pow_iff_modEq]
      exact Nat.ModEq.of_dvd (orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hmod, map_one])) h
  have hpow : ∀ θ : Kˣ →* ℂˣ, ∃ k, θ = lam ^ k := by
    intro θ
    have h1 : θ γ ^ (g ^ d - 1) = 1 := by rw [← map_pow, hmod, map_one]
    haveI : NeZero (g ^ d - 1) := ⟨hN0.ne'⟩
    have h1' : ((θ γ : ℂˣ) : ℂ) ^ (g ^ d - 1) = 1 := by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
    obtain ⟨k, -, hk0⟩ := (IsPrimitiveRoot.coe_units_iff.2 hprim).eq_pow_of_pow_eq_one h1'
    have hk : lam γ ^ k = θ γ := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hk0)
    refine ⟨k, MonoidHom.ext fun u => ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hγ u)
    rw [map_zpow, map_zpow, MonoidHom.pow_apply, hk]
  let kOf : (Kˣ →* ℂˣ) → ℕ := fun θ => (hpow θ).choose
  have hkOf : ∀ θ, θ = lam ^ kOf θ := fun θ => (hpow θ).choose_spec
  have hreg : ∀ θ, IsRegularChar g d θ → ∀ i : ℕ, 0 < i → i < d →
      ¬ kOf θ * Nat.card (ZMod g) ^ i ≡ kOf θ [MOD Nat.card (ZMod g) ^ d - 1] := by
    intro θ hθ i hi hid hc
    rw [hcF] at hc
    have e : θ ^ g ^ i = θ ^ g ^ 0 := by
      rw [hkOf θ, ← pow_mul, ← pow_mul, pow_zero, mul_one]
      exact (hpow_eq _ _).2 hc
    exact absurd (hθ i 0 hid hd e) hi.ne'
  have hadd : ∀ k, IsAdditive (rootSum θ₀ k) := fun k => (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow (ZMod g) θ₀ k).1
  have hfr : 0 < Module.finrank (ZMod g) (Fin d → ZMod g) := by rw [Module.finrank_fin_fun]; exact hd
  refine ⟨fun θ x => (-1) ^ (d - 1) *
    psi (rootSum θ₀ (kOf θ)) (Fin d → ZMod g) (Matrix.toLin' (x : Matrix (Fin d) (Fin d) (ZMod g))),
    fun θ hθ => ⟨?_, ?_, ?_⟩, fun θ θ' hθ hθ' => ?_⟩
  · exact GlobalTheory.ParamLabel.isCusp_psi θ₀ hθ₀ hd (hreg θ hθ)
  · show (-1) ^ (d - 1) * psi _ _ (Matrix.toLin' ((1 : Gn g d) : Matrix (Fin d) (Fin d) (ZMod g))) = _
    have h1 := GlobalTheory.T.invariantSubspaceMobiusInverse_one_prod_Ico (ZMod g) (Fin d → ZMod g) (rootSum θ₀ (kOf θ)) (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow (ZMod g) θ₀ (kOf θ)).2 hfr
    rw [Units.val_one, Matrix.toLin'_one, ← Module.End.one_eq_id, h1, Module.finrank_fin_fun, hcF,
      show ((-1 : ℂ)) ^ (d - 1) = ∏ i ∈ Finset.Ico 1 d, (-1 : ℂ) by rw [Finset.prod_const, Nat.card_Ico],
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by ring
  · intro y hy z hz
    show (-1) ^ (d - 1) * psi _ _ _ = _
    have h := GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_of_irreducible (ZMod g) (Fin d → ZMod g) _ (hadd (kOf θ)) (Matrix.toLin' (y : Mt g d))
      (by rw [Matrix.charpoly_toLin']; exact hy)
    rw [h, Matrix.charpoly_toLin']
    congr 1
    have hz' : aeval (ι (z : K)) (y : Mt g d).charpoly = 0 := by rw [aeval_algHom_apply, hz, map_zero]
    have hnd : (y : Mt g d).charpoly.natDegree = d := by simp
    change ((Formalism.CyclotomicNorms.rootsBar _).map _).sum = _
    rw [GlobalTheory.GreenExists.rootsBar_eq hy hz', hnd, Multiset.map_map, Finset.sum_eq_multiset_sum]
    congr 1
    refine Multiset.map_congr rfl fun i _ => ?_
    conv_rhs => rw [hkOf θ]
    show θ₀ (ι ↑z ^ g ^ i) ^ kOf θ = _
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hlam, Units.val_pow_eq_pow_val, map_pow ι]
  · have hsign : ((-1 : ℂ) ^ (d - 1)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
    have hunit : ∀ G : Module.End (ZMod g) (Fin d → ZMod g), IsUnit G →
        ∃ x : Gn g d, Matrix.toLin' (x : Mt g d) = G := by
      intro G hG
      have hM : IsUnit (LinearMap.toMatrix' G) :=
        hG.map (LinearMap.toMatrixAlgEquiv' : Module.End (ZMod g) (Fin d → ZMod g) ≃ₐ[ZMod g] Mt g d)
      exact ⟨hM.unit, by rw [IsUnit.unit_spec, Matrix.toLin'_toMatrix']⟩
    have hxU : ∀ x : Gn g d, IsUnit (Matrix.toLin' (x : Mt g d)) := fun x =>
      x.isUnit.map (Matrix.toLinAlgEquiv' : Mt g d ≃ₐ[ZMod g] Module.End (ZMod g) (Fin d → ZMod g))
    have heqU : ∀ k k' : ℕ, (∀ x : Gn g d, psi (rootSum θ₀ k) (Fin d → ZMod g) (Matrix.toLin' (x : Mt g d)) =
        psi (rootSum θ₀ k') (Fin d → ZMod g) (Matrix.toLin' (x : Mt g d))) → ∀ l : ℕ,
        ipGL (psi (rootSum θ₀ k) (Fin d → ZMod g)) (fun G => rootSum θ₀ l (LinearMap.charpoly G)) =
          ipGL (psi (rootSum θ₀ k') (Fin d → ZMod g)) (fun G => rootSum θ₀ l (LinearMap.charpoly G)) := by
      intro k k' h l
      refine finsum_mem_congr rfl fun G hG => ?_
      obtain ⟨x, rfl⟩ := hunit G hG
      rw [h x]
    have hgram : ∀ k l : ℕ, ipGL (psi (rootSum θ₀ k) (Fin d → ZMod g))
        (fun G => rootSum θ₀ l (LinearMap.charpoly G)) = glCard (ZMod g) d *
          (((Finset.range d).filter fun i => k * g ^ i ≡ l [MOD g ^ d - 1]).card : ℂ) := by
      intro k l
      have h := GlobalTheory.T.invertibleEndInnerProduct_rootPowerSum_mobius (ZMod g) (Fin d → ZMod g) θ₀ hθ₀ hfr k l
      rwa [Module.finrank_fin_fun, hcF] at h
    have hGL : glCard (ZMod g) d ≠ 0 := by
      unfold glCard
      exact Nat.cast_ne_zero.2 Nat.card_pos.ne'
    constructor
    · intro hτ
      have hx : ∀ x : Gn g d, psi (rootSum θ₀ (kOf θ)) (Fin d → ZMod g) (Matrix.toLin' (x : Mt g d)) =
          psi (rootSum θ₀ (kOf θ')) (Fin d → ZMod g) (Matrix.toLin' (x : Mt g d)) :=
        fun x => mul_left_cancel₀ hsign (congrFun hτ x)
      have e1 := heqU _ _ hx (kOf θ')
      rw [hgram, hgram] at e1
      have h2 := mul_left_cancel₀ hGL e1
      have hmem : 0 ∈ (Finset.range d).filter fun i => kOf θ' * g ^ i ≡ kOf θ' [MOD g ^ d - 1] := by
        rw [Finset.mem_filter, Finset.mem_range, pow_zero, mul_one]
        exact ⟨hd, Nat.ModEq.refl _⟩
      have hne : ((Finset.range d).filter fun i => kOf θ * g ^ i ≡ kOf θ' [MOD g ^ d - 1]).Nonempty := by
        rw [← Finset.card_pos]
        refine Nat.pos_of_ne_zero fun h0 => ?_
        have h3 := (Finset.card_pos.2 ⟨0, hmem⟩).ne'
        rw [h0, Nat.cast_zero] at h2
        exact h3 (by exact_mod_cast h2.symm)
      obtain ⟨i, hi⟩ := hne
      rw [Finset.mem_filter, Finset.mem_range] at hi
      refine ⟨i, hi.1, ?_⟩
      rw [hkOf θ', hkOf θ, ← pow_mul]
      exact ((hpow_eq _ _).2 hi.2).symm
    · rintro ⟨i, hi, hθi⟩
      have hk : kOf θ' ≡ kOf θ * g ^ i [MOD g ^ d - 1] := by
        rw [← hpow_eq, pow_mul, ← hkOf θ, ← hkOf θ']
        exact hθi
      funext x
      refine congrArg (fun t : ℂ => (-1 : ℂ) ^ (d - 1) * t) ?_
      have hcl : ∀ k : ℕ, IsClassFn (psi (rootSum θ₀ k) (Fin d → ZMod g)) := fun k e G =>
        GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj (ZMod g) _ _ _ e G
      have hexp := fun k : ℕ => GlobalTheory.T.primitiveClassFunction_expansion_rootSums (ZMod g) (Fin d → ZMod g) θ₀ hθ₀ _ (hcl k)
        (GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse (ZMod g) (Fin d → ZMod g) _ (hadd k)) hfr _ (hxU x)
      have e1 := hexp (kOf θ)
      have e2 := hexp (kOf θ')
      rw [Module.finrank_fin_fun, hcF] at e1 e2
      have hsum : ∀ l : ℕ, ipGL (psi (rootSum θ₀ (kOf θ)) (Fin d → ZMod g))
          (fun G => rootSum θ₀ l (LinearMap.charpoly G)) = ipGL (psi (rootSum θ₀ (kOf θ')) (Fin d → ZMod g))
          (fun G => rootSum θ₀ l (LinearMap.charpoly G)) := by
        intro l
        rw [hgram, hgram, filter_modEq_congr hk, card_filter_shift hg hd _ _ _ hi.le]
      rw [Finset.sum_congr rfl fun l _ => by rw [hsum l]] at e1
      exact mul_left_cancel₀ (mul_ne_zero hGL (Nat.cast_ne_zero.2 hd.ne')) (e1.trans e2.symm)

end GlobalTheory.GreenRegular
