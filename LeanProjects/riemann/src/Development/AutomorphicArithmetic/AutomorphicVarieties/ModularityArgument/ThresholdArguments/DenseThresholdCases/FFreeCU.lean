import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.FreeCU
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RRFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.IsAutCsdA

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th
open scoped Pointwise
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem cont_units {Γ R : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Monoid R]
    [TopologicalSpace R] (f : Γ →* Rˣ) (h : Continuous fun s => (f s : R)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  exact h.comp continuous_inv
private theorem conj_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ)
    (g : GL (Fin n) k) (s : Γ) :
    ((g * tw r χ s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      (χ s : k) • ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  simp only [Units.val_mul, tw_val, Matrix.mul_smul, Matrix.smul_mul]
private theorem flag_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) (H : Subgroup Γ)
    (κ : Fin n → ↥H →* kˣ) (g : GL (Fin n) k)
    (hg : ∀ s : ↥H, (∀ i j, j < i → (g * r s * g⁻¹ : GL (Fin n) k) i j = 0) ∧
      ∀ i, (g * r s * g⁻¹ : GL (Fin n) k) i i = (κ i s : k)) :
    W.HasFlag ((tw r χ).comp H.subtype) fun i => κ i * χ.comp H.subtype := by
  refine ⟨g, fun s => ⟨fun i j hij => ?_, fun i => ?_⟩⟩
  · have := (hg s).1 i j hij
    show ((g * tw r χ s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j = 0
    rw [conj_tw, Matrix.smul_apply]
    exact smul_eq_zero_of_right _ this
  · have := (hg s).2 i
    show ((g * tw r χ s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i = _
    rw [conj_tw, Matrix.smul_apply, smul_eq_mul, this]
    exact mul_comm _ _
private theorem pow_fixes (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] {M : ℕ} (hM : 1 ≤ M) :
    ∃ k : ℕ, 0 < k ∧ ∀ (s : G F Ω) (ζ : Ω), ζ ^ M = 1 → (s ^ k) ζ = ζ := by
  classical
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
    refine ((Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet).subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots (show 0 < M by omega)] using hζ
  haveI : Finite {ζ : Ω // ζ ^ M = 1} := hfin
  let f : G F Ω →* Equiv.Perm {ζ : Ω // ζ ^ M = 1} :=
    { toFun := fun s => Equiv.Perm.subtypePerm (s : Ω ≃ₐ[F] Ω).toEquiv fun x => by
        change s x ^ M = 1 ↔ x ^ M = 1
        rw [← map_pow, map_eq_one_iff _ (s : Ω ≃ₐ[F] Ω).injective]
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨Nat.card (Equiv.Perm {ζ : Ω // ζ ^ M = 1}), Nat.card_pos, fun s ζ hζ => ?_⟩
  have h1 : f (s ^ Nat.card (Equiv.Perm {ζ : Ω // ζ ^ M = 1})) = 1 := by
    rw [map_pow, pow_card_eq_one']
  exact congrArg (fun p : Equiv.Perm {ζ : Ω // ζ ^ M = 1} => (p ⟨ζ, hζ⟩ : Ω)) h1
theorem UpperTheory.V.Z.J.free_at_of_unlinked_of_automorphic_cyclotomic_twist :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (F Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
        ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (r : G F Ω →* GL (Fin n) (Qbar l)) (a : ℤ) (M : ℕ) (m : Fin n → ℤ), Continuous r →
          _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (Af.tw r (cycBar F Ω l ^ a)) → 1 ≤ M → StrictAnti m → Unl l M m r → FreeAt l r := by
  intro P F Ω _ _ _ _ _ _ l _ hl ι n hn r a M m hr haut hM hm hun A' hA'
  obtain ⟨w, hw', hw⟩ := (Formalism.VB.Cmp.exists_over_above_iff (K := F) A' l).2 hA'
  obtain ⟨A, hA, κ, ⟨χ, hk, ⟨g, hg⟩, hκ⟩, hne⟩ := hun w hw
  have hAl : A.valuation (l : Ω) < 1 := (Formalism.VB.Cmp.exists_over_above_iff (K := F) A l).1 ⟨w, hA, hw⟩
  obtain ⟨k, hk0, hkf⟩ := pow_fixes F Ω hM
  have hz : Continuous fun s : G F Ω => ((cycZ F Ω l s : ℤ_[l]ˣ) : ℤ_[l]) :=
    Units.continuous_val.comp (continuous_cycZ F Ω l)
  have hcyc : Continuous fun s : G F Ω => (cycBar F Ω l s : Qbar l) :=
    (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp (continuous_subtype_val.comp hz)
  have hχ : Continuous fun s : G F Ω => cycBar F Ω l s ^ a := (cont_units _ hcyc).zpow a
  have hc : Continuous (tw r (cycBar F Ω l ^ a)) := by
    refine cont_units _ ?_
    simp only [tw_val]
    exact (Units.continuous_val.comp hχ).smul (Units.continuous_val.comp hr)
  obtain ⟨s, hs1, hs2⟩ := _root_.UpperTheory.V.Z.Win.RR.exists_cycZ_eq_one_freeRatios_of_ne_mul_cycBar P F Ω l hl ι n hn _ hc haut A hAl
    (fun i => κ i * (cycBar F Ω l ^ a).comp (Dec (F := F) A).subtype) (fun i => m i + a) k
    (flag_tw r _ _ κ g hg)
    (fun i j hij => by have := hm hij; dsimp only; omega) hk0
    (fun i s hs => by
      show (κ i s * cycBar F Ω l s ^ a * cycBar F Ω l s ^ (-(m i + a))) ^ k = 1
      rw [hκ i s hs, mul_right_comm _ (χ i s), ← zpow_add, mul_right_comm, ← zpow_add, add_neg_cancel, zpow_zero, one_mul,
        ← map_pow]
      exact hk i _ (hkf s))
    (by
      intro i j e
      apply hne i j
      rw [mul_right_comm] at e
      exact mul_right_cancel e)
  have hb : cycBar F Ω l s = 1 := by
    simp only [cycBar, MonoidHom.comp_apply, hs1, map_one]
  have hfr : Pr.FreeRatios fun i => κ i s := by
    have e : (fun i => (κ i * (cycBar F Ω l ^ a).comp (Dec (F := F) A).subtype) s) = fun i => κ i s := by
      funext i
      show κ i s * cycBar F Ω l s ^ a = κ i s
      rw [hb, one_zpow, mul_one]
    rwa [e] at hs2
  obtain ⟨t, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) hA hw'
  refine ⟨t * s * t⁻¹, ?_, ?_, fun i => κ i s, hfr, ?_⟩
  · rw [mem_Dec, mul_smul, inv_smul_smul, mul_smul, mem_Dec.1 s.2]
  · rw [map_mul, map_mul, hs1, mul_one, map_inv, mul_inv_cancel]
  · have e : r (t * s * t⁻¹) = (r t * g⁻¹) * (g * r s * g⁻¹) * (r t * g⁻¹)⁻¹ := by
      rw [map_mul, map_mul, map_inv]; group
    show (r (t * s * t⁻¹)).val.charpoly = _
    rw [e, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj,
      Matrix.charpoly_of_upperTriangular _ (fun i j hij => (hg s).1 i j hij)]
    exact Finset.prod_congr rfl fun i _ => by rw [(hg s).2 i]
end
