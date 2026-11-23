import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueAdmissibleLocalComponentDefiniteUnit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GelfandPairSphericalVectorUnique
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Heckecomm
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLocalIntegralPointsMemOpenSubgroupDefiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedVectorGivesLocalComponentSphericalVectStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.SphLine

theorem finiteDimensional_fixed_of_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ G V} {τ : Representation ℂ G W} (T : ρ.Equiv τ) (U : Subgroup G)
    [FiniteDimensional ℂ (fixed ρ U)] : FiniteDimensional ℂ (fixed τ U) := by
  have hle : fixed τ U ≤ (fixed ρ U).map (T.toLinearEquiv : V →ₗ[ℂ] W) := by
    intro y hy
    refine ⟨T.toLinearEquiv.symm y, ?_, T.toLinearEquiv.apply_symm_apply y⟩
    show _ ∈ fixed ρ U
    rw [GlobalTheory.GelfandLine.mem_fixed_iff] at hy ⊢
    intro k hk
    apply T.toLinearEquiv.injective
    have h2 := LinearMap.congr_fun (T.isIntertwining' k) (T.toLinearEquiv.symm y)
    simp only [LinearMap.comp_apply] at h2
    rw [LinearEquiv.apply_symm_apply]
    convert h2.trans ?_ using 1
    · rfl
    · change τ k (T.toLinearEquiv (T.toLinearEquiv.symm y)) = y
      rw [LinearEquiv.apply_symm_apply]
      exact hy k hk
  exact Submodule.finiteDimensional_of_le hle

theorem exists_gelfand_anti : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E), ∃ θ : UL n w → UL n w, (∀ x y, θ (x * y) = θ y * θ x) ∧ (∀ x, θ (θ x) = x) ∧ ∀ g, ∃ a ∈ KL n w, ∃ b ∈ KL n w, θ g = a * g * b := by
  intro E _ _ _ hU n w
  by_cases hs : IsSplitAt w
  · have hUL : UL n w = ⊤ := if_pos hs
    have hm : ∀ g : GLw n w, g ∈ UL n w := fun g => by rw [hUL]; trivial
    refine ⟨fun g => ⟨Formalism.UG.P.heckecomm_tr g.1, hm _⟩, fun x y => Subtype.ext (Formalism.UG.P.heckecomm_tr_mul _ _),
      fun x => Subtype.ext (Formalism.UG.P.heckecomm_tr_tr _), fun g => ?_⟩
    obtain ⟨a, b, e⟩ := Formalism.UG.P.heckecomm_tr_dc Formalism.UG.P.cartan_decomposition_holds E w n g.1
    exact ⟨⟨a, hm _⟩, Subgroup.mem_subgroupOf.2 a.2, ⟨b, hm _⟩, Subgroup.mem_subgroupOf.2 b.2, Subtype.ext e⟩
  · obtain ⟨-, -, -, hns, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
    obtain ⟨-, ⟨ϖ, q, hq, -⟩, -⟩ := hns hs
    have hUL : UL n w = UJ (cj w) 1 := if_neg hs
    refine ⟨fun g => g⁻¹, fun x y => mul_inv_rev x y, fun x => inv_inv x, fun g => ?_⟩
    have hg : (g : GLw n w) ∈ UJ (cj w) ((1 : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
      rw [Units.val_one, ← hUL]; exact g.2
    have hJ : ∀ i j : Fin n, cj w (((1 : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) =
        ((1 : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) j i := by
      intro i j
      rw [Units.val_one, Matrix.one_apply, Matrix.one_apply]
      by_cases h : i = j
      · subst h; simp
      · rw [if_neg h, if_neg (Ne.symm h), map_zero]
    obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := GlobalTheory.UnitarySwap.inv_mem_doubleCoset hq (one_mem _) hJ hg
    have m1 : k₁ ∈ UL n w := by rw [hUL]; have := hk₁.1; rwa [Units.val_one] at this
    have m2 : k₂ ∈ UL n w := by rw [hUL]; have := hk₂.1; rwa [Units.val_one] at this
    exact ⟨⟨k₁, m1⟩, Subgroup.mem_subgroupOf.2 hk₁.2, ⟨k₂, m2⟩, Subgroup.mem_subgroupOf.2 hk₂.2, Subtype.ext e⟩

theorem finrank_fixed_KL_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ σ : ∀ w : Pl E, SmIrr (UL n w), (∀ w, IsCompU π w (σ w)) →
    ∀ᶠ w in cofinite, Module.finrank ℂ (fixed (σ w).ρ (KL n w)) = 1 := by
  intro E _ _ _ hU n hn π hπ σ hσ
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hπ.ne_bot
  let L : Subgroup (finU E n) :=
    { carrier := {k | RU E n k φ = φ}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hLo : IsOpen (L : Set (finU E n)) := (hπ.aut φ hφ).level
  have hunr : ∀ᶠ w in cofinite, IsUnramU π w := by
    filter_upwards [GlobalTheory.T.eventually_localIntegralPoints_mem_openSubgroup_definiteUnitary E n L hLo] with w hw
    exact ⟨φ, hφ, hφ0, fun x hx hxK => hw x hx hxK hx.1⟩
  have hadm : ∀ w, IsAdmissible (σ w).ρ := by
    intro w
    obtain ⟨⟨σ₀, hσ₀, hfd⟩, huniq⟩ := GlobalTheory.BCT.LocCompU.exists_unique_locComp E hU n hn π hπ w
    obtain ⟨T⟩ := huniq σ₀ (σ w) hσ₀ (hσ w)
    refine ⟨(σ w).smooth, fun K hKo _ => ?_⟩
    haveI := hfd K hKo
    exact finiteDimensional_fixed_of_equiv T K
  filter_upwards [hunr] with w hw
  have hne := GlobalTheory.T.unramifiedVector_gives_localComponent_sphericalVector E hU n π hπ w (σ w) (hσ w) hw
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨θ, h1, h2, h3⟩ := exists_gelfand_anti E hU n w
  obtain ⟨hKo, hKc⟩ := GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w
  have := GlobalTheory.fixed_eq_span_of_gelfandPair (UL n w) (KL n w) hKo hKc θ h1 h2 h3 (σ w).V (σ w).ρ (σ w).irred (hadm w) x hx hx0
  rw [this, finrank_span_singleton hx0]

end GlobalTheory.BCT.SphLine
