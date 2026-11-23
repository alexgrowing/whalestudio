import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsHostFrame
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia Module

private theorem twDual_inv_eq_zero {Γ k M : Type} [Group Γ] [Field k] [AddCommGroup M] [Module k M]
    (N : ℕ) [Module (ZMod N) M] (μ : Γ →* (ZMod N)ˣ) (ρ : Representation k Γ M)
    (g : Γ) (a : k) (n : ℕ) (hg : ∀ m, ρ g m = a • m) (hn : (n : ZMod N) = μ g) (han : a ≠ (n : k))
    (y : H0 (twDual μ (GlobalTheory.Published.zmodRep N ρ))) : y = 0 := by
  obtain ⟨φ, hφ⟩ := y
  apply Subtype.ext
  have h1 : twDual μ (GlobalTheory.Published.zmodRep N ρ) g φ = φ := hφ _
  show φ = 0
  ext x
  set m : M := (a - (n : k))⁻¹ • x with hm
  have hx : x = a • m - n • m := by
    rw [← Nat.cast_smul_eq_nsmul k, ← sub_smul, hm, smul_smul,
      mul_inv_cancel₀ (sub_ne_zero.2 han), one_smul]
  have h3 := congrArg (fun ψ : TDual (ZMod N) M => ψ (GlobalTheory.Published.zmodRep N ρ g m)) h1
  simp only [twDual_apply] at h3
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
    ← hn] at h3
  have h4 : GlobalTheory.Published.zmodRep N ρ g m = a • m := hg m
  rw [h4] at h3
  show φ x = 0
  rw [hx]
  refine (LinearMap.map_sub (φ : Module.Dual (ZMod N) M) _ _).trans (sub_eq_zero.mpr ?_)
  refine h3.symm.trans ?_
  rw [← nsmul_eq_mul]
  exact (map_nsmul (F := Module.Dual (ZMod N) M) φ n m).symm

theorem UpperTheory.global_cohomology_finite_set :
    GlobalTheory.Published.PoitouTateNormalised → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (k M : Type) [Field k] [Finite k] [CharP k l] [AddCommGroup M] [Module k M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset Pl) (A : S → ValuationSubring Ω) (ρ : Representation k (Gam Ω S) M),
                 ContainsAbove S l → (∀ v, Formalism.ConjugateSelfDual.IsPlaceOver (A v) v.1) → ContAction ρ →
                 (∃ (σ : Formalism.ConjugateSelfDual.G ℚ Ω) (a : k) (n : ℕ), (∀ m, ρ (toGS Ω _ σ) m = a • m) ∧ (n : ZMod (l ^ 1)) = (cycMod ℚ Ω l 1 σ : (ZMod (l ^ 1))ˣ) ∧ a ≠ (n : k)) →
                 ∀ κ : ∀ v : S, Z2 (ρ.comp ((toGS Ω _).comp (Dec (F := ℚ) (A v)).subtype) : Representation k (Dec (F := ℚ) (A v)) M), ∃ z : Z2 ρ, ∀ v : S,
                   (fun p : Dec (F := ℚ) (A v) × Dec (F := ℚ) (A v) => z.1 (toGS Ω _ p.1.1, toGS Ω _ p.2.1)) - (κ v).1 ∈
                     B2 (ρ.comp ((toGS Ω _).comp (Dec (F := ℚ) (A v)).subtype) : Representation k (Dec (F := ℚ) (A v)) M) := by
  intro hPT Ω _ _ _ l _ hl k M _ _ _ _ _ _ _ _ S A ρ hS hA hρ hσ κ
  obtain ⟨σ, a, n, hσa, hn, han⟩ := hσ
  have hM : ∀ m : M, (l ^ 1) • m = 0 := fun m => by
    rw [pow_one, ← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]
  letI : Module (ZMod (l ^ 1)) M := AddCommGroup.zmodModule hM
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ 1)
  obtain ⟨μ, hμ⟩ := GlobalTheory.Published.PoitouTate.exists_lift_cycMod (F := ℚ) (Ω := Ω) (l := l) (r := 1) hS
  obtain ⟨inv, -, h⟩ := hPT ℚ Ω l 1 (Or.inl hl) Nat.one_pos ζ hζ
  have hex := (h S hS A hA μ hμ M (GlobalTheory.Published.zmodRep (l ^ 1) ρ) hρ).1
  have hμσ : μ (toGS Ω _ σ) = cycMod ℚ Ω l 1 σ := DFunLike.congr_fun hμ σ
  obtain ⟨z, hz⟩ := (hex.mem_range_localization_H2_iff
    (fun v => Submodule.Quotient.mk ⟨(κ v).1, (κ v).2⟩)).2 (fun y => by
      rw [twDual_inv_eq_zero (l ^ 1) μ ρ _ a n hσa (by rw [hμσ]; exact hn) han y]
      simp only [map_zero, Finset.sum_const_zero])
  induction z using Submodule.Quotient.induction_on with
  | H z =>
    refine ⟨⟨z.1, z.2⟩, fun v => ?_⟩
    have e : (Submodule.Quotient.mk (restrictCocycles2 (GlobalTheory.Published.zmodRep (l ^ 1) ρ) (locFam S A v)
        (continuous_locFam S A v) z) : H2 ((GlobalTheory.Published.zmodRep (l ^ 1) ρ).comp (locFam S A v))) =
        Submodule.Quotient.mk ⟨(κ v).1, (κ v).2⟩ := congrFun hz v
    obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem _ _).1 ((Submodule.Quotient.eq _).1 e)
    exact (separated_dvr_second_cohomology_mem _ _).2 ⟨c, hc, hcf⟩
