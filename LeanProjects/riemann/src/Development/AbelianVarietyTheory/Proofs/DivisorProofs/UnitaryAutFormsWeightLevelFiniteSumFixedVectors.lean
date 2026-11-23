import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalDefiniteUnitaryLevelForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenProductOfLocalLevelsUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDimensionalArchRestrictionSpaceOfWeiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedVectorsIrreducibleSubrepDecompositionStatement

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.BCT.forms_decomp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → FiniteDimensional ℂ (forms S lam K') ∧ ∃ (ι : Type) (_ : Fintype ι) (π : ι → Submodule ℂ (UA E n → ℂ)), (∀ i, IsAutRepU (π i) ∧ (∀ v, HasWeightAt (π i) v.embedding (lam v)) ∧ π i ⊓ fixed (RF E n) (globLev S K') ≠ ⊥) ∧ iSupIndep (fun i => π i ⊓ fixed (RF E n) (globLev S K')) ∧ (⨆ i, π i ⊓ fixed (RF E n) (globLev S K')) = forms S lam K' ∧ ∀ π₀, IsAutRepU π₀ → (∀ v, HasWeightAt π₀ v.embedding (lam v)) → π₀ ⊓ fixed (RF E n) (globLev S K') ≠ ⊥ → ∃ i, ∀ w (σ : SmIrr (UL n w)), IsCompU π₀ w σ → IsCompU (π i) w σ := by
  intro E _ _ _ hU n _ S _ lam K' hK
  have hLo := GlobalTheory.T.isOpen_productOfLocalLevelsUnitary E hU n S K' hK
  obtain ⟨C, hCf, hC⟩ := GlobalTheory.T.exists_finiteDimensional_archRestriction_space_of_weight E n lam
  have hcls : ∀ L : Subgroup (finU E n), IsOpen (L : Set (finU E n)) → ∃ S : Finset (UA E n), ∀ g : UA E n,
      ∃ γ ∈ ratU E n, ∃ s ∈ S, ∃ k ∈ L, ∃ y ∈ infU E n, g = γ * s * (k : UA E n) * y := by
    intro L hL
    obtain ⟨S₀, hS₀⟩ := GlobalTheory.DefU.ClassFin.classSet_finite E n L hL
    refine ⟨S₀, fun g => ?_⟩
    obtain ⟨γ, hγ, s, hs, x, hx, k, hk, rfl⟩ := hS₀ g
    exact ⟨γ, hγ, s, hs, k, hk, x, hx, by rw [mul_assoc (γ * s) x, ← GlobalTheory.DefU.fin_mul_inf k.2 hx, ← mul_assoc]⟩
  have hfin := GlobalTheory.UnitaryBC.finiteDimensional_levelForms E n hcls _ hLo C hCf
  have hmemF : ∀ φ : UA E n → ℂ, φ ∈ fixed (RF E n) (globLev S K') ↔ ∀ k ∈ globLev S K', RU E n (k : UA E n) φ = φ := by
    intro φ
    change (∀ h : globLev S K', _) ↔ _
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    exact ⟨fun h k hk => h ⟨k, hk⟩, fun h k => h k.1 k.2⟩
  have hle : forms S lam K' ≤ Submodule.span ℂ {ψ : UA E n → ℂ | (∀ γ ∈ ratU E n, ∀ g, ψ (γ * g) = ψ g) ∧
      (∀ k ∈ globLev S K', ∀ g, ψ (g * (k : UA E n)) = ψ g) ∧ ∀ g, (fun y : infU E n => ψ (g * (y : UA E n))) ∈ C} := by
    refine iSup₂_le fun π hπ φ hφ => Submodule.subset_span ⟨(hπ.1.aut φ hφ.1).left, fun k hk g => ?_, hC π hπ.1 hπ.2 φ hφ.1⟩
    exact congrFun ((hmemF φ).1 hφ.2 k hk) g
  haveI : FiniteDimensional ℂ (forms S lam K') := Submodule.finiteDimensional_of_le hle
  refine ⟨inferInstance, ?_⟩
  obtain ⟨ι, hι, π, h1, h2, h3, h4⟩ := GlobalTheory.T.fixed_vectors_irreducible_subrep_decomposition (RU E n) {x | ∃ k ∈ globLev S K', x = ((k : finU E n) : UA E n)}
    (fixed (RF E n) (globLev S K')) (fun φ => by
      rw [hmemF]
      exact ⟨fun h x ⟨k, hk, e⟩ => e ▸ h k hk, fun h k hk => h _ ⟨k, hk, rfl⟩⟩)
    {π | IsAutRepU π ∧ ∀ v, HasWeightAt π v.embedding (lam v)}
    (fun P hP => ⟨hP.1.ne_bot, hP.1.stable, hP.1.irred⟩) (by assumption)
  refine ⟨ι, hι, π, fun i => ⟨(h1 i).1.1, (h1 i).1.2, (h1 i).2⟩, h2, h3, fun π₀ hπ₀ hw₀ hne => ?_⟩
  obtain ⟨i, T, hT1, hT2, hT3⟩ := h4 π₀ ⟨hπ₀, hw₀⟩ hne
  refine ⟨i, fun w σ ⟨p, hp, hirr, f, hf0, hfπ, hfe⟩ => ⟨p, hp, hirr, T ∘ₗ f, fun h => hf0 ?_, fun v => hT1 _ (hfπ v), fun x v => ?_⟩⟩
  · ext v : 1
    exact hT2 _ (hfπ v) (LinearMap.congr_fun h v)
  · rw [LinearMap.comp_apply, hfe x v]
    exact hT3 _ _ (hfπ v)
