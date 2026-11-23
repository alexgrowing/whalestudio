import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ProjEx
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenFormEqFiniteSumAutRepEigenForms
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.sumRep_of :
    UpperTheory.Gal.Wt.SumRep := by
  intro E _ _ _ a S hfin hS
  classical
  obtain ⟨B₀, -, -, hd, hi⟩ := GlobalTheory.T.exists_invariant_positive_petersson_form E a
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (autU E a).subtype (autU E a).ker_subtype
  have hpv : ∀ (φ : UA E a → ℂ) (h : IsAutFormU φ), p φ = ⟨φ, h⟩ := fun φ h =>
    LinearMap.congr_fun hp (⟨φ, h⟩ : autU E a)
  let B : (UA E a → ℂ) →ₗ⋆[ℂ] (UA E a → ℂ) →ₗ[ℂ] ℂ := (B₀.compl₂ p).comp p
  have hB : ∀ φ φ', B φ φ' = B₀ (p φ) (p φ') := fun _ _ => rfl
  have hsum : ∀ φ : UA E a → ℂ, IsAutFormU φ → φ ∈ sSup {U : Submodule ℂ (UA E a → ℂ) | IsAutRepU U} := by
    intro φ hφ
    have h := UpperTheory.mem_iSup_automorphicReps_of_invariant_form E a B (fun f hf h0 => by
        rw [hB, hpv f hf] at h0
        exact congrArg Subtype.val (hd _ h0))
      (fun x f g hf hg => by
        rw [hB, hB, hpv f hf, hpv g hg, hpv _ (RU_mem_autU x f hf), hpv _ (RU_mem_autU x g hg)]
        exact hi x ⟨f, hf⟩ ⟨g, hg⟩) φ hφ
    exact (iSup_le fun σ => le_sSup σ.2 : _ ≤ sSup {U : Submodule ℂ (UA E a → ℂ) | IsAutRepU U}) h
  let b := Module.finBasis ℂ S
  have hex : ∀ i, ∃ s : Finset (Submodule ℂ (UA E a → ℂ)), (↑s ⊆ {U : Submodule ℂ (UA E a → ℂ) | IsAutRepU U}) ∧
      (b i : UA E a → ℂ) ∈ ⨆ U ∈ s, U :=
    fun i => Submodule.mem_sSup_iff_exists_finset.1 (hsum _ (hS _ (b i).2))
  choose s hsA hsm using hex
  let s0 := Finset.univ.biUnion s
  have hs0A : ∀ U ∈ s0, IsAutRepU U := by
    intro U hU
    obtain ⟨i, -, hi'⟩ := Finset.mem_biUnion.1 hU
    exact hsA i hi'
  obtain ⟨t, hts, hti, htS⟩ := GlobalTheory.EigenDecomp.exists_indep s0 hs0A
  refine ⟨t, fun U hU => hs0A U (hts hU), hti, ?_⟩
  intro φ hφ
  rw [htS]
  have e : φ = ∑ i, (b.repr ⟨φ, hφ⟩ i) • (b i : UA E a → ℂ) := by
    have h := congrArg Subtype.val (b.sum_repr ⟨φ, hφ⟩)
    rw [Submodule.coe_sum] at h
    exact h.symm
  rw [e]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  refine (iSup₂_le fun U hU => le_sSup ?_ : (⨆ U ∈ s i, U) ≤ sSup (s0 : Set (Submodule ℂ (UA E a → ℂ)))) (hsm i)
  exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hU⟩)
