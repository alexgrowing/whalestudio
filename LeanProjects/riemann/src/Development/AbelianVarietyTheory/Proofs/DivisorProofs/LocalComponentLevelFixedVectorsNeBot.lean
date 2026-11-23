import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueAdmissibleLocalComponentDefiniteUnit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorAtSplitPlaceIsoty
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.LocFix

theorem fixed_ne_bot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π →
    (∀ v, HasWeightAt π v.embedding (lam v)) → π ⊓ fixed (RF E n) (globLev S K') ≠ ⊥ →
    ∀ w ∈ S, ∀ σ : SmIrr (UL n w), IsCompU π w σ → fixed σ.ρ (K' w) ≠ ⊥ := by
  intro E _ _ _ hU n _ S hS lam K' hK' π hπ _ hne w hw σ hσ
  classical
  obtain ⟨p, hp, -, f, hf0, hfm, hf⟩ := hσ
  obtain ⟨e, he⟩ := GlobalTheory.BCT.LocCompU.exists_equiv hU n w
  have hpe : ∀ x, p x = e x := fun x => Subtype.ext ((hp x).trans (he x).symm)
  have hps : Function.Surjective p := fun g => ⟨e.symm g, by rw [hpe, e.apply_symm_apply]⟩
  obtain ⟨r, -, -, hr⟩ := GlobalTheory.DefU.LocRet.exists_ret E n w
  let π' : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
  let F : Representation.IntertwiningMap (σ.ρ.comp p) (π'.rep.comp (locU n w).subtype) :=
    ⟨f.codRestrict π hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
  have hF0 : F ≠ 0 := fun h =>
    hf0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))
  have hσirr := GlobalTheory.BCT.LocCompU.isIrreducible_comp_of_surjective σ.ρ p hps σ.irred
  have htop := (GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (locU n w) π σ.V σ.V π'.rep (locU n w).subtype
    (σ.ρ.comp p) (σ.ρ.comp p) π'.isIrreducible_rep hσirr hσirr (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1

  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hφπ : φ ∈ π := (Submodule.mem_inf.1 hφ).1
  have hφfix : φ ∈ fixed (RF E n) (globLev S K') := (Submodule.mem_inf.1 hφ).2

  have hfixx : ∀ x : locU n w, p x ∈ K' w → RU E n (x : UA E n) φ = φ := by
    intro x hx
    have hxfin : (x : UA E n) ∈ finU E n := (Subgroup.mem_inf.1 x.2).1
    have hy : (⟨x, hxfin⟩ : finU E n) ∈ globLev S K' := by
      simp only [globLev, Subgroup.mem_iInf]
      intro w' hw'
      rw [Subgroup.mem_comap, Subgroup.mem_map]
      by_cases hww : w' = w
      · subst hww
        exact ⟨p x, hx, hp x⟩
      · have hund : w'.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E)) :=
          fun h => hww ((hS w).unique ⟨hw', h⟩ ⟨hw, rfl⟩)
        have h1 : cLoc w' (x : UA E n) = 1 := by
          have h2 := (Subgroup.mem_inf.1 x.2).2
          rw [Subgroup.mem_iInf] at h2
          exact Subgroup.mem_iInf.1 (h2 w') hund
        exact ⟨1, (K' w').one_mem, by simp [h1]⟩
    have h3 : RF E n ⟨x, hxfin⟩ φ = φ := by simpa using hφfix ⟨_, hy⟩
    exact h3
  have hmem : (⟨φ, hφπ⟩ : π) ∈ ⨆ F : Representation.IntertwiningMap (σ.ρ.comp p) (π'.rep.comp (locU n w).subtype),
      LinearMap.range F.toLinearMap := by
    rw [htop]; trivial
  obtain ⟨c, hc, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hmem
  choose u hu using fun i => LinearMap.mem_range.1 (hc i)
  let ρK : Representation ℂ (K' w) σ.V := σ.ρ.comp (K' w).subtype
  have hsumF : ∀ g : K' w, ∑ i ∈ c.support, (i.toLinearMap : σ.V →ₗ[ℂ] π) (ρK g (u i)) =
      (((1 : K' w →* ℂˣ) g : ℂˣ) : ℂ) • (⟨φ, hφπ⟩ : π) := by
    intro g
    have hpx : p (e.symm g) = g := by rw [hpe, e.apply_symm_apply]
    have hterm : ∀ i ∈ c.support, (i.toLinearMap : σ.V →ₗ[ℂ] π) (ρK g (u i)) = π'.rep (e.symm g : UA E n) (c i) := by
      intro i _
      have h1 := LinearMap.congr_fun (i.isIntertwining' (e.symm g)) (u i)
      simp only [LinearMap.comp_apply, MonoidHom.comp_apply, Subgroup.coe_subtype] at h1
      rw [hpx] at h1
      rw [← hu i]
      exact h1
    rw [Finset.sum_congr rfl hterm, ← map_sum]
    have hs : ∑ i ∈ c.support, c i = (⟨φ, hφπ⟩ : π) := hsum
    rw [hs]
    apply Subtype.ext
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    exact hfixx (e.symm g) (by rw [hpx]; exact g.2)
  let H : Subgroup (K' w) := ⨅ i ∈ c.support, GlobalTheory.LocVec.stabSub ρK (u i)
  have hHo : IsOpen (H : Set (K' w)) := by
    simp only [H, Subgroup.coe_iInf]
    refine isOpen_biInter_finset fun i _ => ?_
    have : (GlobalTheory.LocVec.stabSub ρK (u i) : Set (K' w)) =
        (fun g : K' w => (g : UL n w)) ⁻¹' {x | σ.ρ x (u i) = u i} := rfl
    rw [this]
    exact (σ.smooth (u i)).preimage continuous_subtype_val
  have hKc := (GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).2
  haveI : H.FiniteIndex := GlobalTheory.LocVec.finiteIndex_of_isOpen (K' w) hKc (fun g hg => (hK'.1 w).2.1 hg) H hHo
  obtain ⟨v, hv0, hv⟩ := GlobalTheory.LocVec.exists_eigen_of_sum ρK (1 : K' w →* ℂˣ) H (fun h _ => MonoidHom.mem_ker.2 rfl)
    c.support u (fun i hi h hh => (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hh i) hi))
    (fun i => (i.toLinearMap : σ.V →ₗ[ℂ] π)) ⟨φ, hφπ⟩ (fun h => hφ0 (congrArg Subtype.val h)) hsumF
  have hvmem : v ∈ fixed σ.ρ (K' w) := fun h => hv h
  intro hb
  rw [hb] at hvmem
  exact hv0 ((Submodule.mem_bot ℂ).1 hvmem)

end GlobalTheory.BCT.LocFix
