import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrrParIffCuspidalProduct
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspidalMultiplicityEqDiscreteSeriesModelMapsStatement

noncomputable section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SpecFinite

open GlobalTheory.CuspMult GlobalTheory.PRep

section Abstract

variable {H X : Type} [Group H] [TopologicalSpace H] [AddCommGroup X] [Module ℂ X]

theorem simple_asSubmodule {ρ : Representation ℂ H X} (U : Subrepresentation ρ) (hU : U.toRepresentation.IsIrreducible) :
    IsSimpleModule (MonoidAlgebra ℂ H) U.asSubmodule := by
  haveI : IsSimpleModule (MonoidAlgebra ℂ H) U.toRepresentation.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).1 hU
  exact IsSimpleModule.congr (GlobalTheory.RepCount.subEquiv U).symm

theorem exists_sub_equiv {W : Type} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ H W} {ρ : Representation ℂ H X}
    (h1 : σ.IsIrreducible) {f : W →ₗ[ℂ] X} (hf : ∀ g s, f (σ g s) = ρ g (f s)) (h0 : f ≠ 0) :
    ∃ U : Subrepresentation ρ, U.toSubmodule = LinearMap.range f ∧ Function.Injective f ∧
      ∃ e : W ≃ₗ[ℂ] U.toSubmodule, (∀ s, (e s : X) = f s) ∧ ∀ g s, e (σ g s) = U.toRepresentation g (e s) := by
  let F := f.intertwiningMap_of_isIntertwiningMap σ ρ hf
  have hi : Function.Injective f := by
    rcases Representation.IsIrreducible.injective_or_eq_zero F with hi | hz
    · exact hi
    · exact absurd (LinearMap.ext fun s => DFunLike.congr_fun hz s) h0
  exact ⟨F.range, rfl, hi, LinearEquiv.ofInjective f hi, fun s => rfl, fun g s => Subtype.ext (hf g s)⟩

theorem rank_homInto_lt {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ H W) (ρ : Representation ℂ H X)
    (C : Submodule ℂ X) (K : Subgroup H) (hA : FiniteDimensional ℂ ↥(C ⊓ fixed ρ K)) (h1 : σ.IsIrreducible)
    {x : W} (hx0 : x ≠ 0) (hx : ∀ k ∈ K, σ k x = x) : Module.rank ℂ (homInto σ ρ C) < Cardinal.aleph0 := by
  let ev : homInto σ ρ C →ₗ[ℂ] ↥(C ⊓ fixed ρ K) :=
    { toFun := fun f => ⟨(f : W →ₗ[ℂ] X) x, f.2.1 x, GlobalTheory.CuspDec.mem_fixed.2 fun k hk => by rw [← f.2.2, hx k hk]⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective ev := by
    refine (injective_iff_map_eq_zero ev).2 fun f hf => ?_
    by_contra hne
    obtain ⟨U, -, hi, -⟩ := exists_sub_equiv h1 f.2.2 (fun h => hne (Subtype.ext h))
    have h0 : (f : W →ₗ[ℂ] X) x = (f : W →ₗ[ℂ] X) 0 := by
      rw [map_zero]
      exact congrArg Subtype.val hf
    exact hx0 (hi h0)
  haveI := FiniteDimensional.of_injective ev hinj
  exact Module.rank_lt_aleph0 ℂ _

theorem finite_classes (ρ : Representation ℂ H X) (C : Submodule ℂ X) (K : Subgroup H)
    (hA : FiniteDimensional ℂ ↥(C ⊓ fixed ρ K)) :
    ∃ (n : ℕ) (Ws : Fin n → Type) (_ : ∀ i, AddCommGroup (Ws i)) (_ : ∀ i, Module ℂ (Ws i))
      (σs : ∀ i, Representation ℂ H (Ws i)),
      ((∀ i, (σs i).IsIrreducible) ∧ (∀ i, IsAdmissible (σs i)) ∧ ∀ i j, i ≠ j → IsEmpty ((σs i).Equiv (σs j))) ∧
      ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ H W), σ.IsIrreducible → IsAdmissible σ →
        homInto σ ρ C ≠ ⊥ → (∃ x : W, x ≠ 0 ∧ ∀ k ∈ K, σ k x = x) → ∃ i, Nonempty (σ.Equiv (σs i)) := by
  classical
  let S : Set (Subrepresentation ρ) := {U | U.toSubmodule ≤ C ∧ U.toRepresentation.IsIrreducible ∧
    IsAdmissible U.toRepresentation ∧ U.toSubmodule ⊓ fixed ρ K ≠ ⊥}
  let comp : Subrepresentation ρ → Submodule (MonoidAlgebra ℂ H) ρ.asModule :=
    fun U => isotypicComponent (MonoidAlgebra ℂ H) ρ.asModule U.asSubmodule
  let T : Set (Submodule (MonoidAlgebra ℂ H) ρ.asModule) := comp '' S
  have hT : sSupIndep T := (sSupIndep_isotypicComponents (MonoidAlgebra ℂ H) ρ.asModule).mono (by
    rintro _ ⟨U, hU, rfl⟩
    exact ⟨U.asSubmodule, simple_asSubmodule U hU.2.1, rfl⟩)
  have hy : ∀ c : T, ∃ y : ↥(C ⊓ fixed ρ K), y ≠ 0 ∧
      ρ.asModuleEquiv.symm (y : X) ∈ (c : Submodule (MonoidAlgebra ℂ H) ρ.asModule) := by
    rintro ⟨_, U, hU, rfl⟩
    obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hU.2.2.2
    exact ⟨⟨y, hU.1 hy.1, hy.2⟩, fun h => hy0 (congrArg Subtype.val h), U.asSubmodule.le_isotypicComponent hy.1⟩
  choose y hy0 hyc using hy
  have hsm : ∀ (c : T) (a : ℂ), ρ.asModuleEquiv.symm ((a • y c : ↥(C ⊓ fixed ρ K)) : X) ∈
      (c : Submodule (MonoidAlgebra ℂ H) ρ.asModule) := fun c a => by
    rw [Submodule.coe_smul, map_smul]
    exact Submodule.smul_of_tower_mem _ a (hyc c)
  have hli : LinearIndependent ℂ y := by
    rw [linearIndependent_iff']
    intro s g hs i hi
    have hx : ρ.asModuleEquiv.symm ((g i • y i : ↥(C ⊓ fixed ρ K)) : X) ∈
        (i : Submodule (MonoidAlgebra ℂ H) ρ.asModule) ⊓ sSup (T \ {(i : Submodule (MonoidAlgebra ℂ H) ρ.asModule)}) := by
      refine ⟨hsm i (g i), ?_⟩
      have he : (g i • y i : ↥(C ⊓ fixed ρ K)) = - ∑ j ∈ s.erase i, g j • y j := by
        rw [eq_neg_iff_add_eq_zero, Finset.add_sum_erase s (fun j => g j • y j) hi, hs]
      rw [he, Submodule.coe_neg, Submodule.coe_sum, map_neg, map_sum]
      refine Submodule.neg_mem _ (Submodule.sum_mem _ fun j hj => ?_)
      refine (le_sSup (show (j : Submodule (MonoidAlgebra ℂ H) ρ.asModule) ∈ T \ {(i : Submodule (MonoidAlgebra ℂ H) ρ.asModule)} from
          ⟨j.2, fun h => Finset.ne_of_mem_erase hj (Subtype.ext h)⟩) :
        (j : Submodule (MonoidAlgebra ℂ H) ρ.asModule) ≤ _) (hsm j (g j))
    rw [(hT i.2).eq_bot, Submodule.mem_bot, LinearEquiv.map_eq_zero_iff, Submodule.coe_eq_zero, smul_eq_zero] at hx
    exact hx.resolve_right (hy0 i)
  haveI : Finite T := hli.finite
  haveI := Fintype.ofFinite T
  let e := Fintype.equivFin T
  have hrep : ∀ c : T, ∃ U ∈ S, comp U = c := fun c => c.2
  choose U hUS hUc using hrep
  refine ⟨Fintype.card T, fun i => ↥(U (e.symm i)).toSubmodule, fun i => inferInstance, fun i => inferInstance,
    fun i => (U (e.symm i)).toRepresentation, ⟨fun i => (hUS _).2.1, fun i => (hUS _).2.2.1, fun i j hij => ⟨fun φ => hij ?_⟩⟩, ?_⟩
  · obtain ⟨ψ⟩ := (GlobalTheory.CuspFactor.nonempty_equiv_iff _ _).1 ⟨φ⟩
    have h3 := ((GlobalTheory.RepCount.subEquiv _).symm.trans (ψ.trans (GlobalTheory.RepCount.subEquiv _))).isotypicComponent_eq
      (M := ρ.asModule)
    exact e.symm.injective (Subtype.ext ((hUc _).symm.trans (h3.trans (hUc _))))
  · rintro W _ _ σ h1 h2 hne ⟨x, hx0, hx⟩
    obtain ⟨f, hf, hf0⟩ := (Submodule.ne_bot_iff _).1 hne
    obtain ⟨V, hV, hi, ev, hev, heq⟩ := exists_sub_equiv h1 hf.2 hf0
    haveI : IsSimpleModule (MonoidAlgebra ℂ H) σ.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule _).1 h1
    let ψ : σ.asModule ≃ₗ[MonoidAlgebra ℂ H] V.toRepresentation.asModule :=
      LinearEquiv.ofBijective (GlobalTheory.RepCount.modMap ev.toLinearMap heq) ev.bijective
    have hVirr : V.toRepresentation.IsIrreducible :=
      (Representation.irreducible_iff_isSimpleModule_asModule _).2 (IsSimpleModule.congr ψ.symm)
    have hVS : V ∈ S := by
      refine ⟨?_, hVirr, GlobalTheory.RepCount.isAdmissible_of_injective ev.symm.toLinearMap (fun g s => ?_) ev.symm.injective h2, ?_⟩
      · rw [hV]
        rintro _ ⟨s, rfl⟩
        exact hf.1 s
      · rw [LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_eq, heq, LinearEquiv.apply_symm_apply]
      · rw [Submodule.ne_bot_iff]
        refine ⟨f x, ⟨hV ▸ ⟨x, rfl⟩, GlobalTheory.CuspDec.mem_fixed.2 fun k hk => by rw [← hf.2, hx k hk]⟩, fun h => hx0 (hi ?_)⟩
        rw [h, map_zero]
    refine ⟨e ⟨comp V, V, hVS, rfl⟩, ?_⟩
    show Nonempty (σ.Equiv (U (e.symm (e ⟨comp V, V, hVS, rfl⟩))).toRepresentation)
    generalize hc : e.symm (e ⟨comp V, V, hVS, rfl⟩) = c
    rw [Equiv.symm_apply_apply] at hc
    haveI := simple_asSubmodule V hVirr
    haveI := simple_asSubmodule (U c) (hUS c).2.1
    have hle : (U c).asSubmodule ≤ comp V :=
      ((U c).asSubmodule.le_isotypicComponent).trans_eq ((hUc c).trans (congrArg Subtype.val hc).symm)
    obtain ⟨χ⟩ := isIsotypicOfType_submodule_iff.mp
      (IsIsotypicOfType.isotypicComponent (MonoidAlgebra ℂ H) ρ.asModule V.asSubmodule) _ hle
    exact (GlobalTheory.CuspFactor.nonempty_equiv_iff _ _).2
      ⟨(ψ.trans (GlobalTheory.RepCount.subEquiv V)).trans (χ.symm.trans (GlobalTheory.RepCount.subEquiv _).symm)⟩

end Abstract

theorem specFin : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.DixmierMalliavinFactorisation →
    SpecFin := by
  intro hQ hP hDM D V S M μ _ _
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  have hm : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), IsAdmissible σ →
      mCuspDS μ σ M = Module.rank ℂ (homInto σ (finRep M) (allMaps θ M)) := fun W _ _ σ h =>
    (GlobalTheory.T.cuspidalMultiplicity_eq_discreteSeriesModel_maps hQ hP hDM D θ hθ V S M μ W σ h.1).symm
  refine ⟨fun W _ _ σ h1 h2 => ?_, fun K hK => ?_⟩
  · haveI := GlobalTheory.CuspFactor.nontrivial_of_irr σ h1
    obtain ⟨x, hx0⟩ := exists_ne (0 : W)
    let St : Subgroup (GfC V) :=
      { carrier := {g | σ g x = x}
        mul_mem' := fun {a b} ha hb => by
          show σ (a * b) x = x
          rw [map_mul, Module.End.mul_apply, hb, ha]
        one_mem' := by simp
        inv_mem' := fun {a} ha => by
          show σ a⁻¹ x = x
          conv_lhs => rw [← ha]
          simp }
    rw [hm W σ h2]
    exact rank_homInto_lt σ (finRep M) (allMaps θ M) St (GlobalTheory.CuspDec.finiteDimensional_fixed hP hθ St (h2.1 x)) h1 hx0
      (fun k hk => hk)
  · obtain ⟨n, Ws, i1, i2, σs, hs, hcov⟩ :=
      finite_classes (finRep M) (allMaps θ M) K (GlobalTheory.CuspDec.finiteDimensional_fixed hP hθ K hK)
    refine ⟨n, Ws, i1, i2, σs, hs, fun W _ _ σ h1 h2 hm0 hx => hcov W σ h1 h2 (fun h => hm0 ?_) hx⟩
    rw [hm W σ h2, h, rank_bot]

end GlobalTheory.SpecFinite

end
