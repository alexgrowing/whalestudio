import Mathlib
import GroundTheory.ProfiniteCohomology.PoincarePairs.Devissage
import GroundTheory.ProfiniteCohomology.EulerChar
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Dimension
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

noncomputable section

attribute [local instance 2000] Rep.hV2

section Trace

variable {k G : Type u} [CommRing k] [Group G] (U : Subgroup G) [U.FiniteIndex] (A : Rep.{u} k G)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

open Classical in

def coindTracePreimage (a : A) : Rep.coind U.subtype (Rep.res U.subtype A) :=
  ⟨fun g => if g ∈ U then A.ρ g a else 0, fun u g => by
    beta_reduce
    by_cases hg : g ∈ U
    · have hug : U.subtype u * g ∈ U := U.mul_mem u.2 hg
      rw [if_pos hug, if_pos hg, map_mul, Module.End.mul_apply]
      rfl
    · have hug : U.subtype u * g ∉ U := fun h => hg (by
        have := U.mul_mem (U.inv_mem u.2) h
        rwa [Subgroup.coe_subtype, ← mul_assoc, inv_mul_cancel, one_mul] at this)
      rw [if_neg hug, if_neg hg, map_zero]⟩

theorem coindTrace_coindTracePreimage (a : A) : (coindTrace U A).hom (coindTracePreimage U A a) = a := by
  classical
  rw [coindTrace_hom_apply, Finset.sum_eq_single ((1 : G) : G ⧸ U)]
  · rw [coindTraceTerm_apply, inv_one]
    change A.ρ 1 (if (1 : G) ∈ U then A.ρ 1 a else 0) = a
    rw [if_pos U.one_mem, map_one, Module.End.one_apply, Module.End.one_apply]
  · intro c _ hc
    induction c using QuotientGroup.induction_on with
    | H x =>
      rw [coindTraceTerm_apply]
      have hx : x⁻¹ ∉ U := fun h => hc (QuotientGroup.eq.2 (by simpa using h))
      change A.ρ x (if x⁻¹ ∈ U then A.ρ x⁻¹ a else 0) = 0
      rw [if_neg hx, map_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem surjective_coindTrace : Function.Surjective (coindTrace U A).hom :=
  fun a => ⟨coindTracePreimage U A a, coindTrace_coindTracePreimage U A a⟩

end Trace

section Sequence

variable {k G : Type u} [CommRing k] [Group G] (U : Subgroup G) [U.FiniteIndex] (A : Rep.{u} k G)

def coindTraceKer : Submodule k (Rep.coind U.subtype (Rep.res U.subtype A)) :=
  LinearMap.ker (coindTrace U A).hom.toLinearMap

theorem coindTraceKer_le_comap (g : G) :
    coindTraceKer U A ≤ (coindTraceKer U A).comap ((Rep.coind U.subtype (Rep.res U.subtype A)).ρ g) := by
  intro f hf
  change (coindTrace U A).hom ((Rep.coind U.subtype (Rep.res U.subtype A)).ρ g f) = 0
  rw [Rep.hom_comm_apply]
  rw [show (coindTrace U A).hom f = 0 from hf, map_zero]

def coindTraceShortComplex : ShortComplex (Rep.{u} k G) :=
  ShortComplex.mk (Rep.subtype _ (coindTraceKer U A) (coindTraceKer_le_comap U A)) (coindTrace U A) (by
    ext f
    exact f.2)

theorem coindTraceShortComplex_shortExact : (coindTraceShortComplex U A).ShortExact where
  exact := by
    rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{u} k G) (ModuleCat.{u} k)),
      ShortComplex.moduleCat_exact_iff]
    intro f hf
    exact ⟨⟨f, hf⟩, rfl⟩
  mono_f := (Rep.mono_iff_injective _).2 fun _ _ h => Subtype.ext h
  epi_g := (Rep.epi_iff_surjective _).2 (surjective_coindTrace U A)

end Sequence

section Cores

theorem inv_comp_hom_apply_base {k : Type u} [CommRing k] {X Y Z : ModuleCat.{u} k} (e : X ≅ Y) (g : X ⟶ Z)
    (x : X) : (e.inv ≫ g).hom (e.hom.hom x) = g.hom x := by
  have h := congrArg (fun f : X ⟶ X => f.hom x) e.hom_inv_id
  change g.hom (e.inv.hom (e.hom.hom x)) = g.hom x
  exact congrArg g.hom h

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] [∀ v, CompactSpace (Hv v)] (φ : ∀ v, Hv v →ₜ* G)

theorem surjective_compactCores_three (V : OpenSubgroup G) (D : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep D]
    [Finite D] {n : ℕ} (hD : ∀ d : D, n • d = 0)
    (hV : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M], (∀ m : M, n • m = 0) →
      Subsingleton (compactCohomologyRes φ M 4)) :
    Function.Surjective (compactCores φ V D 3).hom := by
  have hS := coindTraceShortComplex_shortExact (V : Subgroup G) D
  have : IsDiscreteRep (coindTraceShortComplex (V : Subgroup G) D).X₂ :=
    inferInstanceAs (IsDiscreteRep (Rep.coind (V : Subgroup G).subtype (Rep.res (V : Subgroup G).subtype D)))
  have : IsDiscreteRep (coindTraceShortComplex (V : Subgroup G) D).X₁ :=
    isDiscreteRep_subrepresentation _ _ _
  have : IsDiscreteRep (coindTraceShortComplex (V : Subgroup G) D).X₃ := inferInstanceAs (IsDiscreteRep D)
  have : Finite (Rep.res (V : Subgroup G).subtype D) := inferInstanceAs (Finite D)
  have : Finite (Rep.coind (V : Subgroup G).subtype (Rep.res (V : Subgroup G).subtype D)) :=
    finite_coind V _
  have : Finite (coindTraceShortComplex (V : Subgroup G) D).X₁ :=
    inferInstanceAs (Finite (coindTraceKer (V : Subgroup G) D))
  have hN : ∀ m : (coindTraceShortComplex (V : Subgroup G) D).X₁, n • m = 0 := fun m =>
    Subtype.ext (Subtype.ext (funext fun x => hD _))
  have h4 := hV _ hN
  have hg : Function.Surjective (compactCohomologyResMap φ (coindTrace (V : Subgroup G) D) 3).hom := fun y =>
    (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1 (compactRes_exact₃ φ hS 3)
      (@Subsingleton.elim _ h4 _ _)
  intro y
  refine (hg y).elim fun x hx => ⟨(mackeyCompactCohomologyIso V φ (Rep.res (V : Subgroup G).subtype D) 3).hom.hom x, ?_⟩
  exact (inv_comp_hom_apply_base _ _ x).trans hx

end Cores

section GS

open IsDedekindDomain NumberField GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem surjective_gs_compactCores_three (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))
    (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
    {n : ℕ} (hn : n ≠ 0) (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (hK : Odd n ∨ IsTotallyComplex K.1) (V : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (D : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep D] [Finite D]
    (hD : ∀ d : D, n • d = 0) :
    Function.Surjective (compactCores (gsFinFamily S ιs) V D 3).hom :=
  surjective_compactCores_three (gsFinFamily S ιs) V D hD fun M _ _ hM =>
    subsingleton_compactCohomology_four K S hn hS hK ιs M hM

end GS

end

end GroundTheory.ProfCoh
