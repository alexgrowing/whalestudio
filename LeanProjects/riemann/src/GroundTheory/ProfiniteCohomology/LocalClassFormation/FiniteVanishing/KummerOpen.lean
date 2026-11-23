import Mathlib
import GroundTheory.ProfiniteCohomology.LocalClassFormationAlt
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.SubsingletonCohomologyOfPrimaryOfFinite
import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality.QuotientToInvariantsFunctorPreservesZeroMorphism
import GroundTheory.ProfiniteCohomology.ClassFormations.Corestriction
import GroundTheory.LocalFields.UnitsPowers
import GroundTheory.LocalFields.SeparableClosure
import GroundTheory.LocalFields.IntermediateField
import GroundTheory.ProfiniteCohomology.TorsionDualFinite
import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.Devissage
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

section Res

variable {K Ksep : Type} [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] (n : ℕ)
  (V : Subgroup Gal(Ksep/K))

abbrev kummerSequenceRes : ShortComplex (Rep (ULift.{0} ℤ) V) :=
  (kummerSequence K Ksep n).map (Rep.resFunctor V.subtype)

instance isDiscreteRep_kummerSequenceRes_X₁ : IsDiscreteRep (kummerSequenceRes (K := K) n V).X₁ :=
  isDiscreteRep_res_subtype _ _

instance isDiscreteRep_kummerSequenceRes_X₂ : IsDiscreteRep (kummerSequenceRes (K := K) n V).X₂ :=
  isDiscreteRep_res_subtype _ _

instance isDiscreteRep_kummerSequenceRes_X₃ : IsDiscreteRep (kummerSequenceRes (K := K) n V).X₃ :=
  isDiscreteRep_res_subtype _ _

theorem kummerSequenceRes_shortExact (hn : (n : K) ≠ 0) :
    (kummerSequenceRes (K := K) (Ksep := Ksep) n V).ShortExact :=
  shortExact_map_res V (kummerSequence_shortExact n hn)

theorem cohomologyMap_kummerSequenceRes_g_apply (i : ℕ)
    (y : cohomology (kummerSequenceRes (K := K) (Ksep := Ksep) n V).X₂ i) :
    (cohomologyMap (kummerSequenceRes (K := K) (Ksep := Ksep) n V).g i).hom y = n • y := by
  have h : (kummerSequenceRes (K := K) (Ksep := Ksep) n V).g =
      n • 𝟙 (kummerSequenceRes (K := K) (Ksep := Ksep) n V).X₂ := by
    ext x
    exact (nsmul_id_hom_apply _ n x).trans (nsmul_id_hom_apply _ n x).symm
  rw [h]
  exact cohomologyMap_nsmul_id_apply _ n i y

end Res

section Local

variable (K Ksep : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] {n : ℕ} (hn : (n : K) ≠ 0)
  (V : OpenSubgroup Gal(Ksep/K))

instance isDiscreteRep_res_galRootsOfUnity (W : Subgroup Gal(Ksep/K)) :
    IsDiscreteRep (Rep.res W.subtype (galRootsOfUnity.{0} K Ksep n)) :=
  isDiscreteRep_res_subtype _ _

instance isDiscreteRep_res_galUnits (W : Subgroup Gal(Ksep/K)) :
    IsDiscreteRep (Rep.res W.subtype (galUnits.{0} K Ksep)) :=
  isDiscreteRep_res_subtype _ _

theorem subsingleton_cohomology_one_galUnits_open :
    Subsingleton (cohomology (Rep.res (V : Subgroup Gal(Ksep/K)).subtype (galUnits.{0} K Ksep)) 1) :=
  (ModuleCat.isZero_iff_subsingleton).1 ((localClassFormationOfIsSepClosure K Ksep).isZero_H1_open_subgroups V)

include hn in

theorem finite_cohomology_one_rootsOfUnity_open :
    Finite (cohomology (Rep.res (V : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n)) 1) := by
  let := GroundTheory.LocalField.algebraicValuativeRel K Ksep
  let := GroundTheory.LocalField.algebraicTopology K Ksep
  have := GroundTheory.LocalField.algebraicTopology_isValuativeTopology K Ksep
  have := GroundTheory.LocalField.algebraicValuativeRel_valuativeExtension K Ksep
  let E := IntermediateField.fixedField (V : Subgroup Gal(Ksep/K))
  let S := kummerSequenceRes (K := K) (Ksep := Ksep) n (V : Subgroup Gal(Ksep/K))
  have hS : S.ShortExact := kummerSequenceRes_shortExact n _ hn
  have h1 : Subsingleton (cohomology S.X₂ 1) := subsingleton_cohomology_one_galUnits_open K Ksep V
  have hfix : ∀ (u : Eˣ) (σ : (V : Subgroup Gal(Ksep/K))),
      S.X₃.ρ σ (Additive.ofMul (Units.map (algebraMap E Ksep : E →* Ksep) u)) =
        Additive.ofMul (Units.map (algebraMap E Ksep : E →* Ksep) u) := fun u σ =>
    congrArg Additive.ofMul (Units.ext ((IntermediateField.mem_fixedField_iff _ _).1 (u : E).2 σ σ.2))
  let φ : Additive Eˣ →+ S.X₃.ρ.invariants :=
    { toFun := fun u => ⟨Additive.ofMul (Units.map (algebraMap E Ksep : E →* Ksep) u.toMul),
        (Representation.mem_invariants _ _).2 (hfix u.toMul)⟩
      map_zero' := Subtype.ext (by
        change Additive.ofMul (Units.map (algebraMap E Ksep : E →* Ksep) 1) = Additive.ofMul (1 : Ksepˣ)
        rw [map_one])
      map_add' := fun a b => Subtype.ext (by
        change Additive.ofMul (Units.map (algebraMap E Ksep : E →* Ksep) (a.toMul * b.toMul)) =
          Additive.ofMul (Units.map (algebraMap E Ksep : E →* Ksep) a.toMul *
            Units.map (algebraMap E Ksep : E →* Ksep) b.toMul)
        rw [map_mul]) }
  let ψ : Additive Eˣ →+ cohomology S.X₁ 1 :=
    (δ hS 0 1 rfl).hom.toAddMonoidHom.comp ((H0Iso S.X₃).inv.hom.toAddMonoidHom.comp φ)
  have hsurj : Function.Surjective ψ := fun x => by
    obtain ⟨v, hv⟩ := exists_δ_H0Iso_inv_eq hS h1 x
    have ha : ((Additive.toMul (v : S.X₃) : Ksepˣ) : Ksep) ∈ E :=
      (IntermediateField.mem_fixedField_iff _ _).2 fun σ hσ =>
        congrArg (fun y : Additive Ksepˣ => ((Additive.toMul y : Ksepˣ) : Ksep))
          ((Representation.mem_invariants _ _).1 v.2 ⟨σ, hσ⟩)
    let u : Eˣ := Units.mk0 ⟨_, ha⟩ fun h => (Additive.toMul (v : S.X₃) : Ksepˣ).ne_zero
      (congrArg Subtype.val h)
    have hu : φ (Additive.ofMul u) = v := Subtype.ext (congrArg Additive.ofMul (Units.ext rfl))
    refine ⟨Additive.ofMul u, ?_⟩
    change (δ hS 0 1 rfl).hom ((H0Iso S.X₃).inv.hom (φ (Additive.ofMul u))) = x
    rw [hu, hv]
  have hker : ∀ u : Additive Eˣ, ψ (n • u) = 0 := fun u => by
    change (δ hS 0 1 rfl).hom ((H0Iso S.X₃).inv.hom (φ (n • u))) = 0
    rw [map_nsmul]
    refine (δ_H0Iso_inv_eq_zero_iff hS (n • φ u)).2 ⟨φ u, Subtype.ext ?_⟩
    exact nsmul_id_hom_apply (galUnits.{0} K Ksep) n _
  have hmE : ((n : ℕ) : E) ≠ 0 := by
    rw [← map_natCast (algebraMap K E) n]
    exact (map_ne_zero_iff _ (algebraMap K E).injective).2 hn
  have hfinE : Finite (Eˣ ⧸ (powMonoidHom n : Eˣ →* Eˣ).range) :=
    GroundTheory.LocalField.finite_quotient_range_pow (K := E) hmE
  let ψm : Eˣ →* Multiplicative (cohomology S.X₁ 1) := AddMonoidHom.toMultiplicativeRight ψ
  have hle : (powMonoidHom n : Eˣ →* Eˣ).range ≤ ψm.ker := by
    rintro _ ⟨u, rfl⟩
    rw [MonoidHom.mem_ker]
    change Multiplicative.ofAdd (ψ (Additive.ofMul (u ^ n))) = 1
    rw [ofMul_pow, hker]
    rfl
  refine Finite.of_surjective (fun q => Multiplicative.toAdd (QuotientGroup.lift _ ψm hle q)) fun x => ?_
  obtain ⟨u, rfl⟩ := hsurj x
  refine ⟨QuotientGroup.mk (Additive.toMul u), ?_⟩
  change Multiplicative.toAdd (QuotientGroup.lift _ ψm hle (QuotientGroup.mk (Additive.toMul u))) = ψ u
  rw [QuotientGroup.lift_mk]
  rfl

include hn in

theorem finite_cohomology_two_rootsOfUnity_open :
    Finite (cohomology (Rep.res (V : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n)) 2) := by
  set F := localClassFormationOfIsSepClosure K Ksep
  have hS := kummerSequenceRes_shortExact (Ksep := Ksep) n (V : Subgroup Gal(Ksep/K)) hn
  have hinj := cohomologyMap_f_injective_of_subsingleton hS 1
    (subsingleton_cohomology_one_galUnits_open K Ksep V)
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h => hn (by simp [h])
  have htors : ∀ x : cohomology (kummerSequenceRes (K := K) (Ksep := Ksep) n V).X₁ 2,
      F.inv V ((cohomologyMap (kummerSequenceRes (K := K) (Ksep := Ksep) n V).f 2).hom x) ∈
        {q : QZ | n • q = 0} := fun x => by
    have e : n • (cohomologyMap (kummerSequenceRes (K := K) (Ksep := Ksep) n V).f 2).hom x = 0 := by
      rw [← cohomologyMap_kummerSequenceRes_g_apply]
      exact cohomologyMap_g_cohomologyMap_f_apply 2 x
    exact ((F.inv V).map_nsmul n _).symm.trans ((congrArg (F.inv V) e).trans (F.inv V).map_zero)
  have := (QZ.finite_setOf_nsmul_eq_zero hn0).to_subtype
  exact Finite.of_injective (fun x => (⟨_, htors x⟩ : {q : QZ | n • q = 0}))
    fun x y h => hinj ((F.inv_bijective V).1 (congrArg Subtype.val h))

include hn in

theorem subsingleton_cohomology_three_rootsOfUnity_open
    (h3 : Subsingleton (cohomology (Rep.res (V : Subgroup Gal(Ksep/K)).subtype (galUnits.{0} K Ksep)) 3)) :
    Subsingleton (cohomology (Rep.res (V : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n)) 3) := by
  set F := localClassFormationOfIsSepClosure K Ksep
  have hS := kummerSequenceRes_shortExact (Ksep := Ksep) n (V : Subgroup Gal(Ksep/K)) hn
  have hn0 : n ≠ 0 := fun h => hn (by simp [h])
  suffices h : ∀ x : cohomology (kummerSequenceRes (K := K) (Ksep := Ksep) n V).X₁ 3, x = 0 from
    ⟨fun x y => (h x).trans (h y).symm⟩
  intro x
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hS 2 3 rfl) x
    (h3.elim _ _)
  obtain ⟨q, hq⟩ := QZ.exists_nsmul_eq hn0 (F.inv V z)
  obtain ⟨w, hw⟩ := (F.inv_bijective V).2 q
  have hzw : z = (cohomologyMap (kummerSequenceRes (K := K) (Ksep := Ksep) n V).g 2).hom w := by
    apply (F.inv_bijective V).1
    refine hq.symm.trans ?_
    rw [← hw, ← map_nsmul]
    exact congrArg (F.inv V) (cohomologyMap_kummerSequenceRes_g_apply n (V : Subgroup Gal(Ksep/K)) 2 w).symm
  rw [← hz, hzw]
  exact congrArg (fun φ => φ.hom w) (comp_δ hS 2 3 rfl)

include hn in

theorem finite_cohomology_rootsOfUnity_open (r : ℕ) (hr : r ≤ 2) :
    Finite (cohomology (Rep.res (V : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n)) r) := by
  have hn0 : n ≠ 0 := fun h => hn (by simp [h])
  have : NeZero n := ⟨hn0⟩
  have : Finite (Rep.res (V : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n)) :=
    inferInstanceAs (Finite (Additive (rootsOfUnity n Ksep)))
  interval_cases r
  · exact finite_cohomology_zero _
  · exact finite_cohomology_one_rootsOfUnity_open K Ksep hn V
  · exact finite_cohomology_two_rootsOfUnity_open K Ksep hn V

end Local

end GroundTheory.ProfCoh
