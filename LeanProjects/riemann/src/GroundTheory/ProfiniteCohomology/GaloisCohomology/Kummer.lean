import Mathlib
import GroundTheory.ProfiniteCohomology.ContinuousCochains.LongExactSequence
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.SubsingletonCohomologyOfPrimaryOfFinite
import GroundTheory.ProfiniteCohomology.KummerBasic
import GroundTheory.ProfiniteCohomology.GaloisCohomology.UnitsInflationCochainsFHomApply
import GroundTheory.ProfiniteCohomology.GaloisCohomology.IsZeroGroupCohomologyQuotientToInvariantsGalAdd
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory CategoryTheory.Limits groupCohomology

universe u

section General

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem shortComplex_exact_of_forall_exists (S : ShortComplex (Rep.{u} k G))
    (h : ∀ x₂ : S.X₂, S.g.hom x₂ = 0 → ∃ x₁ : S.X₁, S.f.hom x₁ = x₂) : S.Exact := by
  rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{u} k G) (ModuleCat.{u} k)),
    ShortComplex.moduleCat_exact_iff]
  exact h

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem nsmul_id_hom_apply (A : Rep.{u} k G) (m : ℕ) (x : A) : (m • 𝟙 A).hom x = m • x := by
  induction m with
  | zero => simp
  | succ m ih => rw [succ_nsmul, Rep.add_hom, Representation.IntertwiningMap.coe_add,
      Pi.add_apply, ih, succ_nsmul]; rfl

@[reassoc]
theorem cocyclesIso₀_hom_comp_f (A : Rep.{u} k G) [IsDiscreteRep A] :
    (cocyclesIso₀ A).hom ≫ (shortComplexH0 A).f = (cochainsComplex A).iCycles 0 := by
  rw [cocyclesIso₀, KernelFork.mapIsoOfIsLimit_hom]
  exact (KernelFork.mapOfIsLimit_ι _ _ _).trans (Category.comp_id _)

theorem shortComplexH0_f_H0Iso_hom (A : Rep.{u} k G) [IsDiscreteRep A] (y : cohomology A 0) :
    (shortComplexH0 A).f.hom ((H0Iso A).hom.hom y) =
      ((cochainsComplex A).iCycles 0).hom ((cochainsComplex A).isoHomologyπ₀.inv.hom y) :=
  congrArg (fun φ => φ.hom ((cochainsComplex A).isoHomologyπ₀.inv.hom y))
    (cocyclesIso₀_hom_comp_f A)

theorem H0Iso_inv_hom_apply (A : Rep.{u} k G) [IsDiscreteRep A] (y : cohomology A 0) :
    (H0Iso A).inv.hom ((H0Iso A).hom.hom y) = y :=
  congrArg (fun φ => φ.hom y) (H0Iso A).hom_inv_id

theorem H0Iso_hom_inv_apply (A : Rep.{u} k G) [IsDiscreteRep A] (v : A.ρ.invariants) :
    (H0Iso A).hom.hom ((H0Iso A).inv.hom v) = v :=
  congrArg (fun φ => φ.hom v) (H0Iso A).inv_hom_id

theorem cohomologyMap_zero_comp_H0Iso_hom {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B]
    (f : A ⟶ B) :
    cohomologyMap f 0 ≫ (H0Iso B).hom = (H0Iso A).hom ≫ (Rep.invariantsFunctor k G).map f := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  apply (ModuleCat.mono_iff_injective (shortComplexH0 B).f).1 inferInstance
  change (shortComplexH0 B).f.hom ((H0Iso B).hom.hom ((cohomologyMap f 0).hom x)) =
    (shortComplexH0 B).f.hom (((Rep.invariantsFunctor k G).map f).hom ((H0Iso A).hom.hom x))
  rw [shortComplexH0_f_H0Iso_hom]
  have e1 := congrArg (fun φ => φ.hom x)
    (CochainComplex.isoHomologyπ₀_inv_naturality (cochainsMap f))
  have e2 := congrArg (fun φ => φ.hom ((cochainsComplex A).isoHomologyπ₀.inv.hom x))
    (HomologicalComplex.cyclesMap_i (cochainsMap f) 0)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e1 e2
  change ((cochainsComplex B).iCycles 0).hom ((cochainsComplex B).isoHomologyπ₀.inv.hom
    ((HomologicalComplex.homologyMap (cochainsMap f) 0).hom x)) = _
  exact (congrArg ((cochainsComplex B).iCycles 0).hom e1).trans (e2.trans
    (congrArg ((cochainsMap f).f 0).hom (shortComplexH0_f_H0Iso_hom A x).symm))

theorem cohomologyMap_zero_H0Iso_inv {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B]
    (f : A ⟶ B) (v : A.ρ.invariants) :
    (cohomologyMap f 0).hom ((H0Iso A).inv.hom v) =
      (H0Iso B).inv.hom (((Rep.invariantsFunctor k G).map f).hom v) := by
  have h := congrArg (fun φ => φ.hom ((H0Iso A).inv.hom v))
    (cohomologyMap_zero_comp_H0Iso_hom f)
  change (H0Iso B).hom.hom ((cohomologyMap f 0).hom ((H0Iso A).inv.hom v)) =
    ((Rep.invariantsFunctor k G).map f).hom ((H0Iso A).hom.hom ((H0Iso A).inv.hom v)) at h
  rw [H0Iso_hom_inv_apply] at h
  rw [← h, H0Iso_inv_hom_apply]

section LongExact

variable {S : ShortComplex (Rep.{u} k G)} [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂]
  [IsDiscreteRep S.X₃] (hS : S.ShortExact)

theorem exists_δ_H0Iso_inv_eq (h1 : Subsingleton (cohomology S.X₂ 1)) (x : cohomology S.X₁ 1) :
    ∃ v : S.X₃.ρ.invariants, (δ hS 0 1 rfl).hom ((H0Iso S.X₃).inv.hom v) = x := by
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hS 0 1 rfl) x
    (h1.elim _ _)
  exact ⟨(H0Iso S.X₃).hom.hom y,
    (congrArg (δ hS 0 1 rfl).hom (H0Iso_inv_hom_apply S.X₃ y)).trans hy⟩

theorem δ_H0Iso_inv_eq_zero_iff (v : S.X₃.ρ.invariants) :
    (δ hS 0 1 rfl).hom ((H0Iso S.X₃).inv.hom v) = 0 ↔
      ∃ w : S.X₂.ρ.invariants, ((Rep.invariantsFunctor k G).map S.g).hom w = v := by
  constructor
  · intro h
    obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₃ hS 0 1 rfl) _ h
    refine ⟨(H0Iso S.X₂).hom.hom z, ?_⟩
    have e := congrArg (fun φ => φ.hom z) (cohomologyMap_zero_comp_H0Iso_hom S.g)
    change (H0Iso S.X₃).hom.hom ((cohomologyMap S.g 0).hom z) =
      ((Rep.invariantsFunctor k G).map S.g).hom ((H0Iso S.X₂).hom.hom z) at e
    rw [← e]
    exact (congrArg (H0Iso S.X₃).hom.hom hz).trans (H0Iso_hom_inv_apply S.X₃ v)
  · rintro ⟨w, rfl⟩
    rw [← cohomologyMap_zero_H0Iso_inv]
    exact congrArg (fun φ => φ.hom ((H0Iso S.X₂).inv.hom w)) (comp_δ hS 0 1 rfl)

include hS in

theorem cohomologyMap_f_injective_of_subsingleton (i : ℕ)
    (h : Subsingleton (cohomology S.X₃ i)) : Function.Injective (cohomologyMap S.f (i + 1)).hom := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hS i (i + 1) rfl) x
    hx
  rw [← hy, Subsingleton.elim y 0]
  exact map_zero _

include hS in

theorem exists_cohomologyMap_f_eq (i : ℕ) (y : cohomology S.X₂ i)
    (hy : (cohomologyMap S.g i).hom y = 0) : ∃ x, (cohomologyMap S.f i).hom x = y :=
  (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₂ hS i) y hy

theorem cohomologyMap_g_cohomologyMap_f_apply (i : ℕ) (x : cohomology S.X₁ i) :
    (cohomologyMap S.g i).hom ((cohomologyMap S.f i).hom x) = 0 :=
  congrArg (fun φ => φ.hom x) (cohomologyMap_f_comp_g (S := S) i)

end LongExact

end General

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

section H0Units

def unitsToInvariants : Additive Kˣ →+ (galUnits.{u} K L).ρ.invariants where
  toFun a := ⟨Additive.ofMul (Units.map (algebraMap K L : K →* L) (Additive.toMul a)), fun σ =>
    Additive.toMul.injective (Units.ext (σ.commutes _))⟩
  map_zero' := Subtype.ext (Additive.toMul.injective (Units.ext (map_one _)))
  map_add' _ _ := Subtype.ext (Additive.toMul.injective (Units.ext (map_mul _ _ _)))

@[simp]
theorem coe_unitsToInvariants_apply (a : Additive Kˣ) :
    ((Additive.toMul (α := Lˣ) (unitsToInvariants K L a).1 : Lˣ) : L) =
      algebraMap K L (Additive.toMul a : Kˣ) :=
  rfl

theorem unitsToInvariants_injective : Function.Injective (unitsToInvariants K L) := by
  intro a b h
  apply Additive.toMul.injective
  apply Units.ext
  exact (algebraMap K L).injective (congrArg (fun v : (galUnits.{u} K L).ρ.invariants =>
    ((Additive.toMul (α := Lˣ) v.1 : Lˣ) : L)) h)

theorem unitsToInvariants_surjective [IsGalois K L] :
    Function.Surjective (unitsToInvariants K L) := by
  intro v
  obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed
    ((Additive.toMul (α := Lˣ) v.1 : Lˣ) : L)).2 fun σ =>
      congrArg (fun w : Additive Lˣ => ((Additive.toMul w : Lˣ) : L)) (v.2 σ)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact (Additive.toMul (α := Lˣ) v.1).ne_zero ha.symm
  exact ⟨Additive.ofMul (Units.mk0 a ha0),
    Subtype.ext (Additive.toMul.injective (Units.ext ha))⟩

noncomputable def unitsInvariantsEquiv [IsGalois K L] :
    Additive Kˣ ≃+ (galUnits.{u} K L).ρ.invariants :=
  AddEquiv.ofBijective (unitsToInvariants K L)
    ⟨unitsToInvariants_injective K L, unitsToInvariants_surjective K L⟩

@[simp]
theorem unitsInvariantsEquiv_apply [IsGalois K L] (a : Additive Kˣ) :
    unitsInvariantsEquiv K L a = unitsToInvariants K L a :=
  rfl

theorem invariantsFunctor_map_nsmul_unitsToInvariants (n : ℕ) (a : Additive Kˣ) :
    ((Rep.invariantsFunctor (ULift.{u} ℤ) Gal(L/K)).map (n • 𝟙 (galUnits.{u} K L))).hom
        (unitsToInvariants K L a) = unitsToInvariants K L (n • a) := by
  apply Subtype.ext
  change (n • 𝟙 (galUnits.{u} K L)).hom (unitsToInvariants K L a).1 = _
  rw [nsmul_id_hom_apply, map_nsmul]
  rfl

end H0Units

section Sequence

variable {K L} (n : ℕ)

theorem kummerSequence_exact : (kummerSequence K L n).Exact := by
  refine shortComplex_exact_of_forall_exists _ fun x hx => ?_
  have hx' : n • (x : Additive Lˣ) = 0 := (nsmul_id_hom_apply (galUnits.{u} K L) n x).symm.trans hx
  have h : (Additive.toMul (α := Lˣ) x) ^ n = 1 := congrArg Additive.toMul hx'
  exact ⟨(Additive.ofMul (⟨Additive.toMul (α := Lˣ) x, (mem_rootsOfUnity n _).2 h⟩ :
    rootsOfUnity n L) : Additive (rootsOfUnity n L)), rfl⟩

theorem rootsOfUnityToUnits_injective :
    Function.Injective (rootsOfUnityToUnits K L n).hom := fun _ _ h =>
  Additive.toMul.injective (Subtype.ext (congrArg (Additive.toMul (α := Lˣ)) h))

theorem nsmul_id_galUnits_surjective [IsSepClosed L] (hn : (n : L) ≠ 0) :
    Function.Surjective (n • 𝟙 (galUnits.{u} K L)).hom := by
  have : NeZero (n : L) := ⟨hn⟩
  intro y
  obtain ⟨z, hz⟩ := IsSepClosed.exists_pow_nat_eq ((Additive.toMul (α := Lˣ) y : Lˣ) : L) n
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn Nat.cast_zero
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hn0] at hz
    exact (Additive.toMul (α := Lˣ) y).ne_zero hz.symm
  refine ⟨(Additive.ofMul (Units.mk0 z hz0) : Additive Lˣ), ?_⟩
  refine (nsmul_id_hom_apply (galUnits.{u} K L) n _).trans ?_
  apply Additive.toMul.injective
  apply Units.ext
  change ((Units.mk0 z hz0 ^ n : Lˣ) : L) = _
  rw [Units.val_pow_eq_pow_val, Units.val_mk0]
  exact hz

theorem kummerSequence_shortExact_of_ne_zero [IsSepClosed L] (hn : (n : L) ≠ 0) :
    (kummerSequence K L n).ShortExact where
  exact := kummerSequence_exact n
  mono_f := (Rep.mono_iff_injective _).2 (rootsOfUnityToUnits_injective n)
  epi_g := (Rep.epi_iff_surjective _).2 (nsmul_id_galUnits_surjective n hn)

theorem kummerSequence_shortExact [IsSepClosure K L] (hn : (n : K) ≠ 0) :
    (kummerSequence K L n).ShortExact := by
  have : IsSepClosed L := IsSepClosure.sep_closed K
  refine kummerSequence_shortExact_of_ne_zero n ?_
  rw [← map_natCast (algebraMap K L)]
  exact (map_ne_zero (algebraMap K L)).2 hn

variable [Algebra.IsIntegral K L]

instance isDiscreteRep_kummerSequence_X₁ : IsDiscreteRep (kummerSequence K L n).X₁ :=
  inferInstanceAs (IsDiscreteRep (galRootsOfUnity.{u} K L n))

instance isDiscreteRep_kummerSequence_X₂ : IsDiscreteRep (kummerSequence K L n).X₂ :=
  inferInstanceAs (IsDiscreteRep (galUnits.{u} K L))

instance isDiscreteRep_kummerSequence_X₃ : IsDiscreteRep (kummerSequence K L n).X₃ :=
  inferInstanceAs (IsDiscreteRep (galUnits.{u} K L))

end Sequence

section H1

variable {K L} [IsSepClosure K L] {n : ℕ} (hn : (n : K) ≠ 0)

noncomputable def kummerH1Hom : Additive Kˣ →+ cohomology (galRootsOfUnity.{u} K L n) 1 :=
  ((δ (kummerSequence_shortExact n hn) 0 1 rfl).hom.toAddMonoidHom.comp
    (H0Iso (kummerSequence K L n).X₃).inv.hom.toAddMonoidHom).comp (unitsToInvariants K L)

include hn in
theorem kummerH1Hom_surjective : Function.Surjective (kummerH1Hom (L := L) hn) := by
  intro x
  obtain ⟨v, hv⟩ := exists_δ_H0Iso_inv_eq (kummerSequence_shortExact (L := L) n hn)
    (subsingleton_cohomology_one_galUnits (K := K) (L := L)) x
  obtain ⟨a, ha⟩ := unitsToInvariants_surjective K L v
  exact ⟨a, (congrArg (fun w => (δ (kummerSequence_shortExact (L := L) n hn) 0 1 rfl).hom
    ((H0Iso (kummerSequence K L n).X₃).inv.hom w)) ha).trans hv⟩

include hn in
theorem kummerH1Hom_eq_zero_iff (a : Additive Kˣ) :
    kummerH1Hom (L := L) hn a = 0 ↔ Additive.toMul a ∈ unitsPow K n := by
  refine (δ_H0Iso_inv_eq_zero_iff (kummerSequence_shortExact (L := L) n hn)
    (unitsToInvariants K L a)).trans ?_
  rw [mem_unitsPow]
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨b, hb⟩ := unitsToInvariants_surjective K L w
    have h : unitsToInvariants K L (n • b) = unitsToInvariants K L a :=
      (invariantsFunctor_map_nsmul_unitsToInvariants K L n b).symm.trans
        ((congrArg (fun w => ((Rep.invariantsFunctor (ULift.{u} ℤ) Gal(L/K)).map
          (n • 𝟙 (galUnits.{u} K L))).hom w) hb).trans hw)
    exact ⟨Additive.toMul b, congrArg Additive.toMul (unitsToInvariants_injective K L h)⟩
  · rintro ⟨b, hb⟩
    refine ⟨unitsToInvariants K L (Additive.ofMul b), ?_⟩
    refine (invariantsFunctor_map_nsmul_unitsToInvariants K L n _).trans ?_
    congr 1

noncomputable def kummerH1QuotHom : UnitsModPow K n →* Multiplicative
    (cohomology (galRootsOfUnity.{u} K L n) 1) :=
  QuotientGroup.lift (unitsPow K n) (kummerH1Hom (L := L) hn).toMultiplicativeRight fun a ha =>
    (MonoidHom.mem_ker).2 (congrArg Multiplicative.ofAdd
      ((kummerH1Hom_eq_zero_iff hn (Additive.ofMul a)).2 ha))

include hn in
theorem kummerH1QuotHom_bijective : Function.Bijective (kummerH1QuotHom (L := L) hn) := by
  constructor
  · refine (injective_iff_map_eq_one _).2 fun q hq => ?_
    induction q using QuotientGroup.induction_on with
    | H a =>
      have h : kummerH1Hom (L := L) hn (Additive.ofMul a) = 0 := congrArg Multiplicative.toAdd hq
      exact (QuotientGroup.eq_one_iff a).2 ((kummerH1Hom_eq_zero_iff hn _).1 h)
  · intro y
    obtain ⟨a, ha⟩ := kummerH1Hom_surjective (L := L) hn (Multiplicative.toAdd y)
    exact ⟨(Additive.toMul a : Kˣ), congrArg Multiplicative.ofAdd ha⟩

noncomputable def kummerH1Equiv :
    cohomology (galRootsOfUnity.{u} K L n) 1 ≃+ Additive (UnitsModPow K n) :=
  (MulEquiv.toAdditiveLeft (MulEquiv.ofBijective _ (kummerH1QuotHom_bijective (L := L) hn))).symm

end H1

section H2

variable {K L} [IsGalois K L]

noncomputable def galoisBrauerGroupTorsion (n : ℕ) : AddSubgroup (galoisBrauerGroup K L) :=
  (nsmulAddMonoidHom (α := galoisBrauerGroup K L) n).ker

theorem cohomologyMap_kummerSequence_g_apply (n i : ℕ) (y : cohomology (galUnits.{u} K L) i) :
    (cohomologyMap (kummerSequence K L n).g i).hom y = n • y :=
  cohomologyMap_nsmul_id_apply (galUnits.{u} K L) n i y

variable [IsSepClosure K L] {n : ℕ} (hn : (n : K) ≠ 0)

noncomputable def kummerH2Hom :
    cohomology (galRootsOfUnity.{u} K L n) 2 →+ galoisBrauerGroupTorsion (K := K) (L := L) n :=
  AddMonoidHom.codRestrict (cohomologyMap (kummerSequence K L n).f 2).hom.toAddMonoidHom _
    fun x => (cohomologyMap_kummerSequence_g_apply n 2 _).symm.trans
      (cohomologyMap_g_cohomologyMap_f_apply 2 x)

include hn in
theorem kummerH2Hom_bijective : Function.Bijective (kummerH2Hom (K := K) (L := L) (n := n)) := by
  have hS := kummerSequence_shortExact (L := L) n hn
  constructor
  · intro x y h
    exact cohomologyMap_f_injective_of_subsingleton hS 1
      (subsingleton_cohomology_one_galUnits (K := K) (L := L)) (congrArg Subtype.val h)
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := exists_cohomologyMap_f_eq hS 2 y
      ((cohomologyMap_kummerSequence_g_apply n 2 y).trans hy)
    exact ⟨x, Subtype.ext hx⟩

noncomputable def kummerH2Equiv :
    cohomology (galRootsOfUnity.{u} K L n) 2 ≃+ galoisBrauerGroupTorsion (K := K) (L := L) n :=
  AddEquiv.ofBijective _ (kummerH2Hom_bijective hn)

end H2

end GroundTheory.ProfCoh
