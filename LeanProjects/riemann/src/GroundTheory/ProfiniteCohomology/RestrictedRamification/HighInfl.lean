import Mathlib
import GroundTheory.ProfiniteCohomology.InflationRestriction
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality.Naturality
import GroundTheory.ProfiniteCohomology.CupProducts
import GroundTheory.ProfiniteCohomology.CupProducts.Projection
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

section Groups

variable {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]

def IsIsoModCoprime (ℓ : ℕ) (f : X →+ Y) : Prop :=
  (∀ x, f x = 0 → ∃ m : ℕ, m.Coprime ℓ ∧ m • x = 0) ∧ ∀ y, ∃ m : ℕ, m.Coprime ℓ ∧ ∃ x, f x = m • y

namespace IsIsoModCoprime

variable {ℓ : ℕ}

theorem of_bijective {f : X →+ Y} (hf : Function.Bijective f) : IsIsoModCoprime ℓ f :=
  ⟨fun x hx => ⟨1, Nat.coprime_one_left ℓ, by rw [one_smul]; exact hf.1 (hx.trans (map_zero f).symm)⟩,
    fun y => ⟨1, Nat.coprime_one_left ℓ, (hf.2 y).imp fun x hx => by rw [hx, one_smul]⟩⟩

theorem comp {g : Y →+ Z} {f : X →+ Y} (hg : IsIsoModCoprime ℓ g) (hf : IsIsoModCoprime ℓ f) :
    IsIsoModCoprime ℓ (g.comp f) := by
  refine ⟨fun x hx => ?_, fun z => ?_⟩
  · obtain ⟨m, hm, hmx⟩ := hg.1 (f x) hx
    obtain ⟨m', hm', hm'x⟩ := hf.1 (m • x) (by rw [map_nsmul, hmx])
    exact ⟨m' * m, Nat.Coprime.mul_left hm' hm, by rw [mul_smul]; exact hm'x⟩
  · obtain ⟨m, hm, y, hy⟩ := hg.2 z
    obtain ⟨m', hm', x, hx⟩ := hf.2 y
    exact ⟨m' * m, Nat.Coprime.mul_left hm' hm, x, by
      rw [AddMonoidHom.comp_apply, hx, map_nsmul, hy, ← mul_smul]⟩

theorem of_comp_surjective {f : X →+ Y} {e : Z →+ X} (h : IsIsoModCoprime ℓ (f.comp e))
    (he : Function.Surjective e) : IsIsoModCoprime ℓ f := by
  refine ⟨fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨z, rfl⟩ := he x
    obtain ⟨m, hm, hmz⟩ := h.1 z hx
    exact ⟨m, hm, by rw [← map_nsmul, hmz, map_zero]⟩
  · obtain ⟨m, hm, z, hz⟩ := h.2 y
    exact ⟨m, hm, e z, hz⟩

theorem congr {f g : X →+ Y} (h : IsIsoModCoprime ℓ f) (hfg : ∀ x, f x = g x) : IsIsoModCoprime ℓ g := by
  obtain rfl : f = g := AddMonoidHom.ext hfg
  exact h

end IsIsoModCoprime

end Groups

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem range_repHom_le_comap {A B : Rep.{u} k G} (f : A ⟶ B) (g : G) :
    LinearMap.range f.hom.toLinearMap ≤ (LinearMap.range f.hom.toLinearMap).comap (B.ρ g) := by
  rintro _ ⟨a, rfl⟩
  exact ⟨A.ρ g a, Rep.hom_comm_apply f g a⟩

section Torsion

variable [CompactSpace G]

theorem exists_coprime_nsmul_cohomology_of_forall (A : Rep.{u} k G) [IsDiscreteRep A] (ℓ : ℕ)
    (hA : ∀ a : A, ∃ m : ℕ, m.Coprime ℓ ∧ m • a = 0) (n : ℕ) (x : cohomology A n) :
    ∃ m : ℕ, m.Coprime ℓ ∧ m • x = 0 := by
  classical
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective A n x
  set c := cochainOf A (cocycleι A n z) with hc
  have hlc : IsLocallyConstant c := (cocycleι A n z : locallyConstantCochains A n).2
  have hfin : (Set.range c).Finite := hlc.range_finite
  choose M hMc hMa using hA
  refine ⟨∏ a ∈ hfin.toFinset, M a, Nat.Coprime.prod_left fun a _ => hMc a, ?_⟩
  have hz : (∏ a ∈ hfin.toFinset, M a) • z = 0 := by
    apply cocycleι_injective
    apply cochainOf_injective
    rw [map_nsmul, map_zero, cochainOf_zero]
    funext g
    have hmem : c g ∈ hfin.toFinset := hfin.mem_toFinset.2 ⟨g, rfl⟩
    change (∏ a ∈ hfin.toFinset, M a) • c g = 0
    obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem M hmem
    rw [hd, mul_comm, ← smul_smul, hMa, smul_zero]
  rw [← map_nsmul, hz, map_zero]

end Torsion

section ShortExact

variable {S : ShortComplex (Rep.{u} k G)} [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂] [IsDiscreteRep S.X₃]

theorem isIsoModCoprime_cohomologyMap_f (hS : S.ShortExact) (ℓ : ℕ)
    (h3 : ∀ i (y : cohomology S.X₃ i), ∃ m : ℕ, m.Coprime ℓ ∧ m • y = 0) (i j : ℕ) (hij : i + 1 = j) :
    IsIsoModCoprime ℓ (cohomologyMap S.f j).hom.toAddMonoidHom := by
  refine ⟨fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨z, rfl⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hS i j hij) x hx
    obtain ⟨m, hm, hmz⟩ := h3 i z
    exact ⟨m, hm, by rw [← map_nsmul, hmz, map_zero]⟩
  · obtain ⟨m, hm, hmy⟩ := h3 j ((cohomologyMap S.g j).hom y)
    obtain ⟨x, hx⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₂ hS j) (m • y)
      (by rw [map_nsmul]; exact hmy)
    exact ⟨m, hm, x, hx⟩

end ShortExact

section Injective

variable [CompactSpace G] {X Y : Rep.{u} k G} [IsDiscreteRep X] [IsDiscreteRep Y]

theorem isIsoModCoprime_cohomologyMap_of_injective (ι : X ⟶ Y) (hι : Function.Injective ι.hom) (ℓ : ℕ)
    (hcok : ∀ y : Y, ∃ m : ℕ, m.Coprime ℓ ∧ ∃ x, ι.hom x = m • y) {j : ℕ} (hj : 1 ≤ j) :
    IsIsoModCoprime ℓ (cohomologyMap ι j).hom.toAddMonoidHom := by
  set W := LinearMap.range ι.hom.toLinearMap
  let S : ShortComplex (Rep.{u} k G) := ShortComplex.mk ι (Rep.mkQ Y W (range_repHom_le_comap ι)) (by
    ext x
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩)
  have : IsDiscreteRep S.X₁ := (inferInstance : IsDiscreteRep X)
  have : IsDiscreteRep S.X₂ := (inferInstance : IsDiscreteRep Y)
  have : IsDiscreteRep S.X₃ := isDiscreteRep_quotient Y W (range_repHom_le_comap ι)
  have hS : S.ShortExact :=
    { exact := by
        rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{u} k G) (ModuleCat.{u} k)),
          ShortComplex.moduleCat_exact_iff]
        intro y hy
        change Submodule.Quotient.mk (p := W) y = 0 at hy
        obtain ⟨x, hx⟩ := (Submodule.Quotient.mk_eq_zero _).1 hy
        exact ⟨x, hx⟩
      mono_f := (Rep.mono_iff_injective _).2 hι
      epi_g := (Rep.epi_iff_surjective _).2 (Submodule.mkQ_surjective _) }
  have h3 : ∀ i (y : cohomology S.X₃ i), ∃ m : ℕ, m.Coprime ℓ ∧ m • y = 0 := by
    refine exists_coprime_nsmul_cohomology_of_forall S.X₃ ℓ fun q => ?_
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective W q
    obtain ⟨m, hm, x, hx⟩ := hcok y
    refine ⟨m, hm, ?_⟩
    change Submodule.Quotient.mk (p := W) (m • y) = 0
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x, hx⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  exact isIsoModCoprime_cohomologyMap_f hS ℓ h3 i (i + 1) rfl

end Injective

section Shift

variable [CompactSpace G] (A : Rep.{u} k G) [IsDiscreteRep A] (N : Subgroup G) [N.Normal]

noncomputable abbrev coindInvariants : ShortComplex (Rep.{u} k (G ⧸ N)) :=
  (coindShortComplex A).map (Rep.quotientToInvariantsFunctor k N)

noncomputable def coindInvQuotShortComplex : ShortComplex (Rep.{u} k (G ⧸ N)) :=
  ShortComplex.mk (coindInvariants A N).f
    (Rep.mkQ _ (LinearMap.range (coindInvariants A N).f.hom.toLinearMap) (range_repHom_le_comap _)) (by
      ext x
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩)

instance isDiscreteRep_coindInvQuotShortComplex_X₁ : IsDiscreteRep (coindInvQuotShortComplex A N).X₁ :=
  isDiscreteRep_quotientToInvariants_of_normal A N

instance isDiscreteRep_coindInvQuotShortComplex_X₂ : IsDiscreteRep (coindInvQuotShortComplex A N).X₂ :=
  isDiscreteRep_quotientToInvariants_of_normal (discreteCoind k G A) N

instance isDiscreteRep_coindInvQuotShortComplex_X₃ : IsDiscreteRep (coindInvQuotShortComplex A N).X₃ :=
  isDiscreteRep_quotient _ _ _

omit [CompactSpace G] in

theorem coindInvQuotShortComplex_shortExact : (coindInvQuotShortComplex A N).ShortExact where
  exact := by
    rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{u} k (G ⧸ N)) (ModuleCat.{u} k)),
      ShortComplex.moduleCat_exact_iff]
    intro y hy
    change Submodule.Quotient.mk (p := LinearMap.range (coindInvariants A N).f.hom.toLinearMap) y = 0 at hy
    obtain ⟨x, hx⟩ := (Submodule.Quotient.mk_eq_zero _).1 hy
    exact ⟨x, hx⟩
  mono_f := (Rep.mono_iff_injective _).2 fun x y h =>
    Subtype.ext (coindEmbedding_injective A (congrArg Subtype.val h))
  epi_g := (Rep.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)

noncomputable def coindInvQuotToInvariants :
    (coindInvQuotShortComplex A N).X₃ ⟶ (coindInvariants A N).X₃ :=
  Rep.ofHom ⟨(LinearMap.range (coindInvariants A N).f.hom.toLinearMap).liftQ
      (coindInvariants A N).g.hom.toLinearMap (by
        rintro _ ⟨x, rfl⟩
        exact congrArg (fun φ => φ.hom x) (coindInvariants A N).zero), fun g =>
    Submodule.linearMap_qext _ (LinearMap.ext fun x => Rep.hom_comm_apply (coindInvariants A N).g g x)⟩

omit [CompactSpace G] in

theorem coindInvQuotToInvariants_injective : Function.Injective (coindInvQuotToInvariants A N).hom := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
  have hx : (coindShortComplex A).g.hom x.1 = 0 := congrArg Subtype.val hq
  have hrk := ((coindShortComplex_shortExact A).exact.map
    (forget₂ (Rep.{u} k G) (ModuleCat k))).moduleCat_range_eq_ker
  have hx' : x.1 ∈ LinearMap.ker
      ((coindShortComplex A).map (forget₂ (Rep.{u} k G) (ModuleCat k))).g.hom := hx
  rw [← hrk] at hx'
  obtain ⟨a, ha⟩ := hx'
  have ha' : (coindEmbedding A).hom a = x.1 := ha
  refine (Submodule.Quotient.mk_eq_zero _).2 ⟨⟨a, fun s => coindEmbedding_injective A ?_⟩, Subtype.ext ha'⟩
  refine (Rep.hom_comm_apply (coindEmbedding A) (s : G) a).trans ?_
  rw [ha']
  exact x.2 s

theorem exists_coindInvQuotToInvariants_eq (ℓ : ℕ)
    (h1 : ∀ y : cohomology (Rep.res N.subtype A) 1, ∃ m : ℕ, m.Coprime ℓ ∧ m • y = 0)
    (c : (coindInvariants A N).X₃) :
    ∃ m : ℕ, m.Coprime ℓ ∧ ∃ q, (coindInvQuotToInvariants A N).hom q = m • c := by
  have hS := shortExact_map_res N (coindShortComplex_shortExact A)
  let v : ((coindShortComplex A).map (Rep.resFunctor N.subtype)).X₃.ρ.invariants := c
  obtain ⟨m, hm, hmv⟩ := h1 ((δ hS 0 1 rfl).hom ((H0Iso _).inv.hom v))
  have h0 : (δ hS 0 1 rfl).hom ((H0Iso _).inv.hom (m • v)) = 0 := by
    rw [map_nsmul, map_nsmul]
    exact hmv
  obtain ⟨w, hw⟩ := (δ_H0Iso_inv_eq_zero_iff hS (m • v)).1 h0
  exact ⟨m, hm, Submodule.Quotient.mk w, Subtype.ext (congrArg Subtype.val hw)⟩

noncomputable def coindInvQuotToSelf :
    (coindInvQuotShortComplex A N).map (Rep.resFunctor (QuotientGroup.mk' N)) ⟶ coindShortComplex A where
  τ₁ := Rep.ofHom (A.ρ.quotientToInvariants_lift N)
  τ₂ := Rep.ofHom ((discreteCoind k G A).ρ.quotientToInvariants_lift N)
  τ₃ := (Rep.resFunctor (QuotientGroup.mk' N)).map (coindInvQuotToInvariants A N) ≫
    Rep.ofHom ((coindCokernel A).ρ.quotientToInvariants_lift N)
  comm₁₂ := rfl
  comm₂₃ := by
    ext x
    rfl

theorem cohomologyInfl_δ_coindInvQuot (i j : ℕ) (hij : i + 1 = j)
    (x : cohomology (coindInvQuotShortComplex A N).X₃ i) :
    (cohomologyInfl A N j).hom ((δ (coindInvQuotShortComplex_shortExact A N) i j hij).hom x) =
      (δ (coindShortComplex_shortExact A) i j hij).hom
        ((cohomologyInfl (coindCokernel A) N i).hom ((cohomologyMap (coindInvQuotToInvariants A N) i).hom x)) := by
  have h := congrArg (fun φ => φ.hom x) (δ_comp_cohomologyMapAlong (QuotientGroup.mk' N)
    (continuous_quotientGroup_mk' N) (coindInvQuotToSelf A N) (coindInvQuotShortComplex_shortExact A N)
    (coindShortComplex_shortExact A) i j hij)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  refine h.trans (congrArg (δ (coindShortComplex_shortExact A) i j hij).hom ?_)
  exact (cohomologyMapAlong_cohomologyMap (QuotientGroup.mk' N) (continuous_quotientGroup_mk' N)
    (coindInvQuotToInvariants A N) (Rep.ofHom ((coindCokernel A).ρ.quotientToInvariants_lift N)) x).symm

omit [CompactSpace G] in

theorem isIsoModCoprime_cohomologyInfl_one (ℓ : ℕ)
    (h1 : ∀ y : cohomology (Rep.res N.subtype A) 1, ∃ m : ℕ, m.Coprime ℓ ∧ m • y = 0) :
    IsIsoModCoprime ℓ (cohomologyInfl A N 1).hom.toAddMonoidHom := by
  refine ⟨fun x hx => ⟨1, Nat.coprime_one_left ℓ, ?_⟩, fun y => ?_⟩
  · rw [one_smul]
    exact cohomologyInfl_one_injective A N (hx.trans (map_zero _).symm)
  · obtain ⟨m, hm, hmy⟩ := h1 ((cohomologyRes A N 1).hom y)
    obtain ⟨x, hx⟩ := exists_cohomologyInfl_one_eq A N (m • y) (by rw [map_nsmul]; exact hmy)
    exact ⟨m, hm, x, hx⟩

theorem isIsoModCoprime_cohomologyInfl_succ (ℓ n : ℕ)
    (h1 : ∀ y : cohomology (Rep.res N.subtype A) 1, ∃ m : ℕ, m.Coprime ℓ ∧ m • y = 0)
    (hC : IsIsoModCoprime ℓ (cohomologyInfl (coindCokernel A) N (n + 1)).hom.toAddMonoidHom) :
    IsIsoModCoprime ℓ (cohomologyInfl A N (n + 1 + 1)).hom.toAddMonoidHom := by
  have hT := coindInvQuotShortComplex_shortExact A N
  have hX := coindShortComplex_shortExact A
  have hδT := isIso_δ_of_isZero hT n
    (isZero_cohomology_quotientToInvariants_discreteCoind (k := k) A N n)
    (isZero_cohomology_quotientToInvariants_discreteCoind (k := k) A N (n + 1))
  have hδX := isIso_δ_of_isZero hX n (isZero_cohomology_discreteCoind k G A n)
    (isZero_cohomology_discreteCoind k G A (n + 1))
  have hι := isIsoModCoprime_cohomologyMap_of_injective (coindInvQuotToInvariants A N)
    (coindInvQuotToInvariants_injective A N) ℓ (exists_coindInvQuotToInvariants_eq A N ℓ h1)
    (j := n + 1) (by omega)
  have hbij : Function.Bijective (δ hX (n + 1) (n + 1 + 1) rfl).hom :=
    ⟨(ModuleCat.mono_iff_injective _).1 inferInstance, (ModuleCat.epi_iff_surjective _).1 inferInstance⟩
  have hsurj : Function.Surjective (δ hT (n + 1) (n + 1 + 1) rfl).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  have hcomp := (IsIsoModCoprime.of_bijective (ℓ := ℓ)
    (f := (δ hX (n + 1) (n + 1 + 1) rfl).hom.toAddMonoidHom) hbij).comp (hC.comp hι)
  refine IsIsoModCoprime.of_comp_surjective
    (e := (δ hT (n + 1) (n + 1 + 1) rfl).hom.toAddMonoidHom) (hcomp.congr fun x => ?_) hsurj
  exact (cohomologyInfl_δ_coindInvQuot A N (n + 1) (n + 1 + 1) rfl x).symm

variable [TotallyDisconnectedSpace G] {A N}

theorem isIsoModCoprime_cohomologyInfl (hN : IsClosed (N : Set G)) (ℓ : ℕ) {r : ℕ} (hr : 1 ≤ r)
    (hA : ∀ i, 1 ≤ i → ∀ y : cohomology (Rep.res N.subtype A) i, ∃ m : ℕ, m.Coprime ℓ ∧ m • y = 0) :
    IsIsoModCoprime ℓ (cohomologyInfl A N r).hom.toAddMonoidHom := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  clear hr
  induction n generalizing A with
  | zero => exact isIsoModCoprime_cohomologyInfl_one A N ℓ (hA 1 le_rfl)
  | succ n ih =>
    refine isIsoModCoprime_cohomologyInfl_succ A N ℓ n (hA 1 le_rfl) (ih fun i hi y => ?_)
    have hS := shortExact_map_res N (coindShortComplex_shortExact A)
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    have hδ := isIso_δ_of_isZero hS m (isZero_cohomology_res_discreteCoind (k := k) A N hN m)
      (isZero_cohomology_res_discreteCoind (k := k) A N hN (m + 1))
    have hinj : Function.Injective (δ hS (m + 1) (m + 1 + 1) rfl).hom :=
      (ModuleCat.mono_iff_injective _).1 inferInstance
    let y' : cohomology ((coindShortComplex A).map (Rep.resFunctor N.subtype)).X₃ (m + 1) := y
    obtain ⟨c, hc, hcy⟩ := hA (m + 1 + 1) (by omega) ((δ hS (m + 1) (m + 1 + 1) rfl).hom y')
    have hcy' : c • (δ hS (m + 1) (m + 1 + 1) rfl).hom y' = 0 := hcy
    have h0 : c • y' = 0 := hinj ((map_nsmul _ c y').trans (hcy'.trans (map_zero _).symm))
    exact ⟨c, hc, h0⟩

end Shift

end GroundTheory.ProfCoh
