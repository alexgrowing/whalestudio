import Mathlib
import GroundTheory.ProfiniteCohomology.InflationRestriction.Section
import GroundTheory.ProfiniteCohomology.CoinducedModules.Acyclic
import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Filter Topology

universe u

section Iso

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

noncomputable def cohomologyIsoOfIso {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B]
    (e : A ≅ B) (n : ℕ) : cohomology A n ≅ cohomology B n where
  hom := cohomologyMap e.hom n
  inv := cohomologyMap e.inv n
  hom_inv_id := by rw [← cohomologyMap_comp, e.hom_inv_id, cohomologyMap_id]
  inv_hom_id := by rw [← cohomologyMap_comp, e.inv_hom_id, cohomologyMap_id]

end Iso

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (X : Type u) [AddCommGroup X] [Module k X]

section Restriction

variable (N : Subgroup G) [N.Normal] {s : G ⧸ N → G} (hs : Continuous s)
  (hsec : ∀ c, (s c : G ⧸ N) = c)

include hsec in

theorem inv_section_mul_mem (x : G) : (s (x : G ⧸ N))⁻¹ * x ∈ N :=
  QuotientGroup.eq.mp (hsec x)

def sectionRetraction (x : G) : N :=
  ⟨(s (x : G ⧸ N))⁻¹ * x, inv_section_mul_mem N hsec x⟩

theorem coe_sectionRetraction (x : G) :
    (sectionRetraction N hsec x : G) = (s (x : G ⧸ N))⁻¹ * x :=
  rfl

include hs in
theorem continuous_sectionRetraction : Continuous (sectionRetraction N hsec) :=
  Continuous.subtype_mk ((hs.comp QuotientGroup.continuous_mk).inv.mul continuous_id) _

theorem section_mul_sectionRetraction (x : G) :
    s (x : G ⧸ N) * (sectionRetraction N hsec x : G) = x := by
  rw [coe_sectionRetraction, mul_inv_cancel_left]

include hsec in
theorem mk_section_mul (c : G ⧸ N) (m : N) : ((s c * m : G) : G ⧸ N) = c :=
  (QuotientGroup.eq.mpr (by rw [mul_inv_rev, inv_mul_cancel_right]; exact N.inv_mem m.2) :
    ((s c * m : G) : G ⧸ N) = (s c : G ⧸ N)).trans (hsec c)

theorem sectionRetraction_section_mul (c : G ⧸ N) (m : N) :
    sectionRetraction N hsec (s c * m) = m := by
  apply Subtype.ext
  rw [coe_sectionRetraction, mk_section_mul N hsec, inv_mul_cancel_left]

include hs in

def restrictSlice (f : LocallyConstant G X) (m : N) : LocallyConstant (G ⧸ N) X :=
  ⟨fun c => f (s c * m), f.isLocallyConstant.comp_continuous (hs.mul continuous_const)⟩

theorem isLocallyConstant_restrictSlice (f : LocallyConstant G X) :
    IsLocallyConstant (restrictSlice X N hs f) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro m₀
  have hc : Continuous fun m : N => (m₀ : G)⁻¹ * m := continuous_const.mul continuous_subtype_val
  have h1 : Tendsto (fun m : N => (m₀ : G)⁻¹ * m) (𝓝 m₀) (𝓝 1) := by
    simpa using hc.tendsto m₀
  filter_upwards [h1.eventually (eventually_forall_mul_eq f)] with m hm
  ext c
  have := hm (s c * m₀)
  simp only [mul_assoc, mul_inv_cancel_left] at this
  exact this

noncomputable def restrictCoindLinear :
    LocallyConstant G X →ₗ[k] LocallyConstant N (LocallyConstant (G ⧸ N) X) where
  toFun f := ⟨restrictSlice X N hs f, isLocallyConstant_restrictSlice X N hs f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def unrestrictCoind (F : LocallyConstant N (LocallyConstant (G ⧸ N) X)) :
    LocallyConstant G X where
  toFun x := F (sectionRetraction N hsec x) (x : G ⧸ N)
  isLocallyConstant := by
    have hF : IsLocallyConstant fun p : N × (G ⧸ N) => F p.1 p.2 := by
      rw [IsLocallyConstant.iff_eventually_eq]
      rintro ⟨m₀, c₀⟩
      have h1 : ∀ᶠ m in 𝓝 m₀, F m = F m₀ := F.isLocallyConstant.eventually_eq m₀
      have h2 : ∀ᶠ c in 𝓝 c₀, F m₀ c = F m₀ c₀ := (F m₀).isLocallyConstant.eventually_eq c₀
      filter_upwards [h1.prod_nhds h2] with p hp
      rw [hp.1, hp.2]
    exact hF.comp_continuous
      ((continuous_sectionRetraction N hs hsec).prodMk QuotientGroup.continuous_mk)

theorem mk_mul_mem (x : G) (m : N) : ((x * m : G) : G ⧸ N) = x :=
  QuotientGroup.eq.mpr (by rw [mul_inv_rev, inv_mul_cancel_right]; exact N.inv_mem m.2)

theorem sectionRetraction_mul (x : G) (m : N) :
    sectionRetraction N hsec (x * m) = sectionRetraction N hsec x * m := by
  apply Subtype.ext
  rw [coe_sectionRetraction, mk_mul_mem, Subgroup.coe_mul, coe_sectionRetraction, mul_assoc]

noncomputable def resDiscreteCoindIso :
    Rep.res N.subtype (discreteCoind k G X) ≅ discreteCoind k N (LocallyConstant (G ⧸ N) X) :=
  have hcomm : ∀ (m : N) (f : LocallyConstant G X),
      restrictCoindLinear (k := k) X N hs (discreteCoindRep k G X m f) =
        discreteCoindRep k N (LocallyConstant (G ⧸ N) X) m (restrictCoindLinear (k := k) X N hs f) := by
    intro m f
    ext m' c
    change f (s c * m' * m) = f (s c * ((m' * m : N) : G))
    rw [Subgroup.coe_mul, mul_assoc]
  { hom := Rep.ofHom ⟨restrictCoindLinear (k := k) X N hs, fun m => LinearMap.ext (hcomm m)⟩
    inv := Rep.ofHom ⟨{ toFun := unrestrictCoind X N hs hsec
                        map_add' := fun _ _ => rfl
                        map_smul' := fun _ _ => rfl }, fun m => by
      ext F x
      change F (sectionRetraction N hsec x * m) (x : G ⧸ N) =
        F (sectionRetraction N hsec (x * m)) ((x * m : G) : G ⧸ N)
      rw [sectionRetraction_mul, mk_mul_mem]⟩
    hom_inv_id := by
      ext f x
      change f (s (x : G ⧸ N) * (sectionRetraction N hsec x : G)) = f x
      rw [section_mul_sectionRetraction]
    inv_hom_id := by
      ext F m c
      change F (sectionRetraction N hsec (s c * m)) ((s c * m : G) : G ⧸ N) = F m c
      rw [sectionRetraction_section_mul N hsec, mk_section_mul N hsec] }

variable [TotallyDisconnectedSpace G]

instance isDiscreteRep_res_discreteCoind : IsDiscreteRep (Rep.res N.subtype (discreteCoind k G X)) :=
  isDiscreteRep_res_subtype _ N

theorem isZero_cohomology_res_discreteCoind (hN : IsClosed (N : Set G)) (n : ℕ) :
    Limits.IsZero (cohomology (Rep.res N.subtype (discreteCoind k G X)) (n + 1)) := by
  obtain ⟨s, hs, hsec, -⟩ := exists_continuous_section N hN
  have : CompactSpace N := isCompact_iff_compactSpace.mp hN.isCompact
  exact (isZero_cohomology_discreteCoind k N (LocallyConstant (G ⧸ N) X) n).of_iso
    (cohomologyIsoOfIso (resDiscreteCoindIso X N hs hsec) (n + 1))

end Restriction

section Invariants

variable (N : Subgroup G) [N.Normal]

variable {X N} in

theorem apply_eq_of_mem_invariants {f : LocallyConstant G X}
    (hf : f ∈ Representation.invariants ((discreteCoindRep k G X).comp N.subtype)) {x y : G}
    (h : (x : G ⧸ N) = y) : f x = f y := by
  have hn : x⁻¹ * y ∈ N := QuotientGroup.eq.mp h
  have := congrArg (fun φ : LocallyConstant G X => φ x) (hf ⟨x⁻¹ * y, hn⟩)
  change f (x * (x⁻¹ * y)) = f x at this
  rw [mul_inv_cancel_left] at this
  exact this.symm

noncomputable def descendInvariant (f : Representation.invariants ((discreteCoindRep k G X).comp N.subtype)) :
    LocallyConstant (G ⧸ N) X where
  toFun c := (f : LocallyConstant G X) c.out
  isLocallyConstant := by
    intro S
    rw [← (QuotientGroup.isQuotientMap_mk N).isOpen_preimage]
    have h : (QuotientGroup.mk ⁻¹' ((fun c : G ⧸ N => (f : LocallyConstant G X) c.out) ⁻¹' S)) =
        (f : LocallyConstant G X) ⁻¹' S := by
      ext x
      simp only [Set.mem_preimage]
      rw [apply_eq_of_mem_invariants f.2 (QuotientGroup.out_eq' (x : G ⧸ N))]
    rw [h]
    exact (f : LocallyConstant G X).isLocallyConstant S

theorem descendInvariant_mk (f : Representation.invariants ((discreteCoindRep k G X).comp N.subtype)) (x : G) :
    descendInvariant X N f x = (f : LocallyConstant G X) x :=
  apply_eq_of_mem_invariants f.2 (QuotientGroup.out_eq' (x : G ⧸ N))

noncomputable def invariantsDiscreteCoindQuotientEquiv :
    Representation.invariants ((discreteCoindRep k G X).comp N.subtype) ≃ₗ[k] LocallyConstant (G ⧸ N) X where
  toFun := descendInvariant X N
  invFun g := ⟨g.comap ⟨QuotientGroup.mk, QuotientGroup.continuous_mk⟩, fun n => by
    ext x
    change g ((x * n : G) : G ⧸ N) = g (x : G ⧸ N)
    rw [QuotientGroup.mk_mul, QuotientGroup.eq_one_iff (n : G) |>.mpr n.2, mul_one]⟩
  map_add' f f' := by
    ext c
    rfl
  map_smul' r f := by
    ext c
    rfl
  left_inv f := by
    ext x
    exact descendInvariant_mk X N f x
  right_inv g := by
    ext c
    change g ((c.out : G) : G ⧸ N) = g c
    rw [QuotientGroup.out_eq']

noncomputable def quotientToInvariantsDiscreteCoindIso :
    (discreteCoind k G X).quotientToInvariants N ≅ discreteCoind k (G ⧸ N) X :=
  have hcomm : ∀ (q : G ⧸ N) (f : Representation.invariants ((discreteCoindRep k G X).comp N.subtype)),
      invariantsDiscreteCoindQuotientEquiv X N ((discreteCoind k G X).ρ.quotientToInvariants N q f) =
        discreteCoindRep k (G ⧸ N) X q (invariantsDiscreteCoindQuotientEquiv X N f) := by
    intro q f
    induction q using QuotientGroup.induction_on with
    | H g =>
      ext c
      change (f : LocallyConstant G X) (c.out * g) =
        (f : LocallyConstant G X) ((c * (g : G ⧸ N)).out)
      apply apply_eq_of_mem_invariants f.2
      rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq']
  { hom := Rep.ofHom ⟨(invariantsDiscreteCoindQuotientEquiv X N).toLinearMap,
      fun q => LinearMap.ext (hcomm q)⟩
    inv := Rep.ofHom ⟨(invariantsDiscreteCoindQuotientEquiv X N).symm.toLinearMap, fun q => by
      refine LinearMap.ext fun g => ?_
      apply (invariantsDiscreteCoindQuotientEquiv X N).injective
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        LinearEquiv.apply_symm_apply]
      rw [hcomm, LinearEquiv.apply_symm_apply]⟩
    hom_inv_id := by
      ext f x
      exact congrArg (fun φ : Representation.invariants ((discreteCoindRep k G X).comp N.subtype) =>
        (φ : LocallyConstant G X) x) ((invariantsDiscreteCoindQuotientEquiv X N).symm_apply_apply f)
    inv_hom_id := by
      ext g c
      exact congrArg (fun φ : LocallyConstant (G ⧸ N) X => φ c)
        ((invariantsDiscreteCoindQuotientEquiv X N).apply_symm_apply g) }

instance isDiscreteRep_quotientToInvariants_discreteCoind :
    IsDiscreteRep ((discreteCoind k G X).quotientToInvariants N) :=
  isDiscreteRep_quotientToInvariants_of_normal _ N

theorem isZero_cohomology_quotientToInvariants_discreteCoind (n : ℕ) :
    Limits.IsZero (cohomology ((discreteCoind k G X).quotientToInvariants N) (n + 1)) :=
  (isZero_cohomology_discreteCoind k (G ⧸ N) X n).of_iso
    (cohomologyIsoOfIso (quotientToInvariantsDiscreteCoindIso X N) (n + 1))

end Invariants

end GroundTheory.ProfCoh
