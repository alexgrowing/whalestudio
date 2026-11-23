import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineForgetFormsBijectiveSiteAndPairsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleFormsCochainsEqDeRhamCochainsSmoothLifStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftRestrictionBijectiveLowDegreesStatement

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDForm

universe u

section Gen

variable {C : Type u} [Category.{0} C]

theorem cx_H1_mk_eq_zero_iff (K : Cx C) (x : K.Z1) :
    (QuotientAddGroup.mk x : K.H1) = 0 ↔ ∃ g, K.D0 g = x.1 := by
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]

theorem cx_H2_mk_eq_zero_iff (K : Cx C) (x : K.Z2) :
    (QuotientAddGroup.mk x : K.H2) = 0 ↔ ∃ g, K.D1 g = x.1 := by
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]

variable {R : Type} [CommRing R] (F : C ⥤ CommAlgCat.{0} R)

theorem single1_mem (f : GlobalTheory.CatCoh.Z1 F) :
    ((f.1 : (Coef.ofAlg F).c1), (fun _ ↦ PUnit.unit : (Coef.zero C).c0)) ∈ (Cx.single (Coef.ofAlg F)).Z1 := by
  show Cx.D1 _ _ = 0
  refine Prod.ext ?_ (Prod.ext (funext fun _ ↦ funext fun _ ↦ funext fun _ ↦ rfl) (funext fun _ ↦ rfl))
  funext T T' T'' φ ψ
  have := f.2 φ ψ
  change (mp F ψ) (f.1 T T' φ) - f.1 T T'' (φ ≫ ψ) + f.1 T' T'' ψ = 0
  rw [this]; abel

theorem single_H1_mk_eq_zero_iff (x : (Cx.single (Coef.ofAlg F)).Z1) :
    (QuotientAddGroup.mk x : (Cx.single (Coef.ofAlg F)).H1) = 0 ↔ ∃ g, GlobalTheory.CatCoh.d0 F g = x.1.1 := by
  rw [cx_H1_mk_eq_zero_iff]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, by rw [← hg]; rfl⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, Prod.ext (by rw [← hg]; rfl) (Subsingleton.elim _ _)⟩

end Gen

section Gen2

variable {C : Type u} [Category.{0} C] {R : Type} [CommRing R] (F : C ⥤ CommAlgCat.{0} R)

theorem single_fst_mem_Z1 (x : (Cx.single (Coef.ofAlg F)).Z1) : x.1.1 ∈ GlobalTheory.CatCoh.Z1 F := by
  intro T T' T'' φ ψ
  have h : Cx.D1 _ x.1 = 0 := x.2
  have := congrArg (fun c ↦ c.1 T T' T'' φ ψ) h
  change (mp F ψ) (x.1.1 T T' φ) - x.1.1 T T'' (φ ≫ ψ) + x.1.1 T' T'' ψ = 0 at this
  linear_combination -this

theorem single2_mem (z : GlobalTheory.CatCoh.Z2 F) :
    ((z.1 : (Coef.ofAlg F).c2), (fun _ _ _ ↦ PUnit.unit : (Coef.zero C).c1), (fun _ ↦ PUnit.unit : (Coef.zero C).c0))
      ∈ (Cx.single (Coef.ofAlg F)).Z2 :=
  ⟨fun T T' T'' T''' φ ψ χ ↦ z.2 φ ψ χ, fun _ _ _ _ _ ↦ Subsingleton.elim _ _, fun _ _ _ ↦ Subsingleton.elim _ _,
    fun _ ↦ Subsingleton.elim _ _⟩

theorem single_fst_mem_Z2 (x : (Cx.single (Coef.ofAlg F)).Z2) : x.1.1 ∈ GlobalTheory.CatCoh.Z2 F :=
  fun _ _ _ _ φ ψ χ ↦ x.2.1 _ _ _ _ φ ψ χ

theorem single_H2_mk_eq_zero_iff (x : (Cx.single (Coef.ofAlg F)).Z2) :
    (QuotientAddGroup.mk x : (Cx.single (Coef.ofAlg F)).H2) = 0 ↔ ∃ g, GlobalTheory.CatCoh.d1 F g = x.1.1 := by
  rw [cx_H2_mk_eq_zero_iff]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g.1, by rw [← hg]; rfl⟩
  · rintro ⟨g, hg⟩
    exact ⟨(g, fun _ ↦ PUnit.unit), Prod.ext (by rw [← hg]; rfl) (Subsingleton.elim _ _)⟩

end Gen2

section Lift

variable {D : Data} (Λ : Lift D)

theorem smoothLiftThickenings_restrictionOne_sub {k k' : ((KK D.κ D.t).res Λ.L).T1} {w w' : Tot1 (OAff D.s)} (h : Λ.Res1 k w)
    (h' : Λ.Res1 k' w') : Λ.Res1 (k - k') (w - w') := by
  refine ⟨fun U V a ↦ ?_, fun U ↦ ?_⟩
  · simp only [Prod.fst_sub, Pi.sub_apply, h.1 U V a, h'.1 U V a, map_sub]
  · simp only [Prod.snd_sub, Pi.sub_apply, h.2 U, h'.2 U, map_sub, Submodule.Quotient.mk_sub]

theorem smoothLiftThickenings_restrictionTwo_sub {k k' : ((KK D.κ D.t).res Λ.L).T2} {w w' : Tot2 (OAff D.s)} (h : Λ.Res2 k w)
    (h' : Λ.Res2 k' w') : Λ.Res2 (k - k') (w - w') := by
  refine ⟨fun U V W a b ↦ ?_, fun U V a ↦ ?_, fun U ↦ ?_⟩
  · simp only [Prod.fst_sub, Pi.sub_apply, h.1 U V W a b, h'.1 U V W a b, map_sub]
  · simp only [Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, h.2.1 U V a, h'.2.1 U V a, map_sub,
      Submodule.Quotient.mk_sub]
  · simp only [Prod.snd_sub, Pi.sub_apply, h.2.2 U, h'.2.2 U, map_sub, Submodule.Quotient.mk_sub]

end Lift

section Main

variable (D : Data) (Λ : Lift D)

theorem crystallineCechDeRham_degreeOne_relation_total : (∀ c, ∃ h, Λ.Rel1 c h) ∧ (∀ h, ∃ c, Λ.Rel1 c h) ∧
    ∀ c h, Λ.Rel1 c h → (c = 0 ↔ h = 0) := by
  have hfn := (GlobalTheory.T.fnMap_pullbackBijective12_kk_and_res D.R D.I D.κ D.X₀ D.t D.X D.i).1.1
  have hres := (GlobalTheory.T.lift_restriction_bijective_low_degrees D Λ).1
  obtain ⟨hW, hK, hZ⟩ := GlobalTheory.T.compatibleFormsCochains_eq_deRhamCochains_smoothLift.1 D Λ
  have key : ∀ k : (KK D.κ D.t).Z1, (∃ g, GlobalTheory.CatCoh.d0 (O D.κ D.t) g = k.1.1) ↔
      ∃ g, ((KK D.κ D.t).res Λ.L).D0 g = ((KK D.κ D.t).resMap Λ.L).p1 k.1 := fun k ↦ by
    have e := (map_eq_zero_iff _ hfn.1 (x := (QuotientAddGroup.mk k : (KK D.κ D.t).H1))).trans
      (map_eq_zero_iff _ hres.1).symm
    exact ((single_H1_mk_eq_zero_iff (O D.κ D.t) ((KK D.κ D.t).fnMap.z1 k)).symm.trans e).trans
      (cx_H1_mk_eq_zero_iff _ (((KK D.κ D.t).resMap Λ.L).z1 k))
  refine ⟨fun c ↦ ?_, fun h ↦ ?_, ?_⟩
  · obtain ⟨f, rfl⟩ := GlobalTheory.CatCoh.H1.mk_surjective _ c
    obtain ⟨x, hx⟩ := hfn.2 (QuotientAddGroup.mk ⟨_, single1_mem (O D.κ D.t) f⟩)
    obtain ⟨k, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨g, hg⟩ := (single_H1_mk_eq_zero_iff (O D.κ D.t) ((KK D.κ D.t).fnMap.z1 k - ⟨_, single1_mem _ f⟩)).1
      (by rw [QuotientAddGroup.mk_sub]; exact sub_eq_zero.2 hx)
    obtain ⟨w, hw, -⟩ := hW (((KK D.κ D.t).resMap Λ.L).p1 k.1)
    have hwZ : w ∈ cechDeRhamTotalCocyclesOne (OAff D.s) := ((hZ _ _ hw).1).1 (((KK D.κ D.t).resMap Λ.L).z1 k).2
    refine ⟨Hyp1.mk _ ⟨w, hwZ⟩, k, ⟨k.1.1, single_fst_mem_Z1 _ ((KK D.κ D.t).fnMap.z1 k)⟩, ⟨w, hwZ⟩, ?_, rfl, rfl, hw⟩
    rw [← sub_eq_zero, ← map_sub, GlobalTheory.CatCoh.H1.mk_eq_zero]
    exact ⟨g, hg⟩
  · obtain ⟨w, rfl⟩ := Hyp1.mk_surjective _ h
    obtain ⟨k0, hk0, -⟩ := hK w.1
    have hk0Z : k0 ∈ ((KK D.κ D.t).res Λ.L).Z1 := ((hZ _ _ hk0).1).2 w.2
    obtain ⟨x, hx⟩ := hres.2 (QuotientAddGroup.mk ⟨k0, hk0Z⟩)
    obtain ⟨k, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨g, hg⟩ := (cx_H1_mk_eq_zero_iff _ (((KK D.κ D.t).resMap Λ.L).z1 k - ⟨k0, hk0Z⟩)).1
      (by rw [QuotientAddGroup.mk_sub]; exact sub_eq_zero.2 hx)
    obtain ⟨w1, hw1, -⟩ := hW (((KK D.κ D.t).resMap Λ.L).p1 k.1)
    have hw1Z : w1 ∈ cechDeRhamTotalCocyclesOne (OAff D.s) := ((hZ _ _ hw1).1).1 (((KK D.κ D.t).resMap Λ.L).z1 k).2
    obtain ⟨g', hg'⟩ := (hZ _ _ (smoothLiftThickenings_restrictionOne_sub Λ hw1 hk0)).2.1 ⟨g, hg⟩
    refine ⟨GlobalTheory.CatCoh.H1.mk _ ⟨k.1.1, single_fst_mem_Z1 _ ((KK D.κ D.t).fnMap.z1 k)⟩, k, _, ⟨w1, hw1Z⟩, rfl, ?_,
      rfl, hw1⟩
    rw [← sub_eq_zero, ← map_sub, Hyp1.mk_eq_zero]
    exact ⟨g', hg'⟩
  · rintro c h ⟨k, f, w, rfl, rfl, hkf, hR⟩
    rw [GlobalTheory.CatCoh.H1.mk_eq_zero, Hyp1.mk_eq_zero, ← hkf]
    exact (key k).trans (hZ _ _ hR).2

set_option maxHeartbeats 1000000 in

theorem crystallineCechDeRham_degreeTwo_relation_total : (∀ c, ∃ h, Λ.Rel2 c h) ∧ (∀ h, ∃ c, Λ.Rel2 c h) ∧
    ∀ c h, Λ.Rel2 c h → (c = 0 ↔ h = 0) := by
  have hfn := (GlobalTheory.T.fnMap_pullbackBijective12_kk_and_res D.R D.I D.κ D.X₀ D.t D.X D.i).1.2
  have hres := (GlobalTheory.T.lift_restriction_bijective_low_degrees D Λ).2
  obtain ⟨hW, hK, hZ⟩ := GlobalTheory.T.compatibleFormsCochains_eq_deRhamCochains_smoothLift.2 D Λ
  have key : ∀ k : (KK D.κ D.t).Z2, (∃ g, GlobalTheory.CatCoh.d1 (O D.κ D.t) g = k.1.1) ↔
      ∃ g, ((KK D.κ D.t).res Λ.L).D1 g = ((KK D.κ D.t).resMap Λ.L).p2 k.1 := fun k ↦ by
    have e := (map_eq_zero_iff _ hfn.1 (x := (QuotientAddGroup.mk k : (KK D.κ D.t).H2))).trans
      (map_eq_zero_iff _ hres.1).symm
    exact ((single_H2_mk_eq_zero_iff (O D.κ D.t) ((KK D.κ D.t).fnMap.z2 k)).symm.trans e).trans
      (cx_H2_mk_eq_zero_iff _ (((KK D.κ D.t).resMap Λ.L).z2 k))
  refine ⟨fun c ↦ ?_, fun h ↦ ?_, ?_⟩
  · obtain ⟨f, rfl⟩ := GlobalTheory.CatCoh.H2.mk_surjective _ c
    obtain ⟨x, hx⟩ := hfn.2 (QuotientAddGroup.mk ⟨_, single2_mem (O D.κ D.t) f⟩)
    obtain ⟨k, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨g, hg⟩ := (single_H2_mk_eq_zero_iff (O D.κ D.t) ((KK D.κ D.t).fnMap.z2 k - ⟨_, single2_mem _ f⟩)).1
      (by rw [QuotientAddGroup.mk_sub]; exact sub_eq_zero.2 hx)
    obtain ⟨w, hw, -⟩ := hW (((KK D.κ D.t).resMap Λ.L).p2 k.1)
    have hwZ : w ∈ cechDeRhamTotalCocyclesTwo (OAff D.s) := ((hZ _ _ hw).1).1 (((KK D.κ D.t).resMap Λ.L).z2 k).2
    refine ⟨Hyp2.mk _ ⟨w, hwZ⟩, k, ⟨k.1.1, single_fst_mem_Z2 _ ((KK D.κ D.t).fnMap.z2 k)⟩, ⟨w, hwZ⟩, ?_, rfl, rfl, hw⟩
    rw [← sub_eq_zero, ← map_sub, GlobalTheory.CatCoh.H2.mk_eq_zero]
    exact ⟨g, hg⟩
  · obtain ⟨w, rfl⟩ := Hyp2.mk_surjective _ h
    obtain ⟨k0, hk0, -⟩ := hK w.1
    have hk0Z : k0 ∈ ((KK D.κ D.t).res Λ.L).Z2 := ((hZ _ _ hk0).1).2 w.2
    obtain ⟨x, hx⟩ := hres.2 (QuotientAddGroup.mk ⟨k0, hk0Z⟩)
    obtain ⟨k, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨g, hg⟩ := (cx_H2_mk_eq_zero_iff _ (((KK D.κ D.t).resMap Λ.L).z2 k - ⟨k0, hk0Z⟩)).1
      (by rw [QuotientAddGroup.mk_sub]; exact sub_eq_zero.2 hx)
    obtain ⟨w1, hw1, -⟩ := hW (((KK D.κ D.t).resMap Λ.L).p2 k.1)
    have hw1Z : w1 ∈ cechDeRhamTotalCocyclesTwo (OAff D.s) := ((hZ _ _ hw1).1).1 (((KK D.κ D.t).resMap Λ.L).z2 k).2
    have hR : Λ.Res2 (((KK D.κ D.t).resMap Λ.L).p2 k.1 - k0) (w1 - w.1) := smoothLiftThickenings_restrictionTwo_sub Λ hw1 hk0
    have hE := ((hZ _ _ hR).2).1
    obtain ⟨g', hg'⟩ := hE ⟨g, by rw [hg, AddSubgroup.coe_sub]; rfl⟩
    refine ⟨GlobalTheory.CatCoh.H2.mk _ ⟨k.1.1, single_fst_mem_Z2 _ ((KK D.κ D.t).fnMap.z2 k)⟩, k, _, ⟨w1, hw1Z⟩, rfl, ?_,
      rfl, hw1⟩
    rw [← sub_eq_zero, ← map_sub, Hyp2.mk_eq_zero]
    exact ⟨g', hg'⟩
  · rintro c h ⟨k, f, w, rfl, rfl, hkf, hR⟩
    rw [GlobalTheory.CatCoh.H2.mk_eq_zero, Hyp2.mk_eq_zero, ← hkf]
    exact (key k).trans (hZ _ _ hR).2

end Main

theorem rel_total_zero : (∀ (D : Data) (Λ : Lift D), (∀ c, ∃ h, Λ.Rel1 c h) ∧ (∀ h, ∃ c, Λ.Rel1 c h) ∧
    ∀ c h, Λ.Rel1 c h → (c = 0 ↔ h = 0)) ∧ ∀ (D : Data) (Λ : Lift D), (∀ c, ∃ h, Λ.Rel2 c h) ∧
    (∀ h, ∃ c, Λ.Rel2 c h) ∧ ∀ c h, Λ.Rel2 c h → (c = 0 ↔ h = 0) :=
  ⟨crystallineCechDeRham_degreeOne_relation_total, crystallineCechDeRham_degreeTwo_relation_total⟩

end GlobalTheory.PDForm
