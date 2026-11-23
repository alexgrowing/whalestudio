import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section
namespace GlobalTheory.ZH

open GlobalTheory.Points

abbrev OO (p : ℕ) [Fact p.Prime] : ValuationSubring (PadicAlgCl p) :=
  (Valued.v : Valuation (PadicAlgCl p) NNReal).valuationSubring

abbrev cPt (p : ℕ) [Fact p.Prime] : Sp (OO p) := IsLocalRing.closedPoint (OO p)

abbrev gPt (p : ℕ) [Fact p.Prime] : Sp (PadicAlgCl p) ⟶ Sp (OO p) := spMap (OO p).subtype

theorem mem_OO_iff {p : ℕ} [Fact p.Prime] (x : PadicAlgCl p) : x ∈ OO p ↔ ‖x‖ ≤ 1 := by
  rw [OO, Valuation.mem_valuationSubring_iff, PadicAlgCl.valuation_def, ← NNReal.coe_le_one, coe_nnnorm]

theorem not_isUnit_OO_iff {p : ℕ} [Fact p.Prime] (x : OO p) : ¬ IsUnit x ↔ ‖(x : PadicAlgCl p)‖ < 1 := by
  have hx : ‖(x : PadicAlgCl p)‖ ≤ 1 := (mem_OO_iff _).1 x.2
  constructor
  · intro h
    by_contra h'
    have h1 : ‖(x : PadicAlgCl p)‖ = 1 := le_antisymm hx (not_lt.1 h')
    have h0 : (x : PadicAlgCl p) ≠ 0 := by
      intro e
      rw [e, norm_zero] at h1
      exact zero_ne_one h1
    apply h
    refine isUnit_iff_exists_inv.2 ⟨⟨(x : PadicAlgCl p)⁻¹, (mem_OO_iff _).2 (by rw [norm_inv, h1, inv_one])⟩, ?_⟩
    exact Subtype.ext (mul_inv_cancel₀ h0)
  · rintro h ⟨u, rfl⟩
    have h2 : ‖(((u⁻¹ : (OO p)ˣ) : OO p) : PadicAlgCl p)‖ ≤ 1 := (mem_OO_iff _).1 ((u⁻¹ : (OO p)ˣ) : OO p).2
    have e : ((u : OO p) : PadicAlgCl p) * (((u⁻¹ : (OO p)ˣ) : OO p) : PadicAlgCl p) = 1 := by
      have := congrArg (fun y : OO p => (y : PadicAlgCl p)) u.mul_inv
      simpa only [MulMemClass.coe_mul, OneMemClass.coe_one] using this
    have e2 : ‖((u : OO p) : PadicAlgCl p)‖ * ‖(((u⁻¹ : (OO p)ˣ) : OO p) : PadicAlgCl p)‖ = 1 := by
      rw [← norm_mul, e, norm_one]
    have e3 := mul_le_mul_of_nonneg_left h2 (norm_nonneg ((u : OO p) : PadicAlgCl p))
    linarith

theorem top_le_preimage_iff {X Y : Scheme.{0}} (y : Y ⟶ X) (U : X.Opens) :
    ⊤ ≤ y ⁻¹ᵁ U ↔ Set.range y ⊆ U := by
  constructor
  · rintro h _ ⟨w, rfl⟩
    exact h (show w ∈ (⊤ : Y.Opens) from trivial)
  · intro h w _
    exact h ⟨w, rfl⟩

theorem top_le_preimage_of_specializes {X Y : Scheme.{0}} {y : Y ⟶ X} {z : X} (h : ∀ w, y w ⤳ z)
    {U : X.Opens} (hz : z ∈ U) : ⊤ ≤ y ⁻¹ᵁ U := fun w _ => (h w).mem_open U.isOpen hz

structure RatModel (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] where

  Z : Scheme.{0}
  [integral : IsIntegral Z]

  s : Z ⟶ Sp o
  sep : IsSeparated s
  lft : LocallyOfFiniteType s
  qc : QuasiCompact s

  pt : Sp Ω ⟶ Z
  pt_s : pt ≫ s = spMap (algebraMap o Ω)
  gen : Set.range pt = {genericPoint Z}
  onto : ∀ x : Ω, ∃ (U : Z.Opens) (f : Γ(Z, U)), (U : Set Z).Nonempty ∧ valF pt U f = x

attribute [instance] RatModel.integral

namespace RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)

theorem pt_apply (w : Sp Ω) : M.pt w = genericPoint M.Z := by
  have h : M.pt w ∈ Set.range M.pt := ⟨w, rfl⟩
  rw [M.gen] at h
  exact h

theorem pt_specializes (w : Sp Ω) (z : M.Z) : M.pt w ⤳ z := by
  rw [M.pt_apply]
  exact genericPoint_specializes z

theorem top_le_preimage_pt {U : M.Z.Opens} (hU : (U : Set M.Z).Nonempty) : ⊤ ≤ M.pt ⁻¹ᵁ U := by
  obtain ⟨z, hz⟩ := hU
  exact top_le_preimage_of_specializes (fun w => M.pt_specializes w z) hz

theorem nonempty_inf {U V : M.Z.Opens} (hU : (U : Set M.Z).Nonempty) (hV : (V : Set M.Z).Nonempty) :
    ((U ⊓ V : M.Z.Opens) : Set M.Z).Nonempty := by
  obtain ⟨z, hz⟩ := hU
  obtain ⟨z', hz'⟩ := hV
  refine ⟨M.pt (IsLocalRing.closedPoint Ω), ?_⟩
  rw [TopologicalSpace.Opens.coe_inf]
  exact ⟨(M.pt_specializes _ z).mem_open U.isOpen hz, (M.pt_specializes _ z').mem_open V.isOpen hz'⟩

instance isDominant_pt : IsDominant M.pt :=
  ⟨by
    rw [DenseRange, M.gen, dense_iff_closure_eq]
    exact genericPoint_spec M.Z⟩

def res (U : M.Z.Opens) (hU : (U : Set M.Z).Nonempty) : Γ(M.Z, U) →+* Ω :=
  (valMap M.pt U (M.top_le_preimage_pt hU)).hom

theorem res_apply (U : M.Z.Opens) (hU : (U : Set M.Z).Nonempty) (f : Γ(M.Z, U)) :
    M.res U hU f = valF M.pt U f := by
  rw [valF_eq_valR, valR_eq _ _ (M.top_le_preimage_pt hU)]
  rfl

theorem valF_resG {U V : M.Z.Opens} (h : V ≤ U) (hV : (V : Set M.Z).Nonempty) (f : Γ(M.Z, U)) :
    valF M.pt V (resG M.Z h f) = valF M.pt U f := by
  rw [valF_eq_valR, valF_eq_valR]
  exact valR_res M.pt h (M.top_le_preimage_pt hV) f

theorem res_resG {U V : M.Z.Opens} (h : V ≤ U) (hV : (V : Set M.Z).Nonempty) (f : Γ(M.Z, U)) :
    M.res V hV (resG M.Z h f) = M.res U (hV.mono h) f := by
  rw [res_apply, res_apply, M.valF_resG h hV]

theorem res_comp_resG {U V : M.Z.Opens} (h : V ≤ U) (hV : (V : Set M.Z).Nonempty) :
    (M.res V hV).comp (resG M.Z h) = M.res U (hV.mono h) := RingHom.ext fun f => M.res_resG h hV f

private theorem stalkClosedPointTo_injective :
    Function.Injective (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) M.pt).hom := by
  have hG : ∀ x : M.Z, x = genericPoint M.Z → IsField (M.Z.presheaf.stalk x) := by
    rintro x rfl
    exact isField_stalk_of_closure_mem_irreducibleComponents M.Z _
      (by simp [irreducibleComponents_eq_singleton])
  have hF := hG _ (M.pt_apply (IsLocalRing.closedPoint Ω))
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra hne
  obtain ⟨b, hb⟩ := hF.mul_inv_cancel hne
  have e := congrArg (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) M.pt).hom hb
  rw [map_mul, ha, zero_mul, map_one] at e
  exact zero_ne_one e

theorem res_injective (U : M.Z.Opens) (hU : (U : Set M.Z).Nonempty) : Function.Injective (M.res U hU) := by
  have h := M.top_le_preimage_pt hU
  have e := germ_stalkClosedPointTo_eq_valMap M.pt U h
  have hf : ∀ a, M.res U hU a = (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) M.pt).hom
      (M.Z.presheaf.germ U _ ((le_preimage_iff M.pt U).1 h) a) := fun a => by
    simp only [res]
    rw [← e]
    rfl
  intro f g hfg
  rw [hf, hf] at hfg
  exact germ_injective_of_isIntegral M.Z _ _ (M.stalkClosedPointTo_injective hfg)

theorem valF_injective {U : M.Z.Opens} (hU : (U : Set M.Z).Nonempty) :
    Function.Injective (valF M.pt U) := by
  intro f g h
  apply M.res_injective U hU
  rw [res_apply, res_apply, h]

theorem resG_eq_of_valF_eq {U V W : M.Z.Opens} (hU : W ≤ U) (hV : W ≤ V) (hW : (W : Set M.Z).Nonempty)
    {f : Γ(M.Z, U)} {g : Γ(M.Z, V)} (h : valF M.pt U f = valF M.pt V g) : resG M.Z hU f = resG M.Z hV g := by
  apply M.valF_injective hW
  rw [M.valF_resG hU hW, M.valF_resG hV hW, h]

theorem valF_constFn {U : M.Z.Opens} (hU : (U : Set M.Z).Nonempty) (a : o) :
    valF M.pt U (constFn M.s U a) = algebraMap o Ω a := by
  rw [valF_eq_valR]
  exact valR_constFn_of_over M.s (algebraMap o Ω) M.pt M.pt_s U (M.top_le_preimage_pt hU) a

def O (z : M.Z) : Subalgebra o Ω where
  carrier := {x | ∃ (U : M.Z.Opens) (f : Γ(M.Z, U)), z ∈ U ∧ valF M.pt U f = x}
  mul_mem' := by
    rintro _ _ ⟨U, f, hU, rfl⟩ ⟨V, g, hV, rfl⟩
    have h : ((U ⊓ V : M.Z.Opens) : Set M.Z).Nonempty := ⟨z, hU, hV⟩
    refine ⟨U ⊓ V, resG M.Z inf_le_left f * resG M.Z inf_le_right g, ⟨hU, hV⟩, ?_⟩
    rw [← M.res_apply _ h, map_mul, res_apply, res_apply, M.valF_resG _ h, M.valF_resG _ h]
  add_mem' := by
    rintro _ _ ⟨U, f, hU, rfl⟩ ⟨V, g, hV, rfl⟩
    have h : ((U ⊓ V : M.Z.Opens) : Set M.Z).Nonempty := ⟨z, hU, hV⟩
    refine ⟨U ⊓ V, resG M.Z inf_le_left f + resG M.Z inf_le_right g, ⟨hU, hV⟩, ?_⟩
    rw [← M.res_apply _ h, map_add, res_apply, res_apply, M.valF_resG _ h, M.valF_resG _ h]
  algebraMap_mem' a := ⟨⊤, constFn M.s ⊤ a, trivial, M.valF_constFn (U := ⊤) ⟨z, trivial⟩ a⟩

def ringOn (U : Set M.Z) : Subalgebra o Ω := ⨅ z ∈ U, M.O z

variable {M}

theorem mem_O {z : M.Z} {x : Ω} :
    x ∈ M.O z ↔ ∃ (U : M.Z.Opens) (f : Γ(M.Z, U)), z ∈ U ∧ valF M.pt U f = x := by rfl

theorem valF_mem_O {z : M.Z} {U : M.Z.Opens} (hz : z ∈ U) (f : Γ(M.Z, U)) : valF M.pt U f ∈ M.O z := ⟨U, f, hz, rfl⟩

theorem exists_affine_of_mem_O {z : M.Z} {x : Ω} (hx : x ∈ M.O z) {V : M.Z.Opens} (hV : z ∈ V) :
    ∃ (U : M.Z.Opens) (f : Γ(M.Z, U)), IsAffineOpen U ∧ z ∈ U ∧ U ≤ V ∧ valF M.pt U f = x := by
  obtain ⟨W, g, hW, rfl⟩ := hx
  obtain ⟨U, hU, hzU, hUs⟩ := exists_isAffineOpen_mem_and_subset (U := W ⊓ V) (x := z) ⟨hW, hV⟩
  have hle : U ≤ W ⊓ V := fun a ha => hUs ha
  exact ⟨U, resG M.Z (hle.trans inf_le_left) g, hU, hzU, hle.trans inf_le_right, M.valF_resG _ ⟨z, hzU⟩ g⟩

theorem mem_ringOn {U : Set M.Z} {x : Ω} : x ∈ M.ringOn U ↔ ∀ z ∈ U, x ∈ M.O z := by
  show x ∈ ⨅ z ∈ U, M.O z ↔ _
  simp only [Algebra.mem_iInf]

theorem ringOn_le_O {U : Set M.Z} {z : M.Z} (hz : z ∈ U) : M.ringOn U ≤ M.O z := fun _ hx => mem_ringOn.1 hx z hz

theorem ringOn_anti {U V : Set M.Z} (h : U ⊆ V) : M.ringOn V ≤ M.ringOn U := fun _ hx => mem_ringOn.2 fun z hz => mem_ringOn.1 hx z (h hz)

theorem mem_ringOn_iff_exists {U : M.Z.Opens} (hU : (U : Set M.Z).Nonempty) {x : Ω} :
    x ∈ M.ringOn U ↔ ∃ f : Γ(M.Z, U), valF M.pt U f = x := by
  constructor
  · intro hx
    have h1 : ∀ z : U, ∃ (W : M.Z.Opens) (g : Γ(M.Z, W)), (z : M.Z) ∈ W ∧ valF M.pt W g = x :=
      fun z => mem_O.1 (mem_ringOn.1 hx z z.2)
    choose W g hzW hg using h1
    let V : U → M.Z.Opens := fun z => W z ⊓ U
    have hVne : ∀ z, ((V z : M.Z.Opens) : Set M.Z).Nonempty := fun z => ⟨z, hzW z, z.2⟩
    let sf : ∀ z : U, Γ(M.Z, V z) := fun z => resG M.Z inf_le_left (g z)
    have hsf : ∀ z, valF M.pt (V z) (sf z) = x := fun z =>
      (M.valF_resG inf_le_left (hVne z) (g z)).trans (hg z)
    have hcomp : TopCat.Presheaf.IsCompatible M.Z.sheaf.1 V sf := by
      intro i j
      exact M.resG_eq_of_valF_eq inf_le_left inf_le_right (M.nonempty_inf (hVne i) (hVne j))
        ((hsf i).trans (hsf j).symm)
    have hcov : U ≤ iSup V := by
      intro y hy
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy⟩, hzW ⟨y, hy⟩, hy⟩
    obtain ⟨s, hs, -⟩ :=
      M.Z.sheaf.existsUnique_gluing' V U (fun z => homOfLE inf_le_right) hcov sf hcomp
    obtain ⟨z0, hz0⟩ := hU
    refine ⟨s, ?_⟩
    rw [← M.valF_resG (inf_le_right : V ⟨z0, hz0⟩ ≤ U) (hVne _) s]
    rw [show resG M.Z (inf_le_right : V ⟨z0, hz0⟩ ≤ U) s = sf ⟨z0, hz0⟩ from hs ⟨z0, hz0⟩, hsf]
  · rintro ⟨f, rfl⟩
    exact mem_ringOn.2 fun z hz => valF_mem_O hz f

variable (M) in

theorem range_res (U : M.Z.Opens) (hU : (U : Set M.Z).Nonempty) :
    (M.res U hU).range = (M.ringOn U).toSubring := by
  ext x
  rw [RingHom.mem_range, Subalgebra.mem_toSubring, mem_ringOn_iff_exists hU]
  simp only [res_apply]

variable (M) in

def sectionsEquiv (U : M.Z.Opens) (hU : (U : Set M.Z).Nonempty) : Γ(M.Z, U) ≃+* M.ringOn U :=
  RingEquiv.ofBijective ((M.res U hU).codRestrict (M.ringOn U) fun f =>
      (mem_ringOn_iff_exists hU).2 ⟨f, (M.res_apply U hU f).symm⟩)
    ⟨fun _ _ h => M.res_injective U hU (congrArg Subtype.val h), fun x => by
      obtain ⟨f, hf⟩ := (mem_ringOn_iff_exists hU).1 x.2
      exact ⟨f, Subtype.ext ((M.res_apply U hU f).trans hf)⟩⟩

theorem coe_sectionsEquiv (U : M.Z.Opens) (hU : (U : Set M.Z).Nonempty) (f : Γ(M.Z, U)) :
    (M.sectionsEquiv U hU f : Ω) = valF M.pt U f := M.res_apply U hU f

variable (M) in

def stalkHom (z : M.Z) : M.Z.presheaf.stalk z →+* Ω :=
  (M.Z.presheaf.stalkSpecializes (M.pt_specializes (IsLocalRing.closedPoint Ω) z) ≫
    Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) M.pt).hom

theorem stalkHom_germ {z : M.Z} {U : M.Z.Opens} (hz : z ∈ U) (f : Γ(M.Z, U)) :
    M.stalkHom z (M.Z.presheaf.germ U z hz f) = valF M.pt U f := by
  have h' : ⊤ ≤ M.pt ⁻¹ᵁ U := M.top_le_preimage_pt ⟨z, hz⟩
  have key : M.Z.presheaf.germ U z hz ≫ M.Z.presheaf.stalkSpecializes
      (M.pt_specializes (IsLocalRing.closedPoint Ω) z) ≫
      Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) M.pt = valMap M.pt U h' := by
    rw [← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes]
    exact germ_stalkClosedPointTo_eq_valMap M.pt U h'
  rw [valF_eq_valR, valR_eq M.pt U h', ← key]
  rfl

variable (M) in

theorem stalkHom_injective (z : M.Z) : Function.Injective (M.stalkHom z) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨U, hz, f, rfl⟩ := M.Z.presheaf.germ_exist a
  rw [stalkHom_germ hz f] at ha
  have hf : f = 0 := M.valF_injective ⟨z, hz⟩ (by rw [ha, ← M.res_apply U ⟨z, hz⟩ 0, map_zero])
  rw [hf, map_zero]

variable (M) in

def stalkEquiv (z : M.Z) : M.Z.presheaf.stalk z ≃+* M.O z :=
  RingEquiv.ofBijective ((M.stalkHom z).codRestrict (M.O z) fun a => by
      obtain ⟨U, hz, f, rfl⟩ := M.Z.presheaf.germ_exist a
      exact ⟨U, f, hz, (stalkHom_germ hz f).symm⟩)
    ⟨fun _ _ h => M.stalkHom_injective z (congrArg Subtype.val h), by
      rintro ⟨_, U, f, hz, rfl⟩
      exact ⟨_, Subtype.ext (stalkHom_germ hz f)⟩⟩

theorem coe_stalkEquiv (z : M.Z) (a : M.Z.presheaf.stalk z) : (M.stalkEquiv z a : Ω) = M.stalkHom z a := rfl

theorem stalkEquiv_germ {z : M.Z} {U : M.Z.Opens} (hz : z ∈ U) (f : Γ(M.Z, U)) :
    M.stalkEquiv z (M.Z.presheaf.germ U z hz f) = ⟨valF M.pt U f, valF_mem_O hz f⟩ := Subtype.ext ((coe_stalkEquiv z _).trans (stalkHom_germ hz f))

instance isLocalRing_O (z : M.Z) : IsLocalRing (M.O z) := (M.stalkEquiv z).isLocalRing

theorem isUnit_O_iff {z : M.Z} (x : M.O z) : IsUnit x ↔ (x : Ω) ≠ 0 ∧ (x : Ω)⁻¹ ∈ M.O z := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : ((u : M.O z) : Ω) * (((u⁻¹ : (M.O z)ˣ) : M.O z) : Ω) = 1 := congrArg Subtype.val u.mul_inv
    refine ⟨left_ne_zero_of_mul_eq_one h1, ?_⟩
    rw [inv_eq_of_mul_eq_one_right h1]
    exact ((u⁻¹ : (M.O z)ˣ) : M.O z).2
  · rintro ⟨h0, hi⟩
    exact ⟨⟨x, ⟨_, hi⟩, Subtype.ext (by simp [h0]), Subtype.ext (by simp [h0])⟩, rfl⟩

theorem isUnit_valF_iff {z : M.Z} {U : M.Z.Opens} (hz : z ∈ U) (f : Γ(M.Z, U)) :
    IsUnit (⟨valF M.pt U f, valF_mem_O hz f⟩ : M.O z) ↔ z ∈ M.Z.basicOpen f := by
  rw [← stalkEquiv_germ hz f, isUnit_map_iff (M.stalkEquiv z), M.Z.mem_basicOpen f z hz]

theorem O_le_of_specializes {ξ z : M.Z} (h : ξ ⤳ z) : M.O z ≤ M.O ξ := by
  intro x hx
  obtain ⟨U, f, hz, rfl⟩ := mem_O.1 hx
  exact valF_mem_O (h.mem_open U.isOpen hz) f

variable (M) in

theorem O_genericPoint : M.O (genericPoint M.Z) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨U, f, hU, rfl⟩ := M.onto x
  exact valF_mem_O (((genericPoint_spec M.Z).mem_open_set_iff U.isOpen).2 (by simpa using hU)) f

theorem exists_eq_div {V : M.Z.Opens} (hV : IsAffineOpen V) (hne : (V : Set M.Z).Nonempty) (x : Ω) :
    ∃ a b : Γ(M.Z, V), valF M.pt V b ≠ 0 ∧ x = valF M.pt V a / valF M.pt V b := by
  obtain ⟨W, f, hW, rfl⟩ := M.onto x
  obtain ⟨z, hz⟩ := M.nonempty_inf hne hW
  simp only [TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe] at hz
  obtain ⟨hzV, hzW⟩ := hz
  obtain ⟨b, hbW, hzb⟩ := hV.exists_basicOpen_le (V := W) ⟨z, hzW⟩ hzV
  have hD : ((M.Z.basicOpen b : M.Z.Opens) : Set M.Z).Nonempty := ⟨z, hzb⟩
  have hb0 : valF M.pt V b ≠ 0 := ((isUnit_O_iff _).1 ((isUnit_valF_iff hzV b).2 hzb)).1
  have := hV.isLocalization_basicOpen b
  obtain ⟨⟨a, s⟩, hx⟩ := IsLocalization.surj (Submonoid.powers b) (resG M.Z hbW f)
  dsimp only at hx
  have key : ∀ c : Γ(M.Z, V),
      M.res _ hD (algebraMap Γ(M.Z, V) Γ(M.Z, M.Z.basicOpen b) c) = valF M.pt V c := fun c => by
    rw [← M.res_apply V hne]
    exact M.res_resG (M.Z.basicOpen_le b) hD c
  have e : valF M.pt _ (resG M.Z hbW f) * valF M.pt V s = valF M.pt V a := by
    have := congrArg (M.res _ hD) hx
    rwa [map_mul, key, key, M.res_apply] at this
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).1 s.2
  have hs0 : valF M.pt V s ≠ 0 := by
    rw [← hn, ← M.res_apply V hne, map_pow, M.res_apply]
    exact pow_ne_zero _ hb0
  refine ⟨a, s, hs0, ?_⟩
  rw [← M.valF_resG hbW hD f, eq_div_iff hs0]
  exact e

theorem isFractionRing_ringOn {V : M.Z.Opens} (hV : IsAffineOpen V) (hne : (V : Set M.Z).Nonempty) :
    IsFractionRing (M.ringOn V) Ω := by
  refine IsFractionRing.of_field _ _ fun x => ?_
  obtain ⟨a, b, -, h⟩ := exists_eq_div hV hne x
  exact ⟨⟨_, (mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩⟩, ⟨_, (mem_ringOn_iff_exists hne).2 ⟨b, rfl⟩⟩, h⟩

instance isFractionRing_O (z : M.Z) : IsFractionRing (M.O z) Ω := by
  refine IsFractionRing.of_field _ _ fun x => ?_
  obtain ⟨V, hV, hz, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := z) trivial
  obtain ⟨a, b, -, h⟩ := exists_eq_div hV ⟨z, hz⟩ x
  exact ⟨⟨_, valF_mem_O hz a⟩, ⟨_, valF_mem_O hz b⟩, h⟩

variable (M) in

theorem isOpen_setOf_mem_O (x : Ω) : IsOpen {z | x ∈ M.O z} := by
  refine isOpen_iff_forall_mem_open.2 fun z hz => ?_
  obtain ⟨U, f, hzU, rfl⟩ := mem_O.1 (show x ∈ M.O z from hz)
  exact ⟨U, fun w hw => valF_mem_O hw f, U.isOpen, hzU⟩

theorem isIntegrallyClosed_O (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z) (z : M.Z) :
    IsIntegrallyClosed (M.O z) := by
  have := (h z).2
  exact IsIntegrallyClosed.of_equiv (M.stalkEquiv z)

variable (M)

def Div {J : Type} (t : J → Ω) (i : J) (z : M.Z) : Prop := t i ≠ 0 ∧ ∀ j, t j / t i ∈ M.O z

def HasDiv {J : Type} (t : J → Ω) : Prop := ∀ z, ∃ i, M.Div t i z

def IsCl {J : Type} (t : J → Ω) : Prop := M.HasDiv t ∧ ∀ i, t i ≠ 0 → ∃ U : M.Z.Opens, IsAffineOpen U ∧
  (U : Set M.Z) = {z | M.Div t i z} ∧ M.ringOn U = Algebra.adjoin o (Set.range fun j => t j / t i)

def IsNm {J : Type} (t : J → Ω) : Prop := M.HasDiv t ∧ ∀ i, t i ≠ 0 → ∃ U : M.Z.Opens, IsAffineOpen U ∧
  (U : Set M.Z) = {z | M.Div t i z} ∧
  ∀ x, x ∈ M.ringOn U ↔ IsIntegral (Algebra.adjoin o (Set.range fun j => t j / t i)) x

theorem isOpen_setOf_div {J : Type} [Finite J] (t : J → Ω) (i : J) : IsOpen {z | M.Div t i z} := by
  by_cases h : t i = 0
  · have e : {z | M.Div t i z} = ∅ := by
      ext z
      simp [Div, h]
    rw [e]
    exact isOpen_empty
  · have e : {z | M.Div t i z} = ⋂ j, {z | t j / t i ∈ M.O z} := by
      ext z
      simp [Div, h]
    rw [e]
    exact isOpen_iInter_of_finite fun j => M.isOpen_setOf_mem_O _

variable {M}

theorem div_genericPoint {J : Type} {t : J → Ω} {i : J} (h : t i ≠ 0) : M.Div t i (genericPoint M.Z) :=
  ⟨h, fun j => by rw [O_genericPoint]; exact Algebra.mem_top⟩

theorem Div.of_specializes {J : Type} {t : J → Ω} {i : J} {ξ z : M.Z} (h : M.Div t i z) (hs : ξ ⤳ z) :
    M.Div t i ξ :=
  ⟨h.1, fun j => O_le_of_specializes hs (h.2 j)⟩

theorem Div.div_iff_isUnit {J : Type} {t : J → Ω} {i : J} {z : M.Z} (h : M.Div t i z) (k : J) :
    M.Div t k z ↔ IsUnit (⟨t k / t i, h.2 k⟩ : M.O z) := by
  rw [isUnit_O_iff]
  show (t k ≠ 0 ∧ ∀ j, t j / t k ∈ M.O z) ↔ t k / t i ≠ 0 ∧ (t k / t i)⁻¹ ∈ M.O z
  have hi := h.1
  constructor
  · rintro ⟨hk, hk'⟩
    refine ⟨div_ne_zero hk hi, ?_⟩
    rw [inv_div]
    exact hk' i
  · rintro ⟨h0, hinv⟩
    have hk : t k ≠ 0 := fun hk => h0 (by rw [hk, zero_div])
    refine ⟨hk, fun j => ?_⟩
    have e : t j / t k = t j / t i * (t k / t i)⁻¹ := by
      rw [inv_div, div_mul_div_comm, mul_comm (t i) (t k), mul_div_mul_right _ _ hi]
    rw [e]
    exact Subalgebra.mul_mem _ (h.2 j) hinv

theorem div_mul_iff {J : Type} {t : J → Ω} {i : J} {z : M.Z} {c : Ω} (hc : c ≠ 0) :
    M.Div (fun j => c * t j) i z ↔ M.Div t i z := by
  simp only [Div]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨right_ne_zero_of_mul h1, fun j => ?_⟩
    rw [← mul_div_mul_left (t j) (t i) hc]
    exact h2 j
  · rintro ⟨h1, h2⟩
    refine ⟨mul_ne_zero hc h1, fun j => ?_⟩
    rw [mul_div_mul_left (t j) (t i) hc]
    exact h2 j

private lemma isIntegral_of_isIntegral_of_le {S T : Subalgebra o Ω} (hST : S ≤ T) {x : Ω} (hx : IsIntegral S x) :
    IsIntegral T x := by
  obtain ⟨p, hp, hpx⟩ := hx
  refine ⟨p.map (Subalgebra.inclusion hST).toRingHom, hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  exact hpx

theorem IsCl.isNm {J : Type} {t : J → Ω} (h : M.IsCl t) (hn : ∀ z, IsIntegrallyClosed (M.O z)) : M.IsNm t := by
  refine ⟨h.1, fun i hi => ?_⟩
  obtain ⟨U, hU, hset, hring⟩ := h.2 i hi
  refine ⟨U, hU, hset, fun x => ?_⟩
  rw [← hring]
  constructor
  · intro hx
    exact isIntegral_algebraMap (R := M.ringOn U) (A := Ω) (x := ⟨x, hx⟩)
  · intro hx
    refine mem_ringOn.2 fun z hz => ?_
    have := hn z
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := M.O z) (K := Ω)).1
      (isIntegral_of_isIntegral_of_le (ringOn_le_O hz) hx)
    rw [← hy]
    exact y.2

variable (M)

open Classical in

def val {K : Type} [Field K] (y : Sp K ⟶ M.Z) (x : Ω) : K :=
  if h : ∃ q : (Σ U : M.Z.Opens, Γ(M.Z, U)), Set.range y ⊆ q.1 ∧ valF M.pt q.1 q.2 = x then
    valF y h.choose.1 h.choose.2 else 0

variable {M}

section Val

variable {K : Type} [Field K]

theorem val_eq {y : Sp K ⟶ M.Z} {U : M.Z.Opens} (hy : Set.range y ⊆ U) {f : Γ(M.Z, U)} {x : Ω}
    (hf : valF M.pt U f = x) : M.val y x = valF y U f := by
  have key : ∀ {V W : M.Z.Opens} (e : W ≤ V), Set.range y ⊆ W → ∀ g : Γ(M.Z, V),
      valF y W (resG M.Z e g) = valF y V g := fun e hW g => by
    rw [valF_eq_valR, valF_eq_valR]
    exact valR_res y e ((top_le_preimage_iff y _).2 hW) g
  have hex : ∃ q : (Σ U : M.Z.Opens, Γ(M.Z, U)), Set.range y ⊆ q.1 ∧ valF M.pt q.1 q.2 = x := ⟨⟨U, f⟩, hy, hf⟩
  unfold RatModel.val
  rw [dif_pos hex]
  obtain ⟨hq1, hq2⟩ := hex.choose_spec
  have hy2 : Set.range y ⊆ ((hex.choose.1 ⊓ U : M.Z.Opens) : Set M.Z) := fun p hp => ⟨hq1 hp, hy hp⟩
  have hW : ((hex.choose.1 ⊓ U : M.Z.Opens) : Set M.Z).Nonempty := ⟨_, hy2 ⟨IsLocalRing.closedPoint K, rfl⟩⟩
  rw [← key (inf_le_left : hex.choose.1 ⊓ U ≤ _) hy2 hex.choose.2, ← key (inf_le_right : hex.choose.1 ⊓ U ≤ U) hy2 f,
    M.resG_eq_of_valF_eq inf_le_left inf_le_right hW (hq2.trans hf.symm)]

theorem val_valF {y : Sp K ⟶ M.Z} {U : M.Z.Opens} (hy : Set.range y ⊆ U) (f : Γ(M.Z, U)) :
    M.val y (valF M.pt U f) = valF y U f := val_eq hy rfl

theorem val_of_notMem {y : Sp K ⟶ M.Z} (w : Sp K) {x : Ω} (hx : x ∉ M.O (y w)) : M.val y x = 0 := by
  unfold RatModel.val
  rw [dif_neg]
  rintro ⟨q, hq, rfl⟩
  exact hx (valF_mem_O (hq ⟨w, rfl⟩) q.2)

theorem val_pt (x : Ω) : M.val M.pt x = x := by
  obtain ⟨U, f, hU, rfl⟩ := M.onto x
  exact val_valF ((top_le_preimage_iff M.pt U).1 (M.top_le_preimage_pt hU)) f

theorem val_algebraMap {y : Sp K ⟶ M.Z} {σ : o →+* K} (hy : y ≫ M.s = spMap σ) (a : o) :
    M.val y (algebraMap o Ω a) = σ a := by
  rw [← M.valF_constFn (U := ⊤) ⟨y (IsLocalRing.closedPoint K), trivial⟩ a, val_valF (U := ⊤) (fun _ _ => trivial),
    valF_eq_valR]
  exact valR_constFn_of_over M.s σ y hy ⊤ (le_preimage_top y) a

theorem specializes_of_range_eq {y : Sp K ⟶ M.Z} {z : M.Z} (h : Set.range y = {z}) (w : Sp K) : y w ⤳ z := by
  have hw : y w ∈ ({z} : Set M.Z) := h ▸ Set.mem_range_self w
  rw [Set.mem_singleton_iff.1 hw]

theorem range_eq_singleton (y : Sp K ⟶ M.Z) (w : Sp K) : Set.range y = {y w} := by
  ext p
  constructor
  · rintro ⟨w', rfl⟩
    rw [Subsingleton.elim w' w]
    rfl
  · rintro rfl
    exact ⟨w, rfl⟩

end Val

def valLoc {C : Type} [CommRing C] [IsLocalRing C] (y : Sp C ⟶ M.Z) (z : M.Z)
    (h : y (IsLocalRing.closedPoint C) ⤳ z) : M.O z →+* C :=
  (M.Z.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of C) y).hom.comp
    (M.stalkEquiv z).symm.toRingHom

theorem valLoc_valF {C : Type} [CommRing C] [IsLocalRing C] (y : Sp C ⟶ M.Z) {z : M.Z}
    (h : y (IsLocalRing.closedPoint C) ⤳ z) {U : M.Z.Opens} (hz : z ∈ U) (f : Γ(M.Z, U)) :
    valLoc y z h ⟨valF M.pt U f, valF_mem_O hz f⟩ = valR y U f := by
  have hy : ⊤ ≤ y ⁻¹ᵁ U := (le_preimage_iff y U).2 (h.mem_open U.isOpen hz)
  have e : (M.stalkEquiv z).symm ⟨valF M.pt U f, valF_mem_O hz f⟩ = M.Z.presheaf.germ U z hz f := by
    rw [RingEquiv.symm_apply_eq, stalkEquiv_germ]
  rw [valR_eq y U hy, ← germ_stalkClosedPointTo_eq_valMap y U hy,
    ← TopCat.Presheaf.germ_stalkSpecializes M.Z.presheaf hz h]
  simp only [valLoc, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e,
    Category.assoc, CommRingCat.hom_comp]

theorem isUnit_valLoc_iff {C : Type} [CommRing C] [IsLocalRing C] (y : Sp C ⟶ M.Z) {z : M.Z}
    (h : y (IsLocalRing.closedPoint C) = z) (x : M.O z) :
    IsUnit (valLoc y z (h ▸ specializes_rfl) x) ↔ IsUnit x := by
  subst h
  have e1 : ∀ p : y (IsLocalRing.closedPoint C) ⤳ y (IsLocalRing.closedPoint C),
      M.Z.presheaf.stalkSpecializes p = 𝟙 _ := fun _ => M.Z.presheaf.stalkSpecializes_refl _
  constructor
  · intro ha
    simp only [valLoc, e1, Category.id_comp, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom] at ha
    have hu := (isUnit_map_iff (Scheme.stalkClosedPointTo (R := CommRingCat.of C) y).hom _).1 ha
    simpa using hu.map (M.stalkEquiv _)
  · intro ha
    exact ha.map _

theorem isLocalHom_valLoc {C : Type} [CommRing C] [IsLocalRing C] (y : Sp C ⟶ M.Z) {z : M.Z}
    (h : y (IsLocalRing.closedPoint C) = z) : IsLocalHom (valLoc y z (h ▸ specializes_rfl)) := ⟨fun a ha => (isUnit_valLoc_iff y h a).1 ha⟩

theorem val_spMap_comp {C K : Type} [CommRing C] [IsLocalRing C] [Field K] (σ : C →+* K) (y : Sp C ⟶ M.Z)
    {z : M.Z} (h : y (IsLocalRing.closedPoint C) ⤳ z) (x : M.O z) :
    M.val (spMap σ ≫ y) x = σ (valLoc y z h x) := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨U, f, hz, rfl⟩ := mem_O.1 hx
  have hy : ⊤ ≤ y ⁻¹ᵁ U := (le_preimage_iff y U).2 (h.mem_open U.isOpen hz)
  have hy' : ⊤ ≤ (spMap σ ≫ y) ⁻¹ᵁ U := le_preimage_comp (spMap σ) y hy (le_preimage_top _)
  refine Eq.trans ?_ (congrArg σ (valLoc_valF y h hz f)).symm
  show M.val (spMap σ ≫ y) (valF M.pt U f) = _
  rw [val_valF ((top_le_preimage_iff _ U).1 hy'), valF_eq_valR, valR_spMap_comp σ y U hy f]

section ValHom

variable {K : Type} [Field K]

theorem valLoc_eq_val (y : Sp K ⟶ M.Z) {z : M.Z} (h : y (IsLocalRing.closedPoint K) ⤳ z) (x : M.O z) :
    valLoc y z h x = M.val y x := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨U, f, hz, rfl⟩ := mem_O.1 hx
  have hy : ⊤ ≤ y ⁻¹ᵁ U := (le_preimage_iff y U).2 (h.mem_open U.isOpen hz)
  refine (valLoc_valF y h hz f).trans ?_
  show valR y U f = M.val y (valF M.pt U f)
  rw [val_valF ((top_le_preimage_iff y U).1 hy), valF_eq_valR]

def valHomOf (y : Sp K ⟶ M.Z) (z : M.Z) (h : ∀ w, y w ⤳ z) : M.O z →+* K :=
  (valLoc y z (h _)).copy (fun x => M.val y x) (funext fun x => (valLoc_eq_val y _ x).symm)

@[simp] theorem valHomOf_apply (y : Sp K ⟶ M.Z) (z : M.Z) (h : ∀ w, y w ⤳ z) (x : M.O z) :
    valHomOf y z h x = M.val y x := rfl

def valHom (y : Sp K ⟶ M.Z) (z : M.Z) (h : Set.range y = {z}) : M.O z →+* K :=
  valHomOf y z (specializes_of_range_eq h)

@[simp] theorem valHom_apply (y : Sp K ⟶ M.Z) (z : M.Z) (h : Set.range y = {z}) (x : M.O z) :
    valHom y z h x = M.val y x := rfl

theorem val_ne_zero_iff {y : Sp K ⟶ M.Z} {z : M.Z} (h : Set.range y = {z}) (x : M.O z) :
    M.val y x ≠ 0 ↔ IsUnit x := by
  have hz : y (IsLocalRing.closedPoint K) = z :=
    Set.mem_singleton_iff.1 (h ▸ Set.mem_range_self (IsLocalRing.closedPoint K))
  rw [← isUnit_valLoc_iff y hz x, valLoc_eq_val, isUnit_iff_ne_zero]

theorem ker_valHom (y : Sp K ⟶ M.Z) (z : M.Z) (h : Set.range y = {z}) :
    RingHom.ker (valHom y z h) = IsLocalRing.maximalIdeal (M.O z) := by
  ext x
  rw [RingHom.mem_ker, valHom_apply, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← val_ne_zero_iff h,
    not_not]

variable {y : Sp K ⟶ M.Z} {z : M.Z}

theorem val_add (h : ∀ w, y w ⤳ z) {a b : Ω} (ha : a ∈ M.O z) (hb : b ∈ M.O z) :
    M.val y (a + b) = M.val y a + M.val y b := by
  have e := map_add (valHomOf y z h) ⟨a, ha⟩ ⟨b, hb⟩
  rw [valHomOf_apply, valHomOf_apply, valHomOf_apply] at e
  exact e

theorem val_mul (h : ∀ w, y w ⤳ z) {a b : Ω} (ha : a ∈ M.O z) (hb : b ∈ M.O z) :
    M.val y (a * b) = M.val y a * M.val y b := by
  have e := map_mul (valHomOf y z h) ⟨a, ha⟩ ⟨b, hb⟩
  rw [valHomOf_apply, valHomOf_apply, valHomOf_apply] at e
  exact e

theorem val_one (y : Sp K ⟶ M.Z) : M.val y 1 = 1 := by
  have h1 : valF M.pt ⊤ (1 : Γ(M.Z, ⊤)) = 1 := by
    rw [valF_eq_valR]
    exact valR_one _ _ (le_preimage_top _)
  rw [val_eq (U := ⊤) (fun _ _ => trivial) h1, valF_eq_valR]
  exact valR_one _ _ (le_preimage_top _)

theorem val_zero (y : Sp K ⟶ M.Z) : M.val y 0 = 0 := by
  have h0 : valF M.pt ⊤ (0 : Γ(M.Z, ⊤)) = 0 := by
    rw [valF_eq_valR]
    exact valR_zero _ _ (le_preimage_top _)
  rw [val_eq (U := ⊤) (fun _ _ => trivial) h0, valF_eq_valR]
  exact valR_zero _ _ (le_preimage_top _)

end ValHom

variable (M)

def IsHom {Ω' : Type} [Field Ω'] [Algebra o Ω'] (M' : RatModel o Ω') (φ : Ω →ₐ[o] Ω') (f : M'.Z ⟶ M.Z) : Prop :=
  M'.pt ≫ f = spMap φ.toRingHom ≫ M.pt

theorem isHom_id : M.IsHom M (AlgHom.id o Ω) (𝟙 M.Z) := by
  show M.pt ≫ 𝟙 M.Z = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ M.pt
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id, Category.id_comp]

variable {M}

section Hom

variable {Ω' : Type} [Field Ω'] [Algebra o Ω'] {M' : RatModel o Ω'} {φ : Ω →ₐ[o] Ω'} {f : M'.Z ⟶ M.Z}

theorem IsHom.comp {Ω'' : Type} [Field Ω''] [Algebra o Ω''] {M'' : RatModel o Ω''} {ψ : Ω' →ₐ[o] Ω''}
    {g : M''.Z ⟶ M'.Z} (hf : M.IsHom M' φ f) (hg : M'.IsHom M'' ψ g) : M.IsHom M'' (ψ.comp φ) (g ≫ f) := by
  have hf' : M'.pt ≫ f = spMap φ.toRingHom ≫ M.pt := hf
  have hg' : M''.pt ≫ g = spMap ψ.toRingHom ≫ M'.pt := hg
  show M''.pt ≫ g ≫ f = Spec.map (CommRingCat.ofHom (ψ.comp φ).toRingHom) ≫ M.pt
  have e : (ψ.comp φ).toRingHom = ψ.toRingHom.comp φ.toRingHom := rfl
  rw [e, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, ← hf', ← Category.assoc, ← Category.assoc, hg']

theorem IsHom.inducedModelMorphism_comp_structureMap (hf : M.IsHom M' φ f) : f ≫ M.s = M'.s := by
  have hf' : M'.pt ≫ f = spMap φ.toRingHom ≫ M.pt := hf
  refine ext_of_isDominant M'.pt ?_
  rw [reassoc_of% hf', M.pt_s, M'.pt_s, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun g => Spec.map (CommRingCat.ofHom g)) φ.comp_algebraMap

theorem IsHom.unique {g : M'.Z ⟶ M.Z} (hf : M.IsHom M' φ f) (hg : M.IsHom M' φ g) : f = g := by
  have hf' : M'.pt ≫ f = spMap φ.toRingHom ≫ M.pt := hf
  have hg' : M'.pt ≫ g = spMap φ.toRingHom ≫ M.pt := hg
  have := M.sep
  exact ext_of_isDominant_of_isSeparated M.s (by rw [hf.inducedModelMorphism_comp_structureMap, hg.inducedModelMorphism_comp_structureMap]) M'.pt (hf'.trans hg'.symm)

theorem IsHom.valF_app (hf : M.IsHom M' φ f) {U : M.Z.Opens} (hU : (U : Set M.Z).Nonempty) (a : Γ(M.Z, U)) :
    valF M'.pt (f ⁻¹ᵁ U) (f.app U a) = φ (valF M.pt U a) := by
  have hf' : M'.pt ≫ f = spMap φ.toRingHom ≫ M.pt := hf
  rw [valF_eq_valR, valF_eq_valR]
  refine (valR_comp M'.pt f U a).symm.trans ?_
  rw [hf']
  exact valR_spMap_comp φ.toRingHom M.pt U (M.top_le_preimage_pt hU) a

theorem IsHom.map_mem_O (hf : M.IsHom M' φ f) {z : M'.Z} {x : Ω} (hx : x ∈ M.O (f z)) : φ x ∈ M'.O z := by
  obtain ⟨U, a, hz, rfl⟩ := mem_O.1 hx
  exact mem_O.2 ⟨f ⁻¹ᵁ U, f.app U a, hz, hf.valF_app ⟨f z, hz⟩ a⟩

theorem IsHom.val_comp (hf : M.IsHom M' φ f) {K : Type} [Field K] (y : Sp K ⟶ M'.Z) (w : Sp K) {x : Ω}
    (hx : x ∈ M.O (f (y w))) : M.val (y ≫ f) x = M'.val y (φ x) := by
  obtain ⟨U, a, hz, rfl⟩ := mem_O.1 hx
  have hy : Set.range y ⊆ (f ⁻¹ᵁ U : Set M'.Z) := by
    rw [range_eq_singleton y w]
    exact Set.singleton_subset_iff.2 hz
  have hyf : Set.range (y ≫ f) ⊆ (U : Set M.Z) := by
    rw [range_eq_singleton (y ≫ f) w]
    exact Set.singleton_subset_iff.2 hz
  rw [val_valF hyf, val_eq hy (hf.valF_app ⟨f (y w), hz⟩ a), valF_eq_valR, valF_eq_valR]
  exact valR_comp y f U a

theorem IsHom.div (hf : M.IsHom M' φ f) {J : Type} {t : J → Ω} {i : J} {z : M'.Z} (h : M.Div t i (f z)) :
    M'.Div (fun j => φ (t j)) i z := by
  show φ (t i) ≠ 0 ∧ ∀ j, φ (t j) / φ (t i) ∈ M'.O z
  refine ⟨(map_ne_zero φ).2 h.1, fun j => ?_⟩
  rw [← map_div₀]
  exact hf.map_mem_O (h.2 j)

end Hom

variable (M) in

def Cen (U : Set M.Z) (z : M.Z) {p : ℕ} [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) : Prop :=
  y (cPt p) = z ∧ Set.range (gPt p ≫ y) ⊆ U

section Classical

variable {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} {z : M.Z}

theorem gPt_specializes (h : y (cPt p) = z) (w : Sp (PadicAlgCl p)) : (gPt p ≫ y) w ⤳ z := by
  subst h
  exact (IsLocalRing.specializes_closedPoint _).map y.continuous

theorem val_gPt (h : y (cPt p) = z) (x : M.O z) :
    M.val (gPt p ≫ y) x = (valLoc y z (h ▸ specializes_rfl) x : OO p) := val_spMap_comp (OO p).subtype y _ x

theorem norm_val_le_one (h : y (cPt p) = z) {x : Ω} (hx : x ∈ M.O z) : ‖M.val (gPt p ≫ y) x‖ ≤ 1 := by
  have e : M.val (gPt p ≫ y) x = (valLoc y z (h ▸ specializes_rfl) ⟨x, hx⟩ : OO p) := val_gPt h ⟨x, hx⟩
  rw [e]
  exact (mem_OO_iff _).1 (SetLike.coe_mem _)

theorem norm_val_lt_one_iff (h : y (cPt p) = z) {x : Ω} (hx : x ∈ M.O z) :
    ‖M.val (gPt p ≫ y) x‖ < 1 ↔ ¬ IsUnit (⟨x, hx⟩ : M.O z) := by
  have e : M.val (gPt p ≫ y) x = (valLoc y z (h ▸ specializes_rfl) ⟨x, hx⟩ : OO p) := val_gPt h ⟨x, hx⟩
  rw [e, ← not_isUnit_OO_iff, isUnit_valLoc_iff y h]

theorem norm_val_eq_one_iff (h : y (cPt p) = z) {x : Ω} (hx : x ∈ M.O z) :
    ‖M.val (gPt p ≫ y) x‖ = 1 ↔ IsUnit (⟨x, hx⟩ : M.O z) := by
  constructor
  · intro h1
    by_contra hn
    have := (norm_val_lt_one_iff h hx).2 hn
    linarith
  · intro hu
    exact le_antisymm (norm_val_le_one h hx) (not_lt.1 fun hl => (norm_val_lt_one_iff h hx).1 hl hu)

theorem Cen.norm_val_le_one {U : Set M.Z} (h : M.Cen U z y) {x : Ω} (hx : x ∈ M.O z) :
    ‖M.val (gPt p ≫ y) x‖ ≤ 1 := RatModel.norm_val_le_one h.1 hx

theorem Cen.norm_val_lt_one_iff {U : Set M.Z} (h : M.Cen U z y) {x : Ω} (hx : x ∈ M.O z) :
    ‖M.val (gPt p ≫ y) x‖ < 1 ↔ ¬ IsUnit (⟨x, hx⟩ : M.O z) := RatModel.norm_val_lt_one_iff h.1 hx

end Classical

variable (M)

structure Lat (J : Type) [Fintype J] [DecidableEq J] where

  E : ∀ z : M.Z, Submodule (M.O z) (J → Ω)
  loc : ∀ z, ∃ (U : M.Z.Opens) (b : Matrix J J Ω), z ∈ U ∧ b.det ≠ 0 ∧
    ∀ z' ∈ U, E z' = Submodule.span (M.O z') (Set.range b)

namespace Lat

variable {J : Type} [Fintype J] [DecidableEq J]

def ofBasis (b : Matrix J J Ω) (hb : b.det ≠ 0) : M.Lat J where
  E z := Submodule.span (M.O z) (Set.range b)
  loc _ := ⟨⊤, b, trivial, hb, fun _ _ => rfl⟩

variable (J) in

def const : M.Lat J := ofBasis M (Matrix.of fun i => Pi.single i 1) (by
  have : (Matrix.of fun i => Pi.single i 1 : Matrix J J Ω) = 1 := by
    ext i j
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [this, Matrix.det_one]
  exact one_ne_zero)

theorem const_E (z : M.Z) :
    (const M J).E z = Submodule.span (M.O z) (Set.range fun i => Pi.single i (1 : Ω)) := rfl

theorem mem_const_iff {z : M.Z} {v : J → Ω} : v ∈ (const M J).E z ↔ ∀ j, v j ∈ M.O z := by
  rw [const_E]
  constructor
  · intro hv j
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      show (Pi.single i (1 : Ω) : J → Ω) j ∈ M.O z
      rw [Pi.single_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul c x _ hx =>
      rw [Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul]
      exact mul_mem c.2 hx
  · intro h
    have e : v = ∑ j, (⟨v j, h j⟩ : M.O z) • Pi.single j (1 : Ω) := by
      ext i
      simp [Subalgebra.smul_def, Finset.sum_apply, Pi.single_apply]
    rw [e]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

variable {M} in

def ofTuple {I : Type} [Finite I] (t : I → Ω) (h : M.HasDiv t) : M.Lat Unit where
  E z := Submodule.span (M.O z) (Set.range fun i _ => t i)
  loc z := by
    obtain ⟨i, hi⟩ := h z
    refine ⟨⟨_, M.isOpen_setOf_div t i⟩, Matrix.of fun _ _ => t i, hi, by simpa using hi.1, fun w hw => ?_⟩
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
    · rintro _ ⟨j, rfl⟩
      have e : (fun _ : Unit => t j) = (⟨t j / t i, hw.2 j⟩ : M.O w) • fun _ : Unit => t i := by
        ext
        simp [Subalgebra.smul_def, hi.1]
      show (fun _ : Unit => t j) ∈ _
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(), rfl⟩)
    · rintro _ ⟨_, rfl⟩
      exact ⟨i, rfl⟩

end Lat

section Affine

variable (o Ω) (A : Type) [CommRing A] [IsDomain A] [Algebra o A] [Algebra.FiniteType o A] [Algebra A Ω]
  [IsScalarTower o A Ω] [IsFractionRing A Ω]

omit [IsDomain A] [IsFractionRing A Ω] in

theorem valF_spMap_algebraMap (a : A) :
    valF (spMap (algebraMap A Ω)) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) = algebraMap A Ω a := by
  rw [valF_eq_valR]
  exact valR_specMap (CommRingCat.ofHom (algebraMap A Ω)) a

private theorem valR_global_eq_algebraMap_gammaSpecIso {L B : Type} [Field L] [CommRing B] [Algebra B L] (y : Γ(Sp B, ⊤)) :
    valR (spMap (algebraMap B L)) ⊤ y = algebraMap B L ((Scheme.ΓSpecIso (CommRingCat.of B)).hom y) := by
  have e := valF_spMap_algebraMap L B ((Scheme.ΓSpecIso (CommRingCat.of B)).hom y)
  rw [CategoryTheory.Iso.hom_inv_id_apply, valF_eq_valR] at e
  exact e

private theorem valR_restrict_basicOpen_eq_valR_global {L B : Type} [Field L] [CommRing B] [Algebra B L] (r y : Γ(Sp B, ⊤))
    (h : ⊤ ≤ (spMap (algebraMap B L)) ⁻¹ᵁ (Sp B).basicOpen r) :
    valR (spMap (algebraMap B L)) _ (algebraMap Γ(Sp B, ⊤) Γ(Sp B, (Sp B).basicOpen r) y) =
      valR (spMap (algebraMap B L)) ⊤ y :=
  valR_res _ ((Sp B).basicOpen_le r) h y

private theorem le_spMap_preimage_basicOpen_of_algebraMap_ne_zero {L B : Type} [Field L] [CommRing B] [Algebra B L] (g : B)
    (hg : algebraMap B L g ≠ 0) :
    ⊤ ≤ (spMap (algebraMap B L)) ⁻¹ᵁ (Sp B).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of B)).inv g) :=
  (le_preimage_basicOpen_iff (spMap (algebraMap B L)) (le_preimage_top _) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv g)).2 (by
    rw [← valF_eq_valR, valF_spMap_algebraMap]
    exact hg.isUnit)

omit [IsDomain A] in

theorem exists_valF_basicOpen_eq_div (a b : A) (hb : algebraMap A Ω b ≠ 0) :
    ∃ f : Γ(Sp A, (Sp A).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv b)),
      valF (spMap (algebraMap A Ω)) _ f = algebraMap A Ω a / algebraMap A Ω b := by
  have h := le_spMap_preimage_basicOpen_of_algebraMap_ne_zero b hb
  let s : Submonoid.powers ((Scheme.ΓSpecIso (CommRingCat.of A)).inv b) := ⟨_, Submonoid.mem_powers _⟩
  refine ⟨IsLocalization.mk' Γ(Sp A, (Sp A).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv b)) ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) s, ?_⟩
  have e := congrArg (valR (spMap (algebraMap A Ω)) _)
    (IsLocalization.mk'_spec Γ(Sp A, (Sp A).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv b)) ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) s)
  rw [valR_mul _ _ h, valR_restrict_basicOpen_eq_valR_global _ _ h, valR_restrict_basicOpen_eq_valR_global _ _ h] at e
  dsimp only [s] at e
  rw [valR_global_eq_algebraMap_gammaSpecIso, valR_global_eq_algebraMap_gammaSpecIso, CategoryTheory.Iso.inv_hom_id_apply,
    CategoryTheory.Iso.inv_hom_id_apply] at e
  rw [eq_div_iff hb, valF_eq_valR]
  exact e

private theorem exists_valF_basicOpen_eq_div_pow (g : A) (hg : algebraMap A Ω g ≠ 0)
    (f : Γ(Sp A, (Sp A).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv g))) :
    ∃ (a : A) (n : ℕ), valF (spMap (algebraMap A Ω)) _ f = algebraMap A Ω a / algebraMap A Ω g ^ n := by
  have h := le_spMap_preimage_basicOpen_of_algebraMap_ne_zero g hg
  obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers ((Scheme.ΓSpecIso (CommRingCat.of A)).inv g)) f
  obtain ⟨n, hn⟩ := s.2
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).hom x, n, ?_⟩
  have e := congrArg (valR (spMap (algebraMap A Ω)) _) hs
  dsimp only at e
  rw [valR_mul _ _ h, valR_restrict_basicOpen_eq_valR_global _ _ h, valR_restrict_basicOpen_eq_valR_global _ _ h, ← hn, valR_pow _ _ (le_preimage_top _),
    valR_global_eq_algebraMap_gammaSpecIso, valR_global_eq_algebraMap_gammaSpecIso, CategoryTheory.Iso.inv_hom_id_apply] at e
  rw [eq_div_iff (pow_ne_zero n hg), valF_eq_valR]
  exact e

private theorem exists_valF_eq_div_of_not_mem_prime {z : PrimeSpectrum A} {U : (Sp A).Opens} (hz : z ∈ U) (f : Γ(Sp A, U)) :
    ∃ a b : A, b ∉ z.asIdeal ∧
      valF (spMap (algebraMap A Ω)) U f = algebraMap A Ω a / algebraMap A Ω b := by
  obtain ⟨_, ⟨g, rfl⟩, hzg, hgU⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.1 PrimeSpectrum.isBasis_basic_opens hz
  have hzg' : g ∉ z.asIdeal := hzg
  have hg : algebraMap A Ω g ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A Ω)).2 fun h0 => hzg' (h0 ▸ z.asIdeal.zero_mem)
  have hle : (Sp A).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv g) ≤ U :=
    (basicOpen_eq_of_affine (R := CommRingCat.of A) g).le.trans hgU
  obtain ⟨a, n, e⟩ := exists_valF_basicOpen_eq_div_pow Ω A g hg (resG (Sp A) hle f)
  refine ⟨a, g ^ n, fun hn => hzg' (z.isPrime.mem_of_pow_mem n hn), ?_⟩
  rw [map_pow, ← e, valF_eq_valR, valF_eq_valR]
  exact (valR_res _ hle (le_spMap_preimage_basicOpen_of_algebraMap_ne_zero g hg) f).symm

def ofAffine : RatModel o Ω where
  Z := Sp A
  s := spMap (algebraMap o A)
  sep := inferInstance
  lft := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2
    (RingHom.finiteType_algebraMap.2 inferInstance)
  qc := inferInstance
  pt := spMap (algebraMap A Ω)
  pt_s := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  gen := by
    have h : ∀ w : Sp Ω, spMap (algebraMap A Ω) w = genericPoint (Sp A) := fun w => by
      rw [genericPoint_eq_bot_of_affine]
      refine PrimeSpectrum.ext ?_
      show Ideal.comap (algebraMap A Ω) w.asIdeal = ⊥
      rw [Subsingleton.elim w (⊥ : PrimeSpectrum Ω)]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective A Ω)
    exact Set.eq_singleton_iff_unique_mem.2 ⟨⟨_, h (IsLocalRing.closedPoint Ω)⟩, by
      rintro _ ⟨w, rfl⟩
      exact h w⟩
  onto x := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A x
    have hb0 := nonZeroDivisors.ne_zero hb
    obtain ⟨f, hf⟩ := exists_valF_basicOpen_eq_div Ω A a b
      ((map_ne_zero_iff _ (IsFractionRing.injective A Ω)).2 hb0)
    refine ⟨_, f, ⟨(⊥ : PrimeSpectrum A), ?_⟩, hf⟩
    rw [basicOpen_eq_of_affine]
    exact hb0

variable {o Ω A}

theorem mem_O_ofAffine {z : PrimeSpectrum A} {x : Ω} :
    x ∈ (ofAffine o Ω A).O z ↔ ∃ a b : A, b ∉ z.asIdeal ∧ x = algebraMap A Ω a / algebraMap A Ω b := by
  constructor
  · intro hx
    obtain ⟨U, f, hz, rfl⟩ := mem_O.1 hx
    obtain ⟨a, b, hb, e⟩ := exists_valF_eq_div_of_not_mem_prime Ω A hz f
    exact ⟨a, b, hb, e⟩
  · rintro ⟨a, b, hb, rfl⟩
    have hb0 : algebraMap A Ω b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective A Ω)).2 fun h0 => hb (h0 ▸ z.asIdeal.zero_mem)
    obtain ⟨f, hf⟩ := exists_valF_basicOpen_eq_div Ω A a b hb0
    refine mem_O.2 ⟨_, f, ?_, hf⟩
    rw [basicOpen_eq_of_affine]
    exact hb

theorem algebraMap_mem_O_ofAffine (z : PrimeSpectrum A) (a : A) : algebraMap A Ω a ∈ (ofAffine o Ω A).O z :=
  mem_O.2 ⟨⊤, (Scheme.ΓSpecIso (CommRingCat.of A)).inv a, trivial, valF_spMap_algebraMap Ω A a⟩

theorem inv_mem_O_ofAffine_iff {z : PrimeSpectrum A} {a : A} (ha : a ≠ 0) :
    (algebraMap A Ω a)⁻¹ ∈ (ofAffine o Ω A).O z ↔ a ∉ z.asIdeal := by
  have had : algebraMap A Ω a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A Ω)).2 ha
  constructor
  · intro h ha'
    obtain ⟨c, d, hd, e⟩ := mem_O_ofAffine.1 h
    have hd0 : algebraMap A Ω d ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective A Ω)).2 fun h0 => hd (h0 ▸ z.asIdeal.zero_mem)
    have key : algebraMap A Ω (a * c) = algebraMap A Ω d := by
      have h1 : algebraMap A Ω a * (algebraMap A Ω c / algebraMap A Ω d) = 1 := by
        rw [← e, mul_inv_cancel₀ had]
      rwa [mul_div_assoc', div_eq_one_iff_eq hd0, ← map_mul] at h1
    exact hd (IsFractionRing.injective A Ω key ▸ z.asIdeal.mul_mem_right c ha')
  · intro h
    exact mem_O_ofAffine.2 ⟨1, a, h, by rw [map_one, one_div]⟩

theorem mem_ringOn_basicOpen_ofAffine {b : A} (hb : b ≠ 0) {x : Ω} :
    x ∈ (ofAffine o Ω A).ringOn {z : PrimeSpectrum A | b ∉ z.asIdeal} ↔
      ∃ (a : A) (n : ℕ), x = algebraMap A Ω a / algebraMap A Ω b ^ n := by
  constructor
  · intro hx
    have hg : algebraMap A Ω b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A Ω)).2 hb
    have hx' : x ∈ (ofAffine o Ω A).ringOn (((Sp A).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv b) : (Sp A).Opens) : Set (Sp A)) := by
      rw [basicOpen_eq_of_affine]
      exact hx
    have hmem : (⊥ : PrimeSpectrum A) ∈ PrimeSpectrum.basicOpen b :=
      (PrimeSpectrum.mem_basicOpen b ⊥).2 (by simpa using hb)
    have hne : (((Sp A).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv b) : (Sp A).Opens) : Set (Sp A)).Nonempty := by
      rw [basicOpen_eq_of_affine]
      exact ⟨_, hmem⟩
    obtain ⟨f, rfl⟩ := (mem_ringOn_iff_exists hne).1 hx'
    obtain ⟨a, n, e⟩ := exists_valF_basicOpen_eq_div_pow Ω A b hg f
    exact ⟨a, n, e⟩
  · rintro ⟨a, n, rfl⟩
    refine mem_ringOn.2 fun z hz => mem_O_ofAffine.2
      ⟨a, b ^ n, fun h => hz (z.isPrime.mem_of_pow_mem n h), by rw [map_pow]⟩

theorem mem_ringOn_univ_ofAffine {x : Ω} :
    x ∈ (ofAffine o Ω A).ringOn Set.univ ↔ x ∈ (algebraMap A Ω).range := by
  constructor
  · intro hx
    have hU : ((⊤ : (ofAffine o Ω A).Z.Opens) : Set (ofAffine o Ω A).Z).Nonempty :=
      ⟨(⊥ : PrimeSpectrum A), trivial⟩
    have hx' : x ∈ (ofAffine o Ω A).ringOn ((⊤ : (ofAffine o Ω A).Z.Opens) : Set (ofAffine o Ω A).Z) := by
      rwa [TopologicalSpace.Opens.coe_top]
    obtain ⟨f, rfl⟩ := (mem_ringOn_iff_exists hU).1 hx'
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).hom f, ?_⟩
    exact ((valF_eq_valR _ _ _).trans (valR_global_eq_algebraMap_gammaSpecIso (L := Ω) (B := A) f)).symm
  · rintro ⟨a, rfl⟩
    exact mem_ringOn.2 fun z _ => algebraMap_mem_O_ofAffine z a

theorem val_ofAffine {K : Type} [Field K] (σ : A →+* K) (a : A) :
    (ofAffine o Ω A).val (spMap σ) (algebraMap A Ω a) = σ a := by
  have e := val_valF (M := ofAffine o Ω A) (y := spMap σ) (U := ⊤) (fun _ _ => trivial)
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)
  erw [valF_spMap_algebraMap Ω A a] at e
  exact e.trans ((valF_eq_valR (spMap σ) ⊤ _).trans (valR_specMap (CommRingCat.ofHom σ) a))

theorem isIntegrallyClosed_O_ofAffine [IsIntegrallyClosed A] (z : PrimeSpectrum A) :
    IsIntegrallyClosed ((ofAffine o Ω A).O z) := by
  let _ : Algebra A ((ofAffine o Ω A).O z) :=
    ((algebraMap A Ω).codRestrict ((ofAffine o Ω A).O z) (algebraMap_mem_O_ofAffine z)).toAlgebra
  have inj : Function.Injective (algebraMap A Ω) := IsFractionRing.injective A Ω
  have ne0 : ∀ {b : A}, b ∉ z.asIdeal → algebraMap A Ω b ≠ 0 := fun hb =>
    (map_ne_zero_iff _ inj).2 fun h0 => hb (h0 ▸ z.asIdeal.zero_mem)
  have : IsLocalization z.asIdeal.primeCompl ((ofAffine o Ω A).O z) := by
    refine (isLocalization_iff z.asIdeal.primeCompl ((ofAffine o Ω A).O z)).2 ⟨fun s => ?_, fun y => ?_, fun {x y} h => ?_⟩
    · have hs : (s : A) ∉ z.asIdeal := Ideal.mem_primeCompl_iff.1 s.2
      refine isUnit_iff_exists_inv.2
        ⟨⟨(algebraMap A Ω s)⁻¹, (inv_mem_O_ofAffine_iff ((map_ne_zero_iff _ inj).1 (ne0 hs))).2 hs⟩, ?_⟩
      exact Subtype.ext (mul_inv_cancel₀ (ne0 hs))
    · obtain ⟨a, b, hb, e⟩ := mem_O_ofAffine.1 y.2
      refine ⟨(a, ⟨b, Ideal.mem_primeCompl_iff.2 hb⟩), Subtype.ext ?_⟩
      show (y : Ω) * algebraMap A Ω b = algebraMap A Ω a
      rw [e, div_mul_cancel₀ _ (ne0 hb)]
    · exact ⟨1, by rw [inj (congrArg Subtype.val h)]⟩
  exact isIntegrallyClosed_of_isLocalization _ z.asIdeal.primeCompl
    (fun s hs => mem_nonZeroDivisors_of_ne_zero fun h => Ideal.mem_primeCompl_iff.1 hs (h ▸ z.asIdeal.zero_mem))

theorem isHom_ofAffine {Ω' B : Type} [Field Ω'] [Algebra o Ω'] [CommRing B] [IsDomain B] [Algebra o B]
    [Algebra.FiniteType o B] [Algebra B Ω'] [IsScalarTower o B Ω'] [IsFractionRing B Ω'] (φ : Ω →ₐ[o] Ω')
    (ψ : A →+* B) (h : ∀ a, algebraMap B Ω' (ψ a) = φ (algebraMap A Ω a)) :
    (ofAffine o Ω A).IsHom (ofAffine o Ω' B) φ (spMap ψ) := by
  show spMap (algebraMap B Ω') ≫ spMap ψ = spMap φ.toRingHom ≫ spMap (algebraMap A Ω)
  have e : (algebraMap B Ω').comp ψ = φ.toRingHom.comp (algebraMap A Ω) := RingHom.ext h
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e]

end Affine

theorem isCl_ofAffine_self [IsDomain o] [IsFractionRing o Ω] {J : Type} (t : J → o)
    (ht : Ideal.span (Set.range t) = ⊤) : (ofAffine o Ω o).IsCl fun j => algebraMap o Ω (t j) := by
  have inj : Function.Injective (algebraMap o Ω) := IsFractionRing.injective o Ω
  have invMem : ∀ (i : J) (S : Subalgebra o Ω),
      (∀ j, algebraMap o Ω (t j) / algebraMap o Ω (t i) ∈ S) → (algebraMap o Ω (t i))⁻¹ ∈ S := by
    intro i S hS
    obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1
      (ht ▸ Submodule.mem_top : (1 : o) ∈ Ideal.span (Set.range t))
    have key : (algebraMap o Ω (t i))⁻¹ =
        c.sum fun j a => algebraMap o Ω a * (algebraMap o Ω (t j) / algebraMap o Ω (t i)) := by
      rw [← one_div, ← map_one (algebraMap o Ω), ← hc]
      simp only [Finsupp.sum, map_sum, Finset.sum_div, smul_eq_mul, map_mul, mul_div_assoc]
    rw [key]
    exact sum_mem fun j _ => mul_mem (Subalgebra.algebraMap_mem _ _) (hS j)
  have divIff : ∀ (z : PrimeSpectrum o) (i : J),
      (ofAffine o Ω o).Div (fun j => algebraMap o Ω (t j)) i z ↔ t i ∉ z.asIdeal := by
    intro z i
    constructor
    · intro hd
      obtain ⟨hi0, hdiv⟩ := hd
      have hti : t i ≠ 0 := fun h => hi0 (by simp [h])
      exact (inv_mem_O_ofAffine_iff hti).1 (invMem i _ hdiv)
    · intro h
      exact And.intro ((map_ne_zero_iff _ inj).2 fun h0 => h (h0 ▸ z.asIdeal.zero_mem))
        fun j => mem_O_ofAffine.2 ⟨t j, t i, h, rfl⟩
  refine And.intro (fun (z : PrimeSpectrum o) => ?_) (fun i hi => ?_)
  · by_contra hz
    push Not at hz
    have hle : Ideal.span (Set.range t) ≤ z.asIdeal := Ideal.span_le.2 (by
      rintro _ ⟨j, rfl⟩
      by_contra h
      exact hz j ((divIff z j).2 h))
    exact z.isPrime.ne_top (top_le_iff.1 (ht ▸ hle))
  · have hti : t i ≠ 0 := fun h => hi (by simp [h])
    refine ⟨PrimeSpectrum.basicOpen (t i), IsAffineOpen.Spec_basicOpen (R := CommRingCat.of o) (t i), ?_, ?_⟩
    · ext z
      exact (divIff z i).symm
    · apply le_antisymm
      · intro x hx
        obtain ⟨a, n, rfl⟩ := (mem_ringOn_basicOpen_ofAffine (Ω := Ω) hti).1 hx
        rw [div_eq_mul_inv, ← inv_pow]
        exact mul_mem (Subalgebra.algebraMap_mem _ a)
          (pow_mem (invMem i (Algebra.adjoin o (Set.range fun j => algebraMap o Ω (t j) / algebraMap o Ω (t i))) fun j => Algebra.subset_adjoin ⟨j, rfl⟩) n)
      · exact Algebra.adjoin_le (Set.range_subset_iff.2 fun j =>
          (mem_ringOn_basicOpen_ofAffine (Ω := Ω) hti).2 ⟨t j, 1, by rw [pow_one]⟩)

variable (o) in

abbrev affineLine [IsDomain o] : RatModel o (RatFunc o) := ofAffine o (RatFunc o) (Polynomial o)

example : (ofAffine ℤ ℚ ℤ).IsCl (fun j => algebraMap ℤ ℚ (![2, 3] j)) ∧
    (ofAffine ℤ ℚ ℤ).IsNm (fun j => algebraMap ℤ ℚ (![2, 3] j)) := by
  have h : (ofAffine ℤ ℚ ℤ).IsCl (fun j => algebraMap ℤ ℚ (![2, 3] j)) := by
    refine isCl_ofAffine_self _ ((Ideal.eq_top_iff_one _).2 ?_)
    rw [show (1 : ℤ) = 3 - 2 by norm_num]
    exact sub_mem (Ideal.subset_span ⟨1, rfl⟩) (Ideal.subset_span ⟨0, rfl⟩)
  exact ⟨h, h.isNm isIntegrallyClosed_O_ofAffine⟩

example (z : PrimeSpectrum (Polynomial ℤ)) :
    (RatFunc.X : RatFunc ℤ)⁻¹ ∈ (affineLine ℤ).O z ↔ Polynomial.X ∉ z.asIdeal :=
  inv_mem_O_ofAffine_iff Polynomial.X_ne_zero

example : (affineLine ℤ).val (spMap (Polynomial.eval₂RingHom (Int.castRingHom ℚ) 2))
    (algebraMap (Polynomial ℤ) (RatFunc ℤ) (Polynomial.X ^ 2 + 1)) = 5 := by
  rw [val_ofAffine]
  norm_num

example (z : PrimeSpectrum ℤ) :
    (fun _ => (2 : ℚ)⁻¹) ∈ (Lat.const (ofAffine ℤ ℚ ℤ) Unit).E z ↔ 2 ∉ z.asIdeal :=
  (Lat.mem_const_iff _).trans (forall_const Unit |>.trans (inv_mem_O_ofAffine_iff (o := ℤ) (Ω := ℚ) two_ne_zero))

example (p : ℕ) [Fact p.Prime] : ∃ (z : (ofAffine ℤ ℚ ℤ).Z) (y : Sp (OO p) ⟶ (ofAffine ℤ ℚ ℤ).Z),
    (ofAffine ℤ ℚ ℤ).Cen Set.univ z y ∧ (ofAffine ℤ ℚ ℤ).val (gPt p ≫ y) (algebraMap ℤ ℚ p) = p := by
  refine ⟨_, spMap (Int.castRingHom (OO p)), ⟨rfl, Set.subset_univ _⟩, ?_⟩
  refine (val_algebraMap (σ := Int.castRingHom _) ?_ _).trans (by simp)
  show (gPt p ≫ spMap (Int.castRingHom (OO p))) ≫ spMap (algebraMap ℤ ℤ) = _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun φ => spMap φ) (RingHom.ext_int _ _)

example : (affineLine ℤ).HasDiv (fun _ : Unit => 1) ∧ ¬ (affineLine ℤ).IsCl fun _ : Unit => 1 := by
  refine ⟨fun z => ⟨(), one_ne_zero, fun _ => by simp⟩, fun h => ?_⟩
  obtain ⟨U, -, -, hR⟩ := h.2 () one_ne_zero
  have hX : algebraMap (Polynomial ℤ) (RatFunc ℤ) Polynomial.X ∈ (affineLine ℤ).ringOn U :=
    mem_ringOn.2 fun z _ => algebraMap_mem_O_ofAffine z _
  have hle : Algebra.adjoin ℤ (Set.range fun _ : Unit => (1 : RatFunc ℤ) / 1) ≤ ⊥ :=
    Algebra.adjoin_le (by rintro _ ⟨_, rfl⟩; exact ⟨1, by simp⟩)
  obtain ⟨c, hc⟩ := Algebra.mem_bot.1 (hle (hR ▸ hX))
  rw [IsScalarTower.algebraMap_apply ℤ (Polynomial ℤ) (RatFunc ℤ)] at hc
  exact Polynomial.X_ne_C c (IsFractionRing.injective _ _ hc).symm

end RatModel
end GlobalTheory.ZH
end
