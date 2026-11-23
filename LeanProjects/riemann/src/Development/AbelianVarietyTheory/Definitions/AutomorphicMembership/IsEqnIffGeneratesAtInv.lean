import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
import Development.AbelianVarietyTheory.Definitions.Divisors.SmoothOfRelativeDimensionPspace
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RingKrullDimOfEtaleMvPolynomial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.CechPic

namespace GlobalTheory.Cartier

variable {X : Scheme.{0}} [IsIntegral X]

theorem gen_mem {U : X.Opens} {x : X} (hx : x ∈ U) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 ⟨x, trivial, hx⟩

omit [IsIntegral X] in

theorem memInf {U V : X.Opens} {x : X} (h : x ∈ U) (h' : x ∈ V) : x ∈ U ⊓ V := ⟨h, h'⟩

def fnOf (U : X.Opens) (h : genericPoint X ∈ U) : Γ(X, U) →+* X.functionField :=
  (X.presheaf.germ U (genericPoint X) h).hom

theorem fnOf_injective (U : X.Opens) (h : genericPoint X ∈ U) : Function.Injective (fnOf U h) :=
  germ_injective_of_isIntegral X _ h

@[simp] theorem fnOf_resG {U V : X.Opens} (e : V ≤ U) (h : genericPoint X ∈ V) (a : Γ(X, U)) :
    fnOf V h (resG X e a) = fnOf U (e h) a := by
  unfold fnOf resG
  exact X.presheaf.germ_res_apply (homOfLE e) _ h a

theorem algebraMap_germ {U : X.Opens} {x : X} (hx : x ∈ U) (a : Γ(X, U)) :
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx a) =
      fnOf U (gen_mem hx) a := by
  exact X.presheaf.germ_stalkSpecializes_apply hx _ a

theorem fn_ext {U : X.Opens} {a b : Γ(X, U)}
    (h : ∀ hU : genericPoint X ∈ U, fnOf U hU a = fnOf U hU b) : a = b := by
  by_cases hU : genericPoint X ∈ U
  · exact fnOf_injective U hU (h hU)
  · exact TopCat.Presheaf.section_ext X.sheaf U a b fun x hx => (hU (gen_mem hx)).elim

def RegAt (x : X) (f : X.functionField) : Prop :=
  ∃ a : X.presheaf.stalk x, algebraMap _ X.functionField a = f

def UnitAt (x : X) (f : X.functionField) : Prop :=
  ∃ a : X.presheaf.stalk x, IsUnit a ∧ algebraMap _ X.functionField a = f

def ZeroAt (x : X) (f : X.functionField) : Prop :=
  ∃ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x), algebraMap _ X.functionField a = f

section Local

variable {x : X} {f g : X.functionField}

theorem UnitAt.regAt (h : UnitAt x f) : RegAt x f :=
  let ⟨a, _, ha⟩ := h; ⟨a, ha⟩

theorem ZeroAt.regAt (h : ZeroAt x f) : RegAt x f :=
  let ⟨a, _, ha⟩ := h; ⟨a, ha⟩

private theorem algebraMap_stalk_functionField_injective (x : X) :
    Function.Injective (algebraMap (X.presheaf.stalk x) X.functionField) := by
  exact IsFractionRing.injective _ _

theorem zeroAt_iff : ZeroAt x f ↔ RegAt x f ∧ ¬ UnitAt x f := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨⟨a, rfl⟩, ?_⟩
    rintro ⟨b, hb, e⟩
    rw [algebraMap_stalk_functionField_injective x e] at hb
    exact (IsLocalRing.mem_maximalIdeal _).1 ha hb
  · rintro ⟨⟨a, rfl⟩, hn⟩
    exact ⟨a, (IsLocalRing.mem_maximalIdeal _).2 fun hu => hn ⟨a, hu, rfl⟩, rfl⟩

theorem regAt_zero (x : X) : RegAt x 0 := ⟨0, map_zero _⟩

theorem unitAt_one (x : X) : UnitAt x 1 := ⟨1, isUnit_one, map_one _⟩

theorem zeroAt_zero (x : X) : ZeroAt x 0 := ⟨0, Ideal.zero_mem _, map_zero _⟩

theorem RegAt.add (hf : RegAt x f) (hg : RegAt x g) : RegAt x (f + g) := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  exact ⟨a + b, map_add _ _ _⟩

theorem RegAt.mul (hf : RegAt x f) (hg : RegAt x g) : RegAt x (f * g) := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  exact ⟨a * b, map_mul _ _ _⟩

theorem UnitAt.mul (hf : UnitAt x f) (hg : UnitAt x g) : UnitAt x (f * g) := by
  obtain ⟨a, ha, rfl⟩ := hf
  obtain ⟨b, hb, rfl⟩ := hg
  exact ⟨a * b, ha.mul hb, map_mul _ _ _⟩

theorem UnitAt.inv (hf : UnitAt x f) : UnitAt x f⁻¹ := by
  obtain ⟨a, ha, rfl⟩ := hf
  refine ⟨↑ha.unit⁻¹, Units.isUnit _, ?_⟩
  rw [map_units_inv, IsUnit.unit_spec]

theorem UnitAt.ne_zero (hf : UnitAt x f) : f ≠ 0 := by
  obtain ⟨a, ha, rfl⟩ := hf
  exact (ha.map _).ne_zero

theorem ZeroAt.mul (hf : ZeroAt x f) (hg : RegAt x g) : ZeroAt x (f * g) := by
  obtain ⟨a, ha, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  exact ⟨a * b, Ideal.mul_mem_right _ _ ha, map_mul _ _ _⟩

theorem ZeroAt.add (hf : ZeroAt x f) (hg : ZeroAt x g) : ZeroAt x (f + g) := by
  obtain ⟨a, ha, rfl⟩ := hf
  obtain ⟨b, hb, rfl⟩ := hg
  exact ⟨a + b, Ideal.add_mem _ ha hb, map_add _ _ _⟩

theorem unitAt_iff (hf : f ≠ 0) : UnitAt x f ↔ RegAt x f ∧ RegAt x f⁻¹ := by
  refine ⟨fun h => ⟨h.regAt, h.inv.regAt⟩, ?_⟩
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  have hab : a * b = 1 := algebraMap_stalk_functionField_injective x (by rw [map_mul, map_one, ha, hb, mul_inv_cancel₀ hf])
  exact ⟨a, ⟨⟨a, b, hab, by rw [mul_comm, hab]⟩, rfl⟩, ha⟩

theorem regAt_fnOf {U : X.Opens} (hx : x ∈ U) (h : genericPoint X ∈ U) (a : Γ(X, U)) :
    RegAt x (fnOf U h a) :=
  ⟨X.presheaf.germ U x hx a, algebraMap_germ hx a⟩

theorem unitAt_fnOf_iff {U : X.Opens} (hx : x ∈ U) (h : genericPoint X ∈ U) (a : Γ(X, U)) :
    UnitAt x (fnOf U h a) ↔ x ∈ X.basicOpen a := by
  rw [X.mem_basicOpen a x hx]
  constructor
  · rintro ⟨b, hb, e⟩
    rwa [← algebraMap_stalk_functionField_injective x (e.trans (algebraMap_germ hx a).symm)]
  · exact fun hu => ⟨_, hu, algebraMap_germ hx a⟩

theorem unitAt_fnOf {U : X.Opens} (hx : x ∈ U) (h : genericPoint X ∈ U) (a : Γ(X, U)ˣ) :
    UnitAt x (fnOf U h a) :=
  ⟨X.presheaf.germ U x hx a, a.isUnit.map _, algebraMap_germ hx (a : Γ(X, U))⟩

theorem RegAt.exists_fnOf (h : RegAt x f) :
    ∃ (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)), fnOf U (gen_mem hx) a = f := by
  obtain ⟨b, rfl⟩ := h
  obtain ⟨U, hx, s, hs⟩ := X.presheaf.exists_germ_eq b
  exact ⟨U, hx, s, by rw [← algebraMap_germ hx s, hs]⟩

theorem UnitAt.exists_nhds (h : UnitAt x f) : ∃ U : X.Opens, x ∈ U ∧ ∀ y ∈ U, UnitAt y f := by
  obtain ⟨b, hu, rfl⟩ := h
  obtain ⟨U, hx, s, hs⟩ := X.presheaf.exists_germ_eq b
  refine ⟨X.basicOpen s, (X.mem_basicOpen s x hx).2 (hs ▸ hu), fun y hy => ?_⟩
  have hyU : y ∈ U := X.basicOpen_le s hy
  refine ⟨X.presheaf.germ U y hyU s, (X.mem_basicOpen s y hyU).1 hy, ?_⟩
  rw [algebraMap_germ, ← hs, algebraMap_germ]

private theorem fnOf_map' {U V : X.Opens} (e : V ⟶ U) (h : genericPoint X ∈ V) (a : Γ(X, U)) :
    fnOf V h (X.presheaf.map e.op a) = fnOf U (e.le h) a :=
  X.presheaf.germ_res_apply e _ h a

theorem exists_fnOf_eq {U : X.Opens} (hU : genericPoint X ∈ U) (h : ∀ x ∈ U, RegAt x f) :
    ∃ a : Γ(X, U), fnOf U hU a = f := by
  have hx : ∀ x : U, ∃ (W : X.Opens) (hW : (x : X) ∈ W) (s : Γ(X, W)),
      fnOf W (gen_mem hW) s = f := fun x => (h x x.2).exists_fnOf
  choose W hW s hs using hx
  let W' : U → X.Opens := fun x => W x ⊓ U
  let sf : ∀ x : U, Γ(X, W' x) := fun x => X.presheaf.map (homOfLE inf_le_left).op (s x)
  have hsf : ∀ x : U, ∀ hg, fnOf (W' x) hg (sf x) = f := fun x hg => by
    simp only [sf]
    rw [fnOf_map']
    exact hs x
  have hres : ∀ (x : U) {V : X.Opens} (e : V ⟶ W' x) (hg : genericPoint X ∈ V),
      fnOf V hg (X.presheaf.map e.op (sf x)) = f := fun x V e hg => by
    rw [fnOf_map', hsf]
  obtain ⟨a, ha, -⟩ := X.sheaf.existsUnique_gluing' W' U (fun x => homOfLE inf_le_right)
    (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hW _, hy⟩) sf
    (fun i j => fn_ext fun hg => (hres i (Opens.infLELeft (W' i) (W' j)) hg).trans
      (hres j (Opens.infLERight (W' i) (W' j)) hg).symm)
  refine ⟨a, ?_⟩
  have e1 := fnOf_map' (homOfLE inf_le_right : W' ⟨_, hU⟩ ⟶ U) ⟨hW _, hU⟩ a
  have e2 : X.presheaf.map (homOfLE inf_le_right : W' ⟨_, hU⟩ ⟶ U).op a = sf ⟨_, hU⟩ :=
    ha ⟨_, hU⟩
  rw [e2] at e1
  exact e1.symm.trans (hsf _ _)

theorem exists_unit_fnOf_eq {U : X.Opens} (h : ∀ x ∈ U, UnitAt x f) :
    ∃ a : Γ(X, U)ˣ, ∀ hU, fnOf U hU a = f := by
  by_cases hU : genericPoint X ∈ U
  · obtain ⟨a, ha⟩ := exists_fnOf_eq hU fun x hx => (h x hx).regAt
    obtain ⟨b, hb⟩ := exists_fnOf_eq hU fun x hx => (h x hx).inv.regAt
    have hf := (h _ hU).ne_zero
    have hab : a * b = 1 :=
      fnOf_injective U hU (by rw [map_mul, map_one, ha, hb, mul_inv_cancel₀ hf])
    exact ⟨⟨a, b, hab, by rw [mul_comm, hab]⟩, fun _ => ha⟩
  · exact ⟨1, fun h' => (hU h').elim⟩

theorem regAt_genericPoint (f : X.functionField) : RegAt (genericPoint X) f := by
  obtain ⟨U, hU, s, hs⟩ := X.presheaf.exists_germ_eq f
  have e : fnOf U hU s = f := hs
  exact e ▸ regAt_fnOf hU hU s

theorem unitAt_genericPoint (hf : f ≠ 0) : UnitAt (genericPoint X) f :=
  (unitAt_iff hf).2 ⟨regAt_genericPoint f, regAt_genericPoint _⟩

end Local

def unitsAt (x : X) : Subgroup X.functionFieldˣ where
  carrier := {u | UnitAt x u}
  one_mem' := unitAt_one x
  mul_mem' := UnitAt.mul
  inv_mem' {u} h := by
    change UnitAt x (u⁻¹ : X.functionFieldˣ)
    rw [Units.val_inv_eq_inv_val]
    exact UnitAt.inv h

abbrev Germ (x : X) : Type := Additive (X.functionFieldˣ ⧸ unitsAt x)

def germOf (x : X) (f : X.functionFieldˣ) : Germ x := Additive.ofMul (QuotientGroup.mk f)

theorem germOf_eq_iff {x : X} {f g : X.functionFieldˣ} :
    germOf x f = germOf x g ↔ UnitAt x ((g : X.functionField) / f) := by
  unfold germOf
  rw [Additive.ofMul.injective.eq_iff, QuotientGroup.eq]
  change UnitAt x ((f⁻¹ * g : X.functionFieldˣ) : X.functionField) ↔ _
  rw [Units.val_mul, Units.val_inv_eq_inv_val, div_eq_inv_mul]

variable (X) in

def cartierGroup : AddSubgroup (∀ x : X, Germ x) where
  carrier := {D | ∀ x, ∃ U : X.Opens, x ∈ U ∧ ∃ f, ∀ y ∈ U, D y = germOf y f}
  zero_mem' _ := ⟨⊤, trivial, 1, fun _ _ => rfl⟩
  add_mem' {D E} hD hE x :=
    have ⟨U, hU, f, hf⟩ := hD x
    have ⟨V, hV, g, hg⟩ := hE x
    ⟨U ⊓ V, ⟨hU, hV⟩, f * g, fun y hy => congrArg₂ (· + ·) (hf y hy.1) (hg y hy.2)⟩
  neg_mem' {D} hD x :=
    have ⟨U, hU, f, hf⟩ := hD x
    ⟨U, hU, f⁻¹, fun y hy => congrArg (- ·) (hf y hy)⟩

variable (X) in

def CartierDiv : Type := cartierGroup X

instance : AddCommGroup (CartierDiv X) := inferInstanceAs (AddCommGroup (cartierGroup X))

namespace CartierDiv

variable {D E : CartierDiv X} {x : X} {f f' : X.functionField} {g g' : X.functionFieldˣ}

def germ (D : CartierDiv X) (x : X) : Germ x := (show cartierGroup X from D).1 x

def IsEqn (D : CartierDiv X) (x : X) (g : X.functionFieldˣ) : Prop := D.germ x = germOf x g

theorem exists_isEqn_nhds (D : CartierDiv X) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ g, ∀ y ∈ U, D.IsEqn y g := by
  obtain ⟨U, hU, f, hf⟩ := (show cartierGroup X from D).2 x
  exact ⟨U, hU, f, hf⟩

theorem exists_isEqn (D : CartierDiv X) (x : X) : ∃ g, D.IsEqn x g := by
  obtain ⟨U, hU, g, hg⟩ := D.exists_isEqn_nhds x
  exact ⟨g, hg x hU⟩

theorem IsEqn.iff_unitAt (h : D.IsEqn x g) :
    D.IsEqn x g' ↔ UnitAt x ((g' : X.functionField) / g) := by
  have h0 : D.germ x = germOf x g := h
  show D.germ x = germOf x g' ↔ _
  rw [h0, germOf_eq_iff]

theorem IsEqn.exists_nhds (h : D.IsEqn x g) : ∃ U : X.Opens, x ∈ U ∧ ∀ y ∈ U, D.IsEqn y g := by
  obtain ⟨U, hU, g₀, hg₀⟩ := D.exists_isEqn_nhds x
  obtain ⟨V, hV, hu⟩ := ((hg₀ x hU).iff_unitAt.1 h).exists_nhds
  exact ⟨U ⊓ V, memInf hU hV, fun y hy => (hg₀ y hy.1).iff_unitAt.2 (hu y hy.2)⟩

theorem ext_of_isEqn (h : ∀ x, ∃ g, D.IsEqn x g ∧ E.IsEqn x g) : D = E := by
  have key : (show cartierGroup X from D) = (show cartierGroup X from E) :=
    Subtype.ext (funext fun x => by
      obtain ⟨g, hD, hE⟩ := h x
      exact Eq.trans (hD : D.germ x = germOf x g) (Eq.symm (hE : E.germ x = germOf x g)))
  exact key

theorem isEqn_genericPoint (D : CartierDiv X) (g : X.functionFieldˣ) :
    D.IsEqn (genericPoint X) g := by
  obtain ⟨g₀, h₀⟩ := D.exists_isEqn (genericPoint X)
  exact h₀.iff_unitAt.2 (unitAt_genericPoint (div_ne_zero g.ne_zero g₀.ne_zero))

theorem isEqn_zero (x : X) : (0 : CartierDiv X).IsEqn x 1 := rfl

theorem IsEqn.add (h : D.IsEqn x g) (h' : E.IsEqn x g') : (D + E).IsEqn x (g * g') := by
  have h0 : D.germ x = germOf x g := h
  have h1 : E.germ x = germOf x g' := h'
  show D.germ x + E.germ x = germOf x (g * g')
  rw [h0, h1]
  rfl

theorem IsEqn.neg (h : D.IsEqn x g) : (-D).IsEqn x g⁻¹ := by
  have h0 : D.germ x = germOf x g := h
  show -(D.germ x) = germOf x g⁻¹
  rw [h0]
  rfl

theorem IsEqn.sub (h : D.IsEqn x g) (h' : E.IsEqn x g') : (D - E).IsEqn x (g / g') := by
  rw [sub_eq_add_neg, div_eq_mul_inv]
  exact h.add h'.neg

theorem IsEqn.nsmul (h : D.IsEqn x g) (n : ℕ) : (n • D).IsEqn x (g ^ n) := by
  induction n with
  | zero => rw [zero_smul, pow_zero]; exact isEqn_zero x
  | succ n ih => rw [succ_nsmul, pow_succ]; exact ih.add h

theorem IsEqn.zsmul (h : D.IsEqn x g) (n : ℤ) : (n • D).IsEqn x (g ^ n) := by
  cases n with
  | ofNat n => rw [Int.ofNat_eq_natCast, natCast_zsmul, zpow_natCast]; exact h.nsmul n
  | negSucc n => rw [negSucc_zsmul, zpow_negSucc]; exact (h.nsmul (n + 1)).neg

def principal (g : X.functionFieldˣ) : CartierDiv X :=
  show cartierGroup X from ⟨fun x => germOf x g, fun _ => ⟨⊤, trivial, g, fun _ _ => rfl⟩⟩

theorem isEqn_principal (g : X.functionFieldˣ) (x : X) : (principal g).IsEqn x g := rfl

theorem principal_one : principal (1 : X.functionFieldˣ) = 0 := rfl

theorem principal_mul (g g' : X.functionFieldˣ) :
    principal (g * g') = principal g + principal g' := rfl

def RegularAt (D : CartierDiv X) (x : X) (f : X.functionField) : Prop :=
  ∃ g, D.IsEqn x g ∧ RegAt x (f * g)

def GeneratesAt (D : CartierDiv X) (x : X) (f : X.functionField) : Prop :=
  ∃ g, D.IsEqn x g ∧ UnitAt x (f * g)

def VanishesAt (D : CartierDiv X) (x : X) (f : X.functionField) : Prop :=
  ∃ g, D.IsEqn x g ∧ ZeroAt x (f * g)

theorem mul_eqn_eq (f : X.functionField) (g g' : X.functionFieldˣ) :
    f * g = f * g' * ((g : X.functionField) / g') := by
  have h := g'.ne_zero
  field_simp

theorem IsEqn.regularAt_iff (h : D.IsEqn x g) : D.RegularAt x f ↔ RegAt x (f * g) := by
  constructor
  · rintro ⟨g₀, h₀, hr⟩
    rw [mul_eqn_eq f g g₀]
    exact hr.mul (h₀.iff_unitAt.1 h).regAt
  · exact fun hr => ⟨g, h, hr⟩

theorem IsEqn.generatesAt_iff (h : D.IsEqn x g) : D.GeneratesAt x f ↔ UnitAt x (f * g) := by
  constructor
  · rintro ⟨g₀, h₀, hr⟩
    rw [mul_eqn_eq f g g₀]
    exact hr.mul (h₀.iff_unitAt.1 h)
  · exact fun hr => ⟨g, h, hr⟩

theorem IsEqn.vanishesAt_iff (h : D.IsEqn x g) : D.VanishesAt x f ↔ ZeroAt x (f * g) := by
  constructor
  · rintro ⟨g₀, h₀, hr⟩
    rw [mul_eqn_eq f g g₀]
    exact hr.mul (h₀.iff_unitAt.1 h).regAt
  · exact fun hr => ⟨g, h, hr⟩

theorem vanishesAt_iff : D.VanishesAt x f ↔ D.RegularAt x f ∧ ¬ D.GeneratesAt x f := by
  obtain ⟨g, hg⟩ := D.exists_isEqn x
  rw [hg.vanishesAt_iff, hg.regularAt_iff, hg.generatesAt_iff, zeroAt_iff]

theorem GeneratesAt.regularAt (h : D.GeneratesAt x f) : D.RegularAt x f := by
  obtain ⟨g, hg, hu⟩ := h
  exact ⟨g, hg, hu.regAt⟩

theorem GeneratesAt.ne_zero (h : D.GeneratesAt x f) : f ≠ 0 := by
  obtain ⟨g, hg, hu⟩ := h
  rintro rfl
  exact hu.ne_zero (zero_mul _)

theorem VanishesAt.regularAt (h : D.VanishesAt x f) : D.RegularAt x f := by
  obtain ⟨g, hg, hz⟩ := h
  exact ⟨g, hg, hz.regAt⟩

theorem isEqn_iff_generatesAt_inv : D.IsEqn x g ↔ D.GeneratesAt x (g : X.functionField)⁻¹ := by
  constructor
  · intro h
    refine ⟨g, h, ?_⟩
    rw [inv_mul_cancel₀ g.ne_zero]
    exact unitAt_one x
  · rintro ⟨g₀, h₀, hu⟩
    have hu' := hu.inv
    rw [mul_inv, inv_inv, ← div_eq_mul_inv] at hu'
    exact h₀.iff_unitAt.2 hu'

theorem generatesAt_genericPoint (D : CartierDiv X) (hf : f ≠ 0) :
    D.GeneratesAt (genericPoint X) f := by
  obtain ⟨g, hg⟩ := D.exists_isEqn (genericPoint X)
  exact ⟨g, hg, unitAt_genericPoint (mul_ne_zero hf g.ne_zero)⟩

theorem vanishesAt_zero (D : CartierDiv X) (x : X) : D.VanishesAt x 0 := by
  obtain ⟨g, hg⟩ := D.exists_isEqn x
  refine ⟨g, hg, ?_⟩
  rw [zero_mul]
  exact zeroAt_zero x

theorem RegularAt.add (h : D.RegularAt x f) (h' : D.RegularAt x f') : D.RegularAt x (f + f') := by
  obtain ⟨g, hg⟩ := D.exists_isEqn x
  rw [hg.regularAt_iff] at h h' ⊢
  rw [add_mul]
  exact h.add h'

theorem VanishesAt.add (h : D.VanishesAt x f) (h' : D.VanishesAt x f') :
    D.VanishesAt x (f + f') := by
  obtain ⟨g, hg⟩ := D.exists_isEqn x
  rw [hg.vanishesAt_iff] at h h' ⊢
  rw [add_mul]
  exact h.add h'

theorem RegularAt.mul (h : D.RegularAt x f) (h' : E.RegularAt x f') :
    (D + E).RegularAt x (f * f') := by
  obtain ⟨g, hg, r⟩ := h
  obtain ⟨g', hg', r'⟩ := h'
  refine ⟨g * g', hg.add hg', ?_⟩
  have e : f * f' * ((g * g' : X.functionFieldˣ) : X.functionField) =
      (f * g) * (f' * g') := by
    rw [Units.val_mul]; ring
  rw [e]
  exact r.mul r'

theorem GeneratesAt.mul (h : D.GeneratesAt x f) (h' : E.GeneratesAt x f') :
    (D + E).GeneratesAt x (f * f') := by
  obtain ⟨g, hg, r⟩ := h
  obtain ⟨g', hg', r'⟩ := h'
  refine ⟨g * g', hg.add hg', ?_⟩
  have e : f * f' * ((g * g' : X.functionFieldˣ) : X.functionField) =
      (f * g) * (f' * g') := by
    rw [Units.val_mul]; ring
  rw [e]
  exact r.mul r'

theorem VanishesAt.mul (h : D.VanishesAt x f) (h' : E.RegularAt x f') :
    (D + E).VanishesAt x (f * f') := by
  obtain ⟨g, hg, r⟩ := h
  obtain ⟨g', hg', r'⟩ := h'
  refine ⟨g * g', hg.add hg', ?_⟩
  have e : f * f' * ((g * g' : X.functionFieldˣ) : X.functionField) =
      (f * g) * (f' * g') := by
    rw [Units.val_mul]; ring
  rw [e]
  exact r.mul r'

theorem regularAt_zero_iff : (0 : CartierDiv X).RegularAt x f ↔ RegAt x f := by
  rw [(isEqn_zero x).regularAt_iff, Units.val_one, mul_one]

theorem generatesAt_zero_iff : (0 : CartierDiv X).GeneratesAt x f ↔ UnitAt x f := by
  rw [(isEqn_zero x).generatesAt_iff, Units.val_one, mul_one]

theorem RegularAt.regAt_mul (h : D.RegularAt x f) (h' : RegAt x f') : D.RegularAt x (f' * f) := by
  obtain ⟨g, hg, r⟩ := h
  refine ⟨g, hg, ?_⟩
  rw [mul_assoc]
  exact h'.mul r

theorem regularAt_add_principal :
    (D + principal g).RegularAt x f ↔ D.RegularAt x (f * g) := by
  obtain ⟨g₀, hg₀⟩ := D.exists_isEqn x
  have e : f * ((g₀ * g : X.functionFieldˣ) : X.functionField) = f * g * g₀ := by
    rw [Units.val_mul]; ring
  rw [(hg₀.add (isEqn_principal g x)).regularAt_iff, hg₀.regularAt_iff, e]

def Eff (D : CartierDiv X) : Prop := ∀ x, D.RegularAt x 1

theorem eff_iff : D.Eff ↔ ∀ x g, D.IsEqn x g → RegAt x g := by
  constructor
  · intro h x g hg
    have := hg.regularAt_iff.1 (h x)
    rwa [one_mul] at this
  · intro h x
    obtain ⟨g, hg⟩ := D.exists_isEqn x
    exact hg.regularAt_iff.2 (by rw [one_mul]; exact h x g hg)

theorem eff_zero : (0 : CartierDiv X).Eff := fun x => regularAt_zero_iff.2 (unitAt_one x).regAt

theorem Eff.add (h : D.Eff) (h' : E.Eff) : (D + E).Eff := by
  intro x
  have := (h x).mul (h' x)
  rwa [one_mul] at this

theorem Eff.eq_zero (h : D.Eff) (h' : (-D).Eff) : D = 0 := by
  refine ext_of_isEqn fun x => ?_
  obtain ⟨g, hg⟩ := D.exists_isEqn x
  have r1 := eff_iff.1 h x g hg
  have r2 := eff_iff.1 h' x _ hg.neg
  rw [Units.val_inv_eq_inv_val] at r2
  have hu : UnitAt x g := (unitAt_iff g.ne_zero).2 ⟨r1, r2⟩
  refine ⟨1, hg.iff_unitAt.2 ?_, isEqn_zero x⟩
  rw [Units.val_one, one_div]
  exact hu.inv

def supp (D : CartierDiv X) : Closeds X where
  carrier := {x | ¬ D.IsEqn x 1}
  isClosed' := isOpen_compl_iff.1 (isOpen_iff_forall_mem_open.2 fun x hx =>
    have ⟨U, hU, h⟩ := IsEqn.exists_nhds (not_not.1 hx)
    ⟨U, fun y hy => not_not.2 (h y hy), U.isOpen, hU⟩)

theorem IsEqn.mem_supp_iff (h : D.IsEqn x g) : x ∈ D.supp ↔ ¬ UnitAt x g := by
  change ¬ D.IsEqn x 1 ↔ _
  rw [h.iff_unitAt, Units.val_one, one_div]
  exact not_congr ⟨fun u => by simpa using u.inv, fun u => u.inv⟩

theorem notMem_supp_iff : x ∉ D.supp ↔ D.GeneratesAt x 1 := by
  obtain ⟨g, hg⟩ := D.exists_isEqn x
  rw [hg.mem_supp_iff, not_not, hg.generatesAt_iff, one_mul]

theorem Eff.mem_supp_iff (h : D.Eff) : x ∈ D.supp ↔ D.VanishesAt x 1 := by
  obtain ⟨g, hg⟩ := D.exists_isEqn x
  rw [hg.mem_supp_iff, hg.vanishesAt_iff, one_mul, zeroAt_iff]
  have r := eff_iff.1 h x g hg
  exact ⟨fun hn => ⟨r, hn⟩, fun hz => hz.2⟩

theorem genericPoint_notMem_supp (D : CartierDiv X) : genericPoint X ∉ D.supp := notMem_supp_iff.2 (generatesAt_genericPoint D one_ne_zero)

theorem supp_ne_top (D : CartierDiv X) : D.supp ≠ ⊤ := by
  intro h
  apply D.genericPoint_notMem_supp
  rw [h]
  trivial

theorem supp_eq_bot_iff : D.supp = ⊥ ↔ D = 0 := by
  constructor
  · intro h
    refine ext_of_isEqn fun x => ⟨1, ?_, isEqn_zero x⟩
    by_contra hn
    have hx : x ∈ ((D.supp : Closeds X) : Set X) := hn
    rw [h, Closeds.coe_bot] at hx
    exact hx
  · rintro rfl
    refine SetLike.ext fun x => ⟨fun hx => absurd (isEqn_zero x) hx, fun hx => ?_⟩
    have h2 : x ∈ ((⊥ : Closeds X) : Set X) := hx
    rw [Closeds.coe_bot] at h2
    exact h2.elim

theorem supp_add_le (D E : CartierDiv X) : (D + E).supp ≤ D.supp ⊔ E.supp := by
  intro x hx
  have hx' : ¬ (D + E).IsEqn x 1 := hx
  show x ∈ ((D.supp ⊔ E.supp : Closeds X) : Set X)
  rw [Closeds.coe_sup]
  by_contra hn
  simp only [Set.mem_union, not_or] at hn
  have hD : D.IsEqn x 1 := Classical.byContradiction fun h => hn.1 h
  have hE : E.IsEqn x 1 := Classical.byContradiction fun h => hn.2 h
  have := hD.add hE
  rw [mul_one] at this
  exact hx' this

theorem algebraMap_top : algebraMap Γ(X, ⊤) X.functionField = fnOf ⊤ trivial := rfl

def secOn (D : CartierDiv X) (S : Set X) : Submodule Γ(X, ⊤) X.functionField where
  carrier := {f | ∀ x ∈ S, D.RegularAt x f}
  zero_mem' x _ := (D.vanishesAt_zero x).regularAt
  add_mem' h h' x hx := (h x hx).add (h' x hx)
  smul_mem' a _ h x hx := (h x hx).regAt_mul (regAt_fnOf (U := ⊤) trivial trivial a)

theorem mem_secOn {S : Set X} : f ∈ D.secOn S ↔ ∀ x ∈ S, D.RegularAt x f := Iff.rfl

def sections (D : CartierDiv X) : Submodule Γ(X, ⊤) X.functionField := D.secOn Set.univ

theorem mem_sections : f ∈ D.sections ↔ ∀ x, D.RegularAt x f := by
  rw [sections, mem_secOn]
  exact ⟨fun h x => h x (Set.mem_univ x), fun h x _ => h x⟩

theorem mem_sections_iff_eff : (g : X.functionField) ∈ D.sections ↔ (principal g + D).Eff := by
  rw [mem_sections, add_comm]
  exact forall_congr' fun x => by rw [regularAt_add_principal, one_mul]

end CartierDiv

open CartierDiv

variable {D E : CartierDiv X} {L M : LB X} {r : L.ι → X.functionFieldˣ} {r' : M.ι → X.functionFieldˣ}

def IsRatSec (L : LB X) (r : L.ι → X.functionFieldˣ) : Prop :=
  ∀ i j (h : genericPoint X ∈ L.U i ⊓ L.U j),
    (r i : X.functionField) = fnOf _ h (L.g i j : Γ(X, L.U i ⊓ L.U j)) * r j

structure Presents (D : CartierDiv X) (L : LB X) (r : L.ι → X.functionFieldˣ) : Prop where

  isLB : L.IsLB

  isRatSec : IsRatSec L r

  isEqn : ∀ i, ∀ x ∈ L.U i, D.IsEqn x (r i)

theorem IsRatSec.germOf_eq (hr : IsRatSec L r) {i j : L.ι} {x : X} (hi : x ∈ L.U i)
    (hj : x ∈ L.U j) : germOf x (r j) = germOf x (r i) := by
  have hij : x ∈ L.U i ⊓ L.U j := memInf hi hj
  have hq : (r i : X.functionField) / r j = fnOf _ (gen_mem hij) (L.g i j : Γ(X, L.U i ⊓ L.U j)) := by
    rw [hr i j (gen_mem hij), mul_div_assoc, div_self (r j).ne_zero, mul_one]
  rw [germOf_eq_iff, hq]
  exact unitAt_fnOf hij (gen_mem hij) (L.g i j)

def divOfRatSec (hL : L.IsLB) (hr : IsRatSec L r) : CartierDiv X :=
  show cartierGroup X from ⟨fun x => germOf x (r (exists_chart hL x).choose), fun x =>
    ⟨_, (exists_chart hL x).choose_spec, _,
      fun y hy => hr.germOf_eq hy (exists_chart hL y).choose_spec⟩⟩

theorem presents_divOfRatSec (hL : L.IsLB) (hr : IsRatSec L r) :
    Presents (divOfRatSec hL hr) L r :=
  ⟨hL, hr, fun _ x hx => hr.germOf_eq hx (exists_chart hL x).choose_spec⟩

theorem Presents.unique (h : Presents D L r) (h' : Presents E L r) : D = E := by
  refine ext_of_isEqn fun x => ?_
  obtain ⟨i, hi⟩ := exists_chart h.isLB x
  exact ⟨r i, h.isEqn i x hi, h'.isEqn i x hi⟩

open Classical in

def frameRat (L : LB X) (i₀ : L.ι) (h₀ : genericPoint X ∈ L.U i₀) (i : L.ι) : X.functionFieldˣ :=
  if h : genericPoint X ∈ L.U i then
    Units.map (fnOf (L.U i ⊓ L.U i₀) (memInf h h₀)).toMonoidHom (L.g i i₀) else 1

theorem val_frameRat (i₀ : L.ι) (h₀ : genericPoint X ∈ L.U i₀) (i : L.ι)
    (h : genericPoint X ∈ L.U i) :
    (frameRat L i₀ h₀ i : X.functionField) = fnOf _ (memInf h h₀) (L.g i i₀ : Γ(X, L.U i ⊓ L.U i₀)) := by
  rw [frameRat, dif_pos h]
  rfl

private theorem units_val_res_eq_resG {U V : X.Opens} (e : V ≤ U) (u : Γ(X, U)ˣ) :
    ((res e u : Γ(X, V)ˣ) : Γ(X, V)) = resG X e (u : Γ(X, U)) := by
  rfl

theorem isRatSec_frameRat (hL : L.IsLB) (i₀ : L.ι) (h₀ : genericPoint X ∈ L.U i₀) :
    IsRatSec L (frameRat L i₀ h₀) := by
  intro i j h
  have hi : genericPoint X ∈ L.U i := h.1
  have hj : genericPoint X ∈ L.U j := h.2
  have hV : genericPoint X ∈ L.U i ⊓ L.U j ⊓ L.U i₀ := ⟨h, h₀⟩
  rw [val_frameRat i₀ h₀ i hi, val_frameRat i₀ h₀ j hj]
  have hc := congrArg (fun u : Γ(X, L.U i ⊓ L.U j ⊓ L.U i₀)ˣ =>
    fnOf (L.U i ⊓ L.U j ⊓ L.U i₀) hV (u : Γ(X, L.U i ⊓ L.U j ⊓ L.U i₀))) (hL.cocycle i j i₀)
  simp only [Units.val_mul, map_mul, units_val_res_eq_resG, fnOf_resG] at hc
  exact hc.symm

private theorem coe_res_eq_resG {U V : X.Opens} (e : V ≤ U) (u : Γ(X, U)ˣ) :
    ((res e u : Γ(X, V)ˣ) : Γ(X, V)) = resG X e (u : Γ(X, U)) := by
  rfl

theorem frameRat_self (hL : L.IsLB) (i₀ : L.ι) (h₀ : genericPoint X ∈ L.U i₀) :
    frameRat L i₀ h₀ i₀ = 1 := by
  apply Units.ext
  rw [val_frameRat i₀ h₀ i₀ h₀, Units.val_one]
  have h2 := congrArg (fun u : Γ(X, L.U i₀)ˣ => fnOf (L.U i₀) h₀ (u : Γ(X, L.U i₀))) (hL.g_self i₀)
  simp only [coe_res_eq_resG, fnOf_resG, Units.val_one, map_one] at h2
  exact h2

def ofLB (hL : L.IsLB) (i₀ : L.ι) (h₀ : genericPoint X ∈ L.U i₀) : CartierDiv X :=
  divOfRatSec hL (isRatSec_frameRat hL i₀ h₀)

theorem presents_ofLB (hL : L.IsLB) (i₀ : L.ι) (h₀ : genericPoint X ∈ L.U i₀) :
    Presents (ofLB hL i₀ h₀) L (frameRat L i₀ h₀) :=
  presents_divOfRatSec hL _

abbrev EqnChart (D : CartierDiv X) : Type :=
  {p : X.Opens × X.functionFieldˣ // genericPoint X ∈ p.1 ∧ ∀ x ∈ p.1, D.IsEqn x p.2}

theorem exists_trans (i j : EqnChart D) : ∃ a : Γ(X, i.1.1 ⊓ j.1.1)ˣ,
    ∀ h, fnOf _ h a.val = (i.1.2 : X.functionField) / (j.1.2 : X.functionField) :=
  exists_unit_fnOf_eq fun y hy => ((j.2.2 y hy.2).iff_unitAt).1 (i.2.2 y hy.1)

def toLB (D : CartierDiv X) : LB X where
  ι := EqnChart D
  U i := i.1.1
  g i j := (exists_trans i j).choose

theorem fnOf_toLB_g (i j : (toLB D).ι) (h) : fnOf _ h ((toLB D).g i j).val =
    (i.1.2 : X.functionField) / (j.1.2 : X.functionField) :=
  (exists_trans i j).choose_spec h

private theorem val_res_eq_resG {U V : X.Opens} (e : V ≤ U) (u : Γ(X, U)ˣ) :
    ((res e u : Γ(X, V)ˣ) : Γ(X, V)) = resG X e (u : Γ(X, U)) := by
  rfl

theorem isLB_toLB (D : CartierDiv X) : (toLB D).IsLB where
  cover := (by
      refine eq_top_iff.2 fun x _ => ?_
      obtain ⟨U, hx, g, hg⟩ := D.exists_isEqn_nhds x
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(U, g), gen_mem hx, hg⟩, hx⟩)
    ; g_self := fun i => (by
      apply Units.ext
      apply fn_ext
      intro hU
      rw [val_res_eq_resG, fnOf_resG, fnOf_toLB_g, div_self (Units.ne_zero _), Units.val_one, map_one])
    ; cocycle := fun i j k => (by
      apply Units.ext
      apply fn_ext
      intro hU
      simp only [Units.val_mul, map_mul, val_res_eq_resG, fnOf_resG, fnOf_toLB_g]
      rw [div_mul_div_cancel₀ (Units.ne_zero _)])

theorem presents_toLB (D : CartierDiv X) : Presents D (toLB D) fun i => i.1.2 := by
  exact ⟨isLB_toLB D, fun i j h => by rw [fnOf_toLB_g i j h, div_mul_cancel₀ _ (Units.ne_zero _)],
    fun i x hx => i.2.2 x hx⟩

private theorem fnOf_map_homOfLE {U V : X.Opens} (e : V ≤ U) (h : genericPoint X ∈ V) (a : Γ(X, U)) :
    fnOf V h ((X.presheaf.map (homOfLE e).op).hom a) = fnOf U (e h) a := by
  exact fnOf_resG e h a

namespace Presents

def rat (h : Presents D L r) : L.Sec →ₗ[Γ(X, ⊤)] X.functionField where
  toFun s := fnOf _ (exists_chart h.isLB (genericPoint X)).choose_spec (s.f _) /
    r (exists_chart h.isLB (genericPoint X)).choose
  map_add' s t := by rw [LB.add_f, map_add, add_div]
  map_smul' a s := by
    rw [LB.smul_f, map_mul, fnOf_resG, mul_div_assoc]
    rfl

theorem rat_mul (h : Presents D L r) (s : L.Sec) (i : L.ι) (hi : genericPoint X ∈ L.U i) :
    h.rat s * r i = fnOf _ hi (s.f i) := by
  have key : ∀ j (hj : genericPoint X ∈ L.U j),
      fnOf _ hj (s.f j) * r i = fnOf _ hi (s.f i) * r j := by
    intro j hj
    have hij : genericPoint X ∈ L.U i ⊓ L.U j := ⟨hi, hj⟩
    have hc := congrArg (fnOf _ hij) (s.compat i j)
    rw [map_mul, fnOf_map_homOfLE, fnOf_map_homOfLE] at hc
    rw [hc, h.isRatSec i j hij]
    ring
  show fnOf _ _ (s.f _) / r _ * r i = _
  rw [div_mul_eq_mul_div, key _ _, mul_div_assoc, div_self (r _).ne_zero, mul_one]

theorem rat_mem (h : Presents D L r) (s : L.Sec) : h.rat s ∈ D.sections := by
  rw [mem_sections]
  intro x
  obtain ⟨i, hi⟩ := exists_chart h.isLB x
  exact ⟨r i, h.isEqn i x hi, by rw [h.rat_mul s i (gen_mem hi)]; exact regAt_fnOf hi _ _⟩

theorem rat_injective (h : Presents D L r) : Function.Injective h.rat := by
  intro s t hst
  obtain ⟨fs, cs⟩ := s
  obtain ⟨ft, ct⟩ := t
  have : fs = ft := by
    funext i
    apply fn_ext
    intro hU
    have e1 := h.rat_mul ⟨fs, cs⟩ i hU
    have e2 := h.rat_mul ⟨ft, ct⟩ i hU
    rw [hst] at e1
    exact e1.symm.trans e2
  subst this
  rfl

private theorem fnOf_presheaf_map_homOfLE {U V : X.Opens} (e : V ≤ U) (h : genericPoint X ∈ V) (a : Γ(X, U)) :
    fnOf V h ((X.presheaf.map (homOfLE e).op).hom a) = fnOf U (e h) a := by
  exact fnOf_resG e h a

theorem exists_rat_eq (h : Presents D L r) {f : X.functionField} (hf : f ∈ D.sections) :
    ∃ s, h.rat s = f := by
  have hreg : ∀ i, ∃ a : Γ(X, L.U i), ∀ hU, fnOf _ hU a = f * (r i : X.functionField) := by
    intro i
    by_cases hU : genericPoint X ∈ L.U i
    · obtain ⟨a, ha⟩ := exists_fnOf_eq hU (f := f * (r i : X.functionField)) fun x hx =>
        ((h.isEqn i x hx).regularAt_iff).1 ((mem_sections.1 hf) x)
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h' => absurd h' hU⟩
  choose a ha using hreg
  refine ⟨⟨a, fun i j => ?_⟩, ?_⟩
  · apply fn_ext
    intro hU
    have hi : genericPoint X ∈ L.U i := hU.1
    have hj : genericPoint X ∈ L.U j := hU.2
    rw [map_mul, fnOf_presheaf_map_homOfLE, fnOf_presheaf_map_homOfLE, ha i, ha j, h.isRatSec i j hU]
    ring
  · show fnOf _ _ (a _) / r _ = f
    rw [ha, mul_div_assoc, div_self (r _).ne_zero, mul_one]

def secEquiv (h : Presents D L r) : L.Sec ≃ₗ[Γ(X, ⊤)] D.sections :=
  LinearEquiv.ofBijective (h.rat.codRestrict _ h.rat_mem)
    ⟨fun _ _ e => h.rat_injective (congrArg Subtype.val e),
      fun f => have ⟨s, hs⟩ := h.exists_rat_eq f.2; ⟨s, Subtype.ext hs⟩⟩

@[simp] theorem coe_secEquiv (h : Presents D L r) (s : L.Sec) :
    (h.secEquiv s : X.functionField) = h.rat s := rfl

theorem generatesAt_rat_iff (h : Presents D L r) (s : L.Sec) {x : X} :
    D.GeneratesAt x (h.rat s) ↔ x ∈ nonzeroLocus s := by
  have key : ∀ k (hk : x ∈ L.U k), D.GeneratesAt x (h.rat s) ↔ x ∈ X.basicOpen (s.f k) := by
    intro k hk
    rw [(h.isEqn k x hk).generatesAt_iff, h.rat_mul s k (gen_mem hk), unitAt_fnOf_iff hk]
  unfold nonzeroLocus
  constructor
  · intro hg
    obtain ⟨i, hi⟩ := exists_chart h.isLB x
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (key i hi).1 hg⟩
  · intro hx
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact (key k (X.basicOpen_le _ hk)).2 hk

theorem vanishesAt_rat_iff (h : Presents D L r) (s : L.Sec) {x : X} :
    D.VanishesAt x (h.rat s) ↔ x ∉ nonzeroLocus s := by
  rw [vanishesAt_iff, h.generatesAt_rat_iff]
  exact and_iff_right ((mem_sections.1 (h.rat_mem s)) x)

theorem add_principal (h : Presents D L r) (g : X.functionFieldˣ) :
    Presents (D + principal g) L fun i => r i * g :=
  ⟨h.isLB, fun i j hij => by rw [Units.val_mul, Units.val_mul, h.isRatSec i j hij, mul_assoc],
    fun i x hx => (h.isEqn i x hx).add (isEqn_principal g x)⟩

private theorem val_res_units_eq_resG {U V : X.Opens} (e : V ≤ U) (u : Γ(X, U)ˣ) :
    ((res e u : Γ(X, V)ˣ) : Γ(X, V)) = resG X e (u : Γ(X, U)) := by
  rfl

private theorem fnOf_resG_mul {U U' V : X.Opens} (e : V ≤ U) (e' : V ≤ U') (h : genericPoint X ∈ V)
    (a : Γ(X, U)) (b : Γ(X, U')) :
    fnOf V h (resG X e a * resG X e' b) = fnOf U (e h) a * fnOf U' (e' h) b := by
  rw [map_mul, fnOf_resG, fnOf_resG]

theorem tens (h : Presents D L r) (h' : Presents E M r') :
    Presents (D + E) (tens L M) fun p => r p.1 * r' p.2 := by
  refine ⟨isLB_tens h.isLB h'.isLB, fun p q hpq => ?_, fun p x hx => (h.isEqn p.1 x hx.1).add (h'.isEqn p.2 x hx.2)⟩
  have h1 : genericPoint X ∈ L.U p.1 ⊓ L.U q.1 := ⟨hpq.1.1, hpq.2.1⟩
  have h2 : genericPoint X ∈ M.U p.2 ⊓ M.U q.2 := ⟨hpq.1.2, hpq.2.2⟩
  have key := fnOf_resG_mul (V := L.U p.1 ⊓ M.U p.2 ⊓ (L.U q.1 ⊓ M.U q.2))
    (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
    (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)) hpq
    (L.g p.1 q.1 : Γ(X, L.U p.1 ⊓ L.U q.1)) (M.g p.2 q.2 : Γ(X, M.U p.2 ⊓ M.U q.2))
  dsimp only [GlobalTheory.CechPic.tens]
  simp only [Units.val_mul, val_res_units_eq_resG]
  erw [key]
  rw [h.isRatSec _ _ h1, h'.isRatSec _ _ h2]
  ring

private theorem fnOf_res_units {U V : X.Opens} (e : V ≤ U) (h : genericPoint X ∈ V) (u : Γ(X, U)ˣ) :
    fnOf V h ((res e u : Γ(X, V)ˣ) : Γ(X, V)) = fnOf U (e h) (u : Γ(X, U)) := by
  exact fnOf_resG e h (u : Γ(X, U))

private theorem fnOf_res_mul_inv_mul {A B C V : X.Opens} (ea : V ≤ A) (eb : V ≤ B) (ec : V ≤ C)
    (h : genericPoint X ∈ V) (a : Γ(X, A)ˣ) (b : Γ(X, B)ˣ) (c : Γ(X, C)ˣ) :
    fnOf V h ((res ea a * (res eb b)⁻¹ * res ec c : Γ(X, V)ˣ) : Γ(X, V)) =
      fnOf A (ea h) (a : Γ(X, A)) * (fnOf B (eb h) (b : Γ(X, B)))⁻¹ * fnOf C (ec h) (c : Γ(X, C)) := by
  rw [Units.val_mul, Units.val_mul, map_mul, map_mul, map_units_inv]
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·) (fnOf_resG ea h (a : Γ(X, A)))
    (congrArg (·⁻¹) (fnOf_resG eb h (b : Γ(X, B))))) (fnOf_resG ec h (c : Γ(X, C)))

theorem lbIso (h : Presents D L r) (h' : Presents D M r') : LBIso L M := by
  have ex : ∀ p : M.ι × L.ι, ∃ a : Γ(X, M.U p.1 ⊓ L.U p.2)ˣ, ∀ hU,
      fnOf (M.U p.1 ⊓ L.U p.2) hU (a : Γ(X, M.U p.1 ⊓ L.U p.2)) =
        (r' p.1 : X.functionField) / (r p.2 : X.functionField) :=
    fun p => exists_unit_fnOf_eq fun x hx => ((h.isEqn p.2 x hx.2).iff_unitAt).1 (h'.isEqn p.1 x hx.1)
  choose s hs using ex
  refine ⟨⟨s⟩, ?_⟩
  intro p q
  apply Units.ext
  apply fn_ext
  intro hU
  have h1 : genericPoint X ∈ M.U p.1 ⊓ M.U q.1 := ⟨hU.1.1, hU.2.1⟩
  have h2 : genericPoint X ∈ L.U p.2 ⊓ L.U q.2 := ⟨hU.1.2, hU.2.2⟩
  have n1 : fnOf _ h2 ((L.g p.2 q.2 : Γ(X, L.U p.2 ⊓ L.U q.2))) ≠ 0 :=
    ((L.g p.2 q.2).isUnit.map (fnOf _ h2)).ne_zero
  have n2 := (r q.2).ne_zero
  have n3 := (r p.2).ne_zero
  have k1 := fnOf_res_units (U := M.U p.1 ⊓ L.U p.2) (V := M.U p.1 ⊓ L.U p.2 ⊓ (M.U q.1 ⊓ L.U q.2))
    inf_le_left hU (s p)
  have k2 := fnOf_res_mul_inv_mul (V := M.U p.1 ⊓ L.U p.2 ⊓ (M.U q.1 ⊓ L.U q.2))
    (A := M.U p.1 ⊓ M.U q.1) (B := L.U p.2 ⊓ L.U q.2) (C := M.U q.1 ⊓ L.U q.2)
    (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
    (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)) inf_le_right hU
    (M.g p.1 q.1) (L.g p.2 q.2) (s q)
  have hsp : ∀ hp, fnOf (M.U p.1 ⊓ L.U p.2) hp ((s p : Γ(X, M.U p.1 ⊓ L.U p.2))) =
      (r' p.1 : X.functionField) / (r p.2 : X.functionField) := fun hp => hs p hp
  have hsq : ∀ hq, fnOf (M.U q.1 ⊓ L.U q.2) hq ((s q : Γ(X, M.U q.1 ⊓ L.U q.2))) =
      (r' q.1 : X.functionField) / (r q.2 : X.functionField) := fun hq => hs q hq
  rw [hsp] at k1
  rw [hsq] at k2
  dsimp only [LB.div]
  erw [k1, k2]
  rw [h'.isRatSec p.1 q.1 h1, h.isRatSec p.2 q.2 h2]
  field_simp

end Presents

theorem presents_zero : Presents (0 : CartierDiv X) (LB.triv X) fun _ => 1 := by
  refine ⟨⟨?_, fun _ => map_one _, fun _ _ _ => by simp⟩, fun i j h => ?_,
    fun _ x _ => isEqn_zero x⟩
  · exact eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨PUnit.unit, trivial⟩
  · change (1 : X.functionField) = fnOf _ h (1 : Γ(X, ⊤ ⊓ ⊤)) * 1
    rw [map_one, mul_one]

def toPic : CartierDiv X →+ Pic X := AddMonoidHom.mk' (fun D => cls _ (isLB_toLB D)) fun D E =>
  (cls_eq_iff _ (isLB_tens (isLB_toLB D) (isLB_toLB E))).2
    ((presents_toLB _).lbIso ((presents_toLB D).tens (presents_toLB E)))

theorem toPic_apply (D : CartierDiv X) : toPic D = cls _ (isLB_toLB D) := rfl

theorem Presents.toPic_eq (h : Presents D L r) : toPic D = cls L h.isLB := by
  rw [toPic_apply, cls_eq_iff]
  exact (presents_toLB D).lbIso h

theorem toPic_principal (g : X.functionFieldˣ) : toPic (principal g) = 0 := by
  have h1 := presents_zero.add_principal g
  rw [zero_add] at h1
  rw [h1.toPic_eq, ← presents_zero.toPic_eq, map_zero]

theorem toPic_surjective : Function.Surjective (toPic (X := X)) := by
  intro c
  refine Quotient.inductionOn c fun a => ?_
  obtain ⟨L, hL⟩ := a
  obtain ⟨i₀, h₀⟩ := exists_chart hL (genericPoint X)
  exact ⟨ofLB hL i₀ h₀, (presents_ofLB hL i₀ h₀).toPic_eq⟩

section Canonical

open TopForm

variable {k : Type} [CommRing k] (p : X ⟶ Sp k) (d : ℕ)

def constFn : k →+* X.functionField := (fnOf ⊤ trivial).comp (algX p ⊤)

theorem fnOf_comp_algX (U : X.Opens) (h : genericPoint X ∈ U) :
    (fnOf U h).comp (algX p U) = constFn p := by
  ext c
  simp only [constFn, RingHom.comp_apply]
  rw [← resG_comp_algX p (le_top : U ≤ ⊤), RingHom.comp_apply, fnOf_resG]

abbrev RatForms : Type := Forms (constFn p) d

variable {p d}

def formOf (U : X.Opens) (h : genericPoint X ∈ U) : FormsOn p d U →ₛₗ[fnOf U h] RatForms p d :=
  formMap d (fnOf U h) (fnOf_comp_algX p U h)

@[simp] theorem formOf_resForm {U V : X.Opens} (e : V ≤ U) (h : genericPoint X ∈ V)
    (ω : FormsOn p d U) : formOf V h (resForm e ω) = formOf U (e h) ω := by
  simp only [formOf, resForm]
  exact formMap_formMap _ _ _ (RingHom.ext fun a => fnOf_resG e h a) _ _ _ ω

theorem isFreeGen_formOf {U : X.Opens} (h : genericPoint X ∈ U) {ω : FormsOn p d U}
    (hω : IsFrame ω) : IsFreeGen X.functionField (formOf U h ω) := by
  let _ := (algX p U).toAlgebra
  let _ := (constFn p).toAlgebra
  let _ := (fnOf U h).toAlgebra
  have _ : IsScalarTower k Γ(X, U) X.functionField :=
    IsScalarTower.of_algebraMap_eq' (fnOf_comp_algX p U h).symm
  have _ : Nonempty U := ⟨⟨_, h⟩⟩
  have _ : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen (U := U) (hU := hω.affine)
  have _ : Algebra.FormallyEtale Γ(X, U) X.functionField :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors Γ(X, U))
  have hb : IsBaseChange X.functionField (KaehlerDifferential.map k k Γ(X, U) X.functionField) :=
    KaehlerDifferential.isBaseChange_of_formallyEtale ..
  exact IsFreeGen.of_isBaseChange (isBaseChange_exteriorPower hb d) hω.gen

theorem formOf_eq_ratio_smul {U U' : X.Opens} (h : genericPoint X ∈ U) (h' : genericPoint X ∈ U')
    {ω : FormsOn p d U} {ω' : FormsOn p d U'} (hω : IsFrame ω) (hω' : IsFrame ω') :
    formOf U' h' ω' = fnOf (U ⊓ U') (memInf h h') (hω.ratio hω').val • formOf U h ω := by
  obtain ⟨W, hWa, hgW, hWle⟩ := exists_isAffineOpen_mem_and_subset (memInf h h')
  have h1 : W ≤ U := fun y hy => (hWle hy).1
  have h2 : W ≤ U' := fun y hy => (hWle hy).2
  rw [← formOf_resForm h2 hgW ω', hω.resForm_eq_ratio_smul hω' hWa h1 h2, map_smulₛₗ,
    formOf_resForm, fnOf_resG]

def IsDivOfForm (D : CartierDiv X) (η : RatForms p d) : Prop :=
  ∀ (U : X.Opens) (ω : FormsOn p d U), IsFrame ω → ∀ (x : X) (hx : x ∈ U) (g : X.functionFieldˣ),
    η = (g : X.functionField) • formOf U (gen_mem hx) ω → D.IsEqn x g

variable (p d) [SmoothOfRelativeDimension d p]

def baseChart : (CanonLB.all p d).bundle.ι :=
  (exists_chart (CanonLB.all p d).isLB (genericPoint X)).choose

abbrev baseOpen : X.Opens := (CanonLB.all p d).bundle.U (baseChart p d)

theorem gen_mem_baseOpen : genericPoint X ∈ baseOpen p d :=
  (exists_chart (CanonLB.all p d).isLB (genericPoint X)).choose_spec

abbrev baseFrame : FormsOn p d (baseOpen p d) := (CanonLB.all p d).om (baseChart p d)

theorem isFrame_baseFrame : IsFrame (baseFrame p d) :=
  (CanonLB.all p d).isFrame (baseChart p d)

def baseForm : RatForms p d := formOf _ (gen_mem_baseOpen p d) (baseFrame p d)

theorem isFreeGen_baseForm : IsFreeGen X.functionField (baseForm p d) :=
  isFreeGen_formOf (gen_mem_baseOpen p d) (isFrame_baseFrame p d)

theorem baseForm_ne_zero : baseForm p d ≠ 0 := by
  intro h0
  exact one_ne_zero ((isFreeGen_baseForm p d).1
    (show (1 : X.functionField) • baseForm p d = (0 : X.functionField) • baseForm p d by simp [h0]))

def canonical : CartierDiv X := ofLB (CanonLB.all p d).isLB (baseChart p d) (gen_mem_baseOpen p d)

theorem presents_canonical : Presents (canonical p d) (CanonLB.all p d).bundle
    (frameRat _ (baseChart p d) (gen_mem_baseOpen p d)) :=
  presents_ofLB _ _ _

theorem isDivOfForm_canonical : IsDivOfForm (canonical p d) (baseForm p d) := by
  intro U ω hω x hx g e
  obtain ⟨i, hi⟩ := exists_chart (CanonLB.all p d).isLB x
  have hE := (presents_canonical p d).isEqn i x hi
  have hgi : genericPoint X ∈ (CanonLB.all p d).bundle.U i := gen_mem hi
  have hF := isFreeGen_formOf (gen_mem hx) hω
  have e1 := formOf_eq_ratio_smul hgi (gen_mem_baseOpen p d) ((CanonLB.all p d).isFrame i)
    (isFrame_baseFrame p d)
  have e2 := formOf_eq_ratio_smul (gen_mem hx) hgi hω ((CanonLB.all p d).isFrame i)
  have hu := unitAt_fnOf (memInf hx hi) (memInf (gen_mem hx) hgi)
    (hω.ratio ((CanonLB.all p d).isFrame i))
  have key : (g : X.functionField) =
      (frameRat _ (baseChart p d) (gen_mem_baseOpen p d) i : X.functionField) *
        fnOf _ (memInf (gen_mem hx) hgi) (hω.ratio ((CanonLB.all p d).isFrame i)).val := by
    apply hF.1
    dsimp only
    rw [← e, mul_smul, ← e2, val_frameRat _ _ _ hgi, CanonLB.g_eq_ratio, ← e1]
    rfl
  rw [hE.iff_unitAt, key, mul_div_cancel_left₀ _ (Units.ne_zero _)]
  exact hu

variable {p d} in

theorem IsDivOfForm.unique {η : RatForms p d} (hη : η ≠ 0) (h : IsDivOfForm D η)
    (h' : IsDivOfForm E η) : D = E := by
  apply ext_of_isEqn
  intro x
  obtain ⟨U, ω, hx, hω⟩ := exists_isFrame p d x
  obtain ⟨a, ha⟩ := (isFreeGen_formOf (gen_mem hx) hω).2 η
  dsimp only at ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hη (by rw [← ha, zero_smul])
  exact ⟨Units.mk0 a ha0, h U ω hω x hx _ (by rw [Units.val_mk0, ha]),
    h' U ω hω x hx _ (by rw [Units.val_mk0, ha])⟩

omit [SmoothOfRelativeDimension d p] in
variable {p d} in

theorem IsDivOfForm.smul {η : RatForms p d} (h : IsDivOfForm D η) (g : X.functionFieldˣ) :
    IsDivOfForm (D + principal g) ((g : X.functionField) • η) := by
  intro U ω hω x hx g' e
  have h1 : η = ((g⁻¹ * g' : X.functionFieldˣ) : X.functionField) • formOf U (gen_mem hx) ω := by
    rw [Units.val_mul, mul_smul, ← e, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_smul]
  have h2 := (h U ω hω x hx _ h1).add (isEqn_principal g x)
  rwa [mul_comm (g⁻¹ * g') g, mul_inv_cancel_left] at h2

end Canonical

end GlobalTheory.Cartier
