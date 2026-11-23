import Development.AbelianVarietyTheory.Definitions.Divisors.CechFam
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSubsingletonCohTwistTensLbPow
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogDR.LatSheaf

variable {X : Scheme.{0}} [IsIntegral X] {V : Type} [AddCommGroup V] [Module X.functionField V]

def secGrp (M : X → AddSubgroup V) (U : X.Opens) : AddSubgroup V where
  carrier := {v | (∀ y ∈ U, v ∈ M y) ∧ (genericPoint X ∉ U → v = 0)}
  add_mem' := fun {a b} ha hb =>
    ⟨fun y hy => add_mem (ha.1 y hy) (hb.1 y hy), fun h => by rw [ha.2 h, hb.2 h, add_zero]⟩
  zero_mem' := ⟨fun y _ => zero_mem _, fun _ => rfl⟩
  neg_mem' := fun {a} ha => ⟨fun y hy => neg_mem (ha.1 y hy), fun h => by rw [ha.2 h, neg_zero]⟩

variable (M : X → AddSubgroup V)

theorem val_eq_zero {U : X.Opens} (h : genericPoint X ∉ U) (s : secGrp M U) : (s : V) = 0 := s.2.2 h

open Classical in

def resHom {U W : X.Opens} (e : W ≤ U) : secGrp M U →+ secGrp M W where
  toFun s := if h : genericPoint X ∈ W then ⟨(s : V), fun y hy => s.2.1 y (e hy), fun h' => (h' h).elim⟩
    else 0
  map_zero' := by split_ifs <;> rfl
  map_add' s t := by split_ifs <;> first | rfl | simp

open Classical in
theorem val_resHom {U W : X.Opens} (e : W ≤ U) (s : secGrp M U) :
    ((resHom M e s : secGrp M W) : V) = if genericPoint X ∈ W then (s : V) else 0 := by
  unfold resHom; simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]; split_ifs <;> rfl

theorem val_resHom_of_mem {U W : X.Opens} (e : W ≤ U) (h : genericPoint X ∈ W) (s : secGrp M U) :
    ((resHom M e s : secGrp M W) : V) = s := by rw [val_resHom, if_pos h]

def pre : TopCat.Presheaf Ab.{0} X where
  obj U := AddCommGrpCat.of (secGrp M U.unop)
  map f := AddCommGrpCat.ofHom (resHom M (leOfHom f.unop))
  map_id U := by
    ext s
    change ((resHom M le_rfl s : secGrp M U.unop) : V) = s
    rw [val_resHom]; split_ifs with h
    · rfl
    · exact (val_eq_zero M h s).symm
  map_comp f g := by
    ext s
    change ((resHom M (leOfHom (f ≫ g).unop) s : secGrp M _) : V) =
      ((resHom M (leOfHom g.unop) (resHom M (leOfHom f.unop) s) : secGrp M _) : V)
    rw [val_resHom, val_resHom, val_resHom]
    split_ifs with h1 h2 <;> first | rfl | exact (h2 (leOfHom g.unop h1)).elim

theorem sec_ext {U : X.Opens} {s t : secGrp M U} (h : genericPoint X ∈ U → (s : V) = t) : s = t := by
  by_cases hU : genericPoint X ∈ U
  · exact Subtype.ext (h hU)
  · exact Subtype.ext ((val_eq_zero M hU s).trans (val_eq_zero M hU t).symm)

def sv (U : (X.Opens)ᵒᵖ) (s : (pre M).obj U) : V := @Subtype.val V (· ∈ secGrp M U.unop) s

theorem sv_mem (U : (X.Opens)ᵒᵖ) (s : (pre M).obj U) : sv M U s ∈ secGrp M U.unop :=
  @Subtype.property V (· ∈ secGrp M U.unop) s

theorem sv_ext {U : (X.Opens)ᵒᵖ} {s t : (pre M).obj U} (h : genericPoint X ∈ U.unop → sv M U s = sv M U t) :
    s = t :=
  sec_ext M (U := U.unop) (s := s) (t := t) h

def mk (U : (X.Opens)ᵒᵖ) (v : V) (h : v ∈ secGrp M U.unop) : (pre M).obj U :=
  (⟨v, h⟩ : secGrp M U.unop)

@[simp] theorem sv_mk (U : (X.Opens)ᵒᵖ) (v : V) (h : v ∈ secGrp M U.unop) : sv M U (mk M U v h) = v := rfl

open Classical in
theorem sv_map {U W : (X.Opens)ᵒᵖ} (f : U ⟶ W) (s : (pre M).obj U) :
    sv M W ((pre M).map f s) = if genericPoint X ∈ W.unop then sv M U s else 0 :=
  val_resHom M (leOfHom f.unop) s

theorem isSheaf_pre : (pre M).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro κ W sf hsf
  have key : ∀ k l, genericPoint X ∈ W k → genericPoint X ∈ W l →
      sv M _ (sf k) = sv M _ (sf l) := fun k l hk hl => by
    have := congrArg (sv M _) (hsf k l)
    rw [sv_map, sv_map, if_pos (show genericPoint X ∈ W k ⊓ W l from ⟨hk, hl⟩),
      if_pos (show genericPoint X ∈ W k ⊓ W l from ⟨hk, hl⟩)] at this
    exact this
  by_cases hg : genericPoint X ∈ iSup W
  · obtain ⟨k₀, hk₀⟩ := Opens.mem_iSup.1 hg
    have mem : sv M _ (sf k₀) ∈ secGrp M (iSup W) := by
      refine ⟨fun y hy => ?_, fun h => (h hg).elim⟩
      obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hy
      rw [key k₀ k hk₀ (gen_mem hk)]
      exact (sv_mem M _ (sf k)).1 y hk
    refine ⟨mk M (Opposite.op (iSup W)) _ mem, fun k => ?_, fun t ht => ?_⟩
    · refine sv_ext M fun hk => ?_
      rw [sv_map, if_pos hk, sv_mk]
      exact key k₀ k hk₀ hk
    · refine sv_ext M fun _ => ?_
      have := congrArg (sv M _) (ht k₀)
      rw [sv_map, if_pos hk₀] at this
      rw [sv_mk]
      exact this
  · refine ⟨mk M (Opposite.op (iSup W)) 0 (zero_mem _), fun k => ?_, fun t _ => ?_⟩
    · exact sv_ext M fun hk => (hg (Opens.mem_iSup.2 ⟨k, hk⟩)).elim
    · exact sv_ext M fun h => (hg h).elim

variable {M}
variable (hM : ∀ y (f : X.functionField) (v : V), RegAt y f → v ∈ M y → f • v ∈ M y)

open Classical in

def smulSec (U : X.Opens) (r : Γ(X, U)) (s : secGrp M U) : secGrp M U :=
  if h : genericPoint X ∈ U then
    ⟨fnOf U h r • (s : V), fun y hy => hM y _ _ (regAt_fnOf hy h r) (s.2.1 y hy), fun h' => (h' h).elim⟩
  else 0

theorem val_smulSec {U : X.Opens} (h : genericPoint X ∈ U) (r : Γ(X, U)) (s : secGrp M U) :
    (smulSec hM U r s : V) = fnOf U h r • (s : V) := by
  rw [smulSec, dif_pos h]

def secModule (U : X.Opens) : Module Γ(X, U) (secGrp M U) where
  smul := smulSec hM U
  one_smul s := sec_ext M fun h => by
    change (smulSec hM U 1 s : V) = s
    rw [val_smulSec hM h, map_one, one_smul]
  mul_smul a b s := sec_ext M fun h => by
    change (smulSec hM U (a * b) s : V) = smulSec hM U a (smulSec hM U b s)
    rw [val_smulSec hM h, val_smulSec hM h, val_smulSec hM h, map_mul, mul_smul]
  smul_zero a := sec_ext M fun h => by
    change (smulSec hM U a 0 : V) = ((0 : secGrp M U) : V)
    rw [val_smulSec hM h, ZeroMemClass.coe_zero, smul_zero]
  smul_add a s t := sec_ext M fun h => by
    change (smulSec hM U a (s + t) : V) = ((smulSec hM U a s + smulSec hM U a t : secGrp M U) : V)
    rw [AddSubgroup.coe_add, val_smulSec hM h, val_smulSec hM h, val_smulSec hM h, AddSubgroup.coe_add,
      smul_add]
  add_smul a b s := sec_ext M fun h => by
    change (smulSec hM U (a + b) s : V) = ((smulSec hM U a s + smulSec hM U b s : secGrp M U) : V)
    rw [AddSubgroup.coe_add, val_smulSec hM h, val_smulSec hM h, val_smulSec hM h, map_add, add_smul]
  zero_smul s := sec_ext M fun h => by
    change (smulSec hM U 0 s : V) = ((0 : secGrp M U) : V)
    rw [val_smulSec hM h, map_zero, zero_smul, ZeroMemClass.coe_zero]

theorem resHom_smulSec {U W : X.Opens} (e : W ≤ U) (r : Γ(X, U)) (s : secGrp M U) :
    resHom M e (smulSec hM U r s) = smulSec hM W (resG X e r) (resHom M e s) :=
  sec_ext M fun h => by
    rw [val_resHom_of_mem M e h, val_smulSec hM h, val_smulSec hM (e h), fnOf_resG,
      val_resHom_of_mem M e h]

def toMod : X.Modules :=
  letI : ∀ U, Module (X.ringCatSheaf.obj.obj U) ((pre M).obj U) := fun U => secModule hM U.unop
  { val := PresheafOfModules.ofPresheaf (pre M) fun _ _ f r m => resHom_smulSec hM (leOfHom f.unop) r m
    isSheaf := isSheaf_pre M }

def latModel : LatModel M (toMod hM) where
  val U _ := { toFun := fun s => sv M (Opposite.op U) s, map_zero' := rfl, map_add' := fun _ _ => rfl }
  inj U _ s t e := sv_ext M fun _ => e
  range U h := by
    ext v
    simp only [AddMonoidHom.mem_range, AddMonoidHom.coe_mk, ZeroHom.coe_mk, latSec,
      AddSubgroup.mem_iInf]
    constructor
    · rintro ⟨s, rfl⟩ y hy
      exact (sv_mem M _ s).1 y hy
    · intro hv
      exact ⟨mk M (Opposite.op U) v ⟨hv, fun h' => (h' h).elim⟩, rfl⟩
  res U W e h s := by
    exact (sv_map M (homOfLE e).op s).trans (if_pos h)
  smul U h r s := val_smulSec hM h r s

end GlobalTheory.LogDR.LatSheaf

theorem GlobalTheory.LogDR.exists_latModel : ∀ (X : Scheme.{0}) [IsIntegral X] {V : Type} [AddCommGroup V]
    [Module X.functionField V] (M : X → AddSubgroup V),
    (∀ y (f : X.functionField) (v : V), RegAt y f → v ∈ M y → f • v ∈ M y) →
      ∃ F : X.Modules, Nonempty (LatModel M F) :=
  fun _ _ _ _ _ _ hM => ⟨LatSheaf.toMod hM, ⟨LatSheaf.latModel hM⟩⟩
