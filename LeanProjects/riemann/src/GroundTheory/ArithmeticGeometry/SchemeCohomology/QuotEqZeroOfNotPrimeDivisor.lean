import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveCohomology

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Topology

universe w' u

namespace GroundTheory.Arith.SchemeCoh

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

section Repartitions

variable [IsIntegral X] [IsNoetherian X] [IsNormalScheme X]

variable (k X) in

def repartitions : Submodule k (PrimeDivisor X → X.functionField) where
  carrier := {a | {Z : PrimeDivisor X | ¬ Z.valuation (a Z) ≤ 1}.Finite}
  zero_mem' := by simp
  add_mem' {a b} ha hb := by
    refine (ha.union hb).subset fun Z hZ => ?_
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hc
    exact hZ ((Valuation.map_add _ _ _).trans (max_le hc.1 hc.2))
  smul_mem' c {a} ha := by
    refine ha.subset fun Z hZ => ?_
    intro h
    apply hZ
    change Z.valuation (c • a Z) ≤ 1
    rw [Algebra.smul_def, map_mul]
    calc _ ≤ 1 * 1 := mul_le_mul' (Z.valuation_algebraMap_scalar_le_one c) h
      _ = 1 := one_mul 1

variable (k) in

def boundedRepartitions (D : WeilDivisor X) : Submodule k (repartitions k X) where
  carrier := {a | ∀ Z : PrimeDivisor X, a.1 Z ∈ Z.divisorSubgroup D}
  zero_mem' Z := (Z.divisorSubgroup D).zero_mem
  add_mem' {a b} ha hb Z := (Z.divisorSubgroup D).add_mem (ha Z) (hb Z)
  smul_mem' c {a} ha Z := by
    have h := ha Z
    rw [PrimeDivisor.mem_divisorSubgroup] at h ⊢
    change Z.valuation (c • a.1 Z) ≤ _
    rw [Algebra.smul_def, map_mul]
    calc _ ≤ 1 * WithZero.exp (D Z) := mul_le_mul' (Z.valuation_algebraMap_scalar_le_one c) h
      _ = _ := one_mul _

lemma mem_boundedRepartitions (D : WeilDivisor X) (a : repartitions k X) :
    a ∈ boundedRepartitions k D ↔ ∀ Z : PrimeDivisor X, a.1 Z ∈ Z.divisorSubgroup D := Iff.rfl

lemma const_mem_repartitions (f : X.functionField) :
    (fun _ : PrimeDivisor X => f) ∈ repartitions k X := by
  refine (finite_not_mem_divisorSubgroup (0 : WeilDivisor X) f).subset fun Z hZ => ?_
  simpa only [Set.mem_ofPred_eq, PrimeDivisor.mem_divisorSubgroup, Finsupp.coe_zero,
    Pi.zero_apply, WithZero.exp_zero] using hZ

variable (k X) in

def diagRepartition : X.functionField →ₗ[k] repartitions k X where
  toFun f := ⟨fun _ => f, const_mem_repartitions f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Repartitions

section Principal

variable [IsIntegral X] [IsNoetherian X] [IsNormalScheme X] (D : WeilDivisor X)

open Classical in

noncomputable def extendRep (a : PrimeDivisor X → X.functionField) (x : X) : X.functionField :=
  if h : ringKrullDim (X.presheaf.stalk x) = 1 then a (PrimeDivisor.ofPoint x h) else 0

omit [AlgebraicGeometry.IsNoetherian X] [IsNormalScheme X] in
lemma extendRep_point (a : PrimeDivisor X → X.functionField) (Z : PrimeDivisor X) :
    extendRep a Z.point = a Z := by
  rw [extendRep, dif_pos (show ringKrullDim (X.presheaf.stalk Z.point) = 1 from Z.2)]
  rfl

lemma quot_eq_zero_of_not_primeDivisor {x : X} (hx : ¬ ringKrullDim (X.presheaf.stalk x) = 1)
    (q : X.functionField ⧸ pointSubgroup D x) : q = 0 := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective q
  rw [QuotientAddGroup.eq_zero_iff, mem_pointSubgroup_iff]
  exact fun h => absurd h hx

lemma mk_extendRep_mem (a : repartitions k X) :
    (fun z : (⊤ : X.Opens) =>
      (QuotientAddGroup.mk (extendRep a.1 z.1) : X.functionField ⧸ pointSubgroup D z.1)) ∈
      quotSections D ⊤ := by
  intro y
  refine ⟨⊤, trivial, ?_⟩
  have hfin : {Z : PrimeDivisor X | a.1 Z ∉ Z.divisorSubgroup D}.Finite := by
    refine (a.2.union D.support.finite_toSet).subset fun Z hZ => ?_
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, Finset.mem_coe,
      Finsupp.mem_support_iff] at hc
    apply hZ
    rw [PrimeDivisor.mem_divisorSubgroup, hc.2, WithZero.exp_zero]
    exact hc.1
  have hinj : Function.Injective (fun z : (⊤ : X.Opens) => z.1) := Subtype.val_injective
  refine ((hfin.image PrimeDivisor.point).preimage hinj.injOn).subset ?_
  rintro z ⟨-, hz⟩
  by_cases h : ringKrullDim (X.presheaf.stalk z.1) = 1
  · refine ⟨PrimeDivisor.ofPoint z.1 h, fun hmem => hz ?_, rfl⟩
    rw [QuotientAddGroup.eq_zero_iff, extendRep, dif_pos h, mem_pointSubgroup_iff]
    intro h'
    exact (PrimeDivisor.mem_divisorSubgroup _ _ _).mp hmem
  · exact absurd (quot_eq_zero_of_not_primeDivisor D h _) hz

variable (k) in

noncomputable def repToQuot : repartitions k X →+ quotSections D ⊤ where
  toFun a := ⟨fun z => QuotientAddGroup.mk (extendRep a.1 z.1), mk_extendRep_mem D a⟩
  map_zero' := by
    apply Subtype.ext
    funext z
    change (QuotientAddGroup.mk (extendRep 0 z.1) : X.functionField ⧸ pointSubgroup D z.1) = 0
    unfold extendRep
    split_ifs <;> rfl
  map_add' a b := by
    apply Subtype.ext
    funext z
    change (QuotientAddGroup.mk (extendRep (a.1 + b.1) z.1) :
      X.functionField ⧸ pointSubgroup D z.1) =
      QuotientAddGroup.mk (extendRep a.1 z.1) + QuotientAddGroup.mk (extendRep b.1 z.1)
    rw [← QuotientAddGroup.mk_add]
    unfold extendRep
    split_ifs
    · rfl
    · rw [add_zero]

lemma repToQuot_apply (a : repartitions k X) (z : (⊤ : X.Opens)) :
    (repToQuot k D a).1 z = QuotientAddGroup.mk (extendRep a.1 z.1) := rfl

lemma repToQuot_eq_zero_iff (a : repartitions k X) :
    repToQuot k D a = 0 ↔ a ∈ boundedRepartitions k D := by
  constructor
  · intro h Z
    have := congrArg (fun s : quotSections D ⊤ => s.1 ⟨Z.point, trivial⟩) h
    change (QuotientAddGroup.mk (extendRep a.1 Z.point) :
      X.functionField ⧸ pointSubgroup D Z.point) = 0 at this
    rw [QuotientAddGroup.eq_zero_iff, extendRep_point, mem_pointSubgroup_primeDivisor] at this
    exact this
  · intro h
    apply Subtype.ext
    funext z
    change (QuotientAddGroup.mk (extendRep a.1 z.1) : X.functionField ⧸ pointSubgroup D z.1) = 0
    by_cases hz : ringKrullDim (X.presheaf.stalk z.1) = 1
    · rw [QuotientAddGroup.eq_zero_iff, extendRep, dif_pos hz, mem_pointSubgroup_iff]
      intro _
      exact (PrimeDivisor.mem_divisorSubgroup _ _ _).mp (h _)
    · exact quot_eq_zero_of_not_primeDivisor D hz _

lemma quotSections_top_finite (s : quotSections D ⊤) :
    {z : (⊤ : X.Opens) | s.1 z ≠ 0}.Finite := by
  choose W hW hfin using fun y : (⊤ : X.Opens) => s.2 y
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y : (⊤ : X.Opens) => (W y : Set X))
    (fun y => (W y).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨⟨x, trivial⟩, hW _⟩)
  refine (t.finite_toSet.biUnion fun y _ => hfin y).subset fun z hz => ?_
  obtain ⟨y, hy, hzy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ z.1))
  exact Set.mem_iUnion₂.mpr ⟨y, hy, hzy, hz⟩

open Classical in

lemma repToQuot_surjective : Function.Surjective (repToQuot k D) := by
  intro s
  let r : PrimeDivisor X → X.functionField := fun Z =>
    if s.1 ⟨Z.point, trivial⟩ = 0 then 0
    else (QuotientAddGroup.mk_surjective (s.1 ⟨Z.point, trivial⟩)).choose
  have hr : ∀ Z : PrimeDivisor X,
      (QuotientAddGroup.mk (r Z) : X.functionField ⧸ pointSubgroup D Z.point) =
        s.1 ⟨Z.point, trivial⟩ := by
    intro Z
    simp only [r]
    split_ifs with h
    · rw [h]
      rfl
    · exact (QuotientAddGroup.mk_surjective (s.1 ⟨Z.point, trivial⟩)).choose_spec
  have hmem : r ∈ repartitions k X := by
    have hinj : Function.Injective (fun Z : PrimeDivisor X => (⟨Z.point, trivial⟩ : (⊤ : X.Opens))) :=
      fun Z Z' h => PrimeDivisor.point_injective (congrArg (fun p : (⊤ : X.Opens) => p.1) h :)
    refine ((quotSections_top_finite D s).preimage hinj.injOn).subset fun Z hZ => ?_
    intro h0
    have h1 : r Z = 0 := if_pos h0
    change ¬ Z.valuation (r Z) ≤ 1 at hZ
    rw [h1, map_zero] at hZ
    exact hZ zero_le
  refine ⟨⟨r, hmem⟩, ?_⟩
  apply Subtype.ext
  funext z
  rw [repToQuot_apply]
  by_cases hz : ringKrullDim (X.presheaf.stalk z.1) = 1
  · have := hr (PrimeDivisor.ofPoint z.1 hz)
    rw [extendRep, dif_pos hz]
    exact this
  · exact (quot_eq_zero_of_not_primeDivisor D hz _).trans
      (quot_eq_zero_of_not_primeDivisor D hz _).symm

lemma quotSmul_repToQuot (c : k) (a : repartitions k X) :
    (quotSmul D c).hom.app (op ⊤) (repToQuot k D a) = repToQuot k D (c • a) := by
  apply Subtype.ext
  funext z
  change quotMul D c z.1 (QuotientAddGroup.mk (extendRep a.1 z.1)) =
    QuotientAddGroup.mk (extendRep (c • a.1) z.1)
  rw [quotMul_mk]
  unfold extendRep
  split_ifs
  · rw [Pi.smul_apply, Algebra.smul_def]
  · rw [mul_zero]

lemma constToQuot_top (t : constSections (⊤ : X.Opens)) :
    (constToQuot D).hom.app (op ⊤) t =
      repToQuot k D (diagRepartition k X (t.1 ⟨genericPoint X, trivial⟩)) := by
  apply Subtype.ext
  funext z
  rw [constToQuot_app_apply, repToQuot_apply]
  by_cases hz : ringKrullDim (X.presheaf.stalk z.1) = 1
  · rw [extendRep, dif_pos hz, constSections_apply_eq t z ⟨genericPoint X, trivial⟩]
    rfl
  · exact (quot_eq_zero_of_not_primeDivisor D hz _).trans
      (quot_eq_zero_of_not_primeDivisor D hz _).symm

end Principal

section H1

variable [IsIntegral X] [IsNoetherian X] [IsNormalScheme X]
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]
  (hX : topologicalKrullDim X ≤ 1) (D : WeilDivisor X)

variable (k) in

noncomputable def repToQuotTop : repartitions k X →+ (quotSheaf D).obj.obj (op ⊤) where
  toFun a := repToQuot k D a
  map_zero' := (repToQuot k D).map_zero
  map_add' := (repToQuot k D).map_add

omit [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})] in
lemma quotSmul_repToQuotTop (c : k) (a : repartitions k X) :
    (quotSmul D c).hom.app (op ⊤) (repToQuotTop k D a) = repToQuotTop k D (c • a) :=
  quotSmul_repToQuot D c a

omit [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})] in
lemma constToQuot_constSection (f : X.functionField) :
    (constToQuot D).hom.app (op ⊤) (show (constSheaf X).obj.obj (op ⊤) from constSection ⊤ f) =
      repToQuotTop k D (diagRepartition k X f) :=
  constToQuot_top D (constSection ⊤ f)

noncomputable def quotDelta :
    Sheaf.H.{w'} (quotSheaf D) 0 →+ Sheaf.H.{w'} (modulesAb (divisorSheaf D)) 1 :=
  H.δ.{w'} (divisorSeq_shortExact D hX) 0 1 rfl

lemma quotDelta_surjective : Function.Surjective (quotDelta.{w'} hX D) := fun x =>
  H.exact₁ (divisorSeq_shortExact D hX) (n₀ := 0) rfl x
    (H_eq_zero_of_isFlasque (constSheaf X) 0 _)

lemma quotDelta_eq_zero_iff (y : Sheaf.H.{w'} (quotSheaf D) 0) :
    quotDelta hX D y = 0 ↔
      ∃ w : Sheaf.H.{w'} (constSheaf X) 0, Sheaf.H.map (constToQuot D) 0 w = y :=
  ⟨fun h => H.exact₃ (divisorSeq_shortExact D hX) rfl y h, fun ⟨w, hw⟩ => hw ▸
    H.δ_map_g (divisorSeq_shortExact D hX) rfl w⟩

lemma quotDelta_smul (c : k) (y : Sheaf.H.{w'} (quotSheaf D) 0) :
    quotDelta hX D (Sheaf.H.map (quotSmul D c) 0 y) = c • quotDelta hX D y :=
  H.δ_naturality (divisorSeq_shortExact D hX) (divisorSeq_shortExact D hX) (divisorSeqSmul D c)
    0 1 rfl y

variable (k) in

noncomputable def repartitionToH1 : repartitions k X →+ Sheaf.H.{w'} (modulesAb (divisorSheaf D)) 1 :=
  (quotDelta hX D).comp
    ((Sheaf.H.equiv₀ (quotSheaf D) isTerminalTop).symm.toAddMonoidHom.comp (repToQuotTop k D))

lemma repartitionToH1_apply (a : repartitions k X) :
    repartitionToH1 k hX D a = quotDelta hX D
      ((Sheaf.H.equiv₀ (quotSheaf D) isTerminalTop).symm (repToQuotTop k D a)) := rfl

lemma repartitionToH1_surjective : Function.Surjective (repartitionToH1.{w'} k hX D) := by
  intro x
  obtain ⟨y, rfl⟩ := quotDelta_surjective hX D x
  obtain ⟨a, ha⟩ := repToQuot_surjective (k := k) D
    (Sheaf.H.equiv₀ (quotSheaf D) isTerminalTop y)
  refine ⟨a, ?_⟩
  have ha' : repToQuotTop k D a = Sheaf.H.equiv₀ (quotSheaf D) isTerminalTop y := ha
  rw [repartitionToH1_apply, ha', AddEquiv.symm_apply_apply]

lemma repartitionToH1_eq_zero_iff (a : repartitions k X) :
    repartitionToH1.{w'} k hX D a = 0 ↔
      a ∈ boundedRepartitions k D ⊔ LinearMap.range (diagRepartition k X) := by
  constructor
  · intro h
    rw [repartitionToH1_apply, quotDelta_eq_zero_iff] at h
    obtain ⟨w, hw⟩ := h
    let t : (constSheaf X).obj.obj (op ⊤) := Sheaf.H.equiv₀ (constSheaf X) isTerminalTop w
    have e1 : (constToQuot D).hom.app (op ⊤) t =
        Sheaf.H.equiv₀ (quotSheaf D) isTerminalTop (Sheaf.H.map (constToQuot D) 0 w) :=
      Sheaf.H.equiv₀_naturality (hT := isTerminalTop) (constToQuot D) w
    rw [hw, AddEquiv.apply_symm_apply] at e1
    have e3 : (constToQuot D).hom.app (op ⊤) t =
        repToQuotTop k D (diagRepartition k X ((show constSections ⊤ from t).1
          ⟨genericPoint X, trivial⟩)) :=
      constToQuot_top D t
    have hb : a - diagRepartition k X ((show constSections ⊤ from t).1 ⟨genericPoint X, trivial⟩) ∈
        boundedRepartitions k D := by
      rw [← repToQuot_eq_zero_iff, map_sub]
      change repToQuotTop k D a - repToQuotTop k D _ = 0
      rw [← e1, e3, sub_self]
    exact Submodule.mem_sup.mpr ⟨_, hb, _, ⟨_, rfl⟩, sub_add_cancel _ _⟩
  · intro h
    obtain ⟨b, hb, d, ⟨f, rfl⟩, rfl⟩ := Submodule.mem_sup.mp h
    rw [map_add]
    have h1 : repartitionToH1.{w'} k hX D b = 0 := by
      have : repToQuotTop k D b = repToQuotTop k D 0 :=
        ((repToQuot_eq_zero_iff D b).mpr hb).trans (map_zero (repToQuot k D)).symm
      rw [repartitionToH1_apply, this, ← repartitionToH1_apply hX D 0, map_zero]
    have h2 : repartitionToH1.{w'} k hX D (diagRepartition k X f) = 0 := by
      rw [repartitionToH1_apply, ← constToQuot_constSection, ← Sheaf.H.equiv₀_symm_naturality,
        quotDelta_eq_zero_iff]
      exact ⟨_, rfl⟩
    rw [h1, h2, add_zero]

lemma repartitionToH1_smul (c : k) (a : repartitions k X) :
    repartitionToH1.{w'} k hX D (c • a) = c • repartitionToH1.{w'} k hX D a := by
  rw [repartitionToH1_apply, repartitionToH1_apply, ← quotSmul_repToQuotTop, ← quotDelta_smul,
    Sheaf.H.equiv₀_symm_naturality]

variable (k) in

noncomputable def repartitionToH1Linear :
    repartitions k X →ₗ[k] Sheaf.H.{w'} (modulesAb (divisorSheaf D)) 1 where
  toFun := repartitionToH1 k hX D
  map_add' := map_add _
  map_smul' := repartitionToH1_smul hX D

lemma ker_repartitionToH1Linear :
    LinearMap.ker (repartitionToH1Linear.{w'} k hX D) =
      boundedRepartitions k D ⊔ LinearMap.range (diagRepartition k X) := by
  ext a
  exact repartitionToH1_eq_zero_iff hX D a

variable (k) in

noncomputable def divisorH1Equiv : Sheaf.H.{w'} (modulesAb (divisorSheaf D)) 1 ≃ₗ[k]
    (repartitions k X ⧸ (boundedRepartitions k D ⊔ LinearMap.range (diagRepartition k X))) :=
  ((Submodule.quotEquivOfEq _ _ (ker_repartitionToH1Linear hX D).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (repartitionToH1_surjective hX D))).symm

end H1

end GroundTheory.Arith.SchemeCoh
