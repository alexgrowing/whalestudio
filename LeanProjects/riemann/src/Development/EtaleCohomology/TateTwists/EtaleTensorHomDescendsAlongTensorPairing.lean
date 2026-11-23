import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.EtaleCohomology.TateTwists.EtaleTensorComplexDescendsNaturalFamily

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.TensFam

theorem res_res {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res h (Sec.res g y) = Sec.res (h ≫ g) y := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, h1⟩ := hP
  obtain ⟨T, hT, h2⟩ := hQ
  exact ⟨S ⊓ T, (Scheme.etaleTopology).intersection_covering hS hT, fun V g hg => ⟨h1 V g hg.1, h2 V g hg.2⟩⟩

theorem loc_top {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, (Scheme.etaleTopology).top_mem U, fun V g _ => h V g⟩

theorem sep {S : Type} [CommRing S] (M : Shv S) {U : Scheme.{0}} (s s' : Sec M U)
    (h : Loc U fun V g => Sec.res g s = Sec.res g s') : s = s' := by
  obtain ⟨T, hT, h1⟩ := h
  have hM := (isSheaf_iff_isSheaf_of_type _ _).mp ((Presheaf.isSheaf_iff_isSheaf_forget Scheme.etaleTopology M.obj (forget _)).mp M.2)
  exact (hM T hT).isSeparatedFor.ext fun V g hg => h1 V g hg

theorem glue {S : Type} [CommRing S] (M : Shv S) {U : Scheme.{0}} (T : Sieve U) (hT : T ∈ Scheme.etaleTopology U)
    (t : ∀ (V : Scheme.{0}) (g : V ⟶ U), T.arrows g → Sec M V)
    (ht : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : T.arrows g),
      t W (k ≫ g) (T.downward_closed hg k) = Sec.res k (t V g hg)) :
    ∃ s : Sec M U, ∀ V g (hg : T.arrows g), Sec.res g s = t V g hg := by
  have hM := (isSheaf_iff_isSheaf_of_type _ _).mp ((Presheaf.isSheaf_iff_isSheaf_forget Scheme.etaleTopology M.obj (forget _)).mp M.2)
  let x : Presieve.FamilyOfElements (M.obj ⋙ forget _) T.arrows := fun V g hg => t V g hg
  have hx : x.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro V W g k hg
    exact ht V W g k hg
  exact ⟨(hM T hT).amalgamate x hx, fun V g hg => (hM T hT).valid_glue hx g hg⟩

theorem lift_res {R : Type} [CommRing R] {I J K : Cx R} (τ : Pair I J K) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ)
    (x : Tens I J U w) : Sec.res g (τ.lift U w x) = τ.lift V w (Tens.res g w x) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb => simp only [Sec.res, map_add] at *; rw [ha, hb]
  | of i z =>
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [Sec.res, map_add] at *; rw [ha, hb]
    | tmul a c =>
      rw [← DirectSum.lof_eq_of (ULift.{1} R)]
      simp only [Pair.lift, Tens.res, DirectSum.lmap_lof, DirectSum.toModule_lof, TensorProduct.lift.tmul, TensorProduct.map_tmul]
      exact τ.nat g _ _ w _ a c

theorem res_add {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (a c : Sec F U) :
    Sec.res g (a + c) = Sec.res g a + Sec.res g c := map_add _ _ _

section Main
variable {R S : Type} [CommRing R] [CommRing S] {I J K : Cx R}

def Good (τ : Pair I J K) (w : ℤ) (M : Shv S) (b : ∀ U : Scheme.{0}, Tens I J U w →+ Sec M U)
    (U : Scheme.{0}) (y : Sec (K.X w) U) (s : Sec M U) : Prop :=
  Loc U fun V g => ∃ x, τ.lift V w x = Sec.res g y ∧ Sec.res g s = b V x

variable (τ : Pair I J K) (hτ : τ.IsTensor) (w : ℤ) (M : Shv S) (b : ∀ U : Scheme.{0}, Tens I J U w →+ Sec M U)
  (hb : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (b U x) = b V (Tens.res g w x))
include hτ hb

theorem key {U : Scheme.{0}} (x1 x2 : Tens I J U w) (h : τ.lift U w x1 = τ.lift U w x2) : b U x1 = b U x2 := by
  have h0 : τ.lift U w (x1 - x2) = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨T, hT, hT'⟩ := hτ.2 U w _ h0
  apply sep M
  refine ⟨T, hT, fun V g hg => ?_⟩
  have h1 : Tens.res g w (x1 - x2) = 0 := hT' V g hg
  rw [map_sub, sub_eq_zero] at h1
  show Sec.res g (b U x1) = Sec.res g (b U x2)
  rw [hb, hb, h1]

theorem uniq {U : Scheme.{0}} {y : Sec (K.X w) U} {s s' : Sec M U}
    (h1 : Good τ w M b U y s) (h2 : Good τ w M b U y s') : s = s' := by
  apply sep M
  obtain ⟨T, hT, h⟩ := loc_and h1 h2
  refine ⟨T, hT, fun V g hg => ?_⟩
  obtain ⟨⟨x, hx, hs⟩, ⟨x', hx', hs'⟩⟩ := h V g hg
  rw [hs, hs']
  exact key τ hτ w M b hb x x' (hx.trans hx'.symm)

theorem good_exists (U : Scheme.{0}) (y : Sec (K.X w) U) : ∃ s, Good τ w M b U y s := by
  obtain ⟨T, hT, hc⟩ := hτ.1 U w y
  let t : ∀ (V : Scheme.{0}) (g : V ⟶ U), T.arrows g → Sec M V := fun V g hg => b V (hc V g hg).choose
  obtain ⟨s, hs⟩ := glue M T hT t (by
    intro V W g k hg
    simp only [t]
    rw [hb]
    apply key τ hτ w M b hb
    rw [(hc W (k ≫ g) (T.downward_closed hg k)).choose_spec, ← lift_res, (hc V g hg).choose_spec, res_res])
  exact ⟨s, T, hT, fun V g hg => ⟨(hc V g hg).choose, (hc V g hg).choose_spec, hs V g hg⟩⟩

omit hτ in
theorem good_add {U : Scheme.{0}} {y1 y2 : Sec (K.X w) U} {s1 s2 : Sec M U}
    (h1 : Good τ w M b U y1 s1) (h2 : Good τ w M b U y2 s2) : Good τ w M b U (y1 + y2) (s1 + s2) := by
  obtain ⟨T, hT, h⟩ := loc_and h1 h2
  refine ⟨T, hT, fun V g hg => ?_⟩
  obtain ⟨⟨x, hx, hs⟩, ⟨x', hx', hs'⟩⟩ := h V g hg
  exact ⟨x + x', by rw [map_add, hx, hx', res_add], by rw [res_add, hs, hs', map_add]⟩

omit hτ hb in
theorem good_zero (U : Scheme.{0}) : Good τ w M b U 0 0 :=
  loc_top fun V g => ⟨0, by simp, by simp⟩

omit hτ in
theorem good_nat {V U : Scheme.{0}} (g : V ⟶ U) {y : Sec (K.X w) U} {s : Sec M U}
    (h : Good τ w M b U y s) : Good τ w M b V (Sec.res g y) (Sec.res g s) := by
  obtain ⟨T, hT, h1⟩ := h
  refine ⟨T.pullback g, (Scheme.etaleTopology).pullback_stable g hT, fun W k hk => ?_⟩
  obtain ⟨x, hx, hs⟩ := h1 W (k ≫ g) hk
  exact ⟨x, by rw [res_res, hx], by rw [res_res, hs]⟩

omit hτ in
theorem good_lift (U : Scheme.{0}) (x : Tens I J U w) : Good τ w M b U (τ.lift U w x) (b U x) :=
  loc_top fun V g => ⟨Tens.res g w x, (lift_res τ g w x).symm, hb V U g x⟩

end Main

end LateralTheory.EtaleFoundations.TensFam

open LateralTheory.EtaleFoundations.TensFam in
theorem LateralTheory.EtaleFoundations.etale_tensor_hom_descends_along_tensor_pairing : LateralTheory.EtaleFoundations.EtaleTensorComplexDescendsNaturalFamily := by
  intro R S _ _ I J K τ hτ w M b hb
  have ex := good_exists τ hτ w M b hb
  let φ : ∀ U : Scheme.{0}, Sec (K.X w) U →+ Sec M U := fun U =>
    { toFun := fun y => (ex U y).choose
      map_zero' := uniq τ hτ w M b hb (ex U 0).choose_spec (good_zero τ w M b U)
      map_add' := fun y1 y2 => uniq τ hτ w M b hb (ex U _).choose_spec
        (good_add τ w M b hb (ex U y1).choose_spec (ex U y2).choose_spec) }
  refine ⟨φ, fun V U g y => ?_, fun U x => ?_⟩
  · exact uniq τ hτ w M b hb (good_nat τ w M b hb g (ex U y).choose_spec) (ex V _).choose_spec
  · exact uniq τ hτ w M b hb (ex U _).choose_spec (good_lift τ w M b hb U x)
