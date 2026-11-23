import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlue
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

namespace DescLoc

variable {S : Type} [CommRing S] {P Q : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1}} (φ : P ⟶ Q)

theorem res_res {M : Shv S} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (a : Sec M U) :
    Sec.res k (Sec.res g a) = Sec.res (k ≫ g) a := by
  simp [Sec.res]

theorem res_add {M : Shv S} {V U : Scheme.{0}} (g : V ⟶ U) (a a' : Sec M U) :
    Sec.res g (a + a') = Sec.res g a + Sec.res g a' := map_add _ _ _

theorem pmap_comp (P : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1}) {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (x : P.obj (op U)) : (P.map k.op).hom ((P.map g.op).hom x) = (P.map (k ≫ g).op).hom x := by
  simp

theorem nat_apply {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    (φ.app (op V)).hom ((P.map g.op).hom x) = (Q.map g.op).hom ((φ.app (op U)).hom x) := by
  have := congrArg (fun f => f.hom x) (φ.naturality g.op)
  simpa using this

section Main
variable {S : Type} [CommRing S] {P Q : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1}} (φ : P ⟶ Q) (M : Shv S)
  (b : ∀ U : Scheme.{0}, P.obj (op U) →+ Sec M U)
  (hb : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (b U x) = b V ((P.map g.op).hom x))

theorem ext_loc {U : Scheme.{0}} (a a' : Sec M U) (h : Loc U fun _ g => Sec.res g a = Sec.res g a') : a = a' :=
  (sec_ext_glue S M U).1 a a' h

include hb in

theorem key (h2 : ∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0)
    {V : Scheme.{0}} (x x' : P.obj (op V)) (hx : (φ.app (op V)).hom x = (φ.app (op V)).hom x') : b V x = b V x' := by
  obtain ⟨T, hT, hz⟩ := h2 V (x - x') (by rw [map_sub, hx, sub_self])
  refine ext_loc M _ _ ⟨T, hT, fun W k hk => ?_⟩
  dsimp only
  rw [hb, hb]
  have := hz W k hk
  dsimp only at this
  rw [map_sub, sub_eq_zero] at this
  rw [this]

def Ch (U : Scheme.{0}) (y : Q.obj (op U)) (a : Sec M U) : Prop :=
  ∀ (V : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op V)), (φ.app (op V)).hom x = (Q.map g.op).hom y → Sec.res g a = b V x

theorem ch_unique (h1 : ∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y)
    {U : Scheme.{0}} (y : Q.obj (op U)) (a a' : Sec M U) (ha : Ch φ M b U y a) (ha' : Ch φ M b U y a') : a = a' := by
  obtain ⟨T, hT, hl⟩ := h1 U y
  refine ext_loc M _ _ ⟨T, hT, fun V g hg => ?_⟩
  obtain ⟨x, hx⟩ := hl V g hg
  rw [ha V g x hx, ha' V g x hx]

include hb in
theorem ch_exists (h1 : ∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y)
    (h2 : ∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0)
    (U : Scheme.{0}) (y : Q.obj (op U)) : ∃ a, Ch φ M b U y a := by
  obtain ⟨T, hT, hl⟩ := h1 U y
  let s : ∀ (V : Scheme.{0}) (g : V ⟶ U), T.arrows g → Sec M V := fun V g hg => b V (hl V g hg).choose
  have hs : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : T.arrows g),
      Sec.res k (s V g hg) = s W (k ≫ g) (T.downward_closed hg k) := by
    intro V W g k hg
    simp only [s]
    rw [hb]
    apply key φ M b hb h2
    rw [nat_apply, (hl V g hg).choose_spec, (hl W (k ≫ g) (T.downward_closed hg k)).choose_spec, pmap_comp]
  obtain ⟨a, ha⟩ := (sec_ext_glue S M U).2 T hT s hs
  refine ⟨a, fun V g x hx => ?_⟩
  refine ext_loc M _ _ ⟨T.pullback g, Scheme.etaleTopology.pullback_stable g hT, fun W k hk => ?_⟩
  dsimp only
  rw [res_res, ha W (k ≫ g) hk, hb]
  simp only [s]
  apply key φ M b hb h2
  rw [nat_apply, hx, (hl W (k ≫ g) hk).choose_spec, pmap_comp]

end Main

section Main2
variable {S : Type} [CommRing S] {P Q : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1}} (φ : P ⟶ Q) (M : Shv S)
  (b : ∀ U : Scheme.{0}, P.obj (op U) →+ Sec M U)
  (hb : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (b U x) = b V ((P.map g.op).hom x))
  (h1 : ∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y)
  (h2 : ∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0)

include hb h1 h2 in
theorem ch_add {U : Scheme.{0}} (y y' : Q.obj (op U)) (a a' : Sec M U) (ha : Ch φ M b U y a) (ha' : Ch φ M b U y' a') :
    Ch φ M b U (y + y') (a + a') := by
  intro V g x hx
  obtain ⟨T1, hT1, hl1⟩ := h1 V ((Q.map g.op).hom y)
  obtain ⟨T2, hT2, hl2⟩ := h1 V ((Q.map g.op).hom y')
  refine ext_loc M _ _ ⟨T1 ⊓ T2, Scheme.etaleTopology.intersection_covering hT1 hT2, fun W k hk => ?_⟩
  obtain ⟨x1, e1⟩ := hl1 W k hk.1
  obtain ⟨x2, e2⟩ := hl2 W k hk.2
  rw [pmap_comp] at e1 e2
  rw [res_res, res_add, ha W (k ≫ g) x1 e1, ha' W (k ≫ g) x2 e2, hb, ← map_add]
  apply key φ M b hb h2
  rw [nat_apply, hx, pmap_comp]
  simp only [map_add, e1, e2]

theorem ch_res {U V : Scheme.{0}} (h : V ⟶ U) (y : Q.obj (op U)) (a : Sec M U) (ha : Ch φ M b U y a) :
    Ch φ M b V ((Q.map h.op).hom y) (Sec.res h a) := by
  intro W k x hx
  rw [res_res]
  exact ha W (k ≫ h) x (by rw [hx, pmap_comp])

include hb h2 in
theorem ch_base {U : Scheme.{0}} (x : P.obj (op U)) : Ch φ M b U ((φ.app (op U)).hom x) (b U x) := by
  intro V g x' hx
  rw [hb]
  apply key φ M b hb h2
  rw [nat_apply, hx]

end Main2
end DescLoc

open DescLoc in
theorem desc_loc : ∀ (S : Type) [CommRing S] (P Q : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1}) (φ : P ⟶ Q), (∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y) → (∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) → ∀ (M : Shv S) (b : ∀ U : Scheme.{0}, P.obj (op U) →+ Sec M U), (∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (b U x) = b V ((P.map g.op).hom x)) → ∃ c : ∀ U : Scheme.{0}, Q.obj (op U) →+ Sec M U, (∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (c U y) = c V ((Q.map g.op).hom y)) ∧ ∀ U x, c U ((φ.app (op U)).hom x) = b U x := by
  intro S _ P Q φ h1 h2 M b hb
  have hex := ch_exists φ M b hb h1 h2
  let c0 : ∀ U : Scheme.{0}, Q.obj (op U) → Sec M U := fun U y => (hex U y).choose
  have hc0 : ∀ U y, Ch φ M b U y (c0 U y) := fun U y => (hex U y).choose_spec
  let c : ∀ U : Scheme.{0}, Q.obj (op U) →+ Sec M U := fun U =>
    AddMonoidHom.mk' (c0 U) (fun y y' => ch_unique φ M b h1 (y + y') _ _ (hc0 U (y + y'))
      (ch_add φ M b hb h1 h2 y y' _ _ (hc0 U y) (hc0 U y')))
  refine ⟨c, fun V U g y => ?_, fun U x => ?_⟩
  · exact ch_unique φ M b h1 _ _ _ (ch_res φ M b g y _ (hc0 U y)) (hc0 V _)
  · exact ch_unique φ M b h1 _ _ _ (hc0 U _) (ch_base φ M b hb h2 x)
end GlobalTheory.EtC
