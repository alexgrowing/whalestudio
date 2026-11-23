import Development.EtaleCohomology.EtaleSheaves.LCSurjPf
import Development.EtaleCohomology.EtaleSheaves.LPrimLocPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut LateralTheory.E.LocallyConstantH0

namespace LateralTheory.E.LocFormPf

instance ls (q : ℕ) (i : ℤ) : Presheaf.IsLocallySurjective Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)) :=
  Presheaf.isLocallySurjective_toSheafify'.{0, 1} (J := Scheme.etaleTopology.{0}) (Scheme.Γ ⋙ twF q i)

theorem loc_top {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => h V g⟩

theorem loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, hS'⟩ := hP
  obtain ⟨T, hT, hT'⟩ := hQ
  exact ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ⟨hS' V g hg.1, hT' V g hg.2⟩⟩

theorem loc_trans {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (hP : ∀ (V W : Scheme.{0}) (k : W ⟶ V) (g : V ⟶ U), P V g → P W (k ≫ g))
    (h : Loc U fun V g => Loc V fun W k => P W (k ≫ g)) : Loc U P := by
  obtain ⟨S, hS, hS'⟩ := h
  let R : Sieve U := { arrows := fun V g => P V g, downward_closed := fun {V W g} hg k => hP V W k g hg }
  refine ⟨R, Scheme.etaleTopology.transitive hS R fun V g hg => ?_, fun V g hg => hg⟩
  obtain ⟨T, hT, hT'⟩ := hS' V g hg
  exact Scheme.etaleTopology.superset_covering (fun W k hk => hT' W k hk) hT

theorem res_comp {R : Type} [CommRing R] (F : Shv R) {X W V : Scheme.{0}} (k : X ⟶ W) (h : W ⟶ V) (s : Sec F V) :
    Sec.res (k ≫ h) s = Sec.res k (Sec.res h s) := by
  show (F.obj.map (k ≫ h).op).hom s = (F.obj.map k.op).hom ((F.obj.map h.op).hom s)
  rw [op_comp, Functor.map_comp]
  rfl

theorem prim_map_comp {q : ℕ} {X W V : Scheme.{0}} (k : X ⟶ W) (h : W ⟶ V) (ζ : Prim q Γ(V, ⊤)) :
    ζ.map (k ≫ h).appTop.hom = (ζ.map h.appTop.hom).map k.appTop.hom := by
  apply Subtype.ext
  show (k ≫ h).appTop.hom ζ.1 = k.appTop.hom (h.appTop.hom ζ.1)
  rw [Scheme.Hom.comp_appTop]
  rfl

theorem sec_res (q : ℕ) (i : ℤ) {W V : Scheme.{0}} (h : W ⟶ V) (x : (twF q i).obj Γ(V, ⊤)) :
    Sec.res h (ofRings.sec (twF q i) V x) = ofRings.sec (twF q i) W ((twF q i).map (Scheme.Γ.map h.op) x) := by
  unfold Sec.res ofRings.sec
  erw [← ModuleCat.comp_apply, ← NatTrans.naturality, ConcreteCategory.comp_apply]

def Q (q : ℕ) (i : ℤ) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U) (V : Scheme.{0}) (g : V ⟶ U) : Prop :=
  ∃ c : ULift.{1} (ZMod q), Sec.res g y = c • twGen i (ζ.map g.appTop.hom)

theorem Q_stable (q : ℕ) (i : ℤ) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U)
    (V W : Scheme.{0}) (k : W ⟶ V) (g : V ⟶ U) (hg : Q q i ζ y V g) : Q q i ζ y W (k ≫ g) := by
  obtain ⟨c, hc⟩ := hg
  refine ⟨c, ?_⟩
  rw [res_comp, hc, prim_map_comp, ← LateralTheory.E.LCBijPf.twGen_res q i k (ζ.map g.appTop.hom)]
  exact LinearMap.map_smul ((tw q i).obj.map k.op).hom c _

end LateralTheory.E.LocFormPf

namespace LateralTheory.E.LocFormPf

theorem sec_add (q : ℕ) (i : ℤ) (V : Scheme.{0}) (x y : (twF q i).obj Γ(V, ⊤)) :
    ofRings.sec (twF q i) V (x + y) = ofRings.sec (twF q i) V x + ofRings.sec (twF q i) V y := by
  unfold ofRings.sec; exact map_add _ _ _

theorem sec_smul (q : ℕ) (i : ℤ) (V : Scheme.{0}) (c : ULift.{1} (ZMod q)) (x : (twF q i).obj Γ(V, ⊤)) :
    ofRings.sec (twF q i) V (c • x) = c • ofRings.sec (twF q i) V x := by
  unfold ofRings.sec; exact map_smul _ _ _

theorem sec_zero (q : ℕ) (i : ℤ) (V : Scheme.{0}) : ofRings.sec (twF q i) V 0 = 0 := by
  unfold ofRings.sec; exact map_zero _

def S (q : ℕ) (i : ℤ) (V : Scheme.{0}) (f : Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) : Sec (tw q i) V :=
  ofRings.sec (twF q i) V (Submodule.Quotient.mk f)

theorem S_zero (q : ℕ) (i : ℤ) (V : Scheme.{0}) : S q i V 0 = 0 := sec_zero q i V

theorem S_add (q : ℕ) (i : ℤ) (V : Scheme.{0}) (f g : Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) :
    S q i V (f + g) = S q i V f + S q i V g :=
  sec_add q i V (Submodule.Quotient.mk f) (Submodule.Quotient.mk g)

theorem S_smul (q : ℕ) (i : ℤ) (V : Scheme.{0}) (a : ULift.{1} (ZMod q)) (f : Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) :
    S q i V (a • f) = a • S q i V f :=
  sec_smul q i V a (Submodule.Quotient.mk f)

theorem S_single (q : ℕ) (i : ℤ) (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤)) (a : ULift.{1} (ZMod q)) :
    S q i V (Finsupp.single ζ a) = a • twGen i ζ := by
  have h3 : Finsupp.single ζ a = a • Finsupp.single ζ (1 : ULift.{1} (ZMod q)) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [h3, S_smul]
  rfl

theorem S_res_single (q : ℕ) (i : ℤ) {W V : Scheme.{0}} (k : W ⟶ V) (ξ : Prim q Γ(V, ⊤)) (a : ULift.{1} (ZMod q)) :
    Sec.res k (S q i V (Finsupp.single ξ a)) = S q i W (Finsupp.single (ξ.map k.appTop.hom) a) := by
  refine (sec_res q i k _).trans ?_
  unfold S
  congr 1
  change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map (Scheme.Γ.map k.op).hom) (Finsupp.single ξ a)) = _
  erw [Finsupp.mapDomain_single]
  rfl

theorem S_rel (q : ℕ) (i : ℤ) (W : Scheme.{0}) (ζ ξ : Prim q Γ(W, ⊤)) (e : (ZMod q)ˣ) (he : ξ.1 = ζ.1 ^ (e : ZMod q).val) :
    S q i W (Finsupp.single ξ 1) = S q i W (Finsupp.single ζ (ULift.up ((e ^ i : (ZMod q)ˣ) : ZMod q))) := by
  unfold S
  congr 1
  exact (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨ζ, ξ, e, he, rfl⟩)

theorem res_add {q : ℕ} (i : ℤ) {W V : Scheme.{0}} (k : W ⟶ V) (x y : Sec (tw q i) V) :
    Sec.res k (x + y) = Sec.res k x + Sec.res k y := map_add _ _ _

theorem res_smul {q : ℕ} (i : ℤ) {W V : Scheme.{0}} (k : W ⟶ V) (c : ULift.{1} (ZMod q)) (x : Sec (tw q i) V) :
    Sec.res k (c • x) = c • Sec.res k x := map_smul _ _ _

theorem res_zero {q : ℕ} (i : ℤ) {W V : Scheme.{0}} (k : W ⟶ V) : Sec.res k (0 : Sec (tw q i) V) = 0 := map_zero _

theorem single_loc (q : ℕ) [NeZero q] (i : ℤ) {V : Scheme.{0}} (ζ ξ : Prim q Γ(V, ⊤)) :
    Loc V fun W k => ∃ c : ULift.{1} (ZMod q), Sec.res k (S q i V (Finsupp.single ξ 1)) = c • twGen i (ζ.map k.appTop.hom) := by
  refine LateralTheory.E.L_prim_locPf.loc_mono' (LateralTheory.E.L_prim_locPf.c2 LateralTheory.E.L_prim_locPf.algPow q V ζ ξ)
    fun W k ⟨e, he⟩ => ⟨ULift.up ((e ^ i : (ZMod q)ˣ) : ZMod q), ?_⟩
  rw [S_res_single, S_rel q i W (ζ.map k.appTop.hom) (ξ.map k.appTop.hom) e he, S_single]

theorem elt_loc (q : ℕ) [NeZero q] (i : ℤ) {V : Scheme.{0}} (ζ : Prim q Γ(V, ⊤)) (f : Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) :
    Loc V fun W k => ∃ c : ULift.{1} (ZMod q), Sec.res k (S q i V f) = c • twGen i (ζ.map k.appTop.hom) := by
  induction f using Finsupp.induction_linear with
  | zero => exact loc_top fun W k => ⟨0, by rw [S_zero, res_zero, zero_smul]⟩
  | add f g hf hg =>
    refine LateralTheory.E.L_prim_locPf.loc_mono' (loc_and hf hg) fun W k ⟨⟨c1, h1⟩, ⟨c2, h2⟩⟩ => ⟨c1 + c2, ?_⟩
    rw [S_add, res_add, h1, h2, add_smul]
  | single ξ a =>
    refine LateralTheory.E.L_prim_locPf.loc_mono' (single_loc q i ζ ξ) fun W k ⟨c, h⟩ => ⟨a * c, ?_⟩
    have h3 : Finsupp.single ξ a = a • Finsupp.single ξ (1 : ULift.{1} (ZMod q)) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [h3, S_smul, res_smul, h, mul_smul]

theorem LocForm_of : LateralTheory.E.LCSurjPf.LocForm := by
  intro q _ i B _ ζ y
  have key : Loc (Spec (CommRingCat.of B)) (Q q i (gam ζ) y) := by
    apply loc_trans (Q_stable q i (gam ζ) y)
    refine ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i))
      (U := op (Spec (CommRingCat.of B))) y, fun V g hg => ?_⟩
    obtain ⟨x, hx⟩ := hg
    obtain ⟨f, hf⟩ := Submodule.Quotient.mk_surjective _ (x : (twF q i).obj Γ(V, ⊤))
    have hy : Sec.res g y = S q i V f := by
      refine (hx.symm : _ = ofRings.sec (twF q i) V x).trans ?_
      exact (congrArg (ofRings.sec (twF q i) V) hf).symm
    refine LateralTheory.E.L_prim_locPf.loc_mono' (elt_loc q i ((gam ζ).map g.appTop.hom) f) fun W k ⟨c, hc⟩ => ⟨c, ?_⟩
    rw [res_comp, prim_map_comp, hy, hc]
  refine LateralTheory.E.L_prim_locPf.loc_mono' key fun V g ⟨c, hc⟩ => ⟨c.down, ?_⟩
  rw [hc, ← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have hcv : ((c.down.val : ℕ) : ULift.{1} (ZMod q)) = c := by
    apply ULift.ext
    rw [ULift.down_natCast, ZMod.natCast_zmod_val]
  rw [hcv]

end LateralTheory.E.LocFormPf
