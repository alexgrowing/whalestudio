import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCochainEvEqOfNaturalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexDifferentialValuesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnityStatement

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC

namespace ClsSpec
variable {R : Type} [CommRing R]

theorem res_zero {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 := map_zero _
theorem res_add {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (a b : Sec F U) :
    Sec.res g (a + b) = Sec.res g a + Sec.res g b := map_add _ _ _
theorem res_sub {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (a b : Sec F U) :
    Sec.res g (a - b) = Sec.res g a - Sec.res g b := map_sub _ _ _
theorem smap_zero {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} : Sec.map φ (0 : Sec F U) = 0 := map_zero _
theorem smap_add {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a + b) = Sec.map φ a + Sec.map φ b := map_add _ _ _
theorem smap_sub {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a - b) = Sec.map φ a - Sec.map φ b := map_sub _ _ _
theorem smap_nsmul {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (k : ℕ) (a : Sec F U) :
    Sec.map φ (k • a) = k • Sec.map φ a := map_nsmul _ _ _

theorem res_comp {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (a : Sec F U) :
    Sec.res k (Sec.res g a) = Sec.res (k ≫ g) a := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem res_id {F : Shv R} {U : Scheme.{0}} (a : Sec F U) : Sec.res (𝟙 U) a = a := by
  simp [Sec.res]

theorem res_map {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.res g (Sec.map φ a) = Sec.map φ (Sec.res g a) :=
  (congrArg (fun f => f.hom a) (φ.hom.naturality g.op)).symm

theorem map_comp {F G K : Shv R} (φ : F ⟶ G) (ψ : G ⟶ K) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map ψ (Sec.map φ a) = Sec.map (φ ≫ ψ) a := rfl

theorem map_zero_hom {F G : Shv R} {U : Scheme.{0}} (a : Sec F U) : Sec.map (0 : F ⟶ G) a = 0 := rfl

theorem d_d (I : Cx R) (i j k : ℤ) {U : Scheme.{0}} (a : Sec (I.X i) U) : Sec.map (I.d j k) (Sec.map (I.d i j) a) = 0 := by
  rw [map_comp, I.d_comp_d, map_zero_hom]

theorem d_resι (F : Shv R) {U : Scheme.{0}} (a : Sec F U) : Sec.map ((res R F).d 0 1) (Sec.map (resι R F) a) = 0 := by
  have h : resι R F ≫ (res R F).d 0 1 = 0 := by
    have h₁ : (resAug F).f 0 ≫ (res R F).d 0 1 = 0 := by
      rw [(resAug F).comm 0 1]
      have : (sgl F).d 0 1 = 0 := rfl
      rw [this, zero_comp]
    change (sglι F ≫ (resAug F).f 0) ≫ _ = 0
    rw [Category.assoc, h₁, comp_zero]
  rw [map_comp, h, map_zero_hom]

theorem sx_res_comp {E : Spc} {p : ℕ} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sx E p U) :
    (x.res g).res k = x.res (k ≫ g) := by
  simp [Sx.res]

theorem sx_res_id {E : Spc} {p : ℕ} {U : Scheme.{0}} (x : Sx E p U) : x.res (𝟙 U) = x := by
  simp [Sx.res]

theorem face_res {E : Spc} {p : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E (p + 1) U) (i : Fin (p + 2)) :
    (x.face i).res g = (x.res g).face i :=
  (congrArg (fun f => f x) ((E.δ i).naturality g.op)).symm

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P) (i : ∀ V g, P V g → Q V g) :
    Loc U Q := GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 U P Q h i

theorem loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P) (i : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.1 U P Q h i

theorem loc_trans {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : Loc U (fun V g => Loc V fun W k => P W (k ≫ g))) : Loc U P := GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.2.1 U P h

theorem sep {F : Shv R} {U : Scheme.{0}} {a b : Sec F U} (h : Loc U fun _ g => Sec.res g a = Sec.res g b) : a = b :=
  (GlobalTheory.T.etaleSheafSections_ext_and_glue R F U).1 a b h

theorem glue_family (F : Shv R) {E : Spc} {p : ℕ} (Rel : ∀ U : Scheme.{0}, Sx E p U → Sec F U → Prop)
    (hex : ∀ (U : Scheme.{0}) (x : Sx E p U), Loc U fun V g => ∃ s, Rel V (x.res g) s)
    (hres : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U) (s : Sec F U), Rel U x s → Rel V (x.res g) (Sec.res g s))
    (huniq : ∀ (U : Scheme.{0}) (x : Sx E p U) (s s' : Sec F U), Rel U x s → Rel U x s' → s = s') :
    ∃ a : ∀ U : Scheme.{0}, Sx E p U → Sec F U,
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a U x) = a V (x.res g)) ∧
      ∀ (U : Scheme.{0}) (x : Sx E p U) (s : Sec F U), Rel U x s → a U x = s := by
  have key : ∀ (U : Scheme.{0}) (x : Sx E p U), ∃ a : Sec F U,
      ∀ (V : Scheme.{0}) (g : V ⟶ U) (s : Sec F V), Rel V (x.res g) s → Sec.res g a = s := by
    intro U x
    obtain ⟨S, hS, hP⟩ := hex U x
    choose s hs using hP
    obtain ⟨a, ha⟩ := (GlobalTheory.T.etaleSheafSections_ext_and_glue R F U).2 S hS s (fun V W g k hg => by
      refine huniq W (x.res (k ≫ g)) _ _ ?_ (hs _ _ _)
      rw [← sx_res_comp]
      exact hres _ _ _ _ _ (hs _ _ hg))
    refine ⟨a, fun V g s' hs' => sep ⟨S.pullback g, Scheme.etaleTopology.pullback_stable g hS, fun W k hk => ?_⟩⟩
    beta_reduce
    rw [res_comp, ha W (k ≫ g) hk]
    refine huniq W (x.res (k ≫ g)) _ _ (hs _ _ _) ?_
    rw [← sx_res_comp]
    exact hres _ _ _ _ _ hs'
  choose a ha using key
  refine ⟨a, fun V U g x => sep (loc_mono (hex V (x.res g)) ?_), fun U x s hs => ?_⟩
  · rintro W k ⟨s, hs⟩
    rw [ha V _ W k s hs, res_comp]
    exact ha U x W (k ≫ g) s (by rwa [← sx_res_comp])
  · rw [← res_id (a U x)]
    exact ha U x U (𝟙 U) s (by rwa [sx_res_id])

theorem exists_single {E : Spc} {I : Cx R} {n : ℤ} (p₀ : ℕ) (s₀ : ℤ) (h₀ : -(p₀ : ℤ) + n = s₀)
    (b : ∀ U : Scheme.{0}, Sx E p₀ U → Sec (I.X s₀) U)
    (hb : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p₀ U), Sec.res g (b U x) = b V (x.res g)) :
    ∃ α : Cochain ((chains R).obj E) I n, (∀ U x, ev α p₀ s₀ h₀ U x = b U x) ∧
      ∀ p s h U x, p ≠ p₀ → ev α p s h U x = 0 := by
  subst h₀
  obtain ⟨α, hα⟩ := GlobalTheory.T.exists_cochain_ev_eq_of_natural' R (E := E) (I := I) (n := n)
    (fun p s h U x => if hp : p = p₀ then (by subst hp; subst h; exact b U x) else 0) (by
      intro p s h V U g x
      by_cases hp : p = p₀
      · subst hp; subst h
        simp only [dif_pos]
        exact hb V U g x
      · simp only [dif_neg hp]
        exact map_zero _)
  refine ⟨α, fun U x => ?_, fun p s h U x hp => ?_⟩
  · rw [hα]; simp only [dif_pos]
  · rw [hα]; simp only [dif_neg hp]

theorem ev_add {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n) (p s h U x) :
    ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x := ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).1 α β p s h U x).1

theorem ev_zero {E : Spc} {I : Cx R} {n : ℤ} (p s h U x) :
    ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).1 0 0 p s h U x).2.2.1

theorem δ_eq_zero {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n)
    (h₀ : ∀ (U : Scheme.{0}) (x : Sx E 0 U), Sec.map (I.d n m) (ev α 0 n (by simp) U x) = 0)
    (h₁ : ∀ (U : Scheme.{0}) (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -(p : ℤ) + n = t) (x : Sx E (p + 1) U),
      Sec.map (I.d s t) (ev α (p + 1) s hs U x) +
        m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t ht U (x.face i) = 0) : δ n m α = 0 := by
  refine (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.2.1 _ _ fun p t ht U x => ?_
  rw [ev_zero]
  cases p with
  | zero =>
    obtain rfl : m = t := by simpa using ht
    exact ((GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values R hm α U).1 x).trans (h₀ U x)
  | succ p => exact ((GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values R hm α U).2 p _ t rfl ht x).trans (h₁ U p _ t rfl _ x)

theorem res_twGen {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := by
  have h := congrArg (fun f => f.hom (Submodule.Quotient.mk (Finsupp.single ζ 1)))
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op)
  refine h.symm.trans ?_
  change ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom
    (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map g.appTop.hom) (Finsupp.single ζ 1))) = _
  rw [Finsupp.mapDomain_single]
  rfl

theorem res_resGen {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (resGen i ζ) = resGen i (ζ.map g.appTop.hom) := by
  unfold resGen
  rw [res_map, res_twGen]

theorem d_resGen {q : ℕ} (i : ℤ) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) :
    Sec.map ((res _ (tw q i)).d 0 1) (resGen i ζ) = 0 := d_resι _ _

theorem resGen_zero_pow {q : ℕ} {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    resGen 0 ξ = resGen 0 ζ := by
  unfold resGen twGen
  congr 2
  refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨ζ, ξ, a, h, ?_⟩)
  rw [zpow_zero]
  rfl

theorem resGen_zero_eq {q : ℕ} [NeZero q] {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) : resGen 0 ξ = resGen 0 ζ := by
  refine sep (loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).2.1 ζ ξ) ?_)
  rintro V g ⟨a, ha⟩
  rw [res_resGen, res_resGen]
  exact resGen_zero_pow _ _ a ha

theorem exists_cocycle_zero {E : Spc} {I : Cx R} (b : ∀ U : Scheme.{0}, Sx E 0 U → Sec (I.X 0) U)
    (hb : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 0 U), Sec.res g (b U x) = b V (x.res g))
    (hd : ∀ U x, Sec.map (I.d 0 1) (b U x) = 0) (hf : ∀ U (y : Sx E 1 U), b U (y.face 0) = b U (y.face 1)) :
    ∃ α : Cocycle ((chains R).obj E) I 0, ∀ U x, ev α.1 0 0 (by simp) U x = b U x := by
  obtain ⟨α, h₁, h₂⟩ := exists_single (I := I) (n := 0) 0 0 (by simp) b hb
  refine ⟨Cocycle.mk α 1 rfl (δ_eq_zero (m := 1) rfl α (fun U x => ?_) (fun U p s t hs ht x => ?_)), h₁⟩
  · rw [h₁, hd]
  · rw [h₂ _ _ _ _ _ (Nat.succ_ne_zero p), smap_zero, zero_add]
    cases p with
    | zero =>
      obtain rfl : t = 0 := by omega
      rw [Fin.sum_univ_two, h₁, h₁, hf]
      simp
    | succ p =>
      rw [Finset.sum_eq_zero fun i _ => by rw [h₂ _ _ _ _ _ (Nat.succ_ne_zero p), smul_zero], smul_zero]

theorem exists_one (q : ℕ) (E : Spc) (hE : Inv q E) : ∃ α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0,
    ∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · refine ⟨0, fun U x ζ => ?_⟩
    have hU : IsEmpty U := by
      by_contra h
      have : Nonempty U := not_isEmpty_iff.1 h
      have : Nonempty (⊤ : U.Opens) := ⟨⟨this.some, trivial⟩⟩
      exact not_isUnit_zero (Nat.cast_zero (R := Γ(U, ⊤)) ▸ ζ.2.1)
    exact sep (GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.2.2.2 U _)
  have : NeZero q := ⟨hq.ne'⟩
  have hloc : ∀ (U : Scheme.{0}) (_ : Sx E 0 U), Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤)) :=
    fun U x => (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).1 (hE U ⟨x⟩)
  obtain ⟨a, ha, hs⟩ := glue_family ((res _ (tw q 0)).X 0) (E := E) (p := 0) (fun U _ s => ∃ ζ, s = resGen 0 ζ)
    (fun U x => loc_mono (hloc U x) fun V g ⟨ζ⟩ => ⟨_, ζ, rfl⟩)
    (by rintro V U g x s ⟨ζ, rfl⟩; exact ⟨_, res_resGen 0 g ζ⟩)
    (by rintro U x s s' ⟨ζ, rfl⟩ ⟨ξ, rfl⟩; exact resGen_zero_eq _ _)
  obtain ⟨α, hα⟩ := exists_cocycle_zero a ha (fun U x => sep (loc_mono (hloc U x) fun V g ⟨ζ⟩ => by
      rw [res_map, ha, hs V _ _ ⟨ζ, rfl⟩, d_resGen, res_zero]))
    (fun U y => sep (loc_mono (hloc U (y.face 0)) fun V g ⟨ζ⟩ => by
      rw [ha, ha, hs V _ _ ⟨ζ, rfl⟩, hs V _ _ ⟨ζ, rfl⟩]))
  exact ⟨α, fun U x ζ => (hα U x).trans (hs U x _ ⟨ζ, rfl⟩)⟩

theorem exists_root {q : ℕ} (i : ℤ) {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) :
    ∃ α : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q i)) 0,
      ∀ (U : Scheme.{0}) (x : U ⟶ X), ev α.1 0 0 (by simp) U x = Sec.res x (resGen i ζ) :=
  exists_cocycle_zero (E := sch.obj X) (fun U (x : U ⟶ X) => Sec.res x (resGen i ζ)) (fun V U g x => res_comp g x _)
    (fun U (x : U ⟶ X) => by rw [← res_map, d_resGen, res_zero]) (fun U y => rfl)

abbrev umap {V U : Scheme.{0}} (g : V ⟶ U) : (Γ(U, ⊤))ˣ →* (Γ(V, ⊤))ˣ := Units.map g.appTop.hom.toMonoidHom

theorem umap_comp {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) : umap (k ≫ g) u = umap k (umap g u) := by
  ext
  change (k ≫ g).appTop.hom _ = _
  rw [Scheme.Hom.comp_appTop]
  rfl

theorem unit_res {q : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (h : IsUnit (q : Γ(U, ⊤))) : IsUnit (q : Γ(V, ⊤)) := by
  simpa using h.map g.appTop.hom

section Kum
variable {q : ℕ} {t : ∀ U : Scheme.{0}, (Γ(U, ⊤))ˣ → Sec ((res _ (tw q 1)).X 0) U}

theorem kum_pow (ht : IsKum q t) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (v : (Γ(U, ⊤))ˣ) (k : ℕ) :
    ∀ w : (Γ(U, ⊤))ˣ, (w : Γ(U, ⊤)) = ζ.1 ^ k * v → t U w = t U v + k • resGen 1 ζ := by
  induction k with
  | zero =>
    intro w hw
    rw [pow_zero, one_mul] at hw
    rw [Units.ext hw, zero_smul, add_zero]
  | succ k ih =>
    intro w hw
    have hw' : (w : Γ(U, ⊤)) = ζ.1 * (ζ.1 ^ k * v) := by rw [hw]; ring
    obtain ⟨z, hz⟩ : IsUnit (ζ.1 ^ k * v) := isUnit_of_mul_isUnit_right (hw' ▸ w.isUnit)
    rw [ht.2 U ζ z w (by rw [hw', hz]), ih z hz, succ_nsmul, add_assoc]

theorem kum_loc [NeZero q] (ht : IsKum q t) {U : Scheme.{0}} (hU : IsUnit (q : Γ(U, ⊤))) {v w : (Γ(U, ⊤))ˣ} (h : v ^ q = w ^ q) :
    Loc U fun V g => ∃ r : Sec ((res _ (tw q 1)).X 0) V, Sec.map ((res _ (tw q 1)).d 0 1) r = 0 ∧
      ∀ z : (Γ(V, ⊤))ˣ, t V (umap g w * z) = t V (umap g v * z) + r := by
  refine loc_trans (loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).1 hU) fun V g ⟨ζ⟩ => ?_)
  have hx : ((umap g (w * v⁻¹) : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) ^ q = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, mul_pow, inv_pow, h, mul_inv_cancel, map_one, Units.val_one]
  refine loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).2.2.1 ζ _ hx) ?_
  rintro W k ⟨a, ha⟩
  refine ⟨a • resGen 1 (ζ.map k.appTop.hom), by rw [smap_nsmul, d_resGen, smul_zero], fun z => ?_⟩
  refine kum_pow ht _ _ a _ ?_
  have h₁ : ((umap (k ≫ g) (w * v⁻¹) : (Γ(W, ⊤))ˣ) : Γ(W, ⊤)) = (ζ.map k.appTop.hom).1 ^ a := by
    rw [umap_comp]; exact ha
  rw [← h₁, ← Units.val_mul, ← mul_assoc, ← map_mul, inv_mul_cancel_right]

theorem kum_d_eq [NeZero q] (ht : IsKum q t) {U : Scheme.{0}} (hU : IsUnit (q : Γ(U, ⊤))) {v w : (Γ(U, ⊤))ˣ} (h : v ^ q = w ^ q) :
    Sec.map ((res _ (tw q 1)).d 0 1) (t U v) = Sec.map ((res _ (tw q 1)).d 0 1) (t U w) := by
  refine sep (loc_mono (kum_loc ht hU h) ?_)
  rintro V g ⟨r, hr, hz⟩
  have := hz 1
  rw [mul_one, mul_one] at this
  rw [res_map, res_map, ht.1 V U g v hU, ht.1 V U g w hU]
  change Sec.map _ (t V (umap g v)) = Sec.map _ (t V (umap g w))
  rw [this, smap_add, hr, add_zero]

theorem kum_sub_eq [NeZero q] (ht : IsKum q t) {U : Scheme.{0}} (hU : IsUnit (q : Γ(U, ⊤))) {v w : (Γ(U, ⊤))ˣ}
    (h : v ^ q = w ^ q) (z : (Γ(U, ⊤))ˣ) : t U v - t U (v * z) = t U w - t U (w * z) := by
  refine sep (loc_mono (kum_loc ht hU h) ?_)
  rintro V g ⟨r, -, hz⟩
  have := hz 1
  rw [mul_one, mul_one] at this
  rw [res_sub, res_sub, ht.1 V U g v hU, ht.1 V U g w hU, ht.1 V U g _ hU, ht.1 V U g _ hU]
  change t V (umap g v) - t V (umap g (v * z)) = t V (umap g w) - t V (umap g (w * z))
  rw [map_mul, map_mul, this, hz]
  abel

theorem kum_two_eq [NeZero q] (ht : IsKum q t) {U : Scheme.{0}} (hU : IsUnit (q : Γ(U, ⊤))) {v w v' w' : (Γ(U, ⊤))ˣ}
    (h : v ^ q = v' ^ q) (h' : w ^ q = w' ^ q) : t U v + t U w - t U (v * w) = t U v' + t U w' - t U (v' * w') := by
  have h₁ := kum_sub_eq ht hU h w
  have h₂ := kum_sub_eq ht hU h' v'
  rw [mul_comm w, mul_comm w'] at h₂
  calc t U v + t U w - t U (v * w) = (t U v - t U (v * w)) + t U w := by abel
    _ = t U v' + (t U w - t U (v' * w)) := by rw [h₁]; abel
    _ = _ := by rw [h₂]; abel

theorem root_loc [NeZero q] {U : Scheme.{0}} (hU : IsUnit (q : Γ(U, ⊤))) (u : (Γ(U, ⊤))ˣ) :
    Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = umap g u := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).2.2.2 hU u

theorem exists_d_family [NeZero q] (ht : IsKum q t) {E : Spc} {p : ℕ}
    (hq : ∀ (U : Scheme.{0}) (_ : Sx E p U), IsUnit (q : Γ(U, ⊤))) (u : ∀ U : Scheme.{0}, Sx E p U → (Γ(U, ⊤))ˣ)
    (hu : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), u V (x.res g) = umap g (u U x)) :
    ∃ a : ∀ U : Scheme.{0}, Sx E p U → Sec ((res _ (tw q 1)).X 1) U,
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a U x) = a V (x.res g)) ∧
      (∀ U x, Sec.map ((res _ (tw q 1)).d 1 2) (a U x) = 0) ∧
      ∀ (U : Scheme.{0}) (x : Sx E p U) (v : (Γ(U, ⊤))ˣ), v ^ q = u U x → a U x = Sec.map ((res _ (tw q 1)).d 0 1) (t U v) := by
  obtain ⟨a, ha, hs⟩ := glue_family ((res _ (tw q 1)).X 1) (E := E) (p := p)
    (fun U x s => ∃ v, v ^ q = u U x ∧ s = Sec.map ((res _ (tw q 1)).d 0 1) (t U v))
    (fun U x => loc_mono (root_loc (hq U x) (u U x)) fun V g ⟨v, hv⟩ => ⟨_, v, hv.trans (hu V U g x).symm, rfl⟩)
    (by
      rintro V U g x s ⟨v, hv, rfl⟩
      exact ⟨umap g v, by rw [← map_pow, hv, hu], by rw [res_map, ht.1 V U g v (hq U x)]⟩)
    (by rintro U x s s' ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩; exact kum_d_eq ht (hq U x) (hv.trans hw.symm))
  refine ⟨a, ha, fun U x => sep (loc_mono (root_loc (hq U x) (u U x)) fun V g ⟨v, hv⟩ => ?_),
    fun U x v hv => hs U x _ ⟨v, hv, rfl⟩⟩
  rw [res_map, ha, hs V _ _ ⟨v, hv.trans (hu V U g x).symm, rfl⟩, d_d, res_zero]

theorem exists_two_family [NeZero q] (ht : IsKum q t) {E : Spc} {p : ℕ}
    (hq : ∀ (U : Scheme.{0}) (_ : Sx E p U), IsUnit (q : Γ(U, ⊤))) (u u' : ∀ U : Scheme.{0}, Sx E p U → (Γ(U, ⊤))ˣ)
    (hu : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), u V (x.res g) = umap g (u U x))
    (hu' : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), u' V (x.res g) = umap g (u' U x)) :
    ∃ a : ∀ U : Scheme.{0}, Sx E p U → Sec ((res _ (tw q 1)).X 0) U,
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a U x) = a V (x.res g)) ∧
      ∀ (U : Scheme.{0}) (x : Sx E p U) (v w : (Γ(U, ⊤))ˣ), v ^ q = u U x → w ^ q = u' U x →
        a U x = t U v + t U w - t U (v * w) := by
  obtain ⟨a, ha, hs⟩ := glue_family ((res _ (tw q 1)).X 0) (E := E) (p := p)
    (fun U x s => ∃ v w, v ^ q = u U x ∧ w ^ q = u' U x ∧ s = t U v + t U w - t U (v * w))
    (fun U x => loc_mono (loc_and (root_loc (hq U x) (u U x)) (root_loc (hq U x) (u' U x))) fun V g ⟨⟨v, hv⟩, w, hw⟩ =>
      ⟨_, v, w, hv.trans (hu V U g x).symm, hw.trans (hu' V U g x).symm, rfl⟩)
    (by
      rintro V U g x s ⟨v, w, hv, hw, rfl⟩
      refine ⟨umap g v, umap g w, by rw [← map_pow, hv, hu], by rw [← map_pow, hw, hu'], ?_⟩
      rw [res_sub, res_add, ht.1 V U g v (hq U x), ht.1 V U g w (hq U x), ht.1 V U g _ (hq U x), ← map_mul])
    (by
      rintro U x s s' ⟨v, w, hv, hw, rfl⟩ ⟨v', w', hv', hw', rfl⟩
      exact kum_two_eq ht (hq U x) (hv.trans hv'.symm) (hw.trans hw'.symm))
  exact ⟨a, ha, fun U x v w hv hw => hs U x _ ⟨v, w, hv, hw, rfl⟩⟩

theorem exists_kum [NeZero q] (ht : IsKum q t) {X : Scheme.{0}} (hX : IsUnit (q : Γ(X, ⊤))) (u : (Γ(X, ⊤))ˣ) :
    ∃ γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1,
    (∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0) ∧
    ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u →
      ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (t U v) := by
  obtain ⟨b, hb, hd, hv⟩ := exists_d_family ht (E := sch.obj X) (p := 0) (fun U (x : U ⟶ X) => unit_res x hX)
    (fun U (x : U ⟶ X) => umap x u) (fun V U g (x : U ⟶ X) => umap_comp g x u)
  obtain ⟨α, h₁, h₂⟩ := exists_single (I := res _ (tw q 1)) (n := 1) 0 1 (by simp) b hb
  refine ⟨Cocycle.mk α 2 rfl (δ_eq_zero (m := 2) rfl α (fun U x => ?_) (fun U p s t hs ht x => ?_)),
    fun U x => h₂ 1 0 _ U x one_ne_zero, fun U x v h => (h₁ U x).trans (hv U x v h)⟩
  · rw [h₁, hd]
  · rw [h₂ _ _ _ _ _ (Nat.succ_ne_zero p), smap_zero, zero_add]
    cases p with
    | zero =>
      obtain rfl : t = 1 := by omega
      have hf : b U (x.face 0) = b U (x.face 1) := rfl
      rw [Fin.sum_univ_two, h₁, h₁, hf]
      simp
    | succ p =>
      rw [Finset.sum_eq_zero fun i _ => by rw [h₂ _ _ _ _ _ (Nat.succ_ne_zero p), smul_zero], smul_zero]

end Kum

theorem face_face {E : Spc} {U : Scheme.{0}} {p : ℕ} (y : Sx E (p + 2) U) (i i' : Fin (p + 3)) (j j' : Fin (p + 2))
    (h : SimplexCategory.δ j ≫ SimplexCategory.δ i = SimplexCategory.δ j' ≫ SimplexCategory.δ i') :
    (y.face i).face j = (y.face i').face j' := by
  have : E.δ i ≫ E.δ j = E.δ i' ≫ E.δ j' := by
    simp only [SimplicialObject.δ, ← Functor.map_comp, ← op_comp, h]
  exact congrArg (fun f => f.app (op U) y) this

theorem sub_zero_one {E : Spc} {U : Scheme.{0}} (y : Sx E 2 U) (h : 0 + 1 ≤ 2) : y.sub 0 1 h = y.face 2 := by
  have : SimplexCategory.subinterval 0 1 h = SimplexCategory.δ 2 := by
    ext i; fin_cases i <;> rfl
  unfold Sx.sub
  rw [this]; rfl

theorem sub_one_one {E : Spc} {U : Scheme.{0}} (y : Sx E 2 U) (h : 1 + 1 ≤ 2) : y.sub 1 1 h = y.face 0 := by
  have : SimplexCategory.subinterval 1 1 h = SimplexCategory.δ 0 := by
    ext i; fin_cases i <;> rfl
  unfold Sx.sub
  rw [this]; rfl

theorem glMat_res {N : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (y : Sx (ofCat (glCat N)) 1 U) :
    glMat (y.res g) = Matrix.GeneralLinearGroup.map g.appTop.hom (glMat y) := rfl

theorem glMat_face {N : ℕ} {U : Scheme.{0}} (y : Sx (ofCat (glCat N)) 2 U) :
    glMat (y.face 1) = glMat (y.face 0) * glMat (y.face 2) :=
  (show ComposableArrows (SingleObj (GL (Fin N) Γ(U, ⊤))) 2 from y).map_comp
    (homOfLE (show (0 : Fin 3) ≤ 1 by decide)) (homOfLE (show (1 : Fin 3) ≤ 2 by decide))

theorem lineUnit_eq {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (x : Sx E 1 U) :
    lineUnit L x = Matrix.GeneralLinearGroup.det (glMat (x.map L)) := rfl

theorem map_res {E E' : Spc} (f : E ⟶ E') {p : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) :
    (x.res g).map f = (x.map f).res g :=
  congrArg (fun φ => φ x) ((f.app (op (SimplexCategory.mk p))).naturality g.op)

theorem map_face {E E' : Spc} (f : E ⟶ E') {p : ℕ} {U : Scheme.{0}} (x : Sx E (p + 1) U) (i : Fin (p + 2)) :
    (x.face i).map f = (x.map f).face i :=
  congrArg (fun φ => φ.app (op U) x) (f.naturality (SimplexCategory.δ i).op)

theorem lineUnit_res {E : Spc} (L : E ⟶ ofCat (glCat 1)) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E 1 U) :
    lineUnit L (x.res g) = umap g (lineUnit L x) := by
  rw [lineUnit_eq, lineUnit_eq, map_res, glMat_res]
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_unique]

theorem lineUnit_face {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (y : Sx E 2 U) :
    lineUnit L (y.face 1) = lineUnit L (y.face 2) * lineUnit L (y.face 0) := by
  rw [lineUnit_eq, lineUnit_eq, lineUnit_eq, map_face, map_face, map_face, glMat_face, map_mul, mul_comm]

theorem exists_etaleCocycle_firstChernClassTateTwist {q : ℕ} {t : ∀ U : Scheme.{0}, (Γ(U, ⊤))ˣ → Sec ((res _ (tw q 1)).X 0) U} [NeZero q] (ht : IsKum q t)
    {E : Spc} (hE : Inv q E) (L : E ⟶ ofCat (glCat 1)) :
    ∃ γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2,
    (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 2 (by simp) U x = 0) ∧
    (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      ev γ.1 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (t U v)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.face 2) →
      w ^ q = lineUnit L (x.face 0) →
      ev γ.1 2 0 (by simp) U x = t U v + t U w - t U (v * w) := by
  have hq₁ : ∀ (U : Scheme.{0}) (_ : Sx E 1 U), IsUnit (q : Γ(U, ⊤)) := fun U x => hE U ⟨x.face 0⟩
  have hq₂ : ∀ (U : Scheme.{0}) (_ : Sx E 2 U), IsUnit (q : Γ(U, ⊤)) := fun U x => hq₁ U (x.face 0)
  have hf : ∀ (i : Fin 3) (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 2 U),
      lineUnit L ((x.res g).face i) = umap g (lineUnit L (x.face i)) := fun i V U g x => by rw [← face_res, lineUnit_res]
  obtain ⟨b, hb, hd, hv⟩ := exists_d_family ht hq₁ (fun U x => lineUnit L x) (fun V U g x => lineUnit_res L g x)
  obtain ⟨e, he, hw⟩ := exists_two_family ht hq₂ (fun U x => lineUnit L (x.face 2)) (fun U x => lineUnit L (x.face 0))
    (hf 2) (hf 0)
  have h₂ : ∀ (U : Scheme.{0}) (y : Sx E 2 U),
      Sec.map ((res _ (tw q 1)).d 0 1) (e U y) = b U (y.face 0) - b U (y.face 1) + b U (y.face 2) := by
    intro U y
    refine sep (loc_mono (loc_and (root_loc (hq₂ U y) (lineUnit L (y.face 2))) (root_loc (hq₂ U y) (lineUnit L (y.face 0)))) ?_)
    rintro V g ⟨⟨v, h⟩, w, h'⟩
    rw [← hf] at h h'
    rw [res_map, res_add, res_sub, he, hb, hb, hb, face_res, face_res, face_res, hw V _ v w h h', hv V _ v h, hv V _ w h',
      hv V _ (v * w) (by rw [mul_pow, h, h', lineUnit_face]), smap_sub, smap_add]
    abel
  have h₃ : ∀ (U : Scheme.{0}) (y : Sx E 3 U),
      e U (y.face 0) - e U (y.face 1) + e U (y.face 2) - e U (y.face 3) = 0 := by
    intro U y
    have hU := hq₂ U (y.face 0)
    refine sep (loc_mono (loc_and (root_loc hU (lineUnit L ((y.face 3).face 2)))
      (loc_and (root_loc hU (lineUnit L ((y.face 0).face 2))) (root_loc hU (lineUnit L ((y.face 0).face 0))))) ?_)
    rintro V g ⟨⟨u, h⟩, ⟨v, h'⟩, w, h''⟩
    rw [← hf, face_res] at h h' h''
    rw [res_sub, res_add, res_sub, he, he, he, he, face_res, face_res, face_res, face_res, res_zero]
    generalize y.res g = z at h h' h'' ⊢
    have e₁ : (z.face 1).face 0 = (z.face 0).face 0 := face_face z _ _ _ _ (by decide)
    have e₂ : (z.face 1).face 2 = (z.face 3).face 1 := face_face z _ _ _ _ (by decide)
    have e₃ : (z.face 2).face 2 = (z.face 3).face 2 := face_face z _ _ _ _ (by decide)
    have e₄ : (z.face 2).face 0 = (z.face 0).face 1 := face_face z _ _ _ _ (by decide)
    have e₅ : (z.face 3).face 0 = (z.face 0).face 2 := face_face z _ _ _ _ (by decide)
    rw [hw V _ v w h' h'', hw V (z.face 1) (u * v) w (by rw [e₂, lineUnit_face, e₅, mul_pow, h, h']) (by rw [e₁, h'']),
      hw V (z.face 2) u (v * w) (by rw [e₃, h]) (by rw [e₄, lineUnit_face, mul_pow, h', h'']),
      hw V (z.face 3) u v h (by rw [e₅, h']), mul_assoc]
    abel
  obtain ⟨α, a₁, a₂⟩ := exists_single (I := res _ (tw q 1)) (n := 2) 1 1 (by simp) b hb
  obtain ⟨β, b₁, b₂⟩ := exists_single (I := res _ (tw q 1)) (n := 2) 2 0 (by simp) e he
  have c₀ : ∀ p s h U x, p ≠ 1 → p ≠ 2 → ev (α + β) p s h U x = 0 := fun p s h U x h₁ h₂ => by
    rw [ev_add, a₂ _ _ _ _ _ h₁, b₂ _ _ _ _ _ h₂, add_zero]
  have c₁ : ∀ h U x, ev (α + β) 1 1 h U x = b U x := fun h U x => by
    rw [ev_add, a₁, b₂ _ _ _ _ _ (by decide), add_zero]
  have c₂ : ∀ h U x, ev (α + β) 2 0 h U x = e U x := fun h U x => by
    rw [ev_add, b₁, a₂ _ _ _ _ _ (by decide), zero_add]
  have hs : (3 : ℤ).negOnePow = -1 := rfl
  refine ⟨Cocycle.mk (α + β) 3 rfl (δ_eq_zero (m := 3) rfl _ (fun U x => ?_) (fun U p s t hs' ht' x => ?_)),
    fun U x => c₀ 0 2 _ U x (by decide) (by decide), fun U x v h => (c₁ _ U x).trans (hv U x v h),
    fun U x v w h h' => (c₂ _ U x).trans (hw U x v w h h')⟩
  · rw [c₀ _ _ _ _ _ (by decide) (by decide), smap_zero]
  · match p with
    | 0 =>
      obtain rfl : s = 1 := by omega
      obtain rfl : t = 2 := by omega
      rw [Finset.sum_eq_zero fun i _ => by rw [c₀ _ _ _ _ _ (by decide) (by decide), smul_zero], smul_zero, add_zero]
      exact (congrArg _ (c₁ _ U x)).trans (hd U x)
    | 1 =>
      obtain rfl : s = 0 := by omega
      obtain rfl : t = 1 := by omega
      rw [Fin.sum_univ_three, c₁, c₁, c₁, c₂, h₂, hs]
      simp
      abel
    | 2 =>
      obtain rfl : t = 0 := by omega
      rw [Fin.sum_univ_four, c₂, c₂, c₂, c₂, c₀ _ _ _ _ _ (by decide) (by decide), smap_zero, zero_add]
      convert smul_zero _
      rw [← h₃ U x]
      norm_num
      abel
    | p + 3 =>
      rw [c₀ _ _ _ _ _ (by omega) (by omega), smap_zero, zero_add,
        Finset.sum_eq_zero fun i _ => by rw [c₀ _ _ _ _ _ (by omega) (by omega), smul_zero], smul_zero]

theorem kumT_cases (q : ℕ) : IsKum q (kumT q) ∨ kumT q = 0 := by
  by_cases h : ∃ t, IsKum q t
  · exact Or.inl (pick_spec h)
  · right
    unfold kumT pick
    rw [dif_neg h]

end ClsSpec

open ClsSpec

theorem one_spec (q : ℕ) (E : Spc) (hE : Inv q E) : ∃ α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0, CohomologyClass.mk α = one q E ∧
    ∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ := by
  obtain ⟨α, h⟩ := exists_one q E hE
  exact pick_spec (P := fun c : Ht q E 0 0 => ∃ α : Cocycle _ _ 0, CohomologyClass.mk α = c ∧
    ∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ) ⟨_, α, rfl, h⟩

theorem rootClass_spec {q : ℕ} (i : ℤ) {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) : ∃ α : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q i)) 0,
    CohomologyClass.mk α = rootClass i ζ ∧ ∀ (U : Scheme.{0}) (x : U ⟶ X), ev α.1 0 0 (by simp) U x = Sec.res x (resGen i ζ) := by
  obtain ⟨α, h⟩ := exists_root i ζ
  exact pick_spec (P := fun c : Ht q (sch.obj X) 0 i => ∃ α : Cocycle _ _ 0, CohomologyClass.mk α = c ∧
    ∀ (U : Scheme.{0}) (x : U ⟶ X), ev α.1 0 0 (by simp) U x = Sec.res x (resGen i ζ)) ⟨_, α, rfl, h⟩

theorem kum_spec (q : ℕ) [NeZero q] {X : Scheme.{0}} (hX : IsUnit (q : Γ(X, ⊤))) (u : (Γ(X, ⊤))ˣ) :
    ∃ γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1, CohomologyClass.mk γ = kum q u ∧
    (∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0) ∧
    ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u →
      ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v) := by
  refine pick_spec (P := fun c : Ht q (sch.obj X) 1 1 => ∃ γ : Cocycle _ _ 1, CohomologyClass.mk γ = c ∧
    (∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0) ∧
    ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u →
      ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ?_
  rcases kumT_cases q with h | h
  · obtain ⟨γ, hγ⟩ := exists_kum h hX u
    exact ⟨_, γ, rfl, hγ⟩
  · refine ⟨_, 0, rfl, fun U x => ev_zero (E := sch.obj X) _ _ _ _ _, fun U x v _ => (ev_zero (E := sch.obj X) _ _ _ _ _).trans ?_⟩
    rw [h]
    exact (smap_zero _).symm

theorem firstChernClassTateTwist_cocycle_representative (q : ℕ) [NeZero q] {E : Spc} (hE : Inv q E) (L : E ⟶ ofCat (glCat 1)) :
    ∃ γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, CohomologyClass.mk γ = c1 q L ∧
    (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 2 (by simp) U x = 0) ∧
    (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      ev γ.1 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
      w ^ q = lineUnit L (x.sub 1 1 (by omega)) →
      ev γ.1 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w) := by
  refine pick_spec (P := fun c : Ht q E 2 1 => ∃ γ : Cocycle _ _ 2, CohomologyClass.mk γ = c ∧
    (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 2 (by simp) U x = 0) ∧
    (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      ev γ.1 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
      w ^ q = lineUnit L (x.sub 1 1 (by omega)) →
      ev γ.1 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)) ?_
  rcases kumT_cases q with h | h
  · obtain ⟨γ, h₀, h₁, h₂⟩ := exists_etaleCocycle_firstChernClassTateTwist h hE L
    exact ⟨_, γ, rfl, h₀, h₁, fun U x v w hv hw => h₂ U x v w (by rw [hv, sub_zero_one]) (by rw [hw, sub_one_one])⟩
  · refine ⟨_, 0, rfl, fun U x => ev_zero _ _ _ _ _, fun U x v _ => (ev_zero _ _ _ _ _).trans ?_,
      fun U x v w _ _ => (ev_zero _ _ _ _ _).trans ?_⟩
    · rw [h]
      exact (smap_zero _).symm
    · rw [h]
      simp

end GlobalTheory.EtC

end
