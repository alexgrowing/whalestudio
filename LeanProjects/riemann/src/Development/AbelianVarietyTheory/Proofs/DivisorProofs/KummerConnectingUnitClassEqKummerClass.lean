import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonSecOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerClassOfUnitCocycleNaturalAdditiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsGlueOfLocallyUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleLocalRootOfUnitOfKummerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerSplittingDifferenceMulRootOfUnityStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.KumUnit
open GlobalTheory.EtC.CupSpec
variable {R : Type} [CommRing R]

theorem sec_eq_zero_of_isZero {F : Shv R} (h : IsZero F) {U : Scheme.{0}} (x : Sec F U) : x = 0 := by
  have e : (𝟙 F) = 0 := h.eq_of_src _ _
  have h1 : Sec.map (𝟙 F) x = Sec.map (0 : F ⟶ F) x := by rw [e]
  exact h1.trans rfl

theorem face_sch {X U : Scheme.{0}} {p : ℕ} (x : Sx (sch.obj X) (p + 1) U) (i : Fin (p + 2)) : x.face i = x := rfl

theorem isZero_res_neg (F : Shv R) (n : ℤ) (hn : n < 0) : IsZero ((res R F).X n) := by
  have : (res R F).IsStrictlyGE 0 := inferInstanceAs ((injectiveResolution F).cochainComplex.IsStrictlyGE 0)
  exact CochainComplex.isZero_of_isStrictlyGE _ 0 _ hn

theorem ev_comp_ofHom {E : Spc} {I J : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (m : I ⟶ J) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
  rw [ev_def, ev_def, Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  rfl

theorem ev_zero_comp {E : Spc} {I J : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I 0) (w : Cochain I J n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (α.comp w (zero_add n)) p s h U x = Sec.map (w.v (-(p : ℤ)) s (by omega)) (ev α p (-(p : ℤ)) (by omega) U x) := by
  rw [ev_def, ev_def, Cochain.zero_cochain_comp_v]
  rfl

theorem resι_d (F : Shv R) : resι R F ≫ (res R F).d 0 1 = 0 := by
  have h := (injectiveResolution F).ι'.comm 0 1
  have h2 : ((singleFunctor (Shv R) 0).obj F).d 0 1 = 0 := by simp
  rw [h2, zero_comp] at h
  unfold resι
  exact (Category.assoc _ _ _).trans ((congrArg _ h).trans comp_zero)

theorem exists_etaleCochain_constant_zeroSimplices {X : Scheme.{0}} {I : Cx R} {n : ℤ} (e : ∀ U : Scheme.{0}, (U ⟶ X) → Sec (I.X n) U)
    (he : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : U ⟶ X), Sec.res g (e U x) = e V (g ≫ x)) :
    ∃ α : Cochain ((chains R).obj (sch.obj X)) I n, (∀ (U : Scheme.{0}) (x : U ⟶ X), ev α 0 n (by simp) U x = e U x) ∧
      ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (x : Sx (sch.obj X) (p + 1) U), ev α (p + 1) s h U x = 0 := by
  obtain ⟨α, hα⟩ := ev_exists (R := R) (E := sch.obj X) (I := I) (n := n)
    (fun p s h U x => if hp : p = 0 then Sec.map (eqToHom (congrArg I.X (by omega : n = s))) (e U x) else 0)
    (by
      intro p s h V U g x
      by_cases hp : p = 0
      · subst hp
        simp only [dif_pos]
        rw [map_res]
        exact congrArg _ (he V U g x)
      · simp only [hp, dif_neg, not_false_eq_true]
        exact map_zero _)
  refine ⟨α, fun U x => ?_, fun p s h U x => ?_⟩
  · refine (hα 0 n _ U x).trans ?_
    simp only [dif_pos, eqToHom_refl]
    rfl
  · refine (hα (p + 1) s h U x).trans ?_
    simp

theorem etaleCochainEval_delta_zeroSimplex {X : Scheme.{0}} {I : Cx R} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj (sch.obj X)) I n)
    (U : Scheme.{0}) (x : U ⟶ X) :
    ev (δ n m α) 0 m (by simp) U x = Sec.map (I.d n m) (ev α 0 n (by simp) U x) :=
  ev_δ_zero hm α U n m (by simp) (by simp) x

theorem etaleCochainEval_delta_succ_of_vanishing {X : Scheme.{0}} {I : Cx R} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj (sch.obj X)) I n)
    (hz : ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (x : Sx (sch.obj X) (p + 1) U), ev α (p + 1) s h U x = 0)
    (p : ℕ) (t : ℤ) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (U : Scheme.{0}) (x : Sx (sch.obj X) (p + 1) U) :
    ev (δ n m α) (p + 1) t ht U x = 0 := by
  rw [ev_δ_succ hm α U p _ t rfl ht x, hz]
  simp only [Sec.map, map_zero, zero_add]
  cases p with
  | zero => simp [Fin.sum_univ_two, face_sch]
  | succ p => simp [hz]

instance res_injective (F : Shv R) (n : ℤ) : Injective ((res R F).X n) :=
  inferInstanceAs (Injective ((injectiveResolution F).cochainComplex.X n))

theorem res_comp {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res h (Sec.res g y) = Sec.res (h ≫ g) y := by
  simp [Sec.res]

theorem res_id {F : Shv R} {U : Scheme.{0}} (y : Sec F U) : Sec.res (𝟙 U) y = y := by
  simp [Sec.res]

theorem res_sub {F : Shv R} {V U : Scheme.{0}} (h : V ⟶ U) (a b : Sec F U) : Sec.res h (a - b) = Sec.res h a - Sec.res h b :=
  map_sub _ a b

theorem map_sub' {F G : Shv R} (f : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) : Sec.map f (a - b) = Sec.map f a - Sec.map f b :=
  map_sub _ a b

theorem ev_zero_comp0 {E : Spc} {I J : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I 0) (w : Cochain I J n)
    (U : Scheme.{0}) (x : Sx E 0 U) :
    ev (α.comp w (zero_add n)) 0 n (by simp) U x = Sec.map (w.v 0 n (zero_add n)) (ev α 0 0 (by simp) U x) :=
  ev_zero_comp α w 0 n _ U x

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P) (hPQ : ∀ V g, P V g → Q V g) :
    Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem sec_eq_of_loc {F : Shv R} {U : Scheme.{0}} (s t : Sec F U) (h : Loc U fun V g => Sec.res g s = Sec.res g t) :
    s = t := by
  obtain ⟨S, hS, hP⟩ := h
  exact Sheaf.isSeparated F U S hS s t (fun V g hg => hP V g hg)

theorem unitSec_res {V U : Scheme.{0}} (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Sec.res g (unitSec u) = unitSec (Units.map g.appTop.hom.toMonoidHom u) := by
  have h := ConcreteCategory.congr_hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).naturality g.op)
    (ULift.up (Additive.ofMul u))
  exact h.symm.trans rfl

theorem unitSec_pow {U : Scheme.{0}} (v : (Γ(U, ⊤))ˣ) (n : ℕ) : unitSec (v ^ n) = n • unitSec v :=
  map_nsmul ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)).hom n (ULift.up (Additive.ofMul v))

theorem map_zsmul_id {F : Shv ℤ} {U : Scheme.{0}} (n : ℤ) (b : Sec F U) : Sec.map (n • 𝟙 F) b = n • b := rfl

theorem units_map_comp {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Units.map (h ≫ g).appTop.hom.toMonoidHom u =
      Units.map h.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom u) := by
  ext
  simp [Scheme.Hom.comp_appTop]
  rfl

theorem isUnit_q_res {V U : Scheme.{0}} (g : V ⟶ U) {q : ℕ} (hq : IsUnit (q : Γ(U, ⊤))) : IsUnit (q : Γ(V, ⊤)) := by
  simpa using hq.map g.appTop.hom

abbrev Tz (q : ℕ) : Shv ℤ := (restr (Int.castRingHom (ZMod q))).obj (tw q 1)

abbrev ρz (q : ℕ) : SemiMap (res (ZMod q) (tw q 1)) (res ℤ (Tz q)) := restrMap (Int.castRingHom (ZMod q)) (tw q 1)

theorem pi_unitSec {q : ℕ} (κ : Tz q ⟶ Gm) (h0 : κ ≫ ((q : ℤ) • 𝟙 Gm) = 0)
    (h5 : ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map (cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0) (U := U)))
    {X : Scheme.{0}} (u : (Γ(X, ⊤))ˣ) (c : Sec (cokernel κ) X) (hq : IsUnit (q : Γ(X, ⊤)))
    (hc : Sec.map (cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0) c = unitSec u) {V : Scheme.{0}} (y : V ⟶ X) (v : (Γ(V, ⊤))ˣ)
    (hv : v ^ q = Units.map y.appTop.hom.toMonoidHom u) : Sec.map (cokernel.π κ) (unitSec v) = Sec.res y c := by
  apply (h5 V (isUnit_q_res y hq)).1
  have e1 : Sec.map (cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0) (Sec.map (cokernel.π κ) (unitSec v)) =
      Sec.map (cokernel.π κ ≫ cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0) (unitSec v) := rfl
  rw [e1, cokernel.π_desc, map_zsmul_id, ← map_res, hc, unitSec_res, ← hv, unitSec_pow, natCast_zsmul]

theorem glue_sections : ∀ {R : Type} [CommRing R] (F : Shv R) (X : Scheme.{0}) (A : ∀ U : Scheme.{0}, (U ⟶ X) → Sec F U → Prop),
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : U ⟶ X) (s : Sec F U), A U x s → A V (g ≫ x) (Sec.res g s)) →
    (∀ (U : Scheme.{0}) (x : U ⟶ X) (s t : Sec F U), A U x s → A U x t → s = t) →
    (∀ (U : Scheme.{0}) (x : U ⟶ X), Loc U fun V g => ∃ s, A V (g ≫ x) s) →
    ∃ e : ∀ U : Scheme.{0}, (U ⟶ X) → Sec F U, (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : U ⟶ X), Sec.res g (e U x) = e V (g ≫ x)) ∧
      ∀ (U : Scheme.{0}) (x : U ⟶ X) (s : Sec F U), A U x s → e U x = s := GlobalTheory.T.etaleSheafSections_glue_of_locally_unique

theorem roots_loc : ∀ (q : ℕ) [NeZero q],
    (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Loc U fun V g => ∃ c : Sec Gm V, Sec.map ((q : ℤ) • 𝟙 Gm) c = Sec.res g b) →
    ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ,
      Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u := GlobalTheory.T.exists_etaleLocal_root_of_unit_of_kummer

theorem D_inv : ∀ (q : ℕ) [NeZero q] (κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm),
    (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 →
      Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u) →
    ∀ φ : Gm ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 0,
      κ ≫ φ = resι ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) →
    ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ (v ω : (Γ(U, ⊤))ˣ), ω ^ q = 1 →
      Sec.map φ (unitSec (ω * v)) - (restrMap (Int.castRingHom (ZMod q)) (tw q 1)).app U 0 (kumT q U (ω * v)) =
        Sec.map φ (unitSec v) - (restrMap (Int.castRingHom (ZMod q)) (tw q 1)).app U 0 (kumT q U v) := GlobalTheory.T.kummerSplittingDifference_mul_rootOfUnity
theorem glue_family : ∀ (q : ℕ) [NeZero q] (κ : Tz q ⟶ Gm) (h0 : κ ≫ ((q : ℤ) • 𝟙 Gm) = 0),
    (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 →
      Sec.map κ (show Sec (Tz q) U from twGen 1 ζ) = unitSec u) →
    (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U,
      Loc U fun V g => ∃ c : Sec Gm V, Sec.map ((q : ℤ) • 𝟙 Gm) c = Sec.res g b) →
    (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map (cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0) (U := U))) →
    ∀ (φ : Gm ⟶ (res ℤ (Tz q)).X 0) (ψ : cokernel κ ⟶ (res ℤ (Tz q)).X 1),
      κ ≫ φ = resι ℤ (Tz q) → cokernel.π κ ≫ ψ = φ ≫ (res ℤ (Tz q)).d 0 1 →
    ∀ (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ) (c : Sec (cokernel κ) X), IsUnit (q : Γ(X, ⊤)) →
      Sec.map (cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0) c = unitSec u →
    ∀ g : ∀ U : Scheme.{0}, (U ⟶ X) → Sec ((res ℤ (Tz q)).X 1) U,
      (∀ (V U : Scheme.{0}) (h : V ⟶ U) (x : U ⟶ X), Sec.res h (g U x) = g V (h ≫ x)) →
      (∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u →
        g U x = Sec.map ((res ℤ (Tz q)).d 0 1) ((ρz q).app U 0 (kumT q U v))) →
    ∃ e : ∀ U : Scheme.{0}, (U ⟶ X) → Sec ((res ℤ (Tz q)).X 0) U,
      (∀ (V U : Scheme.{0}) (h : V ⟶ U) (x : U ⟶ X), Sec.res h (e U x) = e V (h ≫ x)) ∧
      ∀ (U : Scheme.{0}) (x : U ⟶ X), Sec.map ((res ℤ (Tz q)).d 0 1) (e U x) = Sec.res x (Sec.map ψ c) - g U x := by
  intro q _ κ h0 h2 h4 h5 φ ψ hφ hψ X u c hq hc g hgn hgk
  let D : ∀ U : Scheme.{0}, (Γ(U, ⊤))ˣ → Sec ((res ℤ (Tz q)).X 0) U :=
    fun U v => Sec.map φ (unitSec v) - (ρz q).app U 0 (kumT q U v)
  have hDres : ∀ (V U : Scheme.{0}) (h : V ⟶ U) (v : (Γ(U, ⊤))ˣ), IsUnit (q : Γ(U, ⊤)) →
      Sec.res h (D U v) = D V (Units.map h.appTop.hom.toMonoidHom v) := by
    intro V U h v hU
    simp only [D]
    rw [res_sub, map_res, unitSec_res, (ρz q).nat, (kumT_spec q).1 V U h v hU]
  let A : ∀ U : Scheme.{0}, (U ⟶ X) → Sec ((res ℤ (Tz q)).X 0) U → Prop :=
    fun U x s => ∃ v : (Γ(U, ⊤))ˣ, v ^ q = Units.map x.appTop.hom.toMonoidHom u ∧ s = D U v
  have hA : ∀ (V U : Scheme.{0}) (h : V ⟶ U) (x : U ⟶ X) (s : Sec ((res ℤ (Tz q)).X 0) U), A U x s → A V (h ≫ x) (Sec.res h s) := by
    rintro V U h x s ⟨v, hv, rfl⟩
    exact ⟨Units.map h.appTop.hom.toMonoidHom v, by rw [← map_pow, hv, units_map_comp], hDres V U h v (isUnit_q_res x hq)⟩
  have hu : ∀ (U : Scheme.{0}) (x : U ⟶ X) (s t : Sec ((res ℤ (Tz q)).X 0) U), A U x s → A U x t → s = t := by
    rintro U x s t ⟨v, hv, rfl⟩ ⟨v', hv', rfl⟩
    have h := D_inv q κ h2 φ hφ U (isUnit_q_res x hq) v (v' * v⁻¹) (by rw [mul_pow, hv', inv_pow, hv, mul_inv_cancel])
    rw [show v' * v⁻¹ * v = v' by group] at h
    exact h.symm
  have hl : ∀ (U : Scheme.{0}) (x : U ⟶ X), Loc U fun V g => ∃ s, A V (g ≫ x) s := by
    intro U x
    exact loc_mono (roots_loc q h4 U (isUnit_q_res x hq) (Units.map x.appTop.hom.toMonoidHom u))
      (fun V g ⟨v, hv⟩ => ⟨D V v, v, by rw [hv, units_map_comp], rfl⟩)
  obtain ⟨e, hen, heA⟩ := glue_sections ((res ℤ (Tz q)).X 0) X A hA hu hl
  refine ⟨e, hen, fun U x => ?_⟩
  apply sec_eq_of_loc
  refine loc_mono (roots_loc q h4 U (isUnit_q_res x hq) (Units.map x.appTop.hom.toMonoidHom u)) (fun V h ⟨v, hv⟩ => ?_)
  have hv' : v ^ q = Units.map (h ≫ x).appTop.hom.toMonoidHom u := by rw [hv, units_map_comp]
  have k1 : Sec.map ((res ℤ (Tz q)).d 0 1) (Sec.map φ (unitSec v)) = Sec.res (h ≫ x) (Sec.map ψ c) := by
    change Sec.map (φ ≫ (res ℤ (Tz q)).d 0 1) (unitSec v) = _
    rw [← hψ, map_res]
    change Sec.map ψ (Sec.map (cokernel.π κ) (unitSec v)) = _
    rw [pi_unitSec κ h0 h5 u c hq hc (h ≫ x) v hv']
  rw [map_res, hen, heA V (h ≫ x) (D V v) ⟨v, hv', rfl⟩, res_sub, res_comp, hgn, hgk V (h ≫ x) v hv']
  simp only [D]
  rw [map_sub', k1]

theorem kum_connect : ∀ (q : ℕ) [NeZero q] (κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm) (h0 : κ ≫ ((q : ℤ) • 𝟙 Gm) = 0), Mono κ →
  (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u) →
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Sec.map ((q : ℤ) • 𝟙 Gm) b = 0 → ∃ a, Sec.map κ a = b) →
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Loc U fun V g => ∃ c : Sec Gm V, Sec.map ((q : ℤ) • 𝟙 Gm) c = Sec.res g b) →
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map (cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0) (U := U))) →
  ∀ (z : Cocycle (res ℤ (cokernel κ)) (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))) 1) (s : ℤˣ),
  (∀ (φ : Gm ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 0) (ψ : cokernel κ ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 1),
      κ ≫ φ = resι ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) → cokernel.π κ ≫ ψ = φ ≫ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).d 0 1 →
      ∀ w : Cocycle (sgl (cokernel κ)) (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))) 1, sglι (cokernel κ) ≫ w.1.v 0 1 (zero_add 1) = ψ →
        CohomologyClass.mk (zcomp (Cocycle.ofHom (resAug (cokernel κ))) z (zero_add 1)) = s • CohomologyClass.mk w) →
  ∀ (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ) (c : Sec (cokernel κ) X), IsUnit (q : Γ(X, ⊤)) →
    Sec.map (cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0) c = unitSec u →
    HK.ext ℤ _ z 0 (0 + 1) rfl (secClass (cokernel κ) c) = s • restrH (Int.castRingHom (ZMod q)) (sch.obj X) (tw q 1) (0 + 1) (kum q u) := by
  intro q _ κ h0 hmono h2 h3 h4 h5 z s hz X u c hq hc
  have hφ : κ ≫ Injective.factorThru (resι ℤ (Tz q)) κ = resι ℤ (Tz q) := Injective.comp_factorThru _ _
  set φ := Injective.factorThru (resι ℤ (Tz q)) κ with hφdef
  have hφd : κ ≫ (φ ≫ (res ℤ (Tz q)).d 0 1) = 0 := by rw [← Category.assoc, hφ, resι_d]
  set ψ := cokernel.desc κ (φ ≫ (res ℤ (Tz q)).d 0 1) hφd with hψdef
  have hψ : cokernel.π κ ≫ ψ = φ ≫ (res ℤ (Tz q)).d 0 1 := cokernel.π_desc _ _ _
  have hψd : ψ ≫ (res ℤ (Tz q)).d 1 2 = 0 := by
    rw [← cancel_epi (cokernel.π κ), ← Category.assoc, hψ, Category.assoc, HomologicalComplex.d_comp_d, comp_zero, comp_zero]
  have hsd : ∀ i j : ℤ, (sgl (cokernel κ)).d i j = 0 := fun i j => by simp [sgl]
  obtain ⟨w, hw⟩ : ∃ w : Cocycle (sgl (cokernel κ)) (res ℤ (Tz q)) 1, sglι (cokernel κ) ≫ w.1.v 0 1 (zero_add 1) = ψ := by
    refine ⟨Cocycle.mk (Cochain.single (p := 0) (q := 1)
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (cokernel κ)).hom ≫ ψ) 1) 2 rfl ?_, ?_⟩
    · refine Cochain.ext _ _ (fun p r hpr => ?_)
      refine (δ_v 1 2 rfl _ p r hpr (p + 1) (p + 1) (by omega) rfl).trans ?_
      rw [hsd, zero_comp, smul_zero, add_zero, Cochain.zero_v]
      by_cases hp : p = 0
      · subst hp
        obtain rfl : r = 2 := by omega
        erw [Cochain.single_v]
        change ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (cokernel κ)).hom ≫ ψ) ≫ (res ℤ (Tz q)).d 1 2 = 0
        exact (Category.assoc _ _ _).trans ((congrArg _ hψd).trans comp_zero)
      · erw [Cochain.single_v_eq_zero _ _ _ _ _ hp]
        rw [zero_comp]
    · change _ ≫ (Cochain.single _ 1).v 0 1 _ = ψ
      erw [Cochain.single_v]
      exact Iso.inv_hom_id_assoc _ _
  have hzw := hz φ ψ hφ hψ w hw
  obtain ⟨a, ha0, haS⟩ := exists_etaleCochain_constant_zeroSimplices (R := ℤ) (X := X) (I := sgl (cokernel κ)) (n := 0)
    (fun U x => Sec.res x (Sec.map (sglι (cokernel κ)) c)) (fun V U g x => res_comp g x _)
  have hδa : δ 0 1 a = 0 := by
    refine ev_ext _ _ fun p t ht U x => ?_
    rw [ev_zero]
    cases p with
    | zero =>
      obtain rfl : t = 1 := by omega
      rw [etaleCochainEval_delta_zeroSimplex (zero_add 1) a U x, hsd]
      rfl
    | succ p => exact etaleCochainEval_delta_succ_of_vanishing (zero_add 1) a haS p t ht U x
  let acyc : Cocycle ((chains ℤ).obj (sch.obj X)) (sgl (cokernel κ)) 0 := Cocycle.mk a 1 rfl hδa
  have hex : ∃ cl, ∃ α : Cocycle ((chains ℤ).obj (sch.obj X)) (res ℤ (cokernel κ)) 0, CohomologyClass.mk α = cl ∧
      ev α.1 0 0 (by simp) X (𝟙 X) = Sec.map (resι ℤ (cokernel κ)) c := by
    refine ⟨_, zcomp acyc (Cocycle.ofHom (resAug (cokernel κ))) (add_zero 0), rfl, ?_⟩
    change ev (a.comp (Cochain.ofHom (resAug (cokernel κ))) (add_zero 0)) 0 0 _ X (𝟙 X) = _
    refine (ev_comp_ofHom _ _ _ _ _ _ _).trans ?_
    rw [ha0 X (𝟙 X), res_id]
    rfl
  obtain ⟨α, hα1, hα2⟩ := pick_spec hex
  have hαa : α = zcomp acyc (Cocycle.ofHom (resAug (cokernel κ))) (add_zero 0) := by
    refine Cocycle.ext (ev_ext _ _ fun p t ht U x => ?_)
    cases p with
    | zero =>
      obtain rfl : t = 0 := by omega
      change _ = ev (a.comp (Cochain.ofHom (resAug (cokernel κ))) (add_zero 0)) 0 0 _ U x
      refine Eq.trans ?_ (ev_comp_ofHom _ _ _ _ _ _ _).symm
      rw [ha0 U x]
      have h1 := ev_res α.1 0 0 (by simp) (show U ⟶ X from x) (𝟙 X : Sx (sch.obj X) 0 X)
      rw [hα2] at h1
      have e : (Sx.res (show U ⟶ X from x) (𝟙 X : Sx (sch.obj X) 0 X)) = x := Category.comp_id (show U ⟶ X from x)
      rw [e] at h1
      rw [← h1, map_res]
      rfl
    | succ p =>
      exact (sec_eq_zero_of_isZero (isZero_res_neg _ _ (by omega)) _).trans
        (sec_eq_zero_of_isZero (isZero_res_neg _ _ (by omega)) _).symm
  have hL : HK.ext ℤ _ z 0 (0 + 1) rfl (secClass (cokernel κ) c) = s • CohomologyClass.mk (zcomp acyc w (zero_add 1)) := by
    have hα1' : CohomologyClass.mk α = secClass (cokernel κ) c := hα1
    rw [← hα1', hαa]
    change CohomologyClass.mk (zcomp (zcomp acyc (Cocycle.ofHom (resAug _)) (add_zero 0)) z (zero_add 1)) = _
    have e : zcomp (zcomp acyc (Cocycle.ofHom (resAug (cokernel κ))) (add_zero 0)) z (zero_add 1) =
        zcomp acyc (zcomp (Cocycle.ofHom (resAug _)) z (zero_add 1)) (zero_add 1) :=
      Cocycle.ext (Cochain.comp_assoc _ _ _ (add_zero 0) (zero_add 1) (by omega))
    rw [e]
    change cpre acyc _ 1 1 (zero_add 1) (CohomologyClass.mk (zcomp (Cocycle.ofHom (resAug _)) z (zero_add 1))) = _
    rw [hzw, Units.smul_def, map_zsmul, Units.smul_def]
    rfl
  obtain ⟨γ, hγ, hγ1, hγ0⟩ := (GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).1 X u hq
  obtain ⟨⟨β, hβ⟩, hop⟩ := cup_op_spec.2 (ρz q) (sch.obj X) 1 γ
  have hR : restrH (Int.castRingHom (ZMod q)) (sch.obj X) (tw q 1) (0 + 1) (kum q u) = CohomologyClass.mk β := by
    rw [← hγ]
    exact hop β hβ
  rw [hL, hR]
  congr 1
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ 0 (zero_add 1)]
  obtain ⟨E, hEnat, hEd⟩ := glue_family q κ h0 h2 h4 h5 φ ψ hφ hψ X u c hq hc
    (fun U x => (ρz q).app U 1 (ev γ.1 0 1 (by simp) U x))
    (fun V U h x => by
      rw [(ρz q).nat]
      exact congrArg _ (ev_res γ.1 0 1 _ h (show Sx (sch.obj X) 0 U from x)))
    (fun U x v hv => by
      rw [hγ0 U x v hv, (ρz q).comm])
  obtain ⟨η, hη0, hηS⟩ := exists_etaleCochain_constant_zeroSimplices (R := ℤ) (X := X) (I := res ℤ (Tz q)) (n := 0) E hEnat
  refine ⟨η, ev_ext _ _ fun p t ht U x => ?_⟩
  have hsub : ∀ A B : Cochain ((chains ℤ).obj (sch.obj X)) (res ℤ (Tz q)) 1,
      ev (A - B) p t ht U x = ev A p t ht U x - ev B p t ht U x := fun A B => map_sub (evHom _ 1 p t ht U x) A B
  rw [Cocycle.coe_sub, hsub]
  cases p with
  | zero =>
    obtain rfl : t = 1 := by omega
    rw [etaleCochainEval_delta_zeroSimplex (zero_add 1) η U x, hη0 U x, hEd U x, hβ 0 1 _ U x]
    change _ = ev (a.comp w.1 (zero_add 1)) 0 1 _ U x - _
    have key : Sec.map (w.1.v 0 1 (zero_add 1)) (Sec.res x (Sec.map (sglι (cokernel κ)) c)) = Sec.res x (Sec.map ψ c) := by
      refine (map_res (w.1.v 0 1 (zero_add 1)) (show U ⟶ X from x) (Sec.map (sglι (cokernel κ)) c)).symm.trans ?_
      rw [← hw]
      rfl
    congr 1
    exact (((ev_zero_comp0 a w.1 U x).trans (congrArg _ (ha0 U x))).trans key).symm
  | succ p =>
    rw [etaleCochainEval_delta_succ_of_vanishing (zero_add 1) η hηS p t ht U x]
    change 0 = ev (a.comp w.1 (zero_add 1)) (p + 1) t ht U x - _
    rw [ev_zero_comp, haS p _ _ U x, hβ]
    cases p with
    | zero =>
      obtain rfl : t = 0 := by omega
      rw [hγ1 U x]
      simp
    | succ p =>
      rw [sec_eq_zero_of_isZero (isZero_res_neg _ t (by omega)) (ev γ.1 _ t _ U x)]
      simp

end GlobalTheory.EtC.KumUnit
