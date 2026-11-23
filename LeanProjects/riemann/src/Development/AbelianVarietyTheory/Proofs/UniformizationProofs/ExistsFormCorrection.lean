import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SerreVanishingVeryAmpleStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSectionEqMulOfVanishingModElementStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Unif.PolyStep

open MvPolynomial

variable {X X' X'' Z : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

theorem eval₂_scale {σ A : Type} [CommRing A] (φ : R →+* A) (c : A) (x : σ → A) {F : MvPolynomial σ R}
    {e : ℕ} (hF : F.IsHomogeneous e) : eval₂ φ (fun j => c * x j) F = c ^ e * eval₂ φ x F := by
  rw [eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hd : ∑ j ∈ a.support, a j = e := by
    have := hF (mem_support_iff.1 ha)
    rw [← this, Finsupp.weight_apply, Finsupp.sum]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem exists_lift {σ : Type} (g : R →+* R') (hg : Function.Surjective g) {F : MvPolynomial σ R'} {t : ℕ}
    (hF : F.IsHomogeneous t) : ∃ G : MvPolynomial σ R, G.IsHomogeneous t ∧ map g G = F := by
  obtain ⟨G, rfl⟩ := map_surjective g hg F
  refine ⟨homogeneousComponent t G, homogeneousComponent_isHomogeneous t G, ?_⟩
  ext d
  rw [coeff_map, coeff_homogeneousComponent]
  split_ifs with h
  · rw [coeff_map]
  · rw [map_zero, hF.coeff_eq_zero h]

def gsHom (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) : Γ(X, U) →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (r ⁻¹ᵁ U) z h).hom.comp (r.app U).hom

theorem gsHom_apply (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) :
    gsHom r z U h a = gs r z U a := (gs_eq r z U h a).symm

def cstGerm (p : Z ⟶ Spec (CommRingCat.of R)) (z : Z) : R →+* Z.presheaf.stalk z :=
  (gsHom p z ⊤ trivial).comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem gs_eval {σ : Type} (p : X ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U)
    (x : σ → Γ(X, U)) (F : MvPolynomial σ R) :
    gs r z U (eval₂Hom (AbLaw.cst p U) x F) = eval₂ (cstGerm (r ≫ p) z) (fun j => gs r z U (x j)) F := by
  rw [← gsHom_apply r z U h, coe_eval₂Hom, eval₂_comp_left]
  congr 1
  · ext a
    exact (gsHom_apply r z U h _).trans (((gs_res r z le_top h _).trans (gs_pull r p z ⊤ trivial _)).trans
      (gsHom_apply (r ≫ p) z ⊤ trivial _).symm)
  · ext j
    exact gsHom_apply r z U h _

theorem cst_comp (p : X ⟶ Spec (CommRingCat.of R')) (g : R →+* R') (U : X.Opens) :
    AbLaw.cst (p ≫ Spec.map (CommRingCat.ofHom g)) U = (AbLaw.cst p U).comp g := by
  ext a
  have := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  simp only [AbLaw.cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  rw [this]

theorem gs_sec {H : LB X} (s : LB.Sec H) (r : Z ⟶ X) (z : Z) {i j : H.ι} (hi : r z ∈ H.U i) (hj : r z ∈ H.U j) :
    gs r z _ (s.f i) = (gm r z _ (H.g i j)).val * gs r z _ (s.f j) := by
  have hm : r z ∈ H.U i ⊓ H.U j := ⟨hi, hj⟩
  have e := congrArg (gs r z _) (s.compat i j)
  rwa [gs_res _ z _ hm, gs_mul _ z _ hm, gs_res _ z _ hm, gs_unit _ z _ hm] at e

def formSec {σ : Type} (p : X ⟶ Spec (CommRingCat.of R)) {H : LB X} (s : σ → LB.Sec H) {F : MvPolynomial σ R}
    {t : ℕ} (hF : F.IsHomogeneous t) : LB.Sec (AbLaw.pw H t) where
  f := fun k => eval₂Hom (AbLaw.cst p (H.U k)) (fun j => (s j).f k) F
  compat := fun i j => fn_ext fun y hy => by
    refine (gs_res _ y _ hy _).trans (Eq.trans ?_ ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      (gs_unit _ y _ hy _) (gs_res _ y _ hy _))).symm)
    refine (gs_eval p (𝟙 X) y (H.U i) hy.1 _ F).trans (Eq.trans ?_ (congrArg₂ (· * ·)
      (congrArg Units.val (map_zpow (gm (𝟙 X) y (H.U i ⊓ H.U j)) (H.g i j) t))
      (gs_eval p (𝟙 X) y (H.U j) hy.2 _ F)).symm)
    rw [zpow_natCast, Units.val_pow_eq_pow_val, ← eval₂_scale _ _ _ hF]
    congr 1
    exact funext fun a => gs_sec (s a) _ y hy.1 hy.2

def pwIso {H : LB X} {H' : LB X'} {β : X' ⟶ X} (w : LB.Iso H' (H.pull β)) (t : ℤ) :
    LB.Iso (AbLaw.pw H' t) ((AbLaw.pw H t).pull β) := ⟨fun p => w.s p ^ t⟩

theorem gw_pwIso {H : LB X} {H' : LB X'} {β : X' ⟶ X} (w : LB.Iso H' (H.pull β)) (t : ℤ) (r : Z ⟶ X') (z : Z)
    (j : H.ι) (k : H'.ι) : gw (pwIso w t) r z j k = gw w r z j k ^ t :=
  map_zpow (gm r z ((H.pull β).U (fun _ => j) ⊓ H'.U k)) (w.s (fun _ => j, k)) t

theorem pgen_pwIso {H : LB X} {H' : LB X'} {β : X' ⟶ X} {w : LB.Iso H' (H.pull β)} (hw : PGen w) (t : ℤ) :
    PGen (pwIso w t) := by
  intro Y f y j j' k k' hj hj' hk hk'
  have e := congrArg (· ^ t) (hw Y f y j j' k k' hj hj' hk hk')
  simp only [mul_zpow, inv_zpow] at e
  refine (gw_pwIso w t f y j k).trans (e.trans (congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ (congrArg (·⁻¹) ?_))
    (gw_pwIso w t f y j' k').symm))
  · exact (map_zpow _ _ _).symm
  · exact (map_zpow _ _ _).symm

def Rel {H : LB X} {H' : LB X'} (β : X' ⟶ X) (w : LB.Iso H' (H.pull β)) (s : LB.Sec H) (s' : LB.Sec H') : Prop :=
  ∀ z (k : H.ι) (k' : H'.ι), β z ∈ H.U k → z ∈ H'.U k' →
    gs β z _ (s.f k) = (gw w (𝟙 _) z k k').val * gs (𝟙 _) z _ (s'.f k')

theorem gs_stalkMap (r : Z ⟶ X') (β : X' ⟶ X) (z : Z) (U : X.Opens) (h : β (r z) ∈ U) (a : Γ(X, U)) :
    (r.stalkMap z).hom (gs β (r z) U a) = gs (r ≫ β) z U a := by
  rw [← gs_pull r β z U h, gs_eq β _ U h, gs_eq r z _ h]
  exact Scheme.Hom.germ_stalkMap_apply r (β ⁻¹ᵁ U) z h _

theorem Rel.pull {H : LB X} {H' : LB X'} {β : X' ⟶ X} {w : LB.Iso H' (H.pull β)} {s : LB.Sec H} {s' : LB.Sec H'}
    (h : Rel β w s s') (r : Z ⟶ X') (z : Z) (k : H.ι) (k' : H'.ι) (hk : β (r z) ∈ H.U k) (hk' : r z ∈ H'.U k') :
    gs (r ≫ β) z _ (s.f k) = (gw w r z k k').val * gs r z _ (s'.f k') := by
  have hm : r z ∈ (H.pull β).U (fun _ => k) ⊓ H'.U k' := ⟨mem_pull.2 hk, hk'⟩
  have e := congrArg (r.stalkMap z).hom (h (r z) k k' hk hk')
  rw [map_mul, gs_stalkMap r β z _ hk, gs_stalkMap r (𝟙 _) z _ hk', Category.comp_id] at e
  refine e.trans (congrArg (· * _) ?_)
  refine (congrArg (r.stalkMap z).hom (gs_unit (𝟙 X') (r z) _ hm _).symm).trans
    ((gs_stalkMap r (𝟙 _) z _ hm _).trans ?_)
  rw [Category.comp_id]
  exact gs_unit r z _ hm _

theorem Rel.comp {H : LB X} {H' : LB X'} {H'' : LB X''} {β : X' ⟶ X} {β' : X'' ⟶ X'} {w : LB.Iso H' (H.pull β)}
    {w' : LB.Iso H'' (H'.pull β')} {w'' : LB.Iso H'' (H.pull (β' ≫ β))} (T : Tri w w' w'') (hH' : H'.IsLB)
    {s : LB.Sec H} {s' : LB.Sec H'} {s'' : LB.Sec H''} (h : Rel β w s s') (h' : Rel β' w' s' s'') :
    Rel (β' ≫ β) w'' s s'' := by
  intro z k k'' hk hk''
  obtain ⟨i, hi⟩ := exists_chart hH' (β' z)
  rw [h.pull β' z k i hk hi, h' z i k'' hi hk'', T _ (𝟙 _) z k i k'' hk hi hk'', Category.id_comp, Units.val_mul,
    _root_.mul_assoc]

theorem Rel.form {σ : Type} {H : LB X} {H' : LB X'} {β : X' ⟶ X} {w : LB.Iso H' (H.pull β)} {s : σ → LB.Sec H}
    {s' : σ → LB.Sec H'} (h : ∀ j, Rel β w (s j) (s' j)) (p : X ⟶ Spec (CommRingCat.of R))
    {F : MvPolynomial σ R} {t : ℕ} (hF : F.IsHomogeneous t) (z : X') (k : H.ι) (k' : H'.ι) (hk : β z ∈ H.U k)
    (hk' : z ∈ H'.U k') :
    gs β z _ (eval₂Hom (AbLaw.cst p (H.U k)) (fun j => (s j).f k) F) = (gw w (𝟙 _) z k k' ^ (t : ℤ)).val *
      gs (𝟙 _) z _ (eval₂Hom (AbLaw.cst (β ≫ p) (H'.U k')) (fun j => (s' j).f k') F) := by
  rw [gs_eval p β z _ hk, gs_eval (β ≫ p) (𝟙 _) z _ hk', Category.id_comp, zpow_natCast, Units.val_pow_eq_pow_val,
    ← eval₂_scale _ _ _ hF]
  congr 1
  exact funext fun j => h j z k k' hk hk'

section Ring

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}

theorem mem_pow (hϖ : Irreducible ϖ) (n : ℕ) (x : V) : x ∈ IsLocalRing.maximalIdeal V ^ n ↔ ϖ ^ n ∣ x := by
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem mem_ker_factor (hϖ : Irreducible ϖ) {m n : ℕ}
    (h : IsLocalRing.maximalIdeal V ^ n ≤ IsLocalRing.maximalIdeal V ^ m) (x : V) :
    Ideal.Quotient.mk _ x ∈ RingHom.ker (Ideal.Quotient.factor h) ↔ ϖ ^ m ∣ x := by
  rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem, mem_pow hϖ]

theorem ker_factor (hϖ : Irreducible ϖ) {m n : ℕ}
    (h : IsLocalRing.maximalIdeal V ^ n ≤ IsLocalRing.maximalIdeal V ^ m) :
    RingHom.ker (Ideal.Quotient.factor h) = Ideal.span {Ideal.Quotient.mk _ (ϖ ^ m)} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.mem_span_singleton.2 (map_dvd _ ((mem_ker_factor hϖ h x).1 hx))
  · rw [Ideal.span_singleton_le_iff_mem, mem_ker_factor hϖ]

theorem nilpotent_ker (hϖ : Irreducible ϖ) {n : ℕ}
    (h : IsLocalRing.maximalIdeal V ^ n ≤ IsLocalRing.maximalIdeal V ^ (0 + 1)) :
    IsNilpotent (RingHom.ker (Ideal.Quotient.factor h)) := by
  refine ⟨n, ?_⟩
  rw [ker_factor hϖ, Ideal.span_singleton_pow, ← map_pow, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot,
    Ideal.Quotient.eq_zero_iff_mem, mem_pow hϖ]
  simp

theorem mul_eq_zero_iff (hϖ : Irreducible ϖ) {n : ℕ}
    (h : IsLocalRing.maximalIdeal V ^ (n + 1) ≤ IsLocalRing.maximalIdeal V ^ (0 + 1))
    (x : V ⧸ IsLocalRing.maximalIdeal V ^ (n + 1)) :
    Ideal.Quotient.mk _ (ϖ ^ n) * x = 0 ↔ x ∈ RingHom.ker (Ideal.Quotient.factor h) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [mem_ker_factor hϖ, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, mem_pow hϖ, pow_succ, zero_add, pow_one,
    mul_dvd_mul_iff_left (pow_ne_zero n hϖ.ne_zero)]

end Ring

theorem tower {σ : Type} (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
    (H : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (H e) ((H (e + 1)).pull (β e))) (hH : ∀ e, (H e).IsLB ∧ (v e).IsGen)
    (s : ∀ e, σ → LB.Sec (H e)) (hs : ∀ e j, Rel (β e) (v e) (s (e + 1) j) (s e j)) (e : ℕ) :
    ∃ j₀ : (Y 0).left ⟶ (Y (e + 1)).left, IsPullback j₀ (Y 0).hom (Y (e + 1)).hom (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega) : I ^ (e + 1 + 1) ≤ I ^ (0 + 1))))) ∧
      ∃ w : LB.Iso (H 0) ((H (e + 1)).pull j₀), PGen w ∧ ∀ j, Rel j₀ w (s (e + 1) j) (s 0 j) := by
  induction e with
  | zero => exact ⟨β 0, hβ 0, v 0, (isGen_iff _).1 (hH 0).2, hs 0⟩
  | succ e ih =>
    obtain ⟨j₀, hj, w, hw, hr⟩ := ih
    have hv := (isGen_iff _).1 (hH (e + 1)).2
    obtain ⟨w'', T⟩ := exists_comp (hH (e + 1)).1 (v (e + 1)) w hv hw (hH (e + 1 + 1)).1 (hH 0).1
    refine ⟨j₀ ≫ β (e + 1), ?_, w'', T.pgen_comp (hH (e + 1)).1 hv hw,
      fun j => Rel.comp T (hH (e + 1)).1 (hs (e + 1) j) (hr j)⟩
    convert hj.paste_horiz (hβ (e + 1)) using 1
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp]

end GlobalTheory.Unif.PolyStep

open GlobalTheory.Unif.PolyStep in

theorem GlobalTheory.Unif.exists_form_correction : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans V (IsLocalRing.maximalIdeal V) e)) → (∀ e, Flat (Y e).hom) → ∀ (H : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (H e) ((H (e + 1)).pull (β e))), (∀ e, (H e).IsLB ∧ (v e).IsGen) → ∀ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (H e)), (∀ e, (∀ j, (∀ z (k : (H (e + 1)).ι) (k' : (H e).ι), (β e) z ∈ (H (e + 1)).U k → z ∈ (H e).U k' → gs (β e) z _ ((s (e + 1) j).f k) = (Geo.Tor.gw (v e) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s e j).f k')))) → VeryAmpleBy (Y 0).hom (H 0) (s 0) → ∃ t₀ : ℕ, ∀ t, t₀ ≤ t → ∀ (e : ℕ) (F : MvPolynomial (Fin (n + 1)) V), F.IsHomogeneous t → (∀ k : (H e).ι, MvPolynomial.eval₂Hom (cst ((Y (e)).hom ≫ thick V (IsLocalRing.maximalIdeal V) (e)) ((H e).U k)) (fun j => (s e j).f k) (F) = 0) → ∃ G : MvPolynomial (Fin (n + 1)) V, G.IsHomogeneous t ∧ (∀ k : (H (e + 1)).ι, MvPolynomial.eval₂Hom (cst ((Y (e + 1)).hom ≫ thick V (IsLocalRing.maximalIdeal V) (e + 1)) ((H (e + 1)).U k)) (fun j => (s (e + 1) j).f k) (F - MvPolynomial.C (ϖ ^ (e + 1)) * G) = 0) := by
  intro V _ _ _ ϖ hϖ Y β hβ hflat H v hH n s hs hva
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.serre_vanishing_very_ample.2 _ _ (Y 0).hom (H 0) n (s 0) (hH 0).1 hva
  refine ⟨t₀, fun t ht e F hF hF0 => ?_⟩
  obtain ⟨j₀, hj, w, hw, hr⟩ := tower _ Y β hβ H v hH s hs e
  have c₁ : β e ≫ (Y (e + 1)).hom ≫ thick V (IsLocalRing.maximalIdeal V) (e + 1) =
      (Y e).hom ≫ thick V (IsLocalRing.maximalIdeal V) e := by
    rw [← Category.assoc, (hβ e).w, Category.assoc, thickTrans_comp]
  have c₂ : j₀ ≫ (Y (e + 1)).hom ≫ thick V (IsLocalRing.maximalIdeal V) (e + 1) =
      (Y 0).hom ≫ thick V (IsLocalRing.maximalIdeal V) 0 := by
    rw [← Category.assoc, hj.w, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      Ideal.Quotient.factor_comp_mk]
  obtain ⟨τ₀, hτ⟩ := GlobalTheory.T.exists_section_eq_mul_of_vanishing_mod_element _ _ _ _ _ (Ideal.Quotient.mk _ (ϖ ^ (e + 1))) (Ideal.Quotient.factor_surjective _)
    (Ideal.Quotient.factor_surjective _) (nilpotent_ker hϖ _) (ker_factor hϖ _)
    ((mem_ker_factor hϖ _ _).2 (pow_dvd_pow _ (by omega))) (mul_eq_zero_iff hϖ _) _ _ _ _ _ _ j₀ (β e) (hflat (e + 1))
    hj (hβ e) (GlobalTheory.AbLaw.pw (H (e + 1)) t) (GlobalTheory.AbLaw.pw (H 0) t) (pwIso w t) (isLB_pw (hH _).1 _) (isLB_pw (hH _).1 _)
    ((isGen_iff _).2 (pgen_pwIso hw t))
    (formSec ((Y (e + 1)).hom ≫ thick V (IsLocalRing.maximalIdeal V) (e + 1)) (s (e + 1)) hF) (fun k =>
      fn_ext fun z hz => by
        obtain ⟨i, hi⟩ := exists_chart (hH e).1 z
        have h := Rel.form (hs e) ((Y (e + 1)).hom ≫ thick V (IsLocalRing.maximalIdeal V) (e + 1)) hF z k i hz hi
        rw [c₁, hF0 i, ← gsHom_apply (𝟙 _) z _ hi, map_zero, mul_zero] at h
        refine (gs_pull (𝟙 _) (β e) z _ hz _).trans ?_
        rw [Category.id_comp, ← gsHom_apply (𝟙 _) z _ hz, map_zero]
        exact h)
  obtain ⟨G₀, hG₀, hτ₀⟩ := ht₀ t ht τ₀
  obtain ⟨G, hG, rfl⟩ := exists_lift _ Ideal.Quotient.mk_surjective hG₀
  refine ⟨G, hG, fun k => ?_⟩
  have h := hτ (formSec ((Y (e + 1)).hom ≫ thick V (IsLocalRing.maximalIdeal V) (e + 1)) (s (e + 1)) hG)
    (fun z k k' hk hk' => by
      have h := Rel.form hr ((Y (e + 1)).hom ≫ thick V (IsLocalRing.maximalIdeal V) (e + 1)) hG z k k' hk hk'
      rw [c₂, GlobalTheory.Unif.PolyStep.cst_comp (Y 0).hom, ← MvPolynomial.eval₂Hom_map_hom] at h
      exact h.trans (congrArg₂ (· * ·) (congrArg Units.val (gw_pwIso w t (𝟙 _) z k k').symm)
        (congrArg (gs (𝟙 _) z _) (hτ₀ k').symm))) k
  rw [map_sub, map_mul, MvPolynomial.eval₂Hom_C, sub_eq_zero]
  exact h.trans (congrArg (· * _) (RingHom.congr_fun (GlobalTheory.Unif.PolyStep.cst_comp (Y (e + 1)).hom _ _) _).symm)
