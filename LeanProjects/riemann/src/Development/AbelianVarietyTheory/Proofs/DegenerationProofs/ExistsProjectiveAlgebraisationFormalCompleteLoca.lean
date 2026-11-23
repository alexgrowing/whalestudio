import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsHomogeneousXPowMulAddXPowMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomEqOfPullSections
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullbackOfEquationsLift
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SubmoduleEqTopOfSupSmulOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFormLimitIdeal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFormCorrectionNextThickeningLocalStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Degen.FormalEmb

open MvPolynomial

section Germs

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

def gsHom (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) : Γ(X, U) →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (r ⁻¹ᵁ U) z h).hom.comp (r.app U).hom

theorem gsHom_apply (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) :
    gsHom r z U h a = gs r z U a := (gs_eq r z U h a).symm

def cstGerm (p : Z ⟶ Spec (CommRingCat.of R)) (z : Z) : R →+* Z.presheaf.stalk z :=
  (gsHom p z ⊤ trivial).comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem gs_eval_poly {σ : Type} (p : X ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U)
    (x : σ → Γ(X, U)) (F : MvPolynomial σ R) :
    gs r z U (eval₂Hom (AbLaw.cst p U) x F) = eval₂ (cstGerm (r ≫ p) z) (fun j => gs r z U (x j)) F := by
  rw [← gsHom_apply r z U h, coe_eval₂Hom, eval₂_comp_left]
  congr 1
  · ext a
    exact (gsHom_apply r z U h _).trans (((gs_res r z le_top h _).trans (gs_pull r p z ⊤ trivial _)).trans
      (gsHom_apply (r ≫ p) z ⊤ trivial _).symm)
  · ext j
    exact gsHom_apply r z U h _

theorem cst_comp_spec (p : X ⟶ Spec (CommRingCat.of R')) (g : R →+* R') (U : X.Opens) :
    AbLaw.cst (p ≫ Spec.map (CommRingCat.ofHom g)) U = (AbLaw.cst p U).comp g := by
  ext a
  have := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  simp only [AbLaw.cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  rw [this]

theorem gs_sec_chart {H : LB X} (s : LB.Sec H) (r : Z ⟶ X) (z : Z) {i j : H.ι} (hi : r z ∈ H.U i) (hj : r z ∈ H.U j) :
    gs r z _ (s.f i) = (gm r z _ (H.g i j)).val * gs r z _ (s.f j) := by
  have hm : r z ∈ H.U i ⊓ H.U j := ⟨hi, hj⟩
  have e := congrArg (gs r z _) (s.compat i j)
  rwa [gs_res _ z _ hm, gs_mul _ z _ hm, gs_res _ z _ hm, gs_unit _ z _ hm] at e

def Rel {H : LB X} {H' : LB X'} (β : X' ⟶ X) (w : LB.Iso H' (H.pull β)) (s : LB.Sec H) (s' : LB.Sec H') : Prop :=
  ∀ z (k : H.ι) (k' : H'.ι), β z ∈ H.U k → z ∈ H'.U k' →
    gs β z _ (s.f k) = (gw w (𝟙 _) z k k').val * gs (𝟙 _) z _ (s'.f k')

theorem gs_stalkMap_comp (r : Z ⟶ X') (β : X' ⟶ X) (z : Z) (U : X.Opens) (h : β (r z) ∈ U) (a : Γ(X, U)) :
    (r.stalkMap z).hom (gs β (r z) U a) = gs (r ≫ β) z U a := by
  rw [← gs_pull r β z U h, gs_eq β _ U h, gs_eq r z _ h]
  exact Scheme.Hom.germ_stalkMap_apply r (β ⁻¹ᵁ U) z h _

theorem Rel.pull {H : LB X} {H' : LB X'} {β : X' ⟶ X} {w : LB.Iso H' (H.pull β)} {s : LB.Sec H} {s' : LB.Sec H'}
    (h : Rel β w s s') (r : Z ⟶ X') (z : Z) (k : H.ι) (k' : H'.ι) (hk : β (r z) ∈ H.U k) (hk' : r z ∈ H'.U k') :
    gs (r ≫ β) z _ (s.f k) = (gw w r z k k').val * gs r z _ (s'.f k') := by
  have hm : r z ∈ (H.pull β).U (fun _ => k) ⊓ H'.U k' := ⟨mem_pull.2 hk, hk'⟩
  have e := congrArg (r.stalkMap z).hom (h (r z) k k' hk hk')
  rw [map_mul, gs_stalkMap_comp r β z _ hk, gs_stalkMap_comp r (𝟙 _) z _ hk', Category.comp_id] at e
  refine e.trans (congrArg (· * _) ?_)
  refine (congrArg (r.stalkMap z).hom (gs_unit (𝟙 X') (r z) _ hm _).symm).trans
    ((gs_stalkMap_comp r (𝟙 _) z _ hm _).trans ?_)
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
  rw [gs_eval_poly p β z _ hk, gs_eval_poly (β ≫ p) (𝟙 _) z _ hk', Category.id_comp, zpow_natCast, Units.val_pow_eq_pow_val,
    ← eval₂_scale _ _ _ hF]
  congr 1
  exact funext fun j => h j z k k' hk hk'

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

end Germs

variable {X X' : Scheme.{0}} {R : Type} [CommRing R] {σ : Type}

def vanIdeal (p : X ⟶ Spec (CommRingCat.of R)) {H : LB X} (s : σ → LB.Sec H) : Ideal (MvPolynomial σ R) :=
  ⨅ k : H.ι, RingHom.ker (eval₂Hom (AbLaw.cst p (H.U k)) (fun j => (s j).f k))

theorem mem_vanIdeal (p : X ⟶ Spec (CommRingCat.of R)) {H : LB X} (s : σ → LB.Sec H) (F : MvPolynomial σ R) :
    F ∈ vanIdeal p s ↔ ∀ k : H.ι, eval₂Hom (AbLaw.cst p (H.U k)) (fun j => (s j).f k) F = 0 := by
  simp only [vanIdeal, Ideal.mem_iInf, RingHom.mem_ker]

theorem mem_vanIdeal_of_sat (p : X ⟶ Spec (CommRingCat.of R)) {H : LB X} (s : σ → LB.Sec H)
    (hs : ⨆ i, nonzeroLocus (s i) = ⊤) {F : MvPolynomial σ R}
    (h : ∀ i, ∃ m : ℕ, MvPolynomial.X i ^ m * F ∈ vanIdeal p s) : F ∈ vanIdeal p s := by
  rw [mem_vanIdeal]
  intro k
  refine fn_ext fun y hy => ?_
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ i, nonzeroLocus (s i) by rw [hs]; trivial)
  obtain ⟨k', hk'⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
  have hy' : y ∈ H.U k' := X.basicOpen_le _ hk'
  have u' : IsUnit (gs (𝟙 X) y _ ((s i).f k')) := by
    rw [gs_eq (𝟙 X) y _ hy']
    exact (X.mem_basicOpen _ y hy').1 hk'
  have u : IsUnit (gs (𝟙 X) y _ ((s i).f k)) := by
    rw [gs_sec_chart (s i) (𝟙 X) y hy hy']
    exact (Units.isUnit _).mul u'
  obtain ⟨m, hm⟩ := h i
  have e := congrArg (gsHom (𝟙 X) y _ hy) ((mem_vanIdeal p s _).1 hm k)
  rw [map_mul, map_pow, eval₂Hom_X', map_mul, map_pow, map_zero, gsHom_apply (𝟙 X) y _ hy,
    gsHom_apply (𝟙 X) y _ hy] at e
  rw [(u.pow m).mul_right_eq_zero.1 e, ← gsHom_apply (𝟙 X) y _ hy, map_zero]

theorem mem_vanIdeal_pull {H : LB X} {H' : LB X'} (hH : H.IsLB) {β : X' ⟶ X} {w : LB.Iso H' (H.pull β)}
    {s : σ → LB.Sec H} {s' : σ → LB.Sec H'} (h : ∀ j, Rel β w (s j) (s' j)) (p : X ⟶ Spec (CommRingCat.of R))
    {F : MvPolynomial σ R} {t : ℕ} (hF : F.IsHomogeneous t) (h0 : F ∈ vanIdeal p s) : F ∈ vanIdeal (β ≫ p) s' := by
  rw [mem_vanIdeal] at h0 ⊢
  intro k'
  refine fn_ext fun z hz => ?_
  obtain ⟨k, hk⟩ := exists_chart hH (β z)
  have e := Rel.form h p hF z k k' hk hz
  rw [h0 k, ← gsHom_apply β z _ hk, map_zero] at e
  rw [(Units.isUnit _).mul_right_eq_zero.1 e.symm, ← gsHom_apply (𝟙 X') z _ hz, map_zero]

theorem component_mem_span (S : Set (MvPolynomial σ R)) (hS : ∀ F ∈ S, ∃ t, F.IsHomogeneous t) :
    ∀ F ∈ Ideal.span S, ∀ t, homogeneousComponent t F ∈ Ideal.span S := by
  intro F hF t
  letI := MvPolynomial.gradedAlgebra (σ := σ) (R := R)
  have h := Ideal.homogeneous_span (homogeneousSubmodule σ R) S (fun F hF => hS F hF) t hF
  rwa [show (DirectSum.decompose (homogeneousSubmodule σ R) F t : MvPolynomial σ R) = homogeneousComponent t F from
    decomposition.decompose'_apply F t] at h

end GlobalTheory.Degen.FormalEmb

theorem GlobalTheory.Degen.isNilpotent_ker_factor_pow {R : Type} [CommRing R] (I : Ideal R) {n : ℕ}
    (h : I ^ n ≤ I ^ (0 + 1)) : IsNilpotent (RingHom.ker (Ideal.Quotient.factor h)) := by
  have h₁ : RingHom.ker (Ideal.Quotient.factor h) ≤ I.map (Ideal.Quotient.mk (I ^ n)) := by
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem, zero_add, pow_one] at hx
    exact Ideal.mem_map_of_mem _ hx
  refine ⟨n, ?_⟩
  rw [Ideal.zero_eq_bot, eq_bot_iff]
  refine (Ideal.pow_right_mono h₁ n).trans ?_
  rw [← Ideal.map_pow, Ideal.map_quotient_self]

open GlobalTheory.Degen.FormalEmb in

theorem GlobalTheory.Degen.exists_projective_of_formal_embedding_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → IsAdicComplete I R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, Flat (Y e).hom) → ∀ (H : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (H e) ((H (e + 1)).pull (β e))), (∀ e, (H e).IsLB ∧ (v e).IsGen) → ∀ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (H e)), (∀ e j, (∀ z (k : (H (e + 1)).ι) (k' : (H e).ι), (β e) z ∈ (H (e + 1)).U k → z ∈ (H e).U k' → gs (β e) z _ ((s (e + 1) j).f k) = (Geo.Tor.gw (v e) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s e j).f k'))) → VeryAmpleBy (Y 0).hom (H 0) (s 0) → ∃ (B : Over (Spec (CommRingCat.of R))) (H' : LB B.left) (s' : Fin (n + 1) → LB.Sec H') (b : ∀ e, (Y e).left ⟶ B.left) (w : ∀ e, LB.Iso (H e) (H'.pull (b e))), H'.IsLB ∧ VeryAmpleBy B.hom H' s' ∧ (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) ∧ (∀ e, β e ≫ b (e + 1) = b e) ∧ (∀ e, (w e).IsGen ∧ (∀ j, (∀ z (k : (H').ι) (k' : (H e).ι), (b e) z ∈ (H').U k → z ∈ (H e).U k' → gs (b e) z _ ((s' j).f k) = (Geo.Tor.gw (w e) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s e j).f k')))) ∧ ∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → (∀ e, (∀ k : (H e).ι, MvPolynomial.eval₂Hom (cst ((Y (e)).hom ≫ thick R I (e)) ((H e).U k)) (fun j => (s e j).f k) (F) = 0)) → (∀ k : (H').ι, MvPolynomial.eval₂Hom (cst (B.hom) ((H').U k)) (fun j => (s' j).f k) (F) = 0) := by
  intro V _ _ _ I hI hc Y β hβ hflat H v hH n s hs hva
  have hVA : ∀ e, VeryAmpleBy (Y e).hom (H e) (s e) := by
    rintro (_ | e)
    · exact hva
    · obtain ⟨j₀, hj, w, hw, hr⟩ := tower _ Y β hβ H v hH s hs e
      exact GlobalTheory.AbLaw.veryAmpleBy_of_isNilpotent _ _ _ (Ideal.Quotient.factor_surjective _)
        (GlobalTheory.Degen.isNilpotent_ker_factor_pow I _)
        _ _ _ _ j₀ hj _ _ w n _ _ (hH _).1 (hH _).1 ((isGen_iff _).2 hw) hr hva
  have c₁ : ∀ e, β e ≫ (Y (e + 1)).hom ≫ thick V I (e + 1) = (Y e).hom ≫ thick V I e := fun e => by
    rw [← Category.assoc, (hβ e).w, Category.assoc, thickTrans_comp]
  let K : ℕ → Ideal (MvPolynomial (Fin (n + 1)) V) := fun e => vanIdeal ((Y e).hom ≫ thick V I e) (s e)
  let S : Set (MvPolynomial (Fin (n + 1)) V) := {F | (∃ t, F.IsHomogeneous t) ∧ ∀ e, F ∈ K e}
  have hS : ∀ e, Ideal.span S ≤ K e := fun e => Ideal.span_le.2 fun F hF => hF.2 e
  obtain ⟨B, f, H', s', hH', hva', hB⟩ := GlobalTheory.ProjQuot.exists_veryAmpleBy_of_ideal V n (Ideal.span S)
    (component_mem_span S fun F hF => hF.1)
  have hB' : ∀ t (F : MvPolynomial (Fin (n + 1)) V), F.IsHomogeneous t → (∀ e, F ∈ K e) → ∀ k : H'.ι,
      MvPolynomial.eval₂Hom (cst f (H'.U k)) (fun j => (s' j).f k) F = 0 := fun t F hF h =>
    (hB t F hF).2 fun i => ⟨0, by rw [pow_zero, _root_.one_mul]; exact Ideal.subset_span ⟨⟨t, hF⟩, h⟩⟩
  choose b w hb hw hr using fun e => GlobalTheory.exists_hom_of_veryAmpleBy V B f H' n s' hH' hva' _
    ((Y e).hom ≫ thick V I e) (H e) (s e) (hH e).1 (hVA e).1 (fun t F hF h =>
      (mem_vanIdeal _ _ _).1 (mem_vanIdeal_of_sat _ _ (hVA e).1 fun i =>
        ((hB t F hF).1 h i).imp fun _ hm => hS e hm))
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.exists_form_correction_next_thickening_local V I hI Y β hβ hflat H v hH n s hs hva
  refine ⟨Over.mk f, H', s', b, w, hH', hva', fun e => ?_, fun e => ?_, fun e => ⟨hw e, hr e⟩,
    fun t F hF h => hB' t F hF fun e => (mem_vanIdeal _ _ _).2 (h e)⟩
  · refine GlobalTheory.ProjBaseChange.isPullback_of_equations_lift V B f H' n s' hH' hva' _ _ Ideal.Quotient.mk_surjective
      _ (Y e).hom (H e) (s e) (b e) (w e) (hH e).1 (hVA e) (hb e) (hw e) (hr e) t₀ fun t ht F hF h => ?_
    obtain ⟨F₁, hF₁, hK, hG⟩ := GlobalTheory.Degen.exists_form_limit_ideal V I hc _ K t
      (fun e F hF h => by
        have := mem_vanIdeal_pull (hH (e + 1)).1 (hs e) _ hF h
        rwa [c₁] at this)
      (fun e a ha => (mem_vanIdeal _ _ _).2 fun k => by
        rw [MvPolynomial.eval₂Hom_C, cst_comp_spec, RingHom.comp_apply,
          Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero])
      (fun e F hF h => (ht₀ t ht e F hF ((mem_vanIdeal _ _ _).1 h)).imp fun G hG =>
        ⟨hG.1, hG.2.1, (mem_vanIdeal _ _ _).2 hG.2.2⟩) e F hF ((mem_vanIdeal _ _ _).2 h)
    refine ⟨F₁, hF₁, hB' t F₁ hF₁ hK, ?_⟩
    rw [eq_comm, ← sub_eq_zero, ← map_sub]
    ext d
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hG d)
  · have hv := (isGen_iff _).1 (hH e).2
    have hw' := (isGen_iff _).1 (hw (e + 1))
    obtain ⟨w'', T⟩ := exists_comp (hH (e + 1)).1 (w (e + 1)) (v e) hw' hv hH' (hH e).1
    exact GlobalTheory.MapUniq.hom_eq_of_pull_sections V B f H' n s' hH' hva' _ (H e) (s e) _ _ w'' (w e) (hH e).1
      (by rw [Category.assoc, hb, hb, c₁]) ((isGen_iff _).2 (T.pgen_comp (hH (e + 1)).1 hw' hv)) (hw e)
      (fun j => Rel.comp T (hH (e + 1)).1 (hr (e + 1) j) (hs e j)) (hr e)
