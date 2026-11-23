import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionsPowVeryAmpleAreFormsOfClosedFibreStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionsBasisBaseChangeH1VanishingStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.FormCorr

section
open MvPolynomial

variable {X X' Z : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

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

theorem const_comp (p : X ⟶ Spec (CommRingCat.of R')) (g : R →+* R') (U : X.Opens) :
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

theorem gs_cst (p : X ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : R) :
    gs r z U (AbLaw.cst p U a) = cstGerm (r ≫ p) z a := by
  have e := gs_eval (σ := Empty) p r z U h Empty.elim (MvPolynomial.C a)
  rwa [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂_C] at e

theorem gs_lin {n : ℕ} (p : X ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U)
    (c : Fin n → R) (x : Fin n → Γ(X, U)) :
    gs r z U (∑ i, AbLaw.cst p U (c i) * x i) = ∑ i, cstGerm (r ≫ p) z (c i) * gs r z U (x i) := by
  rw [← gsHom_apply r z _ h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, gsHom_apply, gsHom_apply, gs_cst p r z _ h]

theorem germ_rel {n : ℕ} {M : LB X} {M' : LB X'} {β : X' ⟶ X} {w : LB.Iso M' (M.pull β)} {σ : LB.Sec M}
    {σ' : LB.Sec M'} {τ : Fin n → LB.Sec M} {τ' : Fin n → LB.Sec M'} (hσ : Rel β w σ σ')
    (hτ : ∀ i, Rel β w (τ i) (τ' i)) (p : X ⟶ Spec (CommRingCat.of R)) (c : Fin n → R) (z : X') (k : M.ι)
    (k' : M'.ι) (hk : β z ∈ M.U k) (hk' : z ∈ M'.U k') :
    gs β z _ (σ.f k) = gs β z _ (∑ i, AbLaw.cst p (M.U k) (c i) * (τ i).f k) ↔
      gs (𝟙 _) z _ (σ'.f k') = gs (𝟙 _) z _ (∑ i, AbLaw.cst (β ≫ p) (M'.U k') (c i) * (τ' i).f k') := by
  have e : gs β z _ (∑ i, AbLaw.cst p (M.U k) (c i) * (τ i).f k) = (gw w (𝟙 _) z k k').val *
      gs (𝟙 _) z _ (∑ i, AbLaw.cst (β ≫ p) (M'.U k') (c i) * (τ' i).f k') := by
    rw [gs_lin p β z _ hk, gs_lin (β ≫ p) (𝟙 _) z _ hk', Category.id_comp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hτ i z k k' hk hk']
    ring
  rw [e, hσ z k k' hk hk', Units.mul_right_inj]

end

theorem exists_form_correction : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)), Flat f → ∀ (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (K : Type) [Field K] (g₀ : A →+* K), Function.Surjective g₀ → ∀ (X₀ : Scheme.{0}) (π : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ f (Spec.map (CommRingCat.ofHom g₀)) → ∀ (H₀ : LB X₀) (w₀ : LB.Iso H₀ (H.pull π)) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → w₀.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H₀).ι), (π) z ∈ (H).U k → z ∈ (H₀).U k' → gs (π) z _ ((s j).f k) = (Geo.Tor.gw (w₀) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s₀ j).f k'))) → ∀ t : ℕ, FirstCohomologyVanishes (pw H₀ t) → (∀ σ : LB.Sec (pw H₀ t), ∃ P : MvPolynomial (Fin (n + 1)) K, P.IsHomogeneous t ∧ ∀ k : H₀.ι, σ.f k = MvPolynomial.eval₂Hom (cst (f₀) ((H₀).U k)) (fun j => (s₀ j).f k) (P)) → ∀ (A' : Type) [CommRing A'] (g : A →+* A') (X' : Scheme.{0}) (β : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of A')), IsPullback β f' f (Spec.map (CommRingCat.ofHom g)) → ∀ (H' : LB X') (w : LB.Iso H' (H.pull β)) (s' : Fin (n + 1) → LB.Sec H'), H'.IsLB → w.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H').ι), (β) z ∈ (H).U k → z ∈ (H').U k' → gs (β) z _ ((s j).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k'))) → ∀ F : MvPolynomial (Fin (n + 1)) A, F.IsHomogeneous t → (∀ k : (H').ι, MvPolynomial.eval₂Hom (cst (β ≫ f) ((H').U k)) (fun j => (s' j).f k) (F) = 0) → ∃ G : MvPolynomial (Fin (n + 1)) A, G.IsHomogeneous t ∧ (∀ d, g (MvPolynomial.coeff d G) = 0) ∧ (∀ k : (H).ι, MvPolynomial.eval₂Hom (cst (f) ((H).U k)) (fun j => (s j).f k) (F - G) = 0) := by
  intro A _ _ _ X f hf H n s hH hva K _ g₀ hg₀ X₀ π f₀ hπ H₀ w₀ s₀ hH₀ hw₀ hs₀ t h1 hsurj A' _ g X' β f' hβ H' w s'
    hH' hw hs' F hF hF0
  have hM := isLB_pw hH (t : ℤ)
  have hM' := isLB_pw hH' (t : ℤ)
  obtain ⟨m, τ, hτ⟩ := GlobalTheory.T.exists_sections_basis_baseChange_h1Vanishing A X f hf ⟨H, hH, n, s, hva⟩ (AbLaw.pw H t) hM K g₀ hg₀ X₀ π f₀ hπ
    (AbLaw.pw H₀ t) (pwIso w₀ t) (isLB_pw hH₀ _) ((isGen_iff _).2 (pgen_pwIso ((isGen_iff _).1 hw₀) t)) h1
  choose Q hQ hτQ using fun i => GlobalTheory.T.sections_pow_veryAmple_are_forms_of_closedFibre A X f hf H n s hH hva K g₀ hg₀ X₀ π f₀ hπ H₀ w₀ s₀ hH₀ hw₀ hs₀ t h1
    hsurj (τ i)
  have hL := LB.isLB_pull hM (𝟙 X)
  have hu := CubePf.idIsoL_isGen hL
  choose P hP using fun σ => GlobalTheory.SecPullIso.exists_pull (𝟙 X) (AbLaw.pw H t) _ _ hM hL hu σ
  have hid : IsPullback (𝟙 X) f f (Spec.map (CommRingCat.ofHom (RingHom.id A))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨c, hc, -⟩ := hτ A (RingHom.id A) X (𝟙 X) f hid _ _ (fun i => P (τ i)) hL hu (fun i => hP (τ i))
    (P (formSec f s hF))
  have hc' : ∀ k, (formSec f s hF).f k = ∑ i, AbLaw.cst f ((AbLaw.pw H t).U k) (c i) * (τ i).f k := fun k =>
    fn_ext fun z hz => by
      obtain ⟨k', hk'⟩ := exists_chart hL z
      refine (germ_rel (hP _) (fun i => hP (τ i)) f c z k k' hz hk').2 ?_
      rw [Category.id_comp]
      exact congrArg _ (hc k')
  have hw' := (isGen_iff _).2 (pgen_pwIso ((isGen_iff _).1 hw) (t : ℤ))
  choose τ' hτ' using fun i => GlobalTheory.SecPullIso.exists_pull β (AbLaw.pw H t) _ _ hM hM' hw' (τ i)
  have hrel : Rel β (pwIso w t) (formSec f s hF) (formSec (β ≫ f) s' hF) := fun z k k' hk hk' =>
    (Rel.form hs' f hF z k k' hk hk').trans
      (congrArg (· * _) (congrArg Units.val (gw_pwIso w t (𝟙 _) z k k').symm))
  have hc'' : ∀ k', (formSec (β ≫ f) s' hF).f k' =
      ∑ i, AbLaw.cst f' ((AbLaw.pw H' t).U k') (g (c i)) * (τ' i).f k' := fun k' =>
    Eq.trans (fn_ext fun z hz => by
      obtain ⟨k, hk⟩ := exists_chart hM (β z)
      exact (germ_rel hrel hτ' f c z k k' hk hz).1 (congrArg _ (hc' k))) (by
      rw [hβ.w, const_comp]
      rfl)
  have hgc : (fun i => g (c i)) = 0 :=
    (hτ A' g X' β f' hβ _ _ τ' hM' hw' hτ' (formSec (β ≫ f) s' hF)).unique hc'' fun k' =>
      (hF0 k').trans (Finset.sum_eq_zero fun i _ =>
        (congrArg (· * (τ' i).f k') (map_zero (AbLaw.cst f' ((AbLaw.pw H' t).U k')))).trans (zero_mul _)).symm
  refine ⟨∑ i, MvPolynomial.C (c i) * Q i,
    MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => (hQ i).C_mul _, fun d => ?_, fun k => ?_⟩
  · rw [MvPolynomial.coeff_sum, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [MvPolynomial.coeff_C_mul, map_mul, congrFun hgc i, Pi.zero_apply, zero_mul]
  · rw [map_sub, sub_eq_zero, map_sum]
    refine (hc' k).trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [map_mul, MvPolynomial.eval₂Hom_C, hτQ i k]
    rfl

end GlobalTheory.FormCorr
