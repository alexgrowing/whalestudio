import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionsBasisBaseChangeH1VanishingStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionPull

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Degen.FormOnto

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

theorem cst_specMap (p : X ⟶ Spec (CommRingCat.of R')) (g : R →+* R') (U : X.Opens) :
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

def selfIso (L : LB X) : LB.Iso L (L.pull (𝟙 X)) :=
  ⟨fun p => res (show (L.pull (𝟙 X)).U p.1 ⊓ L.U p.2 ≤ L.U (p.1 PUnit.unit) ⊓ L.U p.2 from
    fun _ hx => ⟨mem_pull.1 hx.1, hx.2⟩) (L.g (p.1 PUnit.unit) p.2)⟩

theorem gw_selfIso (L : LB X) (r : Z ⟶ X) (z : Z) {j k : L.ι} (hj : r z ∈ L.U j) (hk : r z ∈ L.U k) :
    gw (selfIso L) r z j k = gm r z _ (L.g j k) :=
  gm_res r z _ (show r z ∈ (L.pull (𝟙 X)).U (fun _ => j) ⊓ L.U k from ⟨mem_pull.2 hj, hk⟩) _

theorem selfIso_isGen {L : LB X} (hL : L.IsLB) : (selfIso L).IsGen := by
  refine (isGen_iff _).2 fun Y r y j j' k k' hj hj' hk hk' => ?_
  rw [gw_selfIso L r y hj hk, gw_selfIso L r y hj' hk', Category.comp_id, mul_right_comm,
    gm_cocycle hL r y hj hj' hk', ← gm_cocycle hL r y hj hk hk', mul_inv_cancel_right]

theorem rel_self {L : LB X} (s : LB.Sec L) : Rel (𝟙 X) (selfIso L) s s := fun z k k' hk hk' => by
  rw [gw_selfIso L (𝟙 X) z hk hk']
  exact gs_sec s (𝟙 X) z hk hk'

theorem gs_cst (p : X ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : R) :
    gs r z U (AbLaw.cst p U a) = cstGerm (r ≫ p) z a := by
  have := gs_eval p r z U h (fun _ : Unit => 0) (MvPolynomial.C a)
  rwa [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂_C] at this

theorem gs_comb (p : X ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) {n : ℕ}
    (c : Fin n → R) (x : Fin n → Γ(X, U)) :
    gs r z U (∑ i, AbLaw.cst p U (c i) * x i) = ∑ i, cstGerm (r ≫ p) z (c i) * gs r z U (x i) := by
  rw [← gsHom_apply r z U h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, gsHom_apply, gsHom_apply, gs_cst p r z U h]

end GlobalTheory.Degen.FormOnto

open GlobalTheory.Degen.FormOnto in

theorem GlobalTheory.Degen.sections_pw_are_forms_of_closed_fibre : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)), Flat f → ∀ (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (K : Type) [Field K] (g₀ : A →+* K), Function.Surjective g₀ → ∀ (X₀ : Scheme.{0}) (π : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ f (Spec.map (CommRingCat.ofHom g₀)) → ∀ (H₀ : LB X₀) (w₀ : LB.Iso H₀ (H.pull π)) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → w₀.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H₀).ι), (π) z ∈ (H).U k → z ∈ (H₀).U k' → gs (π) z _ ((s j).f k) = (Geo.Tor.gw (w₀) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s₀ j).f k'))) → ∀ t : ℕ, FirstCohomologyVanishes (pw H₀ t) → (∀ σ : LB.Sec (pw H₀ t), ∃ P : MvPolynomial (Fin (n + 1)) K, P.IsHomogeneous t ∧ ∀ k : H₀.ι, σ.f k = MvPolynomial.eval₂Hom (cst (f₀) ((H₀).U k)) (fun j => (s₀ j).f k) (P)) → ∀ σ : LB.Sec (pw H t), ∃ P : MvPolynomial (Fin (n + 1)) A, P.IsHomogeneous t ∧ ∀ k : H.ι, σ.f k = MvPolynomial.eval₂Hom (cst (f) ((H).U k)) (fun j => (s j).f k) (P) := by
  intro A _ _ _ X f hf H n s hH hva K _ g₀ hg₀ X₀ π f₀ hπ H₀ w₀ s₀ hH₀ hw₀ hs t h1 hF σ
  have hM := isLB_pw hH (t : ℤ)
  have hM₀ := isLB_pw hH₀ (t : ℤ)
  have hw : (pwIso w₀ t).IsGen := (isGen_iff _).2 (pgen_pwIso ((isGen_iff _).1 hw₀) t)
  obtain ⟨m, τ, hτ⟩ := GlobalTheory.T.exists_sections_basis_baseChange_h1Vanishing A X f hf ⟨H, hH, n, s, hva⟩ _ hM K g₀ hg₀ X₀ π f₀ hπ _ (pwIso w₀ t) hM₀ hw h1
  choose τ₀ hτ₀ using fun i => GlobalTheory.SecPullIso.exists_pull π _ _ (pwIso w₀ t) hM hM₀ hw (τ i)
  have b₀ := hτ K g₀ X₀ π f₀ hπ _ (pwIso w₀ t) τ₀ hM₀ hw hτ₀
  have hid : IsPullback (𝟙 X) f f (Spec.map (CommRingCat.ofHom (RingHom.id A))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  have b := fun s' => (hτ A (RingHom.id A) X (𝟙 X) f hid _ (selfIso _) τ hM (selfIso_isGen hM)
    (fun i => rel_self (τ i)) s').exists
  choose P₀ hP₀ eP₀ using fun i => hF (τ₀ i)
  choose P hP eP using fun i => exists_lift g₀ hg₀ (hP₀ i)
  choose c hc using fun i => b (formSec f s (hP i))
  have key : ∀ i k', (τ₀ i).f k' = ∑ j, GlobalTheory.AbLaw.cst f₀ _ (g₀ (c i j)) * (τ₀ j).f k' := fun i k' => fn_ext fun z hz => by
    obtain ⟨k, hk⟩ := exists_chart hH (π z)
    have h := Rel.form (β := π) (w := w₀) hs f (hP i) z k k' hk hz
    rw [hπ.w, cst_specMap f₀, ← MvPolynomial.eval₂Hom_map_hom, eP i, ← eP₀ i k'] at h
    replace h := h.trans (congrArg (fun u => Units.val u * _) (gw_pwIso w₀ t (𝟙 _) z k k').symm)
    have h₂ := (congrArg (gs π z _) (hc i k)).trans (gs_comb f π z _ hk (c i) fun j => (τ j).f k)
    refine (Units.mul_right_inj (gw (pwIso w₀ t) (𝟙 _) z k k')).1 (h.symm.trans (h₂.trans ?_))
    refine Eq.trans ?_ (congrArg (_ * ·) (gs_comb f₀ (𝟙 _) z _ hz (fun j => g₀ (c i j)) fun j => (τ₀ j).f k').symm)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine (congrArg (_ * ·) (hτ₀ j z k k' hk hz)).trans ((mul_left_comm _ _ _).trans
      (congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) ?_ rfl)))
    rw [← gs_cst f₀ (𝟙 _) z _ hz, ← RingHom.comp_apply, ← cst_specMap f₀, ← hπ.w,
      gs_cst (π ≫ f) (𝟙 _) z _ hz, Category.id_comp]
  have hC : g₀.mapMatrix (Matrix.of c) = 1 := by
    ext i j
    have := (b₀ (τ₀ i)).unique (y₁ := fun j => g₀ (c i j)) (y₂ := fun j => if i = j then 1 else 0) (key i)
      (fun k => by simp [apply_ite])
    exact (congrFun this j).trans (Matrix.one_apply).symm
  have hu : IsUnit (Matrix.of c).det := by
    haveI := IsLocalHom.of_surjective g₀ hg₀
    apply IsUnit.of_map g₀
    rw [RingHom.map_det, hC, Matrix.det_one]
    exact isUnit_one
  obtain ⟨a, ha⟩ := b σ
  refine ⟨∑ i, MvPolynomial.C (Matrix.vecMul a (Matrix.of c)⁻¹ i) * P i,
    MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => (hP i).C_mul _, fun k => (ha k).trans ?_⟩
  have e : Matrix.vecMul (Matrix.vecMul a (Matrix.of c)⁻¹) (Matrix.of c) = a := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]
  generalize Matrix.vecMul a (Matrix.of c)⁻¹ = d at e ⊢
  subst e
  rw [map_sum]
  refine Eq.trans ?_ (Finset.sum_congr rfl fun i _ => ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (MvPolynomial.eval₂Hom_C _ _ _) (hc i k))).symm)
  simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
    _root_.mul_assoc]
  exact Finset.sum_comm
