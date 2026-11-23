import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SecAlg

variable {X X₁ X₂ Z : Scheme.{0}} {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂]

def germCst (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (a : R) : Z.presheaf.stalk z :=
  gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)

theorem germCst_comp (q : Z ⟶ Spec (CommRingCat.of R₂)) (h : R₁ →+* R₂) (z : Z) (a : R₁) :
    germCst (q ≫ Spec.map (CommRingCat.ofHom h)) z a = germCst q z (h a) := by
  refine (gs_pull q (Spec.map (CommRingCat.ofHom h)) z ⊤ trivial _).symm.trans ?_
  exact congrArg (gs q z ⊤) (congrArg (fun t => t.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom h))).symm

theorem gs_cst (p : X ⟶ Spec (CommRingCat.of R)) (W : X.Opens) (r : Z ⟶ X) (z : Z) (hz : r z ∈ W) (a : R) :
    gs r z W (GlobalTheory.AbLaw.cst p W a) = germCst (r ≫ p) z a :=
  (gs_res r z le_top hz _).trans (gs_pull r p z ⊤ trivial _)

variable {p : X ⟶ Spec (CommRingCat.of R)} {N : LB X} (P : Perf p N)

def Given (π : X₁ ⟶ X) (f : X₁ ⟶ Spec (CommRingCat.of R₁)) (v : Fin P.a → R₁) (s : LB.Sec (N.pull π)) : Prop :=
  ∀ i, rs X₁ (le_pull N π (P.le i)) (s.f (fun _ => P.ch i)) =
    ∑ k, GlobalTheory.AbLaw.cst f (π ⁻¹ᵁ P.W i) (v k) * (π.app (P.W i)).hom (P.u k i)

def comb (ψ : Z ⟶ X) (z : Z) (J : (Z ⟶ X) → N.ι) (i : P.I) (c : Fin P.a → Z.presheaf.stalk z) :
    Z.presheaf.stalk z :=
  (gm ψ z (N.U (J ψ) ⊓ N.U (P.ch i)) (N.g (J ψ) (P.ch i))).val * ∑ k, c k * gs ψ z (P.W i) (P.u k i)

variable {P}

theorem Given.sval {π : X₁ ⟶ X} {f : X₁ ⟶ Spec (CommRingCat.of R₁)} {v : Fin P.a → R₁} {s : LB.Sec (N.pull π)}
    (hs : Given P π f v s) (r : Z ⟶ X₁) (z : Z) {J : (Z ⟶ X) → N.ι} (hJ : Good N z J) (i : P.I)
    (hi : (r ≫ π) z ∈ P.W i) :
    sval s r z J = comb P (r ≫ π) z J i (fun k => germCst (r ≫ f) z (v k)) := by
  have hm : r z ∈ π ⁻¹ᵁ P.W i := hi
  refine (sec_trans s r z (hJ.mem _ r) (le_pull N π (P.le i) hm)).trans (congrArg₂ (· * ·) ?_ ?_)
  · simp only [trF, Finset.univ_unique, Finset.prod_singleton, zpow_one]
  · refine (gs_res r z (le_pull N π (P.le i)) hm _).symm.trans ((congrArg (gs r z _) (hs i)).trans ?_)
    rw [gs_eq r z _ hm, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => (gs_eq r z _ hm _).symm.trans ((gs_mul r z _ hm _ _).trans ?_)
    exact congrArg₂ (· * ·) (gs_cst f _ r z hm _) (gs_pull r π z _ hi _)

theorem Given.sval_eq {π₁ : X₁ ⟶ X} {f₁ : X₁ ⟶ Spec (CommRingCat.of R₁)} {v : Fin P.a → R₁}
    {s₁ : LB.Sec (N.pull π₁)} {π₂ : X₂ ⟶ X} {f₂ : X₂ ⟶ Spec (CommRingCat.of R₂)} {s₂ : LB.Sec (N.pull π₂)}
    (h : R₁ →+* R₂) (r : X₂ ⟶ X₁) (hπ : r ≫ π₁ = π₂) (hf : r ≫ f₁ = f₂ ≫ Spec.map (CommRingCat.ofHom h))
    (h₁ : Given P π₁ f₁ v s₁) (h₂ : Given P π₂ f₂ (fun k => h (v k)) s₂) (z : X₂) {J : (X₂ ⟶ X) → N.ι}
    (hJ : Good N z J) : Geo.Tor.sval s₁ r z J = Geo.Tor.sval s₂ (𝟙 _) z J := by
  subst hπ
  have hz : (r ≫ π₁) z ∈ ⨆ i, P.W i := by rw [P.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  rw [h₁.sval r z hJ i hi, h₂.sval (𝟙 _) z hJ i hi, Category.id_comp, Category.id_comp, hf]
  simp only [germCst_comp]

theorem sec_ext {M : LB X} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  obtain ⟨a, ha⟩ := s
  obtain ⟨b, hb⟩ := s'
  obtain rfl : a = b := funext h
  rfl

theorem mulVec_map {a b : ℕ} (D : Matrix (Fin b) (Fin a) R) (g : R →+* R₁) (h : R₁ →+* R₂) {g' : R →+* R₂}
    (hg : h.comp g = g') (v : Fin a → R₁) (j : Fin b) :
    (D.map g').mulVec (fun k => h (v k)) j = h ((D.map g).mulVec v j) := by
  subst hg
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, RingHom.comp_apply]

theorem sval_eq_iff (hN : N.IsLB) {g₁ : R →+* R₁} {g₂ : R →+* R₂}
    {π₁ : X₁ ⟶ X} {f₁ : X₁ ⟶ Spec (CommRingCat.of R₁)} {π₂ : X₂ ⟶ X} {f₂ : X₂ ⟶ Spec (CommRingCat.of R₂)}
    {E₁ : {v : Fin P.a → R₁ // (P.D₀.map g₁).mulVec v = 0} ≃ LB.Sec (N.pull π₁)}
    {E₂ : {v : Fin P.a → R₂ // (P.D₀.map g₂).mulVec v = 0} ≃ LB.Sec (N.pull π₂)}
    (H₁ : ∀ v, Given P π₁ f₁ v.1 (E₁ v)) (H₂ : ∀ v, Given P π₂ f₂ v.1 (E₂ v))
    (h : R₁ →+* R₂) (hg : h.comp g₁ = g₂) (r : X₂ ⟶ X₁) (hπ : r ≫ π₁ = π₂)
    (hf : r ≫ f₁ = f₂ ≫ Spec.map (CommRingCat.ofHom h)) (s₁ : LB.Sec (N.pull π₁)) (s₂ : LB.Sec (N.pull π₂)) :
    (∀ z J, Good N z J → sval s₁ r z J = sval s₂ (𝟙 _) z J) ↔
      ∀ k, h ((E₁.symm s₁).1 k) = (E₂.symm s₂).1 k := by
  obtain ⟨v₁, rfl⟩ := E₁.surjective s₁
  obtain ⟨v₂, rfl⟩ := E₂.surjective s₂
  rw [E₁.symm_apply_apply, E₂.symm_apply_apply]
  let w : {v : Fin P.a → R₂ // (P.D₀.map g₂).mulVec v = 0} := ⟨fun k => h (v₁.1 k), funext fun j => by
    rw [mulVec_map P.D₀ g₁ h hg, v₁.2, Pi.zero_apply, Pi.zero_apply, map_zero]⟩
  have key : ∀ z J, Good N z J → sval (E₁ v₁) r z J = sval (E₂ w) (𝟙 _) z J :=
    fun z J hJ => Given.sval_eq h r hπ hf (H₁ v₁) (H₂ w) z hJ
  constructor
  · intro H k
    have : E₂ w = E₂ v₂ := sec_ext (sec_ext_val hN fun y J hJ => (key y J hJ).symm.trans (H y J hJ))
    exact congrFun (congrArg Subtype.val (E₂.injective this)) k
  · intro H
    obtain rfl : w = v₂ := Subtype.ext (funext H)
    exact key

theorem eq_of_forall_mk (I : Ideal R) [IsHausdorff I R] {x y : R}
    (h : ∀ e : ℕ, Ideal.Quotient.mk (I ^ (e + 1)) x = Ideal.Quotient.mk (I ^ (e + 1)) y) : x = y := by
  refine sub_eq_zero.1 (IsHausdorff.haus' (I := I) _ fun n => ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact Ideal.pow_le_pow_right (Nat.le_succ n) (Ideal.Quotient.eq.1 (h n))

theorem exists_lim (I : Ideal R) [IsPrecomplete I R] (x : ∀ e : ℕ, R ⧸ I ^ (e + 1))
    (hx : ∀ e, Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) (x (e + 1)) = x e) :
    ∃ y : R, ∀ e, Ideal.Quotient.mk (I ^ (e + 1)) y = x e := by
  choose a ha using fun e => Ideal.Quotient.mk_surjective (x e)
  have step : ∀ e, a e - a (e + 1) ∈ I ^ (e + 1) := fun e => by
    refine Ideal.Quotient.eq.1 ?_
    rw [ha, ← hx e, ← ha (e + 1), Ideal.Quotient.factor_mk]
  have cau : ∀ m n, m ≤ n → a m - a n ∈ I ^ (m + 1) := fun m n hmn => by
    induction n, hmn using Nat.le_induction with
    | base => rw [sub_self]; exact zero_mem _
    | succ n hmn ih =>
      have := add_mem ih (Ideal.pow_le_pow_right (Nat.succ_le_succ hmn) (step n))
      rwa [sub_add_sub_cancel] at this
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) a (fun {m n} hmn => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    exact Ideal.pow_le_pow_right (Nat.le_succ m) (cau m n hmn))
  refine ⟨L, fun e => ?_⟩
  have := hL (e + 1)
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
  have h₂ := add_mem (step e) this
  rw [sub_add_sub_cancel] at h₂
  rw [← ha e]
  exact (Ideal.Quotient.eq.2 h₂).symm

theorem existsUnique_sec : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : Over (Spec (CommRingCat.of R))), Smooth Y.hom → IsProjBy Y.hom → ∀ N : LB Y.left, N.IsLB → ∀ f : ∀ e, LB.Sec (N.pull (fstG I e Y).left), (∀ e z J, Good N z J → sval (f (e + 1)) (thickMap R I e Y) z J = sval (f e) (𝟙 _) z J) → ∃! s : LB.Sec (N.pull (𝟙 Y.left)), ∀ e z J, Good N z J → sval s (fstG I e Y).left z J = sval (f e) (𝟙 _) z J := by
  intro R _ _ I hI Y hs hp N hN f hf
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj R Y.left Y.hom hs hp N hN
  have pb₀ : IsPullback (𝟙 Y.left) Y.hom Y.hom (Spec.map (CommRingCat.ofHom (RingHom.id R))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨E₀, H₀⟩ := P.sec R (RingHom.id R) Y.left (𝟙 _) Y.hom pb₀
  choose E H using fun e => P.sec (R ⧸ I ^ (e + 1)) (Ideal.Quotient.mk _) _ (fstG I e Y).left
    (thickObj R I e Y).hom (IsPullback.of_hasPullback Y.hom (thick R I e))
  have c₁ : ∀ e k, Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)))
      (((E (e + 1)).symm (f (e + 1))).1 k) = ((E e).symm (f e)).1 k := fun e =>
    (sval_eq_iff (P := P) hN (H (e + 1)) (H e) _ (Ideal.Quotient.factor_comp_mk _) (thickMap R I e Y)
      ((pullback.lift_fst _ _ _).trans (Category.comp_id _)) (pullback.lift_snd _ _ _) _ _).1 (hf e)
  have c₂ : ∀ e (s : LB.Sec (N.pull (𝟙 Y.left))),
      (∀ z J, Good N z J → sval s (fstG I e Y).left z J = sval (f e) (𝟙 _) z J) ↔
        ∀ k, Ideal.Quotient.mk (I ^ (e + 1)) ((E₀.symm s).1 k) = ((E e).symm (f e)).1 k := fun e s =>
    sval_eq_iff (P := P) hN H₀ (H e) _ (RingHom.comp_id _) (fstG I e Y).left (Category.comp_id _)
      pullback.condition _ _
  choose v hv using fun k => exists_lim I (fun e => ((E e).symm (f e)).1 k) (fun e => c₁ e k)
  have hv₀ : (P.D₀.map (RingHom.id R)).mulVec v = 0 := funext fun j => eq_of_forall_mk I fun e => by
    rw [← mulVec_map P.D₀ (RingHom.id R) _ (RingHom.comp_id _), Pi.zero_apply, map_zero]
    simp only [hv]
    exact congrFun ((E e).symm (f e)).2 j
  refine ⟨E₀ ⟨v, hv₀⟩, fun e => (c₂ e _).2 fun k => ?_, fun s hs => ?_⟩
  · rw [E₀.symm_apply_apply]
    exact hv k e
  · refine (E₀.symm_apply_eq).1 (Subtype.ext (funext fun k => eq_of_forall_mk I fun e => ?_))
    exact ((c₂ e s).1 (hs e) k).trans (hv k e).symm

end GlobalTheory.SecAlg
