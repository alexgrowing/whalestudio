import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenOfFrames
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecOfCompatible

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.Calc
open GlobalTheory.FrameGen GlobalTheory.ConstFam

variable {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {L' : LB G'.left}
  {L : LB G.left} {w : LB.Iso L' (L.pull φ)} {k : ℕ} {T' : Over S'} {T T₁ : Over S}

theorem prod_ext' {Z : Scheme.{0}} {a b : Z ⟶ (T ⊗ G).left} (h₁ : a ≫ (fst T G).left = b ≫ (fst T G).left)
    (h₂ : a ≫ (snd T G).left = b ≫ (snd T G).left) : a = b := pullback.hom_ext h₁ h₂

theorem exists_lift {Z : Scheme.{0}} (a : Z ⟶ T.left) (b : Z ⟶ G.left) (e : a ≫ T.hom = b ≫ G.hom) :
    ∃ H : Z ⟶ (T ⊗ G).left, H ≫ (fst T G).left = a ∧ H ≫ (snd T G).left = b :=
  ⟨pullback.lift a b e, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem prod_w : (fst T G).left ≫ T.hom = (snd T G).left ≫ G.hom := (Over.w _).trans (Over.w _).symm

theorem exists_prod (hφ : φ ≫ G.hom = G'.hom ≫ f) {h : T'.left ⟶ T.left} (hh : h ≫ T.hom = T'.hom ≫ f) :
    ∃ H : (T' ⊗ G').left ⟶ (T ⊗ G).left, H ≫ (fst T G).left = (fst T' G').left ≫ h ∧
      H ≫ (snd T G).left = (snd T' G').left ≫ φ :=
  exists_lift _ _ (by rw [Category.assoc, Category.assoc, hh, hφ, ← Category.assoc, ← Category.assoc, prod_w])

theorem thru_sv {h : T'.left ⟶ T.left} {s : LB.Sec (LPow G L (k : ℤ) T)} {s' : LB.Sec (LPow G' L' (k : ℤ) T')}
    (H : Thru w k h s s') {Z : Scheme.{0}} (r' : Z ⟶ (T' ⊗ G').left) (r : Z ⟶ (T ⊗ G).left)
    (h₁ : r ≫ (fst T G).left = r' ≫ (fst T' G').left ≫ h) (h₂ : r ≫ (snd T G).left = r' ≫ (snd T' G').left ≫ φ)
    (z : Z) {J J'} (hJ : Good L z J) (hJ' : Good L' z J') :
    sv G L k s r z J = (wVal w z J J' (r' ≫ (snd T' G').left) ^ k).val * sv G' L' k s' r' z J' := by
  rw [Units.val_pow_eq_pow_val]
  exact H Z r' r h₁ h₂ z J J' hJ hJ'

theorem existsUnique_thru (hφ : φ ≫ G.hom = G'.hom ≫ f) (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB)
    {h : T'.left ⟶ T.left} (hh : h ≫ T.hom = T'.hom ≫ f) (s : LB.Sec (LPow G L (k : ℤ) T)) :
    ∃! t : LB.Sec (LPow G' L' (k : ℤ) T'), Thru w k h s t := by
  obtain ⟨H, h₁, h₂⟩ := exists_prod hφ hh
  obtain ⟨t, ht⟩ := exists_secThrough (φ' := fun _ : Fin 1 => (snd T' G').left)
    (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (k : ℤ)) (h := H) hw hL hL' (fun _ => h₂.symm) s
  have key : Thru w k h s t := fun Z r' r e₁ e₂ z J J' hJ hJ' => by
    obtain rfl : r = r' ≫ H := prod_ext' (by rw [Category.assoc, h₁, e₁]) (by rw [Category.assoc, h₂, e₂])
    have a := ht.sval (fun _ => h₂.symm) r' hJ hJ'
    rwa [Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val] at a
  refine ⟨t, key, fun t' ht' => SecOps.sec_ext (sec_ext_val hL' fun y J' hJ' => ?_)⟩
  obtain ⟨J, hJ⟩ := exists_good' hL y
  have e₁ : H ≫ (fst T G).left = 𝟙 _ ≫ (fst T' G').left ≫ h := by rw [Category.id_comp, h₁]
  have e₂ : H ≫ (snd T G).left = 𝟙 _ ≫ (snd T' G').left ≫ φ := by rw [Category.id_comp, h₂]
  exact (Units.mul_right_inj _).1 ((thru_sv ht' _ H e₁ e₂ y hJ hJ').symm.trans (thru_sv key _ H e₁ e₂ y hJ hJ'))

theorem cmb_iff (hL : L.IsLB) {n : ℕ} (b : Fin n → LB.Sec (LPow G L (k : ℤ) T)) (a : Fin n → Γ(T.left, ⊤))
    (t : LB.Sec (LPow G L (k : ℤ) T)) :
    ((∀ j, t.f j = ∑ i, liftFun G _ (a i) * (b i).f j) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ G).left) (z : Z) (J), Good L z J →
      sv G L k t r z J = ∑ i, gT (r ≫ (fst T G).left) z (a i) * sv G L k (b i) r z J) ∧
    ((∀ (z : (T ⊗ G).left) (J), Good L z J →
      sv G L k t (𝟙 _) z J = ∑ i, gT (𝟙 _ ≫ (fst T G).left) z (a i) * sv G L k (b i) (𝟙 _) z J) →
      ∀ j, t.f j = ∑ i, liftFun G _ (a i) * (b i).f j) := by
  have key : ∀ t : LB.Sec (LPow G L (k : ℤ) T), (∀ j, t.f j = ∑ i, liftFun G _ (a i) * (b i).f j) →
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ G).left) (z : Z) (J), Good L z J →
      sv G L k t r z J = ∑ i, gT (r ≫ (fst T G).left) z (a i) * sv G L k (b i) r z J := fun t H Z r z J hJ =>
    (SectionScalarValuation.sval_lin (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (k : ℤ)) (s := t)
      (fun i => (fst T G).left.appTop.hom (a i)) b H r z hJ).trans
      (Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) ((gs_top _ _ _).trans (gT_comp _ _ _ _)) rfl)
  refine ⟨key t, fun H j => ?_⟩
  let σ := SectionLimit.linSec (fun i => (fst T G).left.appTop.hom (a i)) b
  exact sec_ext_val (s := t) (s' := σ) hL (fun y J hJ => (H y J hJ).trans (key σ (fun _ => rfl) _ _ y J hJ).symm) j

theorem cmb_of_lin (hφ : φ ≫ G.hom = G'.hom ≫ f) (hL : L.IsLB) (hL' : L'.IsLB) {g : T'.left ⟶ T₁.left}
    (hg : g ≫ T₁.hom = T'.hom ≫ f) {h : T₁ ⟶ T} {p : T'.left ⟶ T.left} (hp : p = g ≫ h.left) {n : ℕ}
    {b : Fin n → LB.Sec (LPow G L (k : ℤ) T)} {c : Fin n → Γ(T₁.left, ⊤)} {s : LB.Sec (LPow G L (k : ℤ) T₁)}
    {b' : Fin n → LB.Sec (LPow G' L' (k : ℤ) T')} {t : LB.Sec (LPow G' L' (k : ℤ) T')} (hl : Lin G L k h b c s)
    (hb : ∀ i, Thru w k p (b i) (b' i)) (ht : Thru w k g s t) :
    ∀ j, t.f j = ∑ i, liftFun G' _ (g.appTop.hom (c i)) * (b' i).f j := by
  subst hp
  refine (cmb_iff hL' b' _ t).2 fun z J' hJ' => ?_
  obtain ⟨J, hJ⟩ := exists_good' hL z
  obtain ⟨H, h₁, h₂⟩ := exists_prod hφ hg
  have e := lin_all hL hl H z hJ
  rw [thru_sv ht (𝟙 _) H (by rw [Category.id_comp, h₁]) (by rw [Category.id_comp, h₂]) z hJ hJ'] at e
  refine (Units.mul_right_inj _).1 (e.trans ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [thru_sv (hb i) (𝟙 _) (H ≫ (h ▷ G).left)
    (by rw [Category.id_comp, Category.assoc, wh_fst, ← Category.assoc, h₁, Category.assoc])
    (by rw [Category.id_comp, Category.assoc, wh_snd, h₂]) z hJ hJ', gT_comp, h₁, Category.id_comp,
    Category.id_comp, mul_left_comm]

theorem exists_thru_up (hφ : IsPullback φ G'.hom G.hom f) (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB)
    {g : T'.left ⟶ T₁.left} {p : T₁.left ⟶ T'.left} (hg : g ≫ T₁.hom = T'.hom ≫ f) (gp : g ≫ p = 𝟙 _) (pg : p ≫ g = 𝟙 _) :
    ∃ H : (T₁ ⊗ G).left ⟶ (T' ⊗ G').left, H ≫ (fst T' G').left ≫ g = (fst T₁ G).left ∧
      H ≫ (snd T' G').left ≫ φ = (snd T₁ G).left ∧
      ∀ t : LB.Sec (LPow G' L' (k : ℤ) T'), ∃ s : LB.Sec (LPow G L (k : ℤ) T₁), Thru w k g s t := by
  have hp : (snd T₁ G).left ≫ G.hom = (((fst T₁ G).left ≫ p) ≫ T'.hom) ≫ f := by
    rw [Category.assoc, ← hg, Category.assoc, ← Category.assoc p, pg, Category.id_comp, prod_w]
  obtain ⟨H, h₁, h₂⟩ := exists_lift (T := T') (G := G') ((fst T₁ G).left ≫ p) (hφ.lift _ _ hp) (hφ.lift_snd _ _ hp).symm
  have h₃ : H ≫ (snd T' G').left ≫ φ = (snd T₁ G).left := by rw [← Category.assoc, h₂, hφ.lift_fst]
  refine ⟨H, by rw [← Category.assoc, h₁, Category.assoc, pg, Category.comp_id], h₃, fun t => ?_⟩
  obtain ⟨t₁, ht₁⟩ := exists_sec_up (φ' := fun _ : Fin 1 => (snd T' G').left) (ε := fun _ => (k : ℤ))
    ((isGen_iff w).1 hw) hL hL' t
  obtain ⟨s, -, hs⟩ := SectionLimit.exists_pull t₁ H (fun _ : Fin 1 => (snd T₁ G).left) (fun _ => h₃)
  refine ⟨s, fun Z r' r e₁ e₂ z J J' hJ hJ' => ?_⟩
  have e₁' : r ≫ H ≫ (fst T' G').left = r' ≫ (fst T' G').left := by
    rw [h₁, ← Category.assoc, e₁, Category.assoc, Category.assoc, gp, Category.comp_id]
  have e : r ≫ H = r' := prod_ext' (by rw [Category.assoc, e₁']) (hφ.hom_ext
    (by rw [Category.assoc, Category.assoc, h₃, e₂, Category.assoc])
    (by rw [Category.assoc, Category.assoc, Category.assoc, ← prod_w, ← Category.assoc H, ← Category.assoc, e₁',
      Category.assoc]))
  have ST : SecThrough w (fun _ : Fin 1 => (snd T' G').left) (fun _ => (snd T' G').left ≫ φ) (fun _ => (k : ℤ)) t t₁
      (𝟙 _) := fun Z r z p q hp hq => by
    rw [Category.comp_id]
    exact ht₁ Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq)
  have a := ST.sval (fun _ => (Category.id_comp _).symm) r' hJ hJ'
  rw [Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val, Category.comp_id] at a
  exact (hs Z r z J hJ).trans ((congrArg (fun q => sval t₁ q z J) e).trans a)

theorem basis_thru (hφ : IsPullback φ G'.hom G.hom f) (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB)
    {g : T'.left ⟶ T₁.left} {p : T₁.left ⟶ T'.left} (hg : g ≫ T₁.hom = T'.hom ≫ f) (gp : g ≫ p = 𝟙 _) (pg : p ≫ g = 𝟙 _)
    {h : T₁ ⟶ T} {q : T'.left ⟶ T.left} (hq : q = g ≫ h.left) {n : ℕ}
    {b : Fin n → LB.Sec (LPow G L (k : ℤ) T)} {b' : Fin n → LB.Sec (LPow G' L' (k : ℤ) T')}
    (hB : BasisAlong G L k h b) (hb : ∀ i, Thru w k q (b i) (b' i)) (t : LB.Sec (LPow G' L' (k : ℤ) T')) :
    ∃! c : Fin n → Γ(T₁.left, ⊤), ∀ j, t.f j = ∑ i, liftFun G' _ (g.appTop.hom (c i)) * (b' i).f j := by
  obtain ⟨H, h₁, h₃, hs⟩ := exists_thru_up (k := k) hφ hw hL hL' hg gp pg
  obtain ⟨s, hst⟩ := hs t
  obtain ⟨c, hc, hu⟩ := hB s
  refine ⟨c, cmb_of_lin hφ.w hL hL' hg hq hc hb hst, fun c' hc' => hu c' fun z J hJ => ?_⟩
  subst hq
  obtain ⟨J', hJ'⟩ := exists_good' hL' z
  have a := thru_sv hst H (𝟙 _) ((Category.id_comp _).trans h₁.symm) ((Category.id_comp _).trans h₃.symm) z hJ hJ'
  refine a.trans ?_
  rw [(cmb_iff hL' b' _ t).1 hc' _ H z J' hJ', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have d := thru_sv (hb i) H (h ▷ G).left (by rw [wh_fst, ← h₁]; simp only [Category.assoc]) (by rw [wh_snd, h₃]) z hJ hJ'
  rw [mul_left_comm, ← d, gT_comp, Category.assoc, h₁]
  exact congrArg₂ (· * ·) (gs_top _ _ _).symm rfl

theorem appTop_fnR {R F : Type} [CommRing R] [CommRing F] (y : R →+* F) (c : R) :
    (spMap y).appTop.hom (fnR c) = fnR (y c) :=
  (congrArg (fun q => q.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom y))).symm

theorem main : ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] (L₀ : LB G₀.left), L₀.IsLB → ∀ (R : Type) [CommRing R] [IsDomain R] (x : Sp (FractionRing R) ⟶ Z) (A : PolAV (Sp (FractionRing R))) (φ : A.A.left ⟶ G₀.left) (w : LB.Iso A.L (L₀.pull φ)), IsGrpPullback A.A G₀ x φ → w.IsGen → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), (∀ (T : Over Z) (p : Sp F ⟶ T.left), p ≫ T.hom = jFK (R := R) F ≫ x → ∀ s : LB.Sec (LPow G₀ L₀ (k : ℤ) T), ∃! t : SecA A F k, Thru w k (T' := TFK (R := R) F) p s t) ∧ (∀ (R' : Type) [CommRing R'] (y : Sp R' ⟶ Z) (T : Over Z) (h : Over.mk y ⟶ T) (ga : R' →+* F), spMap ga ≫ y = jFK (R := R) F ≫ x → ∀ (n : ℕ) (b : Fin n → LB.Sec (LPow G₀ L₀ (k : ℤ) T)) (c : Fin n → R') (s : LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk y))) (bF : Fin n → SecA A F k) (t : SecA A F k), Lin G₀ L₀ k h b (fun i => fnR (c i)) s → (∀ i, Thru w k (T' := TFK (R := R) F) (spMap ga ≫ h.left) (b i) (bF i)) → Thru w k (T' := TFK (R := R) F) (T := Over.mk y) (spMap ga) s t → Cmb bF (fun i => ga (c i)) t) ∧ ∀ (K : Type) [Field K] (y : Sp K ⟶ Z) (ga : K →+* F), spMap ga ≫ y = jFK (R := R) F ≫ x → ∀ (n : ℕ) (τ : Fin n → LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk y))) (τF : Fin n → SecA A F k), AllBasis G₀ L₀ k y τ → (∀ i, Thru w k (T' := TFK (R := R) F) (T := Over.mk y) (spMap ga) (τ i) (τF i)) → ∀ t : SecA A F k, ∃! a : Fin n → F, Cmb τF a t := by
  intro Z G₀ _ L₀ hL R _ _ x A φ w gp hw F _ _ k
  refine ⟨fun T p hp s => existsUnique_thru (T' := TFK (R := R) F) gp.1.w hw hL A.isLB hp s,
    fun R' _ y T h ga e n b c s bF t hl hb ht j => ?_, fun K _ y ga e n τ τF hB hτ t => ?_⟩
  · have := cmb_of_lin (T' := TFK (R := R) F) (T₁ := Over.mk y) (g := spMap ga) gp.1.w hL A.isLB e rfl hl hb ht j
    exact this.trans (Finset.sum_congr rfl fun i _ =>
      congrArg (fun q => liftFun A.A _ q * (bF i).f j) (appTop_fnR ga (c i)))
  · obtain ⟨c, hc, hu⟩ := basis_thru (T' := TFK (R := R) F) (T₁ := Over.mk (jFK (R := R) F ≫ x)) (g := 𝟙 (Sp F))
      (p := 𝟙 (Sp F)) gp.1 hw hL A.isLB (Category.id_comp _) (Category.id_comp _) (Category.id_comp _)
      (Category.id_comp _).symm (hB F ga _ e) hτ t
    let ε := (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.symm
    refine ⟨fun i => ε.symm (c i), fun j => (hc j).trans (Finset.sum_congr rfl fun i _ => ?_), fun a ha => funext fun i => ?_⟩
    · exact congrArg (fun q => liftFun A.A _ q * (τF i).f j) (ε.apply_symm_apply (c i)).symm
    · exact ε.eq_symm_apply.2 (congrFun (hu (fun i => ε (a i)) ha) i)

end GlobalTheory.OneBasis.Calc
end
