import Mathlib
import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField
import Development.EtaleCohomology.KummerTheory.FinSHInv

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace UpperTheory.Cb.BimoduleProjections

def Same (q : ℕ) (i : ℤ) {B Y0 Y1 : Scheme.{0}} (p : Y0 ⟶ B) (g : Y1 ⟶ Y0) {S S' : Scheme.{0}} (t : S ⟶ B)
    (t' : S' ⟶ B) : Prop :=
  (∀ m, Subsingleton (Ht q (sch.obj (pullback p t)) m i) ↔ Subsingleton (Ht q (sch.obj (pullback p t')) m i)) ∧
  (∀ m, pl q i (fibMap g p t) m = 0 ↔ pl q i (fibMap g p t') m = 0) ∧
  (Function.Bijective (pl q i (pullback.snd (g ≫ p) t) 0) ↔ Function.Bijective (pl q i (pullback.snd (g ≫ p) t') 0))

section
variable {q : ℕ} {i : ℤ} {B Y0 Y1 : Scheme.{0}} {p : Y0 ⟶ B} {g : Y1 ⟶ Y0}

theorem Same.symm {S S' : Scheme.{0}} {t : S ⟶ B} {t' : S' ⟶ B} (h : Same q i p g t t') : Same q i p g t' t :=
  ⟨fun m => (h.1 m).symm, fun m => (h.2.1 m).symm, h.2.2.symm⟩

theorem Same.trans {S S' S'' : Scheme.{0}} {t : S ⟶ B} {t' : S' ⟶ B} {t'' : S'' ⟶ B} (h : Same q i p g t t')
    (h' : Same q i p g t' t'') : Same q i p g t t'' :=
  ⟨fun m => (h.1 m).trans (h'.1 m), fun m => (h.2.1 m).trans (h'.2.1 m), h.2.2.trans h'.2.2⟩
end

theorem sq_zero (q : ℕ) (i m : ℤ) {P P' Q Q' : Scheme.{0}} (f1 : P' ⟶ P) (f2 : Q' ⟶ Q) (u : P ⟶ Q) (v : P' ⟶ Q')
    (h : f1 ≫ u = v ≫ f2) (b1 : Function.Bijective (pl q i f1 m)) (b2 : Function.Bijective (pl q i f2 m)) :
    pl q i u m = 0 ↔ pl q i v m = 0 := by
  have key : ∀ x, pl q i f1 m (pl q i u m x) = pl q i v m (pl q i f2 m x) := fun x => by
    rw [← pl_comp, h, pl_comp]
  constructor
  · intro hu
    ext y
    obtain ⟨x, rfl⟩ := b2.2 y
    rw [← key, hu]; simp
  · intro hv
    ext x
    apply b1.1
    rw [key, hv]; simp

theorem sq_bij (q : ℕ) (i m : ℤ) {P P' Q Q' : Scheme.{0}} (f1 : P' ⟶ P) (f2 : Q' ⟶ Q) (u : P ⟶ Q) (v : P' ⟶ Q')
    (h : f1 ≫ u = v ≫ f2) (b1 : Function.Bijective (pl q i f1 m)) (b2 : Function.Bijective (pl q i f2 m)) :
    Function.Bijective (pl q i u m) ↔ Function.Bijective (pl q i v m) := by
  have key : (pl q i f1 m) ∘ (pl q i u m) = (pl q i v m) ∘ (pl q i f2 m) := funext fun x => by
    simp only [Function.comp]
    rw [← pl_comp, h, pl_comp]
  constructor
  · intro hu
    exact (Function.Bijective.of_comp_iff _ b2).1 (key ▸ b1.comp hu)
  · intro hv
    exact (Function.Bijective.of_comp_iff' b1 _).1 (key ▸ hv.comp b2)

theorem sub_iff (q : ℕ) (i m : ℤ) {P P' : Scheme.{0}} (f : P' ⟶ P) (b : Function.Bijective (pl q i f m)) :
    Subsingleton (Ht q (sch.obj P) m i) ↔ Subsingleton (Ht q (sch.obj P') m i) :=
  (Equiv.ofBijective _ b).subsingleton_congr

abbrev bm {Y B S S' : Scheme.{0}} (p : Y ⟶ B) (t : S ⟶ B) (a : S' ⟶ S) : pullback p (a ≫ t) ⟶ pullback p t :=
  pullback.map p (a ≫ t) p t (𝟙 _) a (𝟙 _) (by simp) (by simp)

@[reassoc] theorem bm_fst {Y B S S' : Scheme.{0}} (p : Y ⟶ B) (t : S ⟶ B) (a : S' ⟶ S) :
    bm p t a ≫ pullback.fst p t = pullback.fst p (a ≫ t) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc] theorem bm_snd {Y B S S' : Scheme.{0}} (p : Y ⟶ B) (t : S ⟶ B) (a : S' ⟶ S) :
    bm p t a ≫ pullback.snd p t = pullback.snd p (a ≫ t) ≫ a :=
  pullback.lift_snd _ _ _

@[reassoc] theorem fib_fst {Y1 Y0 B S : Scheme.{0}} (g : Y1 ⟶ Y0) (p : Y0 ⟶ B) (s : S ⟶ B) :
    fibMap g p s ≫ pullback.fst p s = pullback.fst (g ≫ p) s ≫ g :=
  pullback.lift_fst _ _ _

@[reassoc] theorem fib_snd {Y1 Y0 B S : Scheme.{0}} (g : Y1 ⟶ Y0) (p : Y0 ⟶ B) (s : S ⟶ B) :
    fibMap g p s ≫ pullback.snd p s = pullback.snd (g ≫ p) s :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

theorem fst_eq {Y B S S' : Scheme.{0}} (p : Y ⟶ B) (t : S ⟶ B) (a : S' ⟶ S) :
    pullback.fst (pullback.snd p t) a = (pullbackLeftPullbackSndIso p t a).hom ≫ bm p t a := by
  apply pullback.hom_ext
  · rw [Category.assoc, bm_fst, pullbackLeftPullbackSndIso_hom_fst]
  · rw [Category.assoc, bm_snd, pullbackLeftPullbackSndIso_hom_snd_assoc, pullback.condition]

theorem eqv_bm {q : ℕ} {i : ℤ} {Y B S S' : Scheme.{0}} (p : Y ⟶ B) (t : S ⟶ B) (a : S' ⟶ S)
    (h : Eqv _ (sch.map (pullback.fst (pullback.snd p t) a)) (tw q i)) : Eqv _ (sch.map (bm p t a)) (tw q i) := by
  rw [fst_eq, Functor.map_comp] at h
  exact LateralTheory.KummerTheory.AlgExtPf.eqv_cancel _ h (LateralTheory.KummerTheory.AlgExtPf.eqv_sch_iso _ _)

theorem eqv_base {q : ℕ} {i : ℤ} {S S' : Scheme.{0}} (a : S' ⟶ S)
    (h : Eqv _ (sch.map (pullback.fst (𝟙 S) a)) (tw q i)) : Eqv _ (sch.map a) (tw q i) := by
  have e : pullback.fst (𝟙 S) a = pullback.snd (𝟙 S) a ≫ a := by simpa using pullback.condition (f := 𝟙 S) (g := a)
  rw [e, Functor.map_comp] at h
  exact LateralTheory.KummerTheory.AlgExtPf.eqv_cancel _ h (LateralTheory.KummerTheory.AlgExtPf.eqv_sch_iso _ _)

theorem same_of {q : ℕ} {i : ℤ} {B Y0 Y1 S S' : Scheme.{0}} (p : Y0 ⟶ B) (g : Y1 ⟶ Y0) (t : S ⟶ B) (a : S' ⟶ S)
    (h0 : Eqv _ (sch.map (pullback.fst (pullback.snd p t) a)) (tw q i))
    (h1 : Eqv _ (sch.map (pullback.fst (pullback.snd (g ≫ p) t) a)) (tw q i))
    (h2 : Eqv _ (sch.map (pullback.fst (𝟙 S) a)) (tw q i)) : Same q i p g t (a ≫ t) := by
  have e0 := eqv_bm p t a h0
  have e1 := eqv_bm (g ≫ p) t a h1
  have e2 := eqv_base a h2
  refine ⟨fun m => sub_iff q i m _ (e0 m), fun m => ?_, ?_⟩
  · refine sq_zero q i m (bm (g ≫ p) t a) (bm p t a) _ _ ?_ (e1 m) (e0 m)
    apply pullback.hom_ext
    · simp only [Category.assoc, fib_fst, bm_fst, bm_fst_assoc]
    · simp only [Category.assoc, fib_snd, bm_snd, fib_snd_assoc]
  · exact sq_bij q i 0 (bm (g ≫ p) t a) a _ _ (bm_snd _ _ _) (e1 0) (e2 0)

theorem unit_of {k R : Type} [Field k] [CommRing R] {q : ℕ} (hq : IsUnit (q : k)) {B : Scheme.{0}} (b : B ⟶ Sp k)
    (t : Sp R ⟶ B) : IsUnit (q : R) := by
  simpa using hq.map (Spec.preimage (t ≫ b)).hom

theorem smooth_snd {Y B S : Scheme.{0}} (p : Y ⟶ B) (V : B.Opens) (hp : Smooth (p ∣_ V)) (t : S ⟶ B)
    (ht : Set.range t ⊆ V) : Smooth (pullback.snd p t) := by
  have hr : Set.range t ⊆ Set.range V.ι := by simpa using ht
  let t' : S ⟶ V := IsOpenImmersion.lift V.ι t hr
  have ht' : t' ≫ V.ι = t := IsOpenImmersion.lift_fac _ _ _
  have h3 : IsPullback (pullback.fst (p ∣_ V) t' ≫ (p ⁻¹ᵁ V).ι) (pullback.snd (p ∣_ V) t') p (t' ≫ V.ι) :=
    (IsPullback.of_hasPullback (p ∣_ V) t').paste_horiz (isPullback_morphismRestrict p V).flip
  rw [ht'] at h3
  have e : pullback.snd p t = h3.isoPullback.inv ≫ pullback.snd (p ∣_ V) t' := by
    rw [IsPullback.isoPullback_inv_snd]
  rw [e]
  infer_instance

theorem same_alg (h2 : E2) (h3 : E3) {q : ℕ} [NeZero q] {i : ℤ} {B Y0 Y1 : Scheme.{0}} (p : Y0 ⟶ B) (g : Y1 ⟶ Y0)
    (V : B.Opens) (hp : SmP p V) (hg : SmP (g ≫ p) V) {L M : Type} [Field L] [IsAlgClosed L] [Field M] [IsAlgClosed M]
    (hq : IsUnit (q : L)) (x : Sp L ⟶ B) (hx : Set.range x ⊆ V) (f : L →+* M) :
    Same q i p g x (Spec.map (CommRingCat.ofHom f) ≫ x) := by
  have := hp.1
  have := hg.1
  have := smooth_snd p V hp.2 x hx
  have := smooth_snd (g ≫ p) V hg.2 x hx
  exact same_of p g x _ (LateralTheory.Fin.SHInv.etale_cohomology_algebraic_extension_invariance_of_places h2 h3 q L M f hq (pullback.snd p x) i)
    (LateralTheory.Fin.SHInv.etale_cohomology_algebraic_extension_invariance_of_places h2 h3 q L M f hq (pullback.snd (g ≫ p) x) i)
    (LateralTheory.Fin.SHInv.etale_cohomology_algebraic_extension_invariance_of_places h2 h3 q L M f hq (𝟙 _) i)

theorem same_img (h2 : E2) (h3 : E3) {q : ℕ} [NeZero q] {i : ℤ} {B Y0 Y1 : Scheme.{0}} (p : Y0 ⟶ B) (g : Y1 ⟶ Y0)
    (V : B.Opens) (hp : SmP p V) (hg : SmP (g ≫ p) V) {L L' : Type} [Field L] [IsAlgClosed L] [Field L']
    [IsAlgClosed L'] (hq : IsUnit (q : L)) (hq' : IsUnit (q : L')) (x : Sp L ⟶ B) (x' : Sp L' ⟶ B)
    (hx : Set.range x ⊆ V) (hx' : Set.range x' ⊆ V) (u : Sp L) (u' : Sp L') (e : x u = x' u') :
    Same q i p g x x' := by
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback u u' e
  let W := pullback x x'
  let M := AlgebraicClosure (W.residueField z)
  let w : Sp M ⟶ W := Spec.map (CommRingCat.ofHom (algebraMap (W.residueField z) M)) ≫ W.fromSpecResidueField z
  let φ : CommRingCat.of L ⟶ CommRingCat.of M := Spec.preimage (w ≫ pullback.fst x x')
  let φ' : CommRingCat.of L' ⟶ CommRingCat.of M := Spec.preimage (w ≫ pullback.snd x x')
  have a1 : Spec.map (CommRingCat.ofHom φ.hom) = w ≫ pullback.fst x x' := Spec.map_preimage _
  have a2 : Spec.map (CommRingCat.ofHom φ'.hom) = w ≫ pullback.snd x x' := Spec.map_preimage _
  have s1 := same_alg h2 h3 p g V hp hg hq x hx (i := i) φ.hom
  have s2 := same_alg h2 h3 p g V hp hg hq' x' hx' (i := i) φ'.hom
  have e' : Spec.map (CommRingCat.ofHom φ.hom) ≫ x = Spec.map (CommRingCat.ofHom φ'.hom) ≫ x' := by
    rw [a1, a2]
    simp only [Category.assoc, pullback.condition]
  rw [e'] at s1
  exact s1.trans s2.symm

theorem residue_algClosed {T : Type} [CommRing T] [IsLocalRing T] (h : AIC T) : IsAlgClosed (IsLocalRing.ResidueField T) := by
  refine IsAlgClosed.of_exists_root _ fun f hf hi => ?_
  have hl : f ∈ Polynomial.lifts (IsLocalRing.residue T) :=
    Polynomial.map_surjective _ IsLocalRing.residue_surjective f |>.choose_spec ▸ ⟨_, rfl⟩
  obtain ⟨P, hP, hd, hm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hf
  have hd0 : 0 < P.natDegree := by
    rw [hd]; exact hi.natDegree_pos
  obtain ⟨a, ha⟩ := h P hm hd0
  refine ⟨IsLocalRing.residue T a, ?_⟩
  rw [← hP, Polynomial.eval_map, Polynomial.eval₂_hom, ha, map_zero]

theorem exists_strictHenselian_absolutely_closed_local_ring {B : Scheme.{0}} [IsIntegral B] (v : B) :
    ∃ (T : Type) (_ : CommRing T) (_ : IsDomain T) (_ : IsLocalRing T) (τ : Sp T ⟶ B),
      AIC T ∧ SH T ∧ IsAlgClosed (FractionRing T) ∧ IsAlgClosed (IsLocalRing.ResidueField T) ∧
      τ (IsLocalRing.closedPoint T) = v ∧
      ∀ u : Sp (FractionRing T), (Spec.map (CommRingCat.ofHom (algebraMap T (FractionRing T))) ≫ τ) u = genericPoint B := by
  let K := B.functionField
  let Ka := AlgebraicClosure K
  let sp0 := B.presheaf.stalkSpecializes (genericPoint_specializes v)
  let f : B.presheaf.stalk v →+* Ka := (algebraMap K Ka).comp sp0.hom
  obtain ⟨A, hA, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  let f' : B.presheaf.stalk v →+* A := f.codRestrict A.toSubring hA
  obtain ⟨hAIC, hH⟩ := LateralTheory.KummerTheory.ValAIC_of Ka A
  let e : FractionRing A ≃ₐ[A] Ka := FractionRing.algEquiv A Ka
  have hF : IsAlgClosed (FractionRing A) := IsAlgClosed.of_ringEquiv Ka _ e.symm.toRingEquiv
  have hR : IsAlgClosed (IsLocalRing.ResidueField A) := residue_algClosed hAIC
  refine ⟨A, inferInstance, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom f') ≫ B.fromSpecStalk v, hAIC, ⟨hH, inferInstance⟩, hF, hR, ?_, ?_⟩
  · have : Spec.map (CommRingCat.ofHom f') (IsLocalRing.closedPoint A) = IsLocalRing.closedPoint (B.presheaf.stalk v) :=
      IsLocalRing.comap_closedPoint f'
    change B.fromSpecStalk v (Spec.map (CommRingCat.ofHom f') (IsLocalRing.closedPoint A)) = v
    rw [this, Scheme.fromSpecStalk_closedPoint]
  · intro u
    let ψ : K →+* FractionRing A := (e.symm : Ka →+* FractionRing A).comp (algebraMap K Ka)
    have hψ : (CommRingCat.ofHom f' ≫ CommRingCat.ofHom (algebraMap A (FractionRing A))) =
        sp0 ≫ CommRingCat.ofHom ψ := by
      ext a
      change algebraMap A (FractionRing A) (f' a) = e.symm (algebraMap K Ka (sp0.hom a))
      rw [AlgEquiv.eq_symm_apply]
      exact e.commutes (f' a)
    have hc : Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A))) ≫ Spec.map (CommRingCat.ofHom f') ≫
        B.fromSpecStalk v = Spec.map (CommRingCat.ofHom ψ) ≫ B.fromSpecStalk (genericPoint B) := by
      rw [← Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes v), ← Category.assoc, ← Category.assoc,
        ← Spec.map_comp, ← Spec.map_comp, hψ]
      rfl
    rw [hc]
    change B.fromSpecStalk (genericPoint B) (Spec.map (CommRingCat.ofHom ψ) u) = _
    have : Spec.map (CommRingCat.ofHom ψ) u = IsLocalRing.closedPoint (B.presheaf.stalk (genericPoint B)) :=
      Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [this, Scheme.fromSpecStalk_closedPoint]

theorem range_comp_sub {S S' B : Scheme.{0}} (a : S' ⟶ S) (t : S ⟶ B) {V : Set B} (h : Set.range t ⊆ V) :
    Set.range (a ≫ t) ⊆ V := by
  rintro _ ⟨w, rfl⟩
  exact h ⟨a w, by simp⟩

theorem gen_pt (h2 : E2) (h3 : E3) {q : ℕ} [NeZero q] {i : ℤ} {k : Type} [Field k] (hq : IsUnit (q : k))
    {B Y0 Y1 : Scheme.{0}} [IsIntegral B] (b : B ⟶ Sp k) (p : Y0 ⟶ B) (g : Y1 ⟶ Y0) (V : B.Opens) (hp : SmP p V)
    (hg : SmP (g ≫ p) V) {L : Type} [Field L] [IsAlgClosed L] (x : Sp L ⟶ B) (hx : Set.range x ⊆ V) :
    ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F) (y : Sp F ⟶ B), Set.range y ⊆ V ∧ (∀ u, y u = genericPoint B) ∧
      Same q i p g x y := by
  obtain ⟨T, _, _, _, τ, hAIC, hSH, hF, hR, hc, hgen⟩ := exists_strictHenselian_absolutely_closed_local_ring (x (IsLocalRing.closedPoint L))
  have := hp.1
  have := hg.1
  have hτ : Set.range τ ⊆ V := by
    rintro _ ⟨w, rfl⟩
    have h1 : τ w ⤳ τ (IsLocalRing.closedPoint T) := (IsLocalRing.specializes_closedPoint w).map τ.continuous
    rw [hc] at h1
    exact h1.mem_open V.2 (hx ⟨_, rfl⟩)
  have hqT : IsUnit (q : T) := unit_of hq b τ
  let c : Sp (IsLocalRing.ResidueField T) ⟶ Sp T := Spec.map (CommRingCat.ofHom (IsLocalRing.residue T))
  let j : Sp (FractionRing T) ⟶ Sp T := Spec.map (CommRingCat.ofHom (algebraMap T (FractionRing T)))
  have := smooth_snd p V hp.2 τ hτ
  have := smooth_snd (g ≫ p) V hg.2 τ hτ
  have s1 : Same q i p g τ (c ≫ τ) :=
    same_of p g τ c (h2 q T hSH hqT (pullback.snd p τ) i) (h2 q T hSH hqT (pullback.snd (g ≫ p) τ) i)
      (h2 q T hSH hqT (𝟙 _) i)
  have s2 : Same q i p g τ (j ≫ τ) :=
    same_of p g τ j (h3 q T hAIC hqT (pullback.snd p τ) i) (h3 q T hAIC hqT (pullback.snd (g ≫ p) τ) i)
      (h3 q T hAIC hqT (𝟙 _) i)
  have hcl : c (IsLocalRing.closedPoint (IsLocalRing.ResidueField T)) = IsLocalRing.closedPoint T :=
    IsLocalRing.comap_closedPoint (IsLocalRing.residue T)
  have s3 : Same q i p g x (c ≫ τ) :=
    same_img h2 h3 p g V hp hg (unit_of hq b x) (unit_of hq b (c ≫ τ)) x (c ≫ τ) hx (range_comp_sub c τ hτ)
      (IsLocalRing.closedPoint L) (IsLocalRing.closedPoint (IsLocalRing.ResidueField T)) (by change x _ = τ (c _); rw [hcl, hc])
  exact ⟨FractionRing T, inferInstance, hF, j ≫ τ, range_comp_sub j τ hτ, hgen, s3.trans (s1.symm.trans s2)⟩

theorem same_all (h2 : E2) (h3 : E3) {q : ℕ} [NeZero q] {i : ℤ} {k : Type} [Field k] (hq : IsUnit (q : k))
    {B Y0 Y1 : Scheme.{0}} [IsIntegral B] (b : B ⟶ Sp k) (p : Y0 ⟶ B) (g : Y1 ⟶ Y0) (V : B.Opens) (hp : SmP p V)
    (hg : SmP (g ≫ p) V) {L L' : Type} [Field L] [IsAlgClosed L] [Field L'] [IsAlgClosed L'] (x : Sp L ⟶ B)
    (x' : Sp L' ⟶ B) (hx : Set.range x ⊆ V) (hx' : Set.range x' ⊆ V) : Same q i p g x x' := by
  obtain ⟨F, _, _, y, hy, hyg, s⟩ := gen_pt h2 h3 hq b p g V hp hg (i := i) x hx
  obtain ⟨F', _, _, y', hy', hyg', s'⟩ := gen_pt h2 h3 hq b p g V hp hg (i := i) x' hx'
  exact s.trans ((same_img h2 h3 p g V hp hg (unit_of hq b y) (unit_of hq b y') y y' hy hy'
    (IsLocalRing.closedPoint F) (IsLocalRing.closedPoint F') ((hyg _).trans (hyg' _).symm)).trans s'.symm)

theorem leaf : LeafSpec := by
  intro hy q _ k _ hq i B Y0 Y1 _ b V p g hp hg Ω _ _ s hs C0 C1 c0 γ u0 u1 P0 P1 hc A _ t hA ht
  obtain ⟨-, -, -, -, -, -, -, a9, -, -, -, b2, b3, -, -, -, -, -, -, -, -, -, -, -, -, e2, e3⟩ := hy
  have := hp.1
  have := hg.1
  have hA' := hA
  obtain ⟨hHL, hsc⟩ := hA'
  have hqA : IsUnit (q : A) := unit_of hq b t
  let res : Sp (IsLocalRing.ResidueField A) ⟶ Sp A := Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
  have hqκ : IsUnit (q : IsLocalRing.ResidueField A) := unit_of hq b (res ≫ t)
  haveI : IsPurelyInseparable (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A)) :=
    (isSepClosed_iff_isPurelyInseparable_algebraicClosure _ _).mp hsc
  let alg : Sp (AlgebraicClosure (IsLocalRing.ResidueField A)) ⟶ Sp (IsLocalRing.ResidueField A) :=
    Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))))
  have s1 : Same q i p g t (res ≫ t) :=
    same_of p g t res (e2 q A hA hqA (pullback.snd p t) i) (e2 q A hA hqA (pullback.snd (g ≫ p) t) i)
      (e2 q A hA hqA (𝟙 _) i)
  have s2 : Same q i p g (res ≫ t) (alg ≫ res ≫ t) :=
    same_of p g (res ≫ t) alg (LateralTheory.Fin.SHInv.etale_purely_inseparable_extension_cohomology_invariant_in_henselizati a9 b2 b3 q _ _ hqκ (pullback.snd p (res ≫ t)) i)
      (LateralTheory.Fin.SHInv.etale_purely_inseparable_extension_cohomology_invariant_in_henselizati a9 b2 b3 q _ _ hqκ (pullback.snd (g ≫ p) (res ≫ t)) i)
      (LateralTheory.Fin.SHInv.etale_purely_inseparable_extension_cohomology_invariant_in_henselizati a9 b2 b3 q _ _ hqκ (𝟙 _) i)
  have hx : Set.range (alg ≫ res ≫ t) ⊆ V := range_comp_sub alg _ (range_comp_sub res t ht)
  have s3 : Same q i p g s (alg ≫ res ≫ t) := same_all e2 e3 hq b p g V hp hg s _ hs hx
  have S : Same q i p g s t := s3.trans (s2.symm.trans s1.symm)
  let e0 := P0.isoPullback
  let e1 := P1.isoPullback
  have b0 : ∀ m, Function.Bijective (pl q i e0.hom m) := LateralTheory.KummerTheory.AlgExtPf.eqv_sch_iso _ _
  have b1 : ∀ m, Function.Bijective (pl q i e1.hom m) := LateralTheory.KummerTheory.AlgExtPf.eqv_sch_iso _ _
  have bi : ∀ m, Function.Bijective (pl q i (𝟙 (Sp Ω)) m) := LateralTheory.KummerTheory.AlgExtPf.eqv_sch_iso _ _
  have hsq : e1.hom ≫ fibMap g p s = γ ≫ e0.hom := by
    apply pullback.hom_ext
    · simp only [Category.assoc, fib_fst, e0, e1, IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_fst_assoc, hc]
    · simp only [Category.assoc, fib_snd, e0, e1, IsPullback.isoPullback_hom_snd]
  have hsn : e1.hom ≫ pullback.snd (g ≫ p) s = (γ ≫ c0) ≫ 𝟙 _ := by
    simp only [Category.comp_id, e1, IsPullback.isoPullback_hom_snd]
  refine ⟨fun m h => (S.1 m).1 ((sub_iff q i m e0.hom (b0 m)).2 h), fun m h => (S.2.1 m).1 ?_, fun h => S.2.2.1 ?_⟩
  · exact (sq_zero q i m e1.hom e0.hom _ _ hsq (b1 m) (b0 m)).2 h
  · exact (sq_bij q i 0 e1.hom (𝟙 _) _ _ hsn (b1 0) (bi 0)).2 h

end UpperTheory.Cb.BimoduleProjections

end

theorem UpperTheory.Cb.geometric_fibre_cohomology_constant :
    LateralTheory.E.E4.LeafSpec := UpperTheory.Cb.BimoduleProjections.leaf
