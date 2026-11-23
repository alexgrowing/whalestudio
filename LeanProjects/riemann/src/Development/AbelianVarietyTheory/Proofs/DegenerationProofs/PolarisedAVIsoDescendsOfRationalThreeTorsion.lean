import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RatTors
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescOfSmoothOfGeometricPoints
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolAVIsoExtendsOfIsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenRelNeZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleIsoExtendOfNormalBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfRigidifiedFaithfullyFlatDescent
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsPullbackOfFpqcLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.PolIsoDescent

open GlobalTheory.GenSpread

theorem flat_surjective {F C : Type} [Field F] [Field C] (i : Sp F ⟶ Sp C) : Flat i ∧ Surjective i :=
  have : Subsingleton (Sp C) := inferInstanceAs (Subsingleton (PrimeSpectrum C))
  ⟨inferInstance, ⟨fun _ => ⟨(default : PrimeSpectrum F), Subsingleton.elim _ _⟩⟩⟩

theorem charZero_of_hom {F C : Type} [Field F] [Field C] [CharZero C] (i : Sp F ⟶ Sp C) : CharZero F :=
  charZero_of_injective_ringHom (f := (Spec.preimage i).hom) (RingHom.injective _)

theorem exists_torsion_of_algClosed (hM : MulNSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) {F C : Type}
    [Field F] [IsAlgClosed F] [Field C] [IsAlgClosed C] [CharZero C] (i : Sp F ⟶ Sp C) (t : Sp C ⟶ S) {n : ℕ}
    (hn : 1 ≤ n) (x : Over.mk (i ≫ t) ⟶ P.A) (hx : x ^ n = 1) :
    ∃ z : Over.mk t ⟶ P.A, z ^ n = 1 ∧ x.left = i ≫ z.left := by
  have := charZero_of_hom i
  obtain ⟨_, _⟩ := flat_surjective i
  have : Epi i := Flat.epi_of_flat_of_surjective _
  have h := (hM S P n hn).2.2.2.2
  have h₁ := h F (i ≫ t) (Nat.cast_ne_zero.2 (by omega))
  have h₂ := h C t (Nat.cast_ne_zero.2 (by omega))
  let ρ : Over.mk (i ≫ t) ⟶ Over.mk t := Over.homMk i rfl
  let r : {x : Over.mk t ⟶ P.A // x ^ n = 1} → {x : Over.mk (i ≫ t) ⟶ P.A // x ^ n = 1} := fun z =>
    ⟨ρ ≫ z.1, by rw [← MonObj.comp_pow, z.2, MonObj.comp_one]⟩
  have hr : Function.Injective r := fun a b e => Subtype.ext (Over.OverMorphism.ext
    ((cancel_epi i).1 (congrArg (fun q => q.1.left) e)))
  have : Finite {x : Over.mk (i ≫ t) ⟶ P.A // x ^ n = 1} :=
    Nat.finite_of_card_ne_zero (by rw [h₁]; positivity)
  obtain ⟨z, hz⟩ := ((Nat.bijective_iff_injective_and_card r).2 ⟨hr, h₂.trans h₁.symm⟩).2 ⟨x, hx⟩
  exact ⟨z.1, z.2, (congrArg (fun q => q.1.left) hz).symm⟩

theorem eq_of_torsion (hL : Laws) {S : Scheme.{0}} (P : PolAV S) {F : Type} [Field F] [IsAlgClosed F]
    (W : PolAV (Sp F)) {s : Sp F ⟶ S} {f₁ f₂ : W.A.left ⟶ P.A.left} (h₁ : IsGrpPullback W.A P.A s f₁)
    (h₂ : IsGrpPullback W.A P.A s f₂) (l₁ : LBIso W.L (P.L.pull f₁)) (l₂ : LBIso W.L (P.L.pull f₂)) {M : ℕ}
    (hM : 3 ≤ M) (hF : (M : F) ≠ 0)
    (h : ∀ y : Over.mk (𝟙 (Sp F)) ⟶ W.A, y ^ M = 1 → y.left ≫ f₁ = y.left ≫ f₂) : f₁ = f₂ := by
  obtain ⟨θ, hθ, e⟩ := grpPullback_iso h₁ h₂
  obtain ⟨w, hw⟩ := l₁.trans W.isLB (pull_isLB P.isLB _) (pull_isLB W.isLB _)
    (lbIso_pull_of_lbIso l₂ θ.hom.left e.symm).symm
  have := MatchRigid.aut_eq_id hL W (𝟙 _) hM hF θ w hw fun y hy =>
    Over.OverMorphism.ext (h₂.1.hom_ext (by rw [Over.comp_left, Category.assoc, e, h y hy]) (by rw [Over.w, Over.w]))
  rw [← e, this, Over.id_left, Category.id_comp]

theorem comp_eq_of_rational (hL : Laws) {S U : Scheme.{0}} [IsLocallyNoetherian S] (B B' : PolAV S) {C : Type}
    [Field C] [IsAlgClosed C] [CharZero C] (κ : Sp C ⟶ U) (j : U ⟶ S)
    (rB : ∀ x : Over.mk (κ ≫ j) ⟶ B.A, x ^ 3 = 1 → ∃ x₀ : U ⟶ B.A.left, x.left = κ ≫ x₀)
    (rB' : ∀ x : Over.mk (κ ≫ j) ⟶ B'.A, x ^ 3 = 1 → ∃ x₀ : U ⟶ B'.A.left, x.left = κ ≫ x₀)
    {Q : Over (Sp C)} [GrpObj Q] {f : Q.left ⟶ B.A.left} {f' : Q.left ⟶ B'.A.left}
    (hf : IsGrpPullback Q B.A (κ ≫ j) f) (hf' : IsGrpPullback Q B'.A (κ ≫ j) f')
    (hl : LBIso (B'.L.pull f') (B.L.pull f)) {F : Type} [Field F] [IsAlgClosed F] (x x' : Sp F ⟶ Q.left)
    (e : x ≫ f' = x' ≫ f') (e' : (x ≫ Q.hom) ≫ κ = (x' ≫ Q.hom) ≫ κ) : x ≫ f = x' ≫ f := by
  have := charZero_of_hom (x ≫ Q.hom)
  obtain ⟨W, h, hh, -, hm, hw⟩ := hL.polBaseChange S _ (((x ≫ Q.hom) ≫ κ) ≫ j) B'
  have hp : IsGrpPullback W.A B'.A (((x ≫ Q.hom) ≫ κ) ≫ j) h := ⟨hh, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = toBase hh.w x), (Over.OverMorphism.ext hy : y₀ = toBase hh.w y), ← hm]
    rfl⟩
  have key : ∀ i : Sp F ⟶ Sp C, (x ≫ Q.hom) ≫ κ = i ≫ κ → ∃ a : W.A.left ⟶ Q.left, a ≫ f' = h ∧
      a ≫ Q.hom = W.A.hom ≫ i ∧ IsGrpPullback W.A B.A (((x ≫ Q.hom) ≫ κ) ≫ j) (a ≫ f) ∧
      LBIso W.L (B.L.pull (a ≫ f)) := fun i hi => by
    have hi' : ((x ≫ Q.hom) ≫ κ) ≫ j = i ≫ κ ≫ j := by rw [hi, Category.assoc]
    have w : h ≫ B'.A.hom = (W.A.hom ≫ i) ≫ κ ≫ j := by rw [hh.w, hi', Category.assoc]
    have a₁ := hf'.1.lift_fst _ _ w
    have a₂ := hf'.1.lift_snd _ _ w
    exact ⟨_, a₁, a₂, ((hf'.cancel (hp.congr hi' a₁.symm) a₂).comp hf).congr hi'.symm rfl,
      (LBIso.symm hw).trans W.isLB (pull_isLB B'.isLB _) (pull_isLB B.isLB _) (lbIso_pull_comp _ a₁.symm rfl hl)⟩
  obtain ⟨a, a₁, a₂, a₃, a₄⟩ := key _ rfl
  obtain ⟨a', a₁', a₂', a₃', a₄'⟩ := key _ e'
  have E : a ≫ f = a' ≫ f := by
    refine eq_of_torsion hL B W a₃ a₃' a₄ a₄' le_rfl (by norm_num) fun y hy => ?_
    have hyw : y.left ≫ W.A.hom = 𝟙 _ := Over.w y
    let ρ : Over.mk ((x ≫ Q.hom) ≫ κ ≫ j) ⟶ Over.mk (𝟙 _ ≫ ((x ≫ Q.hom) ≫ κ) ≫ j) := Over.homMk (𝟙 _) (by simp)
    obtain ⟨z, hz, ez⟩ := exists_torsion_of_algClosed hL.mulN B' (x ≫ Q.hom) (κ ≫ j) (n := 3) (by norm_num)
      (ρ ≫ pushHom hp _ y) (by rw [← MonObj.comp_pow]; erw [← map_pow, hy, map_one, MonObj.comp_one])
    replace ez : y.left ≫ h = (x ≫ Q.hom) ≫ z.left := (Category.id_comp _).symm.trans ez
    obtain ⟨z₀, hz₀⟩ := rB' z hz
    have hzw : z.left ≫ B'.A.hom = 𝟙 _ ≫ κ ≫ j := (Over.w z).trans (Category.id_comp _).symm
    let u : Over.mk (𝟙 (Sp C)) ⟶ Q := Over.homMk (hf'.1.lift z.left (𝟙 _) hzw) (hf'.1.lift_snd _ _ _)
    have u₁ : u.left ≫ f' = z.left := hf'.1.lift_fst _ _ _
    have u₂ : u.left ≫ Q.hom = 𝟙 _ := Over.w u
    let σ : Over.mk (𝟙 _ ≫ κ ≫ j) ⟶ Over.mk (κ ≫ j) := Over.homMk (𝟙 _) rfl
    let σ' : Over.mk (κ ≫ j) ⟶ Over.mk (𝟙 _ ≫ κ ≫ j) := Over.homMk (𝟙 _) (by simp)
    have hu : u ^ 3 = 1 := by
      have inj : Function.Injective (pushHom hf' (Over.mk (𝟙 _))) := fun p q h => Over.OverMorphism.ext
        (hf'.1.hom_ext (congrArg (fun m => m.left) h) (by rw [Over.w, Over.w]))
      have : pushHom hf' _ u = σ ≫ z := Over.OverMorphism.ext (u₁.trans (Category.id_comp _).symm)
      apply inj
      rw [map_pow, this, ← MonObj.comp_pow, hz, MonObj.comp_one, map_one]
    obtain ⟨v₀, hv₀⟩ := rB (σ' ≫ pushHom hf _ u)
      (by rw [← MonObj.comp_pow]; erw [← map_pow, hu, map_one, MonObj.comp_one])
    replace hv₀ : u.left ≫ f = κ ≫ v₀ := (Category.id_comp _).symm.trans hv₀
    have fin : ∀ (i : Sp F ⟶ Sp C) (b : W.A.left ⟶ Q.left), (x ≫ Q.hom) ≫ κ = i ≫ κ → b ≫ f' = h →
        b ≫ Q.hom = W.A.hom ≫ i → y.left ≫ b ≫ f = (i ≫ κ) ≫ v₀ := fun i b hi b₁ b₂ => by
      have : y.left ≫ b = i ≫ u.left := hf'.1.hom_ext
        (by rw [Category.assoc, b₁, ez, Category.assoc i, u₁, hz₀, ← Category.assoc, hi, Category.assoc])
        (by rw [Category.assoc, b₂, reassoc_of% hyw, Category.assoc, u₂]; exact (Category.comp_id _).symm)
      rw [reassoc_of% this, hv₀, Category.assoc]
    rw [fin _ a rfl a₁ a₂, fin _ a' e' a₁' a₂', e']
  have w : (x ≫ f') ≫ B'.A.hom = 𝟙 _ ≫ ((x ≫ Q.hom) ≫ κ) ≫ j := by simp [hf'.1.w]
  have y₁ := hh.lift_fst _ _ w
  have y₂ := hh.lift_snd _ _ w
  have fin : ∀ (p : Sp F ⟶ Q.left) (b : W.A.left ⟶ Q.left), x ≫ f' = p ≫ f' → b ≫ f' = h →
      b ≫ Q.hom = W.A.hom ≫ p ≫ Q.hom → p = hh.lift _ _ w ≫ b := fun p b hp b₁ b₂ => hf'.1.hom_ext
    (by rw [Category.assoc, b₁, y₁, hp]) (by rw [Category.assoc, b₂, reassoc_of% y₂])
  rw [fin x' a' e a₁' a₂', Category.assoc, ← E, ← Category.assoc, ← fin x a rfl a₁ a₂]

theorem isGrpPullback_of_one (hL : Laws) {S S' : Scheme.{0}} {t : S' ⟶ S} {G : Over S} [GrpObj G] {Q : Over S'}
    [GrpObj Q] (hG : IsAbelianScheme G) (hQ : IsAbelianScheme Q) {f : Q.left ⟶ G.left}
    (hf : IsPullback f Q.hom G.hom t) (h₀ : eSec Q ≫ f = t ≫ eSec G) : IsGrpPullback Q G t f := by
  have hp := isGrpPullback_pullback G t
  let e : Q ≅ (Over.pullback t).obj G :=
    Over.isoMk (hf.isoIsPullback _ _ hp.1) (hf.isoIsPullback_hom_snd _ _ hp.1)
  have he : e.hom.left ≫ pullback.fst G.hom t = f := hf.isoIsPullback_hom_fst _ _ hp.1
  have : IsMonHom e.hom := hL.rigidity _ _ _ hQ (TLinPf.isAb_pullback t G hG) e.hom
    (Over.OverMorphism.ext (hp.1.hom_ext
      ((Category.assoc _ _ _).trans ((congrArg (eSec Q ≫ ·) he).trans (h₀.trans (PolExtend.eSec_fst t G).symm)))
      (by rw [Over.w, Over.w])))
  exact ((isGrpPullback_of_iso e).comp hp).congr (Category.id_comp _) he

theorem lbIso_descend (hG : GlobalFnsSt) {K C : Type} [Field K] [Field C] (κ : Sp C ⟶ Sp K) (X : Over (Sp K))
    [GrpObj X] (hX : IsAbelianScheme X) {L M : LB X.left} (hL : L.IsLB) (hM : M.IsLB)
    (h : LBIso (L.pull (pullback.fst X.hom κ)) (M.pull (pullback.fst X.hom κ))) : LBIso L M := by
  obtain ⟨h₁, h₂⟩ := flat_surjective κ
  have hN := LB.isLB_div hM hL
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  obtain ⟨i, hi⟩ := exists_chart hN (eSec X (default : PrimeSpectrum K))
  exact exists_gen_of_rigidified_of_flat_baseChange hG _ _ κ X _ hX hN h₁ h₂ inferInstance
    (IsoExtend.exists_gen_of_chart hN _ i fun y => by
      rw [Subsingleton.elim (α := Sp K) y (default : PrimeSpectrum K)]; exact hi)
    ((IsoExtend.lbIso_pull_iff_gen L M _).1 h)

end GlobalTheory.PolIsoDescent

open GlobalTheory.PolIsoDescent GlobalTheory.GenSpread in

theorem GlobalTheory.polAV_iso_descends_of_ratTors : Laws → Laws2 → GlobalTheory.LN.HomExtSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (C : Type) [Field C] [IsAlgClosed C] [Algebra (FractionRing R) C] (B B' : PolAV (Sp R)), RatTors B C 3 → RatTors B' C 3 → ∀ (φ : TF (R := R) C ⊗ B.A ≅ TF (R := R) C ⊗ B'.A) (g : (TF (R := R) C ⟶ B.A) ≃* (TF (R := R) C ⟶ B'.A)), φ.hom ≫ fst _ _ = fst _ _ → (∀ x, lift (𝟙 _) x ≫ φ.hom = lift (𝟙 _) (g x)) → LBIso (B.L.pull (snd (TF (R := R) C) B.A).left) (B'.L.pull (φ.hom ≫ snd (TF (R := R) C) B'.A).left) → ∃ Ψ : B'.A ≅ B.A, IsMonHom Ψ.hom ∧ LBIso B'.L (B.L.pull Ψ.hom.left) ∧ ∀ x, g x ≫ Ψ.hom = x := by
  intro hL hL₂ hext R _ _ _ ⟨_, _, _⟩ C _ _ _ B B' rB rB' φ g hφ hg hl
  have : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R _)
  have : CharZero C := charZero_of_injective_algebraMap (algebraMap (FractionRing R) C).injective
  let κ : Sp C ⟶ Sp (FractionRing R) := jFK (R := R) C
  let X := (Over.pullback (jK R)).obj B'.A
  let Y := (Over.pullback (jK R)).obj B.A
  let Q := (Over.pullback κ).obj X
  have hX : IsAbelianScheme X := TLinPf.isAb_pullback _ _ B'.isAb
  have hY : IsAbelianScheme Y := TLinPf.isAb_pullback _ _ B.isAb
  have hQ : IsAbelianScheme Q := TLinPf.isAb_pullback _ _ hX
  let π : Q.left ⟶ X.left := pullback.fst X.hom κ
  let p : X.left ⟶ B'.A.left := pullback.fst B'.A.hom (jK R)
  have hπ : IsGrpPullback Q X κ π := isGrpPullback_pullback X κ
  have hp : IsGrpPullback X B'.A (jK R) p := isGrpPullback_pullback B'.A (jK R)
  have hY' := isGrpPullback_pullback B.A (jK R)
  have hf' := hπ.comp hp
  have pb : ∀ A : Over (Sp R), IsPullback (snd (TF (R := R) C) A).left (fst (TF (R := R) C) A).left A.hom (κ ≫ jK R) :=
    fun A => (IsPullback.of_hasPullback (TF (R := R) C).hom A.hom).flip
  let c := hf'.1.isoIsPullback _ _ (pb B'.A)
  have c₁ : c.hom ≫ (snd (TF (R := R) C) B'.A).left = π ≫ p := hf'.1.isoIsPullback_hom_fst _ _ _
  have c₂ : c.hom ≫ (fst (TF (R := R) C) B'.A).left = Q.hom := hf'.1.isoIsPullback_hom_snd _ _ _
  have hφ' : φ.inv ≫ fst _ _ = fst _ _ := by rw [← hφ, Iso.inv_hom_id_assoc]
  let f : Q.left ⟶ B.A.left := (c.hom ≫ φ.inv.left) ≫ (snd (TF (R := R) C) B.A).left
  have hfp : IsPullback f Q.hom B.A.hom (κ ≫ jK R) := by
    have : IsIso φ.inv.left := inferInstanceAs (IsIso ((Over.forget _).map φ.inv))
    have h : IsPullback (c.hom ≫ φ.inv.left) Q.hom (fst (TF (R := R) C) B.A).left (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.assoc, ← Over.comp_left, hφ', c₂, Category.comp_id]⟩
    exact Category.id_comp (κ ≫ jK R) ▸ h.paste_horiz (pb B.A)
  have pt : ∀ (x : TF (R := R) C ⟶ B.A) (u : Sp C ⟶ Q.left), u ≫ π ≫ p = (g x).left → u ≫ Q.hom = 𝟙 _ →
      u ≫ f = x.left := fun x u u₁ u₂ => by
    have : u ≫ c.hom = (lift (𝟙 _) (g x)).left := (pb B'.A).hom_ext
      (by rw [Category.assoc, c₁, u₁, ← Over.comp_left, lift_snd])
      (by rw [Category.assoc, c₂, u₂, ← Over.comp_left, lift_fst]; rfl)
    change u ≫ (c.hom ≫ _) ≫ _ = _
    rw [Category.assoc, reassoc_of% this, ← Over.comp_left, ← Over.comp_left, ← hg, Category.assoc,
      Iso.hom_inv_id_assoc, lift_snd]
  have one : ∀ P : PolAV (Sp R), (1 : TF (R := R) C ⟶ P.A).left = (κ ≫ jK R) ≫ eSec P.A := fun _ => rfl
  have hf : IsGrpPullback Q B.A (κ ≫ jK R) f := by
    refine isGrpPullback_of_one hL B.isAb hQ hfp ((pt 1 _ ?_ (Over.w η[Q])).trans (one B))
    rw [map_one, one, ← Category.assoc]
    erw [PolExtend.eSec_fst κ X, Category.assoc, PolExtend.eSec_fst (jK R) B'.A, Category.assoc]
  have hl' : LBIso (B'.L.pull (π ≫ p)) (B.L.pull f) := lbIso_pull_comp (c.hom ≫ φ.inv.left)
    (by rw [Category.assoc, ← Over.comp_left, Iso.inv_hom_id_assoc, c₁]) rfl hl.symm
  have wf : f ≫ B.A.hom = (Q.hom ≫ κ) ≫ jK R := by rw [hfp.w, Category.assoc]
  obtain ⟨f₀, hf₀⟩ := exists_desc_of_smooth_of_geometricPoints (FractionRing R) C X Y hX.smooth
    (have := hY.proper; inferInstance) (hY'.1.lift f (Q.hom ≫ κ) wf) ((hY'.1.lift_snd _ _ _).trans hπ.1.w.symm)
    fun F _ _ x x' e => by
      have e' : (x ≫ Q.hom) ≫ κ = (x' ≫ Q.hom) ≫ κ := by
        rw [Category.assoc, Category.assoc, ← hπ.1.w]
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ X.hom) e).trans (Category.assoc _ _ _))
      refine hY'.1.hom_ext ?_ ?_
      · rw [Category.assoc, Category.assoc, hY'.1.lift_fst]
        exact comp_eq_of_rational hL B B' κ (jK R) (fun x hx => (rB x hx).elim fun a h => ⟨a.left, h⟩)
          (fun x hx => (rB' x hx).elim fun a h => ⟨a.left, h⟩) hf hf' hl' x x'
          ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ p) e).trans (Category.assoc _ _ _))) e'
      · rw [Category.assoc, Category.assoc, hY'.1.lift_snd, ← Category.assoc, ← Category.assoc]
        exact e'
  have ef : π ≫ f₀.left ≫ pullback.fst B.A.hom (jK R) = f :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst B.A.hom (jK R)) hf₀).trans (hY'.1.lift_fst _ _ _))
  obtain ⟨k₁, k₂⟩ := flat_surjective κ
  have h₀ : IsGrpPullback X B.A (jK R) (f₀.left ≫ pullback.fst B.A.hom (jK R)) :=
    isGrpPullback_of_fpqc _ _ _ (jK R) κ B.A X Q π _ k₁ k₂ inferInstance hπ (hf.congr rfl ef.symm)
      (by rw [Category.assoc, hY'.1.w, ← Category.assoc, Over.w f₀])
  obtain ⟨ψ, hψ, eψ⟩ := grpPullback_iso h₀ hY'
  rw [← eψ] at ef
  obtain ⟨Ψ, m, hΨ, l⟩ := polAV_iso_extends_of_isIntegrallyClosed hL hL₂ R B B' ψ hψ
    (lbIso_descend hL.globalFns κ X hX (pull_isLB B'.isLB _) (pull_isLB B.isLB _)
      (LBIso.trans (pull_isLB (pull_isLB B'.isLB _) _) (pull_isLB B'.isLB _) (pull_isLB (pull_isLB B.isLB _) _)
        (lbIso_pull_pull B'.isLB π rfl).symm
        (LBIso.trans (pull_isLB B'.isLB _) (pull_isLB B.isLB _) (pull_isLB (pull_isLB B.isLB _) _) hl'
          (lbIso_pull_pull B.isLB π ef.symm)))) hext
  refine ⟨Ψ, m, l, fun x => Over.OverMorphism.ext ?_⟩
  have w : (g x).left ≫ B'.A.hom = 𝟙 _ ≫ κ ≫ jK R := (Over.w (g x)).trans (Category.id_comp _).symm
  have u₁ := hf'.1.lift_fst _ _ w
  have q : ψ.hom.left ≫ pullback.fst B.A.hom (jK R) = p ≫ Ψ.hom.left := by
    rw [← hΨ]
    exact ExtUnique.pullback_map_left_fst (jK R) Ψ.hom
  rw [← pt x _ u₁ (hf'.1.lift_snd _ _ w), ← ef, q, Over.comp_left]
  exact (congrArg (· ≫ Ψ.hom.left) u₁).symm.trans (by simp only [Category.assoc])
