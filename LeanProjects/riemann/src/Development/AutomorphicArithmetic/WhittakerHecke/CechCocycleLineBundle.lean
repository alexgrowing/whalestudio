import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FinCover
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ProjSpaceHom
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowupUniversal
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsFurtherBis

open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor FunctorialResolution.Blowup
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

private lemma eval₂_scale {A S : Type*} [CommRing A] [CommRing S] {n : ℕ} (g : A →+* S)
    (x : Fin n → S) (w : S) {m : ℕ} {a : MvPolynomial (Fin n) A} (ha : a.IsHomogeneous m) :
    eval₂ g (fun l => w * x l) a = w ^ m * eval₂ g x a :=
  _root_.UpperTheory.Reformulated.B.Qk57.eval₂_scale g x w ha

set_option backward.isDefEq.respectTransparency false in
private lemma homOfLE_appTop_topIso {W : Scheme.{0}} {U U' : W.Opens} (e : U' ≤ U) (x : Γ(W, U)) :
    (W.homOfLE e).appTop (U.topIso.inv x) = U'.topIso.inv (W.presheaf.map (homOfLE e).op x) := by
  rw [Scheme.homOfLE_appTop, Scheme.Opens.topIso_inv, Scheme.Opens.topIso_inv,
    ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun t => (W.presheaf.map t) x) (Subsingleton.elim _ _)

private noncomputable def rho {R : Type} [CommRing R] {W : Scheme.{0}} (s : W ⟶ Sp R) :
    R →+* Γ(W, ⊤) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ s.appTop).hom

private lemma toSpecΓ_rho {R : Type} [CommRing R] {W : Scheme.{0}} (s : W ⟶ Sp R) :
    W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (rho s)) = s := by
  refine ext_to_Spec ?_
  change (Scheme.ΓSpecIso _).inv ≫ (W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (rho s))).appTop =
    (Scheme.ΓSpecIso _).inv ≫ s.appTop
  rw [ProjHom.specCorr_comp, Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]
  rfl

section
variable {R : Type} [CommRing R] {W : Scheme.{0}} (s : W ⟶ Sp R) {M : ℕ}

private noncomputable def phi (U : W.Opens) (x : Fin (M + 1) → Γ(W, U)) :
    MvPolynomial (Fin (M + 1)) R →+* Γ(U, ⊤) :=
  eval₂Hom (U.ι.appTop.hom.comp (rho s)) fun l => U.topIso.inv (x l)

private lemma phi_X (U : W.Opens) (x : Fin (M + 1) → Γ(W, U)) (l : Fin (M + 1)) :
    phi s U x (X l) = U.topIso.inv (x l) := by
  simp [phi]

private lemma phi_C (U : W.Opens) (x : Fin (M + 1) → Γ(W, U)) (r : R) :
    phi s U x (C r) = U.ι.appTop (rho s r) := by
  simp [phi]

private lemma phi_irr (U : W.Opens) (x : Fin (M + 1) → Γ(W, U)) (m : Fin (M + 1)) (hx : x m = 1) :
    (HomogeneousIdeal.irrelevant (grading R M)).toIdeal.map (phi s U x) = ⊤ :=
  map_irrelevant_eq_top _ m (by rw [phi_X, hx, map_one]; exact isUnit_one)

private noncomputable def loc (U : W.Opens) (x : Fin (M + 1) → Γ(W, U)) (m : Fin (M + 1))
    (hx : x m = 1) : U.toScheme ⟶ PSpace R M :=
  Proj.fromOfGlobalSections (grading R M) (phi s U x) (phi_irr s U x m hx)

private lemma loc_agree {U U' : W.Opens} (x : Fin (M + 1) → Γ(W, U)) (x' : Fin (M + 1) → Γ(W, U'))
    (m m' : Fin (M + 1)) (hx : x m = 1) (hx' : x' m' = 1)
    (hrel : ∀ l k, W.presheaf.map (homOfLE (inf_le_left : U ⊓ U' ≤ U)).op (x l) *
        W.presheaf.map (homOfLE (inf_le_right : U ⊓ U' ≤ U')).op (x' k) =
      W.presheaf.map (homOfLE (inf_le_left : U ⊓ U' ≤ U)).op (x k) *
        W.presheaf.map (homOfLE (inf_le_right : U ⊓ U' ≤ U')).op (x' l)) :
    W.homOfLE (inf_le_left : U ⊓ U' ≤ U) ≫ loc s U x m hx =
      W.homOfLE (inf_le_right : U ⊓ U' ≤ U') ≫ loc s U' x' m' hx' := by
  unfold loc
  rw [ProjHom.comp_fromOfGlobalSections _ _ (fun l => (X l : MvPolynomial (Fin (M + 1)) R))
      (fun _ => 1) (fun _ => one_pos) (fun l => X_mem l) iSup_basicOpen_X,
    ProjHom.comp_fromOfGlobalSections _ _ (fun l => (X l : MvPolynomial (Fin (M + 1)) R))
      (fun _ => 1) (fun _ => one_pos) (fun l => X_mem l) iSup_basicOpen_X]
  set ψ := (W.homOfLE (inf_le_left : U ⊓ U' ≤ U)).appTop.hom.comp (phi s U x) with hψ
  set ψ' := (W.homOfLE (inf_le_right : U ⊓ U' ≤ U')).appTop.hom.comp (phi s U' x') with hψ'
  have hX : ∀ l, ψ (X l) = (U ⊓ U').topIso.inv (W.presheaf.map (homOfLE inf_le_left).op (x l)) :=
    fun l => by
      rw [hψ, RingHom.comp_apply, phi_X]
      exact homOfLE_appTop_topIso _ _
  have hX' : ∀ l, ψ' (X l) = (U ⊓ U').topIso.inv (W.presheaf.map (homOfLE inf_le_right).op (x' l)) :=
    fun l => by
      rw [hψ', RingHom.comp_apply, phi_X]
      exact homOfLE_appTop_topIso _ _
  have hC : ∀ r, ψ (C r) = ψ' (C r) := fun r => by
    rw [hψ, hψ', RingHom.comp_apply, RingHom.comp_apply, phi_C, phi_C]
    change ((U.ι.appTop ≫ (W.homOfLE (inf_le_left : U ⊓ U' ≤ U)).appTop) _) =
      ((U'.ι.appTop ≫ (W.homOfLE (inf_le_right : U ⊓ U' ≤ U')).appTop) _)
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, Scheme.homOfLE_ι, Scheme.homOfLE_ι]
  have hm : ψ (X m) = 1 := by rw [hX, hx, map_one, map_one]
  have hm' : ψ' (X m') = 1 := by rw [hX', hx', map_one, map_one]
  have hrel' : ∀ l k, ψ (X l) * ψ' (X k) = ψ (X k) * ψ' (X l) := fun l k => by
    rw [hX, hX, hX', hX', ← map_mul, ← map_mul, hrel]
  have hw : IsUnit (ψ (X m')) :=
    IsUnit.of_mul_eq_one (ψ' (X m)) (by rw [← hrel' m m', hm, hm', one_mul])
  have hsc : ∀ l, ψ (X l) = ψ (X m') * ψ' (X l) := fun l => by
    rw [← hrel' l m', hm', mul_one]
  refine ProjHom.fromOfGlobalSections_eq_of_twist _ _ (fun l => X l) (fun _ => 1) (fun _ => one_pos)
    (fun l => X_mem l) iSup_basicOpen_X _ _ (ψ (X m')) hw fun d a ha => ?_
  have e1 : ψ = eval₂Hom (ψ'.comp C) fun l => ψ (X m') * ψ' (X l) :=
    MvPolynomial.ringHom_ext (fun r => by simp [hC]) (fun l => by simp [hsc l])
  have e2 : ψ' = eval₂Hom (ψ'.comp C) fun l => ψ' (X l) :=
    MvPolynomial.ringHom_ext (fun r => by simp) (fun l => by simp)
  calc ψ a = eval₂ (ψ'.comp C) (fun l => ψ (X m') * ψ' (X l)) a := by
        conv_lhs => rw [e1]
        rfl
    _ = ψ (X m') ^ d * eval₂ (ψ'.comp C) (fun l => ψ' (X l)) a := eval₂_scale _ _ _ ha
    _ = ψ (X m') ^ d * ψ' a := by
        congr 1
        conv_rhs => rw [e2]
        rfl
end

section
variable {R : Type} [CommRing R] {W : Scheme.{0}} (s : W ⟶ Sp R) {M : ℕ}

private lemma rho_comp {Y : Scheme.{0}} (h : Y ⟶ W) (r : R) : rho (h ≫ s) r = h.appTop (rho s r) := by
  rw [rho, Scheme.Hom.comp_appTop]
  rfl

private lemma loc_str (U : W.Opens) (x : Fin (M + 1) → Γ(W, U)) (m : Fin (M + 1)) (hx : x m = 1) :
    loc s U x m hx ≫ PSpace.str R M = U.ι ≫ s := by
  unfold loc
  rw [PSpace.str, Proj.fromOfGlobalSections_toSpecZero_assoc, ← Spec.map_comp]
  conv_rhs => rw [← toSpecΓ_rho (U.ι ≫ s)]
  congr 2
  ext r
  refine Eq.trans ?_ (rho_comp s U.ι r).symm
  refine Eq.trans ?_ (phi_C s U x r)
  rfl

private lemma loc_preimage (U : W.Opens) (x : Fin (M + 1) → Γ(W, U)) (m : Fin (M + 1))
    (hx : x m = 1) : loc s U x m hx ⁻¹ᵁ Proj.basicOpen (grading R M) (X m) = ⊤ := by
  unfold loc
  rw [Proj.fromOfGlobalSections_preimage_basicOpen (grading R M) _ _ one_pos (X_mem m), phi_X, hx,
    map_one]
  exact Scheme.basicOpen_of_isUnit _ isUnit_one

set_option backward.isDefEq.respectTransparency false in
private lemma loc_coord (U : W.Opens) (x : Fin (M + 1) → Γ(W, U)) (m l : Fin (M + 1))
    (hx : x m = 1) (g : U.toScheme ⟶ PSpace R M) (hg : g = loc s U x m hx)
    (e : ⊤ ≤ g ⁻¹ᵁ Proj.basicOpen (grading R M) (X m)) :
    g.appLE _ ⊤ e (chartHom m (X l)) = U.topIso.inv (x l) := by
  subst hg
  have hb : U.toScheme.basicOpen (phi s U x (X m)) = ⊤ := by
    rw [phi_X, hx, map_one]
    exact Scheme.basicOpen_of_isUnit _ isUnit_one
  have hmem : (X l : MvPolynomial (Fin (M + 1)) R) ∈ grading R M (1 • 1) := by
    simpa using X_mem l
  have key := ProjHom.corr_fromOfGlobalSections' (grading R M) (phi s U x) (phi_irr s U x m hx)
    one_pos (X_mem m) ⊤ hb e 1 (X l) hmem
  rw [ProjHom.corr_apply, phi_X, phi_X, hx, map_one, map_one, one_pow, mul_one,
    ProjHom.ι_appTop_eq] at key
  have key2 := congrArg (Scheme.Opens.topIso (⊤ : U.toScheme.Opens)).hom key
  simp only [Iso.inv_hom_id_apply] at key2
  rw [chartHom_of_mem m (X_mem l)]
  refine Eq.trans key2 ?_
  have : (homOfLE le_top : (⊤ : U.toScheme.Opens) ⟶ ⊤).op = 𝟙 _ := Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma appLE_ι {Y : Scheme.{0}} (f : W ⟶ Y) (O : Y.Opens) (U : W.Opens)
    (h : U ≤ f ⁻¹ᵁ O) (e : ⊤ ≤ (U.ι ≫ f) ⁻¹ᵁ O) (y : Γ(Y, O)) :
    (U.ι ≫ f).appLE O ⊤ e y = U.topIso.inv (f.appLE O U h y) := by
  rw [← Scheme.Hom.appLE_comp_appLE U.ι f O U ⊤ h (by simp), CommRingCat.comp_apply,
    Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  exact congrArg (fun t => (W.presheaf.map t) (f.appLE O U h y)) (Subsingleton.elim _ _)
end

theorem UpperTheory.cech_cocycle_line_bundle :
    ∀ {R : Type} [CommRing R] {W : Scheme.{0}} (s : W ⟶ Sp R) (M : ℕ) {ι : Type}
        (V : ι → W.Opens), iSup V = ⊤ → ∀ (μ : ι → Fin (M + 1)) (c : ∀ i, Fin (M + 1) → Γ(W, V i)),
        (∀ i, c i (μ i) = 1) →
        (∀ i j l k, W.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (c i l) *
            W.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (c j k) =
          W.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (c i k) *
            W.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (c j l)) →
        ∃ f : W ⟶ PSpace R M, f ≫ PSpace.str R M = s ∧ ∀ i,
          ∃ h : V i ≤ f ⁻¹ᵁ Proj.basicOpen (grading R M) (X (μ i)), ∀ l,
            f.appLE _ (V i) h (chartHom (μ i) (X l)) = c i l := by
  intro R _ W s M ι V hV μ c h1 h2
  let cov := W.openCoverOfIsOpenCover V hV
  let fi : ∀ i, (V i).toScheme ⟶ PSpace R M := fun i => loc s (V i) (c i) (μ i) (h1 i)
  have hag : ∀ i j : ι, pullback.fst (cov.f i) (cov.f j) ≫ fi i =
      pullback.snd (cov.f i) (cov.f j) ≫ fi j := fun i j => by
    have H := isPullback_opens_inf (V i) (V j)
    change pullback.fst (V i).ι (V j).ι ≫ fi i = pullback.snd (V i).ι (V j).ι ≫ fi j
    rw [← H.isoPullback_inv_fst, ← H.isoPullback_inv_snd, Category.assoc, Category.assoc,
      loc_agree s (c i) (c j) (μ i) (μ j) (h1 i) (h1 j) (h2 i j)]
  let f : W ⟶ PSpace R M := cov.glueMorphisms fi hag
  have hι : ∀ i, (V i).ι ≫ f = fi i := fun i => cov.ι_glueMorphisms fi hag i
  refine ⟨f, ?_, fun i => ?_⟩
  · refine cov.hom_ext _ _ fun i => ?_
    have hi : (V i).ι ≫ f ≫ PSpace.str R M = (V i).ι ≫ s := by
      rw [← Category.assoc, hι i]
      exact loc_str s (V i) (c i) (μ i) (h1 i)
    exact hi
  · have hpre : ((V i).ι ≫ f) ⁻¹ᵁ Proj.basicOpen (grading R M) (X (μ i)) = ⊤ := by
      rw [hι i]
      exact loc_preimage s (V i) (c i) (μ i) (h1 i)
    have hle : V i ≤ f ⁻¹ᵁ Proj.basicOpen (grading R M) (X (μ i)) := fun x hx => by
      have hx' : (⟨x, hx⟩ : (V i).toScheme) ∈
          ((V i).ι ≫ f) ⁻¹ᵁ Proj.basicOpen (grading R M) (X (μ i)) := by
        rw [hpre]
        trivial
      exact hx'
    refine ⟨hle, fun l => ?_⟩
    have h3 := appLE_ι f _ (V i) hle hpre.ge (chartHom (μ i) (X l))
    rw [loc_coord s (V i) (c i) (μ i) l (h1 i) _ (hι i) hpre.ge] at h3
    have h4 := congrArg (V i).topIso.hom h3
    simpa only [Iso.inv_hom_id_apply] using h4.symm
