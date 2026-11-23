import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonzeroLocusSecMonoConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIsoOfIsClosedImmersionOfThickenings
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsHomogeneousXPowMulAddXPowMul
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.FormalAlg

theorem rel_of_secMaps {X X' : Scheme.{0}} {H : LB X} {H' : LB X'} {β : X' ⟶ X}
    {w : LB.Iso H' (H.pull β)} {s : H.Sec} {s' : H'.Sec} (h : SecMaps w s' (Cartier.secPull s β)) :
    GlobalTheory.Degen.FormalEmb.Rel β w s s' := by
  intro z k k' hk hk'
  have hm : z ∈ (H.pull β).U (fun _ => k) ⊓ H'.U k' := ⟨mem_pull.2 hk, hk'⟩
  have hm' : z ∈ (H.pull β).U (fun _ => k) := hm.1
  have e := congrArg (gs (𝟙 X') z _) (h ((fun _ => k), k'))
  have e1 : gs (𝟙 X') z _ (resG X' (inf_le_left : (H.pull β).U (fun _ => k) ⊓ H'.U k' ≤ _)
      ((Cartier.secPull s β).f (fun _ => k))) = gs β z _ (s.f k) := by
    refine (gs_res _ z _ hm _).trans ((gs_res _ z _ hm' _).trans ?_)
    rw [gs_pull (𝟙 X') β z _ hk, Category.id_comp]
  rw [e1] at e
  refine e.trans ?_
  rw [gs_mul _ z _ hm, gs_res _ z _ hm, gs_unit _ z _ hm]
  rfl

theorem veryAmpleBy_comp_spec {A B : Type} [CommRing A] [CommRing B] (g : A →+* B)
    (hg : Function.Surjective g) {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of B)) {H : LB X} {m : ℕ}
    {s : Fin (m + 1) → LB.Sec H} (h : VeryAmpleBy f H s) :
    VeryAmpleBy (f ≫ Spec.map (CommRingCat.ofHom g)) H s := by
  refine ⟨h.1, fun i => ?_⟩
  obtain ⟨ha, r, hr, hs⟩ := h.2 i
  refine ⟨ha, r, hr, fun p => ?_⟩
  obtain ⟨q, rfl⟩ := hs p
  obtain ⟨q', rfl⟩ := MvPolynomial.map_surjective g hg q
  refine ⟨q', ?_⟩
  rw [GlobalTheory.Degen.FormalEmb.cst_comp_spec, MvPolynomial.eval₂Hom_map_hom]

theorem isPullback_thickMap {R : Type} [CommRing R] (I : Ideal R) (P : Over (Spec (CommRingCat.of R))) (e : ℕ) :
    IsPullback (thickMap R I e P) (pullback.snd P.hom (thick R I e))
      (pullback.snd P.hom (thick R I (e + 1))) (thickTrans R I e) := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback P.hom (thick R I (e + 1)))
  have h1 : thickMap R I e P ≫ pullback.fst P.hom (thick R I (e + 1)) = pullback.fst P.hom (thick R I e) :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  rw [h1, thickTrans_comp]
  exact IsPullback.of_hasPullback _ _

theorem exists_iso_of_chart {Y : Scheme.{0}} {A L : LB Y} {τ : Type} (t : τ → A.Sec) (s : τ → L.Sec)
    (c : A.ι → τ) (h1 : ∀ a, (t (c a)).f a = 1) (h2 : ∀ a, A.U a ≤ nonzeroLocus (s (c a)))
    (h3 : ∀ a k j, resG Y (inf_le_left : L.U k ⊓ A.U a ≤ L.U k) ((s j).f k) =
      resG Y inf_le_left ((s (c a)).f k) * resG Y inf_le_right ((t j).f a)) :
    ∃ w : LB.Iso A L, w.IsGen ∧ ∀ j, SecMaps w (t j) (s j) := by
  let w : LB.Iso A L := ⟨fun p => (isUnit_resG_sec (s (c p.2)) p.1 (inf_le_right.trans (h2 p.2)) inf_le_left).unit⟩
  refine ⟨w, ?_, fun j => ?_⟩
  · rintro ⟨p, q⟩ ⟨p', q'⟩
    have hp : L.U p ⊓ A.U q ⊓ (L.U p' ⊓ A.U q') ≤ L.U p := inf_le_left.trans inf_le_left
    have hq : L.U p ⊓ A.U q ⊓ (L.U p' ⊓ A.U q') ≤ A.U q := inf_le_left.trans inf_le_right
    have hp' : L.U p ⊓ A.U q ⊓ (L.U p' ⊓ A.U q') ≤ L.U p' := inf_le_right.trans inf_le_left
    have hq' : L.U p ⊓ A.U q ⊓ (L.U p' ⊓ A.U q') ≤ A.U q' := inf_le_right.trans inf_le_right
    have key : res (le_inf hp hq) (@id (Γ(Y, L.U p ⊓ A.U q)ˣ) (w.s (p, q))) *
        res (le_inf hq hq') (A.g q q') = res (le_inf hp hp') (L.g p p') *
          res (le_inf hp' hq') (@id (Γ(Y, L.U p' ⊓ A.U q')ˣ) (w.s (p', q'))) := by
      refine Units.ext ?_
      change resG Y (le_inf hp hq) (resG Y inf_le_left ((s (c q)).f p)) * resG Y (le_inf hq hq') (A.g q q').val =
        resG Y (le_inf hp hp') (L.g p p').val * resG Y (le_inf hp' hq') (resG Y inf_le_left ((s (c q')).f p'))
      rw [resG_resG, resG_resG, ← sec_compat _ p p' hp hp']
      have e1 := congrArg (resG Y (le_inf hp hq)) (h3 q p (c q'))
      rw [map_mul, resG_resG, resG_resG, resG_resG] at e1
      have e2 := sec_compat (t (c q')) q q' hq hq'
      rw [h1 q', map_one, mul_one] at e2
      rw [e1, e2]
    change res (le_inf hp hq) (@id (Γ(Y, L.U p ⊓ A.U q)ˣ) (w.s (p, q))) =
      res (le_inf hp hp') (L.g p p') * (res (le_inf hq hq') (A.g q q'))⁻¹ *
        res (le_inf hp' hq') (@id (Γ(Y, L.U p' ⊓ A.U q')ˣ) (w.s (p', q')))
    rw [mul_right_comm, ← key, mul_inv_cancel_right]
  · rintro ⟨k, a⟩
    exact h3 a k j

theorem secQuad_of_secMaps {X : Scheme.{0}} {A B : LB X} (hB : B.IsLB) (w : LB.Iso A B) {a₁ a₂ a₃ a₄ : A.Sec}
    {b₁ b₂ b₃ b₄ : B.Sec} (h₁ : SecMaps w a₁ b₁) (h₂ : SecMaps w a₂ b₂) (h₃ : SecMaps w a₃ b₃)
    (h₄ : SecMaps w a₄ b₄) (h : ∀ c, b₁.f c * b₂.f c = b₃.f c * b₄.f c) (c : A.ι) :
    a₁.f c * a₂.f c = a₃.f c * a₄.f c := by
  refine ext_germ fun x hx => ?_
  obtain ⟨p, hp⟩ := LB.mem_of_cover hB x
  have hm : x ∈ B.U p ⊓ A.U c := ⟨hp, hx⟩
  have g := fun (b : B.Sec) (a : A.Sec) (hh : SecMaps w a b) => by
    have := congrArg (X.presheaf.germ (B.U p ⊓ A.U c) x hm).hom (hh (p, c))
    rwa [map_mul, germ_resG, germ_resG] at this
  have e := congrArg (X.presheaf.germ (B.U p) x hp).hom (h p)
  rw [map_mul, map_mul, g _ _ h₁, g _ _ h₂, g _ _ h₃, g _ _ h₄] at e
  have u : IsUnit ((X.presheaf.germ (B.U p ⊓ A.U c) x hm).hom
      ((@id (Γ(X, B.U p ⊓ A.U c)ˣ) (w.s (p, c)) : Γ(X, B.U p ⊓ A.U c)))) := (Units.isUnit _).map _
  rw [map_mul, map_mul]
  have e' : ((X.presheaf.germ (B.U p ⊓ A.U c) x hm).hom
      ((@id (Γ(X, B.U p ⊓ A.U c)ˣ) (w.s (p, c)) : Γ(X, B.U p ⊓ A.U c)))) ^ 2 *
      ((X.presheaf.germ _ x hx).hom (a₁.f c) * (X.presheaf.germ _ x hx).hom (a₂.f c)) =
      ((X.presheaf.germ (B.U p ⊓ A.U c) x hm).hom
      ((@id (Γ(X, B.U p ⊓ A.U c)ˣ) (w.s (p, c)) : Γ(X, B.U p ⊓ A.U c)))) ^ 2 *
      ((X.presheaf.germ _ x hx).hom (a₃.f c) * (X.presheaf.germ _ x hx).hom (a₄.f c)) := by
    linear_combination e
  exact (u.pow 2).mul_left_cancel e'

theorem resG_app_resG_app {Y C D : Scheme.{0}} (b : Y ⟶ C) (j : C ⟶ D) {U : D.Opens} {V : C.Opens}
    (hV : V ≤ j ⁻¹ᵁ U) {W' : Y.Opens} (hW' : W' ≤ b ⁻¹ᵁ V) {W : Y.Opens} (hW : W ≤ W')
    (hh : W ≤ (b ≫ j) ⁻¹ᵁ U) (x : Γ(D, U)) :
    resG Y hW (resG Y hW' ((b.app V).hom (resG C hV ((j.app U).hom x)))) = ((b ≫ j).appLE U W hh).hom x := by
  rw [app_resG, resG_resG, resG_resG, Scheme.Hom.comp_appLE]
  simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]

theorem resG_secPull_secPull_coord {R : Type} [CommRing R] {M : ℕ} {Y C : Scheme.{0}} (j : C ⟶ PSpace R M)
    (b : Y ⟶ C) (l : Fin (M + 1)) (a : PUnit → PUnit → Fin (M + 1)) {W : Y.Opens}
    (h : W ≤ (((O1 R M).pull j).pull b).U a) (h' : W ≤ (b ≫ j) ⁻¹ᵁ chart R M (a ⟨⟩ ⟨⟩)) :
    resG Y h ((Cartier.secPull (Cartier.secPull (coord R M l) j) b).f a) =
      pullRatio (b ≫ j) W (a ⟨⟩ ⟨⟩) h' l :=
  resG_app_resG_app b j _ _ h h' _

theorem exists_iso_pull_pull {R : Type} [CommRing R] {M : ℕ} {Y C : Scheme.{0}} {L : LB Y}
    (f : Y ⟶ Spec (CommRingCat.of R)) (s : Fin (M + 1) → L.Sec) (hs : ⨆ i, nonzeroLocus (s i) = ⊤)
    (j : C ⟶ PSpace R M) (b : Y ⟶ C) (h : b ≫ j = toProj f s hs) :
    ∃ w : LB.Iso (((O1 R M).pull j).pull b) L, w.IsGen ∧
      ∀ l, SecMaps w (Cartier.secPull (Cartier.secPull (coord R M l) j) b) (s l) := by
  have hU : ∀ a : PUnit → PUnit → Fin (M + 1),
      (((O1 R M).pull j).pull b).U a ≤ (b ≫ j) ⁻¹ᵁ chart R M (a ⟨⟩ ⟨⟩) := fun a y hy => by
    have h1 := mem_pull.1 hy
    exact mem_pull.1 h1
  have hc : ∀ i, (b ≫ j) ⁻¹ᵁ chart R M i = nonzeroLocus (s i) := fun i => by
    rw [h, toProj_preimage_chart]
  have hsec : ∀ (i l : Fin (M + 1)) (k : L.ι) {W : Y.Opens} (hW : W ≤ (b ≫ j) ⁻¹ᵁ chart R M i)
      (hk : W ≤ L.U k), resG Y hk ((s l).f k) = pullRatio (b ≫ j) W i hW l * resG Y hk ((s i).f k) := by
    intro i l k W hW hk
    revert hW
    rw [h]
    intro hW
    exact sec_eq_pullRatio_toProj_mul f s hs i l k hW hk
  refine exists_iso_of_chart (A := ((O1 R M).pull j).pull b) _ s (fun a => a ⟨⟩ ⟨⟩) (fun a => ?_) (fun a => ?_) (fun a k l => ?_)
  · exact (resG_self _ _).symm.trans ((resG_secPull_secPull_coord j b _ a le_rfl (hU a)).trans pullRatio_self)
  · exact (hU a).trans (hc _).le
  · have hW : L.U k ⊓ (((O1 R M).pull j).pull b).U a ≤ (b ≫ j) ⁻¹ᵁ chart R M (a ⟨⟩ ⟨⟩) :=
      inf_le_right.trans (hU a)
    exact (hsec _ l k hW inf_le_left).trans ((mul_comm _ _).trans
      (congrArg _ (resG_secPull_secPull_coord j b l a inf_le_right hW).symm))

theorem toProj_comp_of_secMaps {R : Type} [CommRing R] {M : ℕ} {Y Z : Scheme.{0}} {L : LB Y} {B : LB Z}
    (g : Z ⟶ Y) (f : Y ⟶ Spec (CommRingCat.of R)) (f' : Z ⟶ Spec (CommRingCat.of R)) (hf : g ≫ f = f')
    (s : Fin (M + 1) → L.Sec) (t : Fin (M + 1) → B.Sec) (hs : ⨆ i, nonzeroLocus (s i) = ⊤)
    (ht : ⨆ i, nonzeroLocus (t i) = ⊤) (w : LB.Iso B (L.pull g))
    (h : ∀ l, SecMaps w (t l) (Cartier.secPull (s l) g)) : g ≫ toProj f s hs = toProj f' t ht := by
  subst hf
  rw [← toProj_secPull hs g]
  exact toProj_eq_of_secMaps ht _ h

theorem isHomogeneous_quadric {R : Type} [CommRing R] {σ : Type} (a b c d : σ) :
    (MvPolynomial.X a * MvPolynomial.X b - MvPolynomial.X c * MvPolynomial.X d :
      MvPolynomial σ R).IsHomogeneous 2 :=
  ((MvPolynomial.isHomogeneous_X R a).mul (MvPolynomial.isHomogeneous_X R b)).sub
    ((MvPolynomial.isHomogeneous_X R c).mul (MvPolynomial.isHomogeneous_X R d))

theorem quadric_app_iff {R : Type} [CommRing R] {M : ℕ} {T : Scheme.{0}} (φ : T ⟶ PSpace R M)
    (a b c d : Fin (M + 1)) :
    (∀ k : PUnit → Fin (M + 1), (Cartier.secPull (coord R M a) φ).f k * (Cartier.secPull (coord R M b) φ).f k =
        (Cartier.secPull (coord R M c) φ).f k * (Cartier.secPull (coord R M d) φ).f k) ↔
      ∀ i, (φ.app (chart R M i)).hom (MvPolynomial.aeval (ratio R M i)
        (MvPolynomial.X a * MvPolynomial.X b - MvPolynomial.X c * MvPolynomial.X d :
          MvPolynomial (Fin (M + 1)) R)) = 0 := by
  have key := fun k : PUnit → Fin (M + 1) =>
    (show MvPolynomial.eval₂Hom (cst (φ ≫ PSpace.str R M) (((O1 R M).pull φ).U k))
        (fun j => (Cartier.secPull (coord R M j) φ).f k)
        (MvPolynomial.X a * MvPolynomial.X b - MvPolynomial.X c * MvPolynomial.X d) = _ by
      simp only [map_sub, map_mul, MvPolynomial.eval₂Hom_X']; rfl).symm.trans
    (GlobalTheory.ProjQuot.eval₂Hom_secPull_coord φ k
      (MvPolynomial.X a * MvPolynomial.X b - MvPolynomial.X c * MvPolynomial.X d))
  constructor
  · intro h i
    have e := (key (fun _ => i)).symm.trans (sub_eq_zero.2 (h _))
    have h' := congrArg (resG _ (Cartier.pull_U (O1 R M) φ (fun _ => i)).ge) e
    exact ((resG_resG _ _ _).trans (resG_self _ _)).symm.trans (h'.trans (map_zero _))
  · intro h k
    refine sub_eq_zero.1 ((key k).trans ((congrArg _ (h _)).trans (map_zero _)))

theorem quadricIdeal_le_ker {R : Type} [CommRing R] {M : ℕ} {T : Scheme.{0}} (ψ : T ⟶ PSpace R M)
    [QuasiCompact ψ] (F : MvPolynomial (Fin (M + 1)) R) (hF : F.IsHomogeneous 2)
    (h : ∀ i, (ψ.app (chart R M i)).hom (MvPolynomial.aeval (ratio R M i) F) = 0) :
    GlobalTheory.ThickeningDetermines.secIdeal (On_isLB R M (2 : ℕ)) (formSec 2 F hF) ≤ ψ.ker := by
  rw [← sup_eq_right]
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (fun i => ⟨chart R M i, isAffineOpen_chart R M i⟩) ?_ fun i => ?_
  · exact top_unique fun y _ => (exists_mem_chart R M y).elim fun i hi => TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  · rw [Scheme.IdealSheafData.ideal_sup, Pi.sup_apply, GlobalTheory.ProjQuot.ideal_secIdeal_formSec, sup_eq_right,
      Scheme.Hom.ker_apply, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
    exact h i

theorem app_eq_zero_of_fac {A B C : Scheme.{0}} (q : A ⟶ B) (ι : B ⟶ C) (j : A ⟶ C) (h : q ≫ ι = j)
    (U : C.Opens) (x : Γ(C, U)) (hx : (ι.app U).hom x = 0) : (j.app U).hom x = 0 := by
  subst h
  rw [Scheme.Hom.comp_app]
  change (q.app _).hom ((ι.app U).hom x) = 0
  rw [hx, map_zero]

theorem app_eq_zero_of_thickenings {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (hc : IsAdicComplete I R) (X : Over (Spec (CommRingCat.of R))) (hX : IsProper X.hom) {M : ℕ}
    (j : X.left ⟶ PSpace R M) (T : ℕ → Scheme.{0}) (b : ∀ e, T e ⟶ X.left)
    (p : ∀ e, T e ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
    (hb : ∀ e, IsPullback (b e) (p e) X.hom (thick R I e)) (hq : ∀ e, QuasiCompact (b e ≫ j))
    [IsClosedImmersion j]
    (F : MvPolynomial (Fin (M + 1)) R) (hF : F.IsHomogeneous 2)
    (h : ∀ e i, ((b e ≫ j).app (chart R M i)).hom (MvPolynomial.aeval (ratio R M i) F) = 0) (i : Fin (M + 1)) :
    (j.app (chart R M i)).hom (MvPolynomial.aeval (ratio R M i) F) = 0 := by
  let K := GlobalTheory.ThickeningDetermines.secIdeal (On_isLB R M (2 : ℕ)) (formSec 2 F hF)
  have hle : ∀ e, Scheme.Hom.ker K.subschemeι ≤ Scheme.Hom.ker (b e ≫ j) := fun e => by
    rw [K.ker_subschemeι]
    have := hq e
    exact quadricIdeal_le_ker _ F hF (h e)
  have hl : ∀ e, IsClosedImmersion.lift K.subschemeι (b e ≫ j) (hle e) ≫ K.subschemeι = b e ≫ j :=
    fun e => IsClosedImmersion.lift_fac _ _ _
  have hiso : IsIso (pullback.fst j K.subschemeι) :=
    GlobalTheory.CompanionTheory.FormalClosed.isIso_of_isClosedImmersion_of_thickenings R I hc X hX _ _ inferInstance fun e =>
      ⟨(hb e).isoPullback.inv ≫ pullback.lift (b e) _ (hl e).symm, by
        rw [Category.assoc, pullback.lift_fst]
        exact (hb e).isoPullback_inv_fst⟩
  have hfac : (inv (pullback.fst j K.subschemeι) ≫ pullback.snd j K.subschemeι) ≫ K.subschemeι = j := by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]
  have hK : (K.subschemeι.app (chart R M i)).hom (MvPolynomial.aeval (ratio R M i) F) = 0 := by
    have m : MvPolynomial.aeval (ratio R M i) F ∈ K.ideal ⟨chart R M i, isAffineOpen_chart R M i⟩ :=
      (GlobalTheory.ProjQuot.ideal_secIdeal_formSec i 2 F hF).ge (Ideal.mem_span_singleton_self _)
    rw [← K.ker_subschemeι_app] at m
    exact RingHom.mem_ker.1 m
  exact app_eq_zero_of_fac _ _ _ hfac _ _ hK

theorem exists_tower_algebraisation : GEClosedProj → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (E : ∀ e, LB (Y e).left) (w : ∀ e, LB.Iso (E e) ((E (e + 1)).pull (β e))), (∀ e, (E e).IsLB ∧ (w e).IsGen) → ∀ (m : ℕ) (z : ∀ e, Fin (m + 1) → LB.Sec (E e)), (∀ e j, SecMaps (w e) (z e j) (Cartier.secPull (z (e + 1) j) (β e))) → VeryAmpleBy (Y 0).hom (E 0) (z 0) → ∃ (X : Over (Spec (CommRingCat.of R))) (Q : LB X.left) (ζ : Fin (m + 1) → LB.Sec Q) (b : ∀ e, (Y e).left ⟶ X.left) (ω : ∀ e, LB.Iso (Q.pull (b e)) (E e)), Q.IsLB ∧ IsProper X.hom ∧ VeryAmpleBy X.hom Q ζ ∧ (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) ∧ (∀ e, β e ≫ b (e + 1) = b e) ∧ (∀ e, (ω e).IsGen) ∧ (∀ e j, SecMaps (ω e) (Cartier.secPull (ζ j) (b e)) (z e j)) ∧ (∀ i₁ i₂ i₃ i₄, (∀ e (c : (E e).ι), (z e i₁).f c * (z e i₂).f c = (z e i₃).f c * (z e i₄).f c) → ∀ c : Q.ι, (ζ i₁).f c * (ζ i₂).f c = (ζ i₃).f c * (ζ i₄).f c) ∧ (∀ S : Set (Fin (m + 1)), (⨆ i ∈ S, nonzeroLocus (z 0 i) = ⊤) → ⨆ i ∈ S, nonzeroLocus (ζ i) = ⊤) := by
  intro hge R _ _ I hc Y β hβ E w hE m z hz hva
  have hVA : ∀ e, VeryAmpleBy (Y e).hom (E e) (z e) := by
    rintro (_ | e)
    · exact hva
    · obtain ⟨j₀, hj, w', hw, hr⟩ := GlobalTheory.Degen.FormalEmb.tower I Y β hβ E w hE z
        (fun e j => rel_of_secMaps (hz e j)) e
      exact GlobalTheory.AbLaw.veryAmpleBy_of_isNilpotent _ _ _ (Ideal.Quotient.factor_surjective _)
        (GlobalTheory.Degen.isNilpotent_ker_factor_pow I _) _ _ _ _ j₀ hj _ _ w' m _ _ (hE _).1 (hE _).1
        ((isGen_iff _).2 hw) hr hva
  let π : ∀ e, (Y e).left ⟶ Spec (CommRingCat.of R) := fun e => (Y e).hom ≫ thick R I e
  have hVR : ∀ e, VeryAmpleBy (π e) (E e) (z e) := fun e =>
    veryAmpleBy_comp_spec _ Ideal.Quotient.mk_surjective _ (hVA e)
  have hs : ∀ e, ⨆ i, nonzeroLocus (z e i) = ⊤ := fun e => (hVA e).1
  let φ : ∀ e, (Y e).left ⟶ PSpace R m := fun e => toProj (π e) (z e) (hs e)
  have hφc : ∀ e, IsClosedImmersion (φ e) := fun e => ((veryAmpleBy_iff _ _).1 (hVR e)).2
  have hφs : ∀ e, φ e ≫ PSpace.str R m = π e := fun e => toProj_str _ _ _
  have hπ : ∀ e, β e ≫ π (e + 1) = π e := fun e => by
    simp only [π]
    rw [← Category.assoc, (hβ e).w, Category.assoc, thickTrans_comp]
  have hφβ : ∀ e, β e ≫ φ (e + 1) = φ e := fun e =>
    toProj_comp_of_secMaps (β e) (π (e + 1)) (π e) (hπ e) _ _ _ _ (w e) (hz e)
  let P : Over (Spec (CommRingCat.of R)) := Over.mk (GroundTheory.Arith.SchemeCoh.ProjSpace.toSpecBase R m)
  let i : ∀ e, (Y e).left ⟶ (thickObj R I e P).left := fun e =>
    pullback.lift (f := P.hom) (g := thick R I e) (φ e) (Y e).hom (hφs e)
  have hifst : ∀ e, i e ≫ pullback.fst P.hom (thick R I e) = φ e := fun e => pullback.lift_fst _ _ _
  have hisnd : ∀ e, i e ≫ pullback.snd P.hom (thick R I e) = (Y e).hom := fun e => pullback.lift_snd _ _ _
  have hic : ∀ e, IsClosedImmersion (i e) := fun e => by
    have : IsClosedImmersion (i e ≫ pullback.fst P.hom (thick R I e)) := by
      rw [hifst]; exact hφc e
    have : IsClosedImmersion (thick R I e) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    exact IsClosedImmersion.of_comp _ (pullback.fst P.hom (thick R I e))
  have hipb : ∀ e, IsPullback (β e) (i e) (i (e + 1)) (thickMap R I e P) := fun e => by
    refine IsPullback.of_bot ?_ ?_ (isPullback_thickMap I P e)
    · rw [hisnd, hisnd]; exact hβ e
    · refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, Category.assoc, hifst]
        exact (hφβ e).trans ((hifst e).symm.trans (congrArg (i e ≫ ·)
          ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).symm))
      · rw [Category.assoc, Category.assoc, hisnd]
        exact (hβ e).w.trans ((congrArg (· ≫ _) (hisnd e).symm).trans ((Category.assoc _ _ _).trans
          (congrArg (i e ≫ ·) (pullback.lift_snd _ _ _).symm)))
  obtain ⟨C', j, b, hj, hb, hbc⟩ := hge R I hc m (fun e => (Y e).left) i β hic hipb
  let j' : C' ⟶ PSpace R m := j
  have hj' : IsClosedImmersion j' := hj
  have hbφ : ∀ e, b e ≫ j' = φ e := fun e => (hb e).w.trans (hifst e)
  let X : Over (Spec (CommRingCat.of R)) := Over.mk (j' ≫ PSpace.str R m)
  have hX : IsProper X.hom := by
    have := isProper_str R m
    change IsProper (j' ≫ PSpace.str R m)
    infer_instance
  choose ω hωg hωs using fun e => exists_iso_pull_pull (π e) (z e) (hs e) j' (b e) (hbφ e)
  have hpb : ∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e) := fun e => by
    have h := (hb e).paste_vert (IsPullback.of_hasPullback P.hom (thick R I e))
    rw [hisnd] at h
    exact h
  have hQ : ((O1 R m).pull j').IsLB := LB.isLB_pull (O1_isLB R m) j'
  refine ⟨X, (O1 R m).pull j', fun l => Cartier.secPull (coord R m l) j', b, ω, hQ, hX,
    veryAmpleBy_secPull_coord j', hpb, hbc, hωg, hωs, ?_, ?_⟩
  · intro a₁ a₂ a₃ a₄ H c
    have hq : ∀ e i₀, ((b e ≫ j').app (chart R m i₀)).hom (MvPolynomial.aeval (ratio R m i₀)
        (MvPolynomial.X a₁ * MvPolynomial.X a₂ - MvPolynomial.X a₃ * MvPolynomial.X a₄ :
          MvPolynomial (Fin (m + 1)) R)) = 0 := fun e => by
      rw [hbφ e]
      exact (quadric_app_iff (φ e) a₁ a₂ a₃ a₄).1 fun k =>
        secQuad_of_secMaps (hE e).1 (toProjIso (π e) (z e) (hs e)) (secMaps_toProjIso _ _ _ a₁)
          (secMaps_toProjIso _ _ _ a₂) (secMaps_toProjIso _ _ _ a₃) (secMaps_toProjIso _ _ _ a₄) (H e) k
    exact (quadric_app_iff j' a₁ a₂ a₃ a₄).2 (fun i₀ => app_eq_zero_of_thickenings I hc X hX j'
      (fun e => (Y e).left) b (fun e => (Y e).hom) hpb
      (fun e => by rw [hbφ e]; have := hφc e; infer_instance) _ (isHomogeneous_quadric _ _ _ _) hq i₀) c
  · intro S hS
    have : UniversallyClosed X.hom := inferInstance
    refine top_unique fun x _ => ?_
    refine GlobalTheory.CompanionTheory.FormalClosed.mem_of_forall_mem_over_closedFibre (IsAdicComplete.le_jacobson_bot I) X.hom
      (W := ((⨆ i ∈ S, nonzeroLocus (Cartier.secPull (coord R m i) j') : X.left.Opens) : Set X.left))
      (TopologicalSpace.Opens.isOpen _) (fun x hx => ?_) x
    have hx' : X.hom x ∈ PrimeSpectrum.zeroLocus (RingHom.ker (Ideal.Quotient.mk (I ^ (0 + 1))) : Set R) :=
      fun a ha => hx (by simpa [Ideal.Quotient.eq_zero_iff_mem] using ha)
    rw [← range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective] at hx'
    obtain ⟨y₀, hy₀⟩ : ∃ y₀, thick R I 0 y₀ = X.hom x := hx'
    obtain ⟨t, ht, -⟩ := Scheme.Pullback.exists_preimage_pullback x y₀ hy₀.symm
    have hy : b 0 ((hpb 0).isoPullback.inv t) = x := by
      rw [← ht, ← (hpb 0).isoPullback_inv_fst]
      rfl
    have hm : (hpb 0).isoPullback.inv t ∈ ⨆ i ∈ S, nonzeroLocus (z 0 i) := by rw [hS]; trivial
    simp only [TopologicalSpace.Opens.mem_iSup] at hm
    obtain ⟨i₀, hi, hm⟩ := hm
    have e₁ := (hωs 0 i₀).nonzeroLocus_eq (LB.isLB_pull hQ _) (hE 0).1
    rw [Cartier.nonzeroLocus_secPull] at e₁
    rw [← e₁] at hm
    have hm' : b 0 ((hpb 0).isoPullback.inv t) ∈ nonzeroLocus (Cartier.secPull (coord R m i₀) j') := hm
    rw [hy] at hm'
    change x ∈ (⨆ i ∈ S, nonzeroLocus (Cartier.secPull (coord R m i) j') : X.left.Opens)
    simp only [TopologicalSpace.Opens.mem_iSup]
    exact ⟨i₀, hi, hm'⟩

end GlobalTheory.CompanionTheory.FormalAlg
