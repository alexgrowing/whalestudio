import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExtTrans
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GmMulEqOfResMulEq

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.GalMul

open GlobalTheory.ArcPull GlobalTheory.ArcQ GlobalTheory.PsiEvenPull

theorem exists_isPullDeg_of_val {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    {i : R →+* R'} (hi : Function.Injective i) (D : DegPre R) (D' : DegPre R')
    {W : (Sp R).Opens} (ψW : PsiOn D W) (s : (TK R).left ⟶ W.toScheme) (hs : s ≫ W.ι = jK R)
    {Φ : D'.P.A.left ⟶ D.P.A.left} (gp : IsGrpPullback D'.P.A D.P.A (spMap i) Φ)
    (w : LB.Iso D'.P.L (D.P.L.pull Φ)) (hw : PGen w)
    (hr : PMaps w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap i))
    (xe : D'.X ≃+ D.X) (hc : ∀ x, (D'.c x).left ≫ Φ = spMap i ≫ (D.c (xe x)).left)
    (hψ : ∀ (x : D'.X) (z : (TK R').left) J J', Good D.P.L z J → Good D'.P.L z J' →
      val (D.psi (xe x)) (genMap hi) z J = (om w z J J' (D'.xK x))⁻¹ * val (D'.psi x) (𝟙 _) z J') :
    ∃ hD : IsPullDeg i D D', proj hD = Φ ∧ hD.xe = xe ∧ HEq hD.w w := by
  obtain ⟨e, e_hom, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf i))
  subst he
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = specOf i ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  obtain ⟨g, sq⟩ : ∃ g : (TK R').left ⟶ (TW W).left, g ≫ W.ι = genMap hi ≫ jK R :=
    ⟨genMap hi ≫ s, (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hs)⟩
  have hg : g ≫ W.ι = jK R' ≫ specOf i := sq.trans ((fracMap_sq hi).symm.trans (Category.id_comp _))
  obtain ⟨lam, l₁, l₂⟩ : ∃ lam : (TK R').left ⟶ (jK R ⁻¹ᵁ W).toScheme, lam ≫ (jK R ⁻¹ᵁ W).ι = genMap hi ∧
      lam ≫ (jK R ∣_ W) = g :=
    ⟨(isPullback_morphismRestrict (jK R) W).lift _ _ sq,
      (isPullback_morphismRestrict (jK R) W).lift_snd _ _ _,
      (isPullback_morphismRestrict (jK R) W).lift_fst _ _ _⟩
  have hx : ∀ x, g ≫ (toUnit (TW W) ≫ D.c (xe x)).left =
      D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) := fun x => by
    show g ≫ W.ι ≫ (D.c (xe x)).left = (jK R' ≫ (D'.c x).left) ≫ _
    rw [Category.assoc, hc, ← Category.assoc, hg, Category.assoc]
  choose b hb vb using fun x => exists_gen D.P.isLB (K' := PUnit)
    (φ' := fun _ => D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx x))
    (LB.pullGen D.P.L _ _ (ψW.psi (xe x)) g) (DVR.pullGen_isGen _ _ _ _ (ψW.psi_gen _) g)
  choose psi hpsi vpsi using fun x => DegPull.exists_down_val hw D.P.isLB D'.P.isLB (K := PUnit)
    (φ' := fun _ => D'.xK x) (ε := fun _ => -1) (fun _ => rfl) (b x) (hb x)
  have eψ : ∀ x, psi x = D'.psi x := fun x => TorusExt.gen_ext_val D'.P.isLB (hpsi x) (D'.psi_gen x) fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
    have v := vpsi x _ (𝟙 _) y _ _ (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))
    have u := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq (xe x)) lam).trans (val_pull hJ _ _ _))
    rw [l₁, l₂, hψ x y J J' hJ hJ'] at u
    have v₁ : val (b x) (𝟙 _) y J = val (ψW.psi (xe x)) g y J :=
      (vb x _ _ y J hJ).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]))
    have v₂ : val (b x) (𝟙 _) y J = (om w y J J' (D'.xK x))⁻¹ * val (psi x) (𝟙 _) y J' := by
      refine v.trans (congrArg₂ (· * ·) ?_ rfl)
      rw [pw, Fintype.prod_unique, zpow_neg_one]
      simp only [om, Category.id_comp]
    exact mul_left_cancel (v₂.symm.trans (v₁.trans u))
  refine ⟨⟨e, e_hom, w, (isGen_iff w).2 hw, hE, ?_, xe, hc, W, ψW, g, hg, fun x => ⟨b x, fun jN jL => ?_,
      corr_of_val D.P.isLB fun y J hJ => vb x _ _ y J hJ⟩⟩, rfl, rfl, HEq.rfl⟩
  · exact (maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf i) _
      (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf i) hE D.P.L) (fun _ => rfl)).2 hr
  · rw [← eψ]
    refine unit_ext fun y hy => ?_
    have v := vpsi x _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
    refine (gm_res _ y _ hy _).trans (v.trans (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      (gm_res _ y _ hy _)))))
    rw [pw, Fintype.prod_unique]
    exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull (𝟙 _) _ y _ hy _))

theorem exists_isPullDeg_comp {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R'']
    [IsDomain R''] {i : R →+* R'} {j : R' →+* R''} (hi : Function.Injective i) (hj : Function.Injective j)
    {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D') (q : IsPullDeg j D' D'') :
    ∃ (r : IsPullDeg (j.comp i) D D'') (w : LB.Iso D''.P.L (D.P.L.pull (proj q ≫ proj p))),
      proj r = proj q ≫ proj p ∧ r.xe = q.xe.trans p.xe ∧ HEq r.w w ∧ Tri p.w q.w w := by
  have hji : Function.Injective (j.comp i) := hj.comp hi
  have sc : spMap j ≫ spMap i = spMap (j.comp i) := (spMap_comp i j).symm
  have gp : IsGrpPullback D''.P.A D.P.A (spMap (j.comp i)) (proj q ≫ proj p) :=
    ((pull_grp q).comp (pull_grp p)).congr sc rfl
  have g₁ := (isGen_iff _).1 p.w_gen
  have g₂ := (isGen_iff _).1 q.w_gen
  obtain ⟨w, T⟩ := Geo.Tor.exists_comp D'.P.isLB p.w q.w g₁ g₂ D.P.isLB D''.P.isLB
  have hr := T.pmaps_comp D'.P.isLB (fun _ => q.he) (FieldPull.pmaps_rig p) (FieldPull.pmaps_rig q)
  rw [sc] at hr
  have hc : ∀ x, (D''.c x).left ≫ proj q ≫ proj p = spMap (j.comp i) ≫ (D.c ((q.xe.trans p.xe) x)).left := fun x =>
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ proj p) (q.c_pr x)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (p.c_pr _)).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) sc)))))
  obtain ⟨s, hs⟩ := GlobalTheory.PullDegComp.exists_generic_lift hi p
  obtain ⟨r, r₁, r₂, r₃⟩ := exists_isPullDeg_of_val hji D D'' p.psiW s hs gp w (T.pgen_comp D'.P.isLB g₁ g₂) hr
    (q.xe.trans p.xe) hc (fun x z J J'' hJ hJ'' => by
      obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
      have sj : jK R'' ≫ spMap j = genMap hj ≫ jK R' := (Category.id_comp _).symm.trans (fracMap_sq hj)
      have s' : genMap hj ≫ jK R' ≫ spMap i = genMap hji ≫ jK R :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) sj.symm).trans ((Category.assoc _ _ _).trans
          ((congrArg (_ ≫ ·) sc).trans ((Category.id_comp _).symm.trans (fracMap_sq hji)))))
      have v₁ := psi_val p _ _ s' hJ hJ' (q.xe x)
      have v₂ := psi_val q _ _ (fracMap_sq hj) hJ' hJ'' x
      have hx : D''.xK x ≫ proj q = genMap hj ≫ D'.xK (q.xe x) := by
        show (jK R'' ≫ (D''.c x).left) ≫ proj q = genMap hj ≫ jK R' ≫ (D'.c (q.xe x)).left
        rw [Category.assoc, q.c_pr, ← Category.assoc, ← Category.assoc, ← sj]
      have t : om w z J J'' (D''.xK x) = om p.w z J J' (D''.xK x ≫ proj q) * om q.w z J' J'' (D''.xK x) :=
        (congrArg (fun u => Geo.Tor.gw w (D''.xK x) z (J u) (J'' (D''.xK x)))
          (Category.assoc (D''.xK x) (proj q) (proj p)).symm).trans
          (T _ _ z _ _ _ (hJ ((D''.xK x ≫ proj q) ≫ proj p)) (hJ' (D''.xK x ≫ proj q)) (hJ'' _))
      rw [v₂, Category.id_comp, ← hx, ← _root_.mul_assoc, ← mul_inv, ← t] at v₁
      exact v₁)
  exact ⟨r, w, r₁, r₂, r₃, T⟩

def Sq {X X' G G' Y Y' : Scheme.{0}} {M : LB X} {M' : LB X'} {L : LB G} {L' : LB G'}
    {F : X' ⟶ X} {B : G' ⟶ G} {p : Y ⟶ X} {p' : Y' ⟶ X'} {f : Y ⟶ G} {f' : Y' ⟶ G'} (h : Y' ⟶ Y)
    (wM : LB.Iso M' (M.pull F)) (wL : LB.Iso L' (L.pull B))
    (w : LB.Iso (L.pull f) (M.pull p)) (w' : LB.Iso (L'.pull f') (M'.pull p')) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (jM : M.ι) (jM' : M'.ι) (jL : L.ι) (jL' : L'.ι),
    F (p' (r z)) ∈ M.U jM → p' (r z) ∈ M'.U jM' → B (f' (r z)) ∈ L.U jL → f' (r z) ∈ L'.U jL' →
    Geo.Tor.gw wM (r ≫ p') z jM jM' * Geo.Tor.gw w' r z jM' (fun _ => jL') =
      Geo.Tor.gw w (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ f') z jL jL'

theorem Sq.comp {X X' X'' G G' G'' Y Y' Y'' : Scheme.{0}} {M : LB X} {M' : LB X'} {M'' : LB X''} {L : LB G} {L' : LB G'}
    {L'' : LB G''} {F : X' ⟶ X} {F' : X'' ⟶ X'} {B : G' ⟶ G} {B' : G'' ⟶ G'} {p : Y ⟶ X} {p' : Y' ⟶ X'} {p'' : Y'' ⟶ X''}
    {f : Y ⟶ G} {f' : Y' ⟶ G'} {f'' : Y'' ⟶ G''} {h : Y' ⟶ Y} {h' : Y'' ⟶ Y'}
    {wM : LB.Iso M' (M.pull F)} {wM' : LB.Iso M'' (M'.pull F')} {wM'' : LB.Iso M'' (M.pull (F' ≫ F))}
    {wL : LB.Iso L' (L.pull B)} {wL' : LB.Iso L'' (L'.pull B')} {wL'' : LB.Iso L'' (L.pull (B' ≫ B))}
    {w : LB.Iso (L.pull f) (M.pull p)} {w' : LB.Iso (L'.pull f') (M'.pull p')} {w'' : LB.Iso (L''.pull f'') (M''.pull p'')}
    (hM : M'.IsLB) (hL : L'.IsLB) (TM : Tri wM wM' wM'') (TL : Tri wL wL' wL'')
    (hf : h' ≫ f' = f'' ≫ B') (hp : p'' ≫ F' = h' ≫ p') (H : Sq h wM wL w w') (H' : Sq h' wM' wL' w' w'') :
    Sq (h' ≫ h) wM'' wL'' w w'' := by
  intro Z r z jM jM'' jL jL'' h₁ h₂ h₃ h₄
  have ef : f' (h' (r z)) = B' (f'' (r z)) := congrArg (fun g => g (r z)) hf
  have ep : p' (h' (r z)) = F' (p'' (r z)) := congrArg (fun g => g (r z)) hp.symm
  obtain ⟨jM', m⟩ := exists_chart hM (F' (p'' (r z)))
  obtain ⟨jL', l⟩ := exists_chart hL (B' (f'' (r z)))
  have a := H Z (r ≫ h') z jM jM' jL jL' (by show F (p' (h' (r z))) ∈ _; rw [ep]; exact h₁)
    (by show p' (h' (r z)) ∈ _; rw [ep]; exact m) (by show B (f' (h' (r z))) ∈ _; rw [ef]; exact h₃)
    (by show f' (h' (r z)) ∈ _; rw [ef]; exact l)
  have b := H' Z r z jM' jM'' jL' jL'' m h₂ l h₄
  have c := TM Z (r ≫ p'') z jM jM' jM'' h₁ m h₂
  have d := TL Z (r ≫ f'') z jL jL' jL'' h₃ l h₄
  rw [Category.assoc, hp, ← Category.assoc] at c
  rw [Category.assoc, ← hf, ← Category.assoc] at d
  rw [c, d, _root_.mul_assoc, b, ← _root_.mul_assoc, a, _root_.mul_assoc, Category.assoc]

theorem isPullUnif_comp {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R'']
    [IsDomain R''] {I : Ideal R} {I' : Ideal R'} {I'' : Ideal R''} {i : R →+* R'} {j : R' →+* R''}
    {D : DegData R I} {D' : DegData R' I'} {D'' : DegData R'' I''} {p : IsPullDeg i D.toPre D'.toPre}
    {q : IsPullDeg j D'.toPre D''.toPre} {r : IsPullDeg (j.comp i) D.toPre D''.toPre}
    {w : LB.Iso D''.toPre.P.L (D.toPre.P.L.pull (proj q ≫ proj p))} (r₁ : proj r = proj q ≫ proj p)
    (r₂ : r.xe = q.xe.trans p.xe) (r₃ : HEq r.w w) (T : Tri p.w q.w w)
    {A : PolAV (Sp (FractionRing R))} {A' : PolAV (Sp (FractionRing R'))} {A'' : PolAV (Sp (FractionRing R''))}
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G']
    {G'' : Over (Sp R'')} [GrpObj G''] [IsCommMonObj G'']
    {b₁ : G' ≅ (Over.pullback (specOf i)).obj G} {b₂ : G'' ≅ (Over.pullback (specOf j)).obj G'}
    {b : G'' ≅ (Over.pullback (specOf (j.comp i))).obj G}
    (hb : b.hom.left ≫ pullback.fst G.hom (specOf (j.comp i)) =
      (b₂.hom.left ≫ pullback.fst G'.hom (specOf j)) ≫ (b₁.hom.left ≫ pullback.fst G.hom (specOf i)))
    {U : Unif I D A G} {U' : Unif I' D' A' G'} {U'' : Unif I'' D'' A'' G''}
    (H₁ : IsPullUnif i p b₁ U U') (H₂ : IsPullUnif j q b₂ U' U'') : IsPullUnif (j.comp i) r b U U'' := by
  have sc : specOf j ≫ specOf i = specOf (j.comp i) := (spMap_comp i j).symm
  obtain ⟨w₁, g₁, e₁, m₁, K₁⟩ := (isPullUnif_iff_stalks _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).1 H₁
  obtain ⟨w₂, g₂, e₂, m₂, K₂⟩ := (isPullUnif_iff_stalks _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).1 H₂
  replace g₁ := (isGen_iff _).1 g₁
  replace g₂ := (isGen_iff _).1 g₂
  replace m₁ := (maps_iff w₁ _ (fun _ => eSec G) _ U'.LG.rig U.LG.rig (specOf i) _
    (rigPull_le (G' := G') (G := G) _ (specOf i) e₁ U.LG.L) (fun _ => rfl)).1 m₁
  replace m₂ := (maps_iff w₂ _ (fun _ => eSec G') _ U''.LG.rig U'.LG.rig (specOf j) _
    (rigPull_le (G' := G'') (G := G') _ (specOf j) e₂ U'.LG.L) (fun _ => rfl)).1 m₂
  obtain ⟨wL, TL⟩ := Geo.Tor.exists_comp U'.LG.isLB w₁ w₂ g₁ g₂ U.LG.isLB U''.LG.isLB
  have key : ∀ (Φ : D''.toPre.P.A.left ⟶ D.toPre.P.A.left) (u : LB.Iso D''.toPre.P.L (D.toPre.P.L.pull Φ))
      (xe : D''.toPre.X ≃+ D.toPre.X) (B : G''.left ⟶ G.left), Φ = proj q ≫ proj p → HEq u w → xe = q.xe.trans p.xe →
      B = (b₂.hom.left ≫ pullback.fst G'.hom (specOf j)) ≫ (b₁.hom.left ≫ pullback.fst G.hom (specOf i)) →
      ∃ wL : LB.Iso U''.LG.L (U.LG.L.pull B), wL.IsGen ∧ ∃ he : eSec G'' ≫ B = specOf (j.comp i) ≫ eSec G,
        LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G'') (fun _ => 1)) U''.LG.rig
          (rigPullOf B (specOf (j.comp i)) he U.LG.L U.LG.rig) ∧
        ∀ e : ℕ, ∃ h : (thickObj R'' I'' e G'').left ⟶ (thickObj R I e G).left,
          h ≫ (fstG I e G).left = (fstG I'' e G'').left ≫ B ∧
          ((U''.gt e).pG.left ≫ Φ = h ≫ (U.gt e).pG.left ∧ ∀ x : D''.toPre.X,
            (∀ κ : Fin 4, D''.toPre.Oφ (U''.gt e).pG x κ ≫ Φ = h ≫ D.toPre.Oφ (U.gt e).pG (xe x) κ) ∧
            PMaps u (D''.toPre.Oφ (U''.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (xe x)) Oinvε ((U''.gt e).t x)
              ((U.gt e).t (xe x)) h) ∧ Sq h u wL (U.w e) (U''.w e) := by
    rintro _ u _ _ rfl hu rfl rfl
    obtain rfl := eq_of_heq hu
    have he : eSec G'' ≫ (b₂.hom.left ≫ pullback.fst G'.hom (specOf j)) ≫ (b₁.hom.left ≫ pullback.fst G.hom (specOf i)) =
        specOf (j.comp i) ≫ eSec G :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e₂).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) e₁).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) sc)))))
    have hr := TL.pmaps_comp U'.LG.isLB (fun _ => e₂) m₁ m₂
    rw [sc] at hr
    refine ⟨wL, (isGen_iff _).2 (TL.pgen_comp U'.LG.isLB g₁ g₂), he,
      (maps_iff wL _ (fun _ => eSec G) _ U''.LG.rig U.LG.rig (specOf (j.comp i)) _
        (rigPull_le (G' := G'') (G := G) _ (specOf (j.comp i)) he U.LG.L) (fun _ => rfl)).2 hr, fun e => ?_⟩
    obtain ⟨h₁, f₁, ⟨p₁, t₁⟩, s₁⟩ := K₁ e
    obtain ⟨h₂, f₂, ⟨p₂, t₂⟩, s₂⟩ := K₂ e
    refine ⟨h₂ ≫ h₁, ?_, ⟨?_, fun x => ⟨fun κ => ?_, ?_⟩⟩, Sq.comp D'.toPre.P.isLB U'.LG.isLB T TL f₂ p₂ s₁ s₂⟩
    · exact (Category.assoc _ _ _).trans ((congrArg (h₂ ≫ ·) f₁).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) f₂).trans (Category.assoc _ _ _))))
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) p₂).trans ((Category.assoc _ _ _).trans
        ((congrArg (h₂ ≫ ·) p₁).trans (Category.assoc _ _ _).symm)))
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) ((t₂ x).1 κ)).trans ((Category.assoc _ _ _).trans
        ((congrArg (h₂ ≫ ·) ((t₁ (q.xe x)).1 κ)).trans (Category.assoc _ _ _).symm)))
    · exact T.pmaps_comp D'.toPre.P.isLB (t₂ x).1 (t₁ (q.xe x)).2 (t₂ x).2
  exact (isPullUnif_iff_stalks _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).2 (key _ r.w r.xe _ r₁ r₃ r₂ hb)

end GlobalTheory.Mum.GalMul

namespace GlobalTheory.Mum

theorem galMap_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (σ τ : Gal ρ) (a b : G'.left ⟶ G'.left), GalMap hD U' σ a → GalMap hD U' τ b → GalMap hD U' (σ * τ) (a ≫ b) := by
  intro R _ _ _ _ R' _ _ _ ρ _ D D' hD A' G' _ _ _ U' σ τ a b ⟨ga, q, b₂, ha, H₂, x₂, c₂⟩ ⟨gb, p, b₁, hb, H₁, x₁, c₁⟩
  have gp : IsGrpPullback G' G' (spMap ((Gal.hom σ).comp (Gal.hom τ))) (a ≫ b) :=
    (ga.comp gb).congr (spMap_comp _ _).symm rfl
  obtain ⟨r, w, r₁, r₂, r₃, T⟩ := GalMul.exists_isPullDeg_comp (i := Gal.hom τ) (j := Gal.hom σ) τ.1.injective σ.1.injective p q
  obtain ⟨bc, -, hbc⟩ := grpPullback_iso gp (isGrpPullback_pullback G' (specOf ((Gal.hom σ).comp (Gal.hom τ))))
  refine ⟨gp, r, bc, hbc, GalMul.isPullUnif_comp r₁ r₂ r₃ T (hbc.trans (by rw [ha, hb])) H₁ H₂, fun x => ?_, ?_⟩
  · exact (congrArg (fun e => e x) r₂).trans ((x₁ _).trans (x₂ x))
  · rintro _ _ rfl rfl
    exact (congrArg (· ≫ _) r₁).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (c₁ _ _ rfl rfl)).trans (c₂ _ _ rfl rfl)))

end GlobalTheory.Mum
