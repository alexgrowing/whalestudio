import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationDeterminedByDegenerationDataNormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupGaloisMapMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegCompOfInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PullUnifId

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem exists_isPullDeg_of_valW' {i : R →+* R'} (D : DegPre R) (D' : DegPre R')
    {W : (Sp R).Opens} (ψW : PsiOn D W) (g : (TK R').left ⟶ (TW W).left) (hg : g ≫ W.ι = jK R' ≫ specOf i)
    {Φ : D'.P.A.left ⟶ D.P.A.left} (gp : IsGrpPullback D'.P.A D.P.A (spMap i) Φ)
    (w : LB.Iso D'.P.L (D.P.L.pull Φ)) (hw : PGen w)
    (hr : PMaps w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap i))
    (xe : D'.X ≃+ D.X) (hc : ∀ x, (D'.c x).left ≫ Φ = spMap i ≫ (D.c (xe x)).left)
    (hψ : ∀ (x : D'.X) (z : (TK R').left) J J', Good D.P.L z J → Good D'.P.L z J' →
      val (ψW.psi (xe x)) g z J = (om w z J J' (D'.xK x))⁻¹ * val (D'.psi x) (𝟙 _) z J') :
    ∃ hD : IsPullDeg i D D', proj hD = Φ ∧ hD.xe = xe ∧ HEq hD.w w := by
  obtain ⟨e, e_hom, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf i))
  subst he
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = specOf i ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
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
    have u := hψ x y J J' hJ hJ'
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

theorem exists_isPullDeg_comp {R'' : Type} [CommRing R''] [IsDomain R''] {i : R →+* R'} {j : R' →+* R''}
    (hj : Function.Injective j) {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D')
    (q : IsPullDeg j D' D'') :
    ∃ (r : IsPullDeg (j.comp i) D D'') (w : LB.Iso D''.P.L (D.P.L.pull (proj q ≫ proj p))),
      proj r = proj q ≫ proj p ∧ r.xe = q.xe.trans p.xe ∧ HEq r.w w ∧ Tri p.w q.w w := by
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
  have sj : jK R'' ≫ spMap j = genMap hj ≫ jK R' := (Category.id_comp _).symm.trans (fracMap_sq hj)
  have hg : (genMap hj ≫ p.g) ≫ p.W.ι = jK R'' ≫ specOf (j.comp i) := by
    rw [Category.assoc, p.g_comm, ← Category.assoc, ← sj, Category.assoc]
    exact congrArg (jK R'' ≫ ·) sc
  obtain ⟨r, r₁, r₂, r₃⟩ := exists_isPullDeg_of_valW' D D'' p.psiW (genMap hj ≫ p.g) hg gp w
    (T.pgen_comp D'.P.isLB g₁ g₂) hr (q.xe.trans p.xe) hc (fun x z J J'' hJ hJ'' => by
      obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
      have v₁ := PsiEvenPull.psi_pull p (q.xe x) (genMap hj) z hJ hJ'
      have v₂ := psi_val q _ _ (fracMap_sq hj) hJ' hJ'' x
      have hx : D''.xK x ≫ proj q = genMap hj ≫ D'.xK (q.xe x) := by
        show (jK R'' ≫ (D''.c x).left) ≫ proj q = genMap hj ≫ jK R' ≫ (D'.c (q.xe x)).left
        rw [Category.assoc, q.c_pr, ← Category.assoc, ← Category.assoc, ← sj]
      have t : om w z J J'' (D''.xK x) = om p.w z J J' (D''.xK x ≫ proj q) * om q.w z J' J'' (D''.xK x) :=
        (congrArg (fun u => Geo.Tor.gw w (D''.xK x) z (J u) (J'' (D''.xK x)))
          (Category.assoc (D''.xK x) (proj q) (proj p)).symm).trans
          (T _ _ z _ _ _ (hJ ((D''.xK x ≫ proj q) ≫ proj p)) (hJ' (D''.xK x ≫ proj q)) (hJ'' _))
      change _ = (om p.w z J J' (genMap hj ≫ D'.xK (q.xe x)))⁻¹ * val (D'.psi (q.xe x)) (genMap hj) z J' at v₁
      rw [v₂, Category.id_comp, ← hx, ← _root_.mul_assoc, ← mul_inv, ← t] at v₁
      exact v₁)
  exact ⟨r, w, r₁, r₂, r₃, T⟩

end GlobalTheory.PullUnifId

namespace GlobalTheory.PullUnifId

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

def pullIdIso (φ : R →+* R') (G : Over (Spec (CommRingCat.of R))) :
    (Over.pullback (specOf (RingHom.id R'))).obj ((Over.pullback (specOf φ)).obj G) ≅ (Over.pullback (specOf φ)).obj G :=
  Over.isoMk (pullbackLeftPullbackSndIso G.hom (specOf φ) (specOf (RingHom.id R')) ≪≫
    pullback.congrHom rfl (by rw [specOf_id, Category.id_comp])) (by
      show _ ≫ pullback.snd _ _ = pullback.snd _ _
      simp only [Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.map]
      erw [pullback.lift_snd]
      simp)

theorem pullIdIso_fst (φ : R →+* R') (G : Over (Spec (CommRingCat.of R))) :
    (pullIdIso φ G).hom.left ≫ pullback.fst G.hom (specOf φ) =
      pullback.fst _ (specOf (RingHom.id R')) ≫ pullback.fst G.hom (specOf φ) := by
  simp only [pullIdIso, Over.isoMk_hom_left, Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.map]
  erw [pullback.lift_fst]
  simp

end GlobalTheory.PullUnifId

namespace GlobalTheory.PullUnifId

open GlobalTheory.PsiEvenPull (proj)

theorem isPullUnif_comp_id : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R')
    (D : DegData R I) (D' D'' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre)
    (hid : IsPullDeg (RingHom.id R') D'.toPre D''.toPre)
    (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A' A'' : PolAV (Spec (CommRingCat.of (FractionRing R'))))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G]
    (G' G'' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G'']
    (bc : G' ≅ (Over.pullback (specOf φ)).obj G) (bc' : G'' ≅ (Over.pullback (specOf (RingHom.id R'))).obj G')
    (U : Unif I D A G) (U' : Unif I' D' A' G') (U'' : Unif I' D'' A'' G''),
    IsPullUnif φ hD bc U U' → IsPullUnif (RingHom.id R') hid bc' U' U'' →
    ∃ (h : IsPullDeg φ D.toPre D''.toPre) (bc'' : G'' ≅ (Over.pullback (specOf φ)).obj G),
      IsPullUnif φ h bc'' U U'' ∧ (∀ x, h.xe x = hD.xe (hid.xe x)) ∧
      h.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ) =
        hid.e.hom.left ≫ pullback.fst D'.toPre.P.A.hom (specOf (RingHom.id R')) ≫
          hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ) ∧
      bc''.hom.left ≫ pullback.fst G.hom (specOf φ) =
        bc'.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id R')) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) ∧
      (IsMonHom bc.hom → IsMonHom bc'.hom → IsMonHom bc''.hom) := by
  intro R R' _ _ _ _ I I' φ D D' D'' hD hid A A' A'' G _ _ G' G'' _ _ _ _ bc bc' U U' U'' H₁ H₂
  obtain ⟨r, w, r₁, r₂, r₃, T⟩ := exists_isPullDeg_comp (j := RingHom.id R') (fun _ _ h => h) hD hid
  let bc'' : G'' ≅ (Over.pullback (specOf φ)).obj G :=
    bc' ≪≫ (Over.pullback (specOf (RingHom.id R'))).mapIso bc ≪≫ pullIdIso φ G
  have hb : bc''.hom.left ≫ pullback.fst G.hom (specOf φ) =
      bc'.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id R')) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) := by
    have := pullIdIso_fst φ G
    simp only [bc'', Iso.trans_hom, Over.comp_left, Category.assoc, this, Functor.mapIso_hom]
    congr 1
    simp only [Over.pullback, pullback.map]
    erw [pullback.lift_fst_assoc]
    rfl
  refine ⟨r, bc'', GalMul.isPullUnif_comp (i := φ) (j := RingHom.id R') r₁ r₂ r₃ T
      (hb.trans (Category.assoc _ _ _).symm) H₁ H₂, fun x => congrArg (fun e => e x) r₂,
      r₁.trans (Category.assoc _ _ _), hb, fun m₁ m₂ => ?_⟩
  have p₁ : IsGrpPullback G' G (specOf φ) (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) :=
    ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G (specOf φ))).congr (Category.id_comp _) rfl
  have p₂ : IsGrpPullback G'' G' (specOf (RingHom.id R')) (bc'.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id R'))) :=
    ((isGrpPullback_of_iso bc').comp (isGrpPullback_pullback G' (specOf (RingHom.id R')))).congr (Category.id_comp _) rfl
  have p : IsGrpPullback G'' G (specOf φ) (bc'.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id R')) ≫
      bc.hom.left ≫ pullback.fst G.hom (specOf φ)) :=
    (p₂.comp p₁).congr (by rw [specOf_id, Category.id_comp]) (Category.assoc _ _ _)
  obtain ⟨e, he, hf⟩ := grpPullback_iso p (isGrpPullback_pullback G (specOf φ))
  have : bc''.hom = e.hom := by
    ext1
    apply pullback.hom_ext
    · exact hb.trans hf.symm
    · exact (Over.w bc''.hom).trans (Over.w e.hom).symm
  rw [this]
  exact he

end GlobalTheory.PullUnifId
