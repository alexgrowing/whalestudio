import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjectiveRepresentationPullbackCoordinates
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionCoordinateVectorExistsLocallyStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSectionCoordinateVectorOfLocallyOnRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.RepMap
variable {X : Scheme.{0}} {σ : Type}

theorem gs_one (x : X) (U : X.Opens) (h : x ∈ U) (f : Γ(X, U)) :
    gs (𝟙 X) x U f = (X.presheaf.germ U x h).hom f := by
  rw [gs_eq (𝟙 X) x U h]; rfl

theorem lbIso_of_germs (A B : LB X) (a : σ → A.Sec) (b : σ → B.Sec)
    (H : ∀ (y : X) (j : B.ι) (k : A.ι), y ∈ B.U j → y ∈ A.U k → (∃ i, IsUnit (gs (𝟙 X) y (A.U k) ((a i).f k))) ∧
      ∃ u : (X.presheaf.stalk y)ˣ, ∀ i, gs (𝟙 X) y (B.U j) ((b i).f j) = u * gs (𝟙 X) y (A.U k) ((a i).f k)) :
    LBIso A B := by
  have uniq : ∀ (y : X) (j : B.ι) (k : A.ι), y ∈ B.U j → y ∈ A.U k → ∀ u u' : (X.presheaf.stalk y)ˣ,
      (∀ i, gs (𝟙 X) y (B.U j) ((b i).f j) = u * gs (𝟙 X) y (A.U k) ((a i).f k)) →
      (∀ i, gs (𝟙 X) y (B.U j) ((b i).f j) = u' * gs (𝟙 X) y (A.U k) ((a i).f k)) → u = u' := by
    intro y j k hj hk u u' h h'
    obtain ⟨i, hi⟩ := (H y j k hj hk).1
    exact Units.ext (hi.mul_right_cancel ((h i).symm.trans (h' i)))
  have loc : ∀ (j : B.ι) (k : A.ι) (y : ↥(B.U j ⊓ A.U k : X.Opens)), ∃ (W : X.Opens) (_ : W ≤ B.U j ⊓ A.U k) (c : Γ(X, W)ˣ),
      y.1 ∈ W ∧ ∀ z ∈ W, ∀ i, gs (𝟙 X) z (B.U j) ((b i).f j) = gm (𝟙 X) z W c * gs (𝟙 X) z (A.U k) ((a i).f k) := by
    rintro j k ⟨y, hy⟩
    obtain ⟨⟨i₀, hi₀⟩, u, hu⟩ := H y j k hy.1 hy.2
    let t : Γ(X, B.U j ⊓ A.U k) := resG X inf_le_left ((b i₀).f j) * resG X inf_le_right ((a i₀).f k)
    have hle := X.basicOpen_le t
    have ht : IsUnit (resG X hle t) := RingedSpace.isUnit_res_basicOpen X.toRingedSpace t
    rw [map_mul] at ht
    obtain ⟨c₁, h₁⟩ := isUnit_of_mul_isUnit_left ht
    obtain ⟨c₂, h₂⟩ := isUnit_of_mul_isUnit_right ht
    refine ⟨X.basicOpen t, hle, c₁ * c₂⁻¹, ?_, fun z hz i => ?_⟩
    · rw [X.mem_basicOpen t y hy, ← gs_one y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy, hu]
      exact (u.isUnit.mul hi₀).mul hi₀
    · obtain ⟨-, u', hu'⟩ := H z j k (hle hz).1 (hle hz).2
      have e₁ : (gm (𝟙 X) z _ c₁).val = gs (𝟙 X) z (B.U j) ((b i₀).f j) := by
        rw [← gs_unit _ z _ hz, h₁, gs_res _ z _ hz, gs_res _ z _ (hle hz)]
      have e₂ : (gm (𝟙 X) z _ c₂).val = gs (𝟙 X) z (A.U k) ((a i₀).f k) := by
        rw [← gs_unit _ z _ hz, h₂, gs_res _ z _ hz, gs_res _ z _ (hle hz)]
      have e : gm (𝟙 X) z _ c₁ = u' * gm (𝟙 X) z _ c₂ := Units.ext (by rw [Units.val_mul, e₁, e₂, hu'])
      rw [map_mul, map_inv, e, mul_inv_cancel_right, hu']
  choose W hW c hy hc using loc
  have glue : ∀ (j : B.ι) (k : A.ι), ∃ w : Γ(X, B.U j ⊓ A.U k)ˣ, ∀ z ∈ B.U j ⊓ A.U k, ∀ i,
      gs (𝟙 X) z (B.U j) ((b i).f j) = gm (𝟙 X) z _ w * gs (𝟙 X) z (A.U k) ((a i).f k) := by
    intro j k
    obtain ⟨w, hw⟩ := glue_unit (B.U j ⊓ A.U k) (W j k) (hW j k)
      (fun z hz => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨z, hz⟩, hy j k ⟨z, hz⟩⟩) (c j k)
      (fun p q z hz => uniq z j k (hW j k p hz.1).1 (hW j k p hz.1).2 _ _ (hc j k p z hz.1) (hc j k q z hz.2))
    refine ⟨w, fun z hz i => ?_⟩
    rw [← gm_res (𝟙 X) z (hW j k ⟨z, hz⟩) (hy j k ⟨z, hz⟩), hw]
    exact hc j k ⟨z, hz⟩ z (hy j k ⟨z, hz⟩) i
  choose w hw using glue
  refine ⟨⟨fun p => w p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div A B (𝟙 X) y p q hy)
    (gm_res _ y _ hy _))).symm)
  refine uniq y p.1 p.2 hy.1.1 hy.1.2 _ _ (hw p.1 p.2 y hy.1) fun i => ?_
  have hB : y ∈ B.U p.1 ⊓ B.U q.1 := ⟨hy.1.1, hy.2.1⟩
  have hA : y ∈ A.U p.2 ⊓ A.U q.2 := ⟨hy.1.2, hy.2.2⟩
  have eB := congrArg (gs (𝟙 X) y _) ((b i).compat p.1 q.1)
  have eA := congrArg (gs (𝟙 X) y _) ((a i).compat p.2 q.2)
  rw [gs_mul _ y _ hB, gs_res _ y _ hB, gs_res _ y _ hB, gs_unit _ y _ hB] at eB
  rw [gs_mul _ y _ hA, gs_res _ y _ hA, gs_res _ y _ hA, gs_unit _ y _ hA] at eA
  rw [eB, eA, hw q.1 q.2 y hy.2 i]
  change _ = ((_ * _ * gm (𝟙 X) y _ (w q.1 q.2) : (X.presheaf.stalk y)ˣ) : X.presheaf.stalk y) * _
  rw [Units.val_mul, Units.val_mul]
  have := (gm (𝟙 X) y _ (A.g p.2 q.2)).inv_mul
  linear_combination (-(gm (𝟙 X) y _ (B.g p.1 q.1)).val * (gm (𝟙 X) y _ (w q.1 q.2)).val *
    gs (𝟙 X) y (A.U q.2) ((a i).f q.2)) * this

theorem coord_germ {M : LB X} {th : σ → M.Sec} {R : Type} [CommRing R] {x : Sp R ⟶ X} {v : σ → R}
    (h : SecCoord M th x v) (p : Sp R) (k : M.ι) (hk : x p ∈ M.U k) :
    ∃ t : ((Sp R).presheaf.stalk p)ˣ, ∀ i, gs x p (M.U k) ((th i).f k) =
      ((Sp R).presheaf.germ ⊤ p trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v i)) * t := by
  obtain ⟨τ, -, h⟩ := h
  have hp : p ∈ (M.pull x).U (fun _ => k) := mem_pull.2 hk
  refine ⟨gm (𝟙 _) p _ (τ.s fun _ => k), fun i => ?_⟩
  have e := congrArg (gs (𝟙 _) p _) (h i (fun _ => k) (RepBC.pull_le M x _))
  rw [gs_appLE x _ _ _ (𝟙 _) p hp, gs_mul _ p _ hp, gs_res _ p _ hp, gs_one p ⊤ trivial, Category.id_comp] at e
  rw [← gs_unit _ p _ hp]
  exact e

theorem lbIso_of_coord (A B : LB X) (a : σ → A.Sec) (b : σ → B.Sec)
    (H : ∀ y : X, ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ X) (v : σ → R), IsOpenImmersion x ∧ y ∈ Set.range x ∧
      Ideal.span (Set.range v) = ⊤ ∧ SecCoord A a x v ∧ SecCoord B b x v) : LBIso A B := by
  refine lbIso_of_germs A B a b fun y j k hj hk => ?_
  obtain ⟨R, _, x, v, _, ⟨p, rfl⟩, hv, hA, hB⟩ := H y
  obtain ⟨t, ht⟩ := coord_germ hA p k hk
  obtain ⟨t', ht'⟩ := coord_germ hB p j hj
  let e := (asIso (x.stalkMap p)).commRingCatIsoToRingEquiv
  have he : ∀ (U : X.Opens) (_ : x p ∈ U) f, gs x p U f = e (gs (𝟙 X) (x p) U f) := fun U h f => gs_stalkMap x p U h f
  let ψ : R →+* (Sp R).presheaf.stalk p :=
    ((Sp R).presheaf.germ ⊤ p trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  constructor
  · have : ∃ i, IsUnit (ψ (v i)) := by
      by_contra hn
      push_neg at hn
      have : Ideal.span (Set.range v) ≤ (IsLocalRing.maximalIdeal _).comap ψ := by
        rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        exact hn i
      rw [hv, top_le_iff, Ideal.comap_eq_top_iff] at this
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top this
    obtain ⟨i, hi⟩ := this
    refine ⟨i, ?_⟩
    rw [← MulEquiv.isUnit_map e, ← he _ hk, ht]
    exact hi.mul t.isUnit
  · refine ⟨Units.map e.symm.toMonoidHom (t' * t⁻¹), fun i => e.injective ?_⟩
    rw [map_mul, ← he _ hk, ← he _ hj, ht, ht']
    have : e (Units.map e.symm.toMonoidHom (t' * t⁻¹)).val = (t' * t⁻¹).val := e.apply_symm_apply _
    rw [this, Units.val_mul]
    linear_combination (-(ψ (v i)) * t'.val) * t.inv_mul

theorem exists_spMap {R R' : Type} [CommRing R] [CommRing R'] (a : Sp R' ⟶ Sp R) : ∃ φ : R →+* R', a = spMap φ :=
  ⟨(Spec.preimage a).hom, (Spec.map_preimage a).symm⟩

theorem exists_factor {U : Scheme.{0}} {R : Type} [CommRing R] (y : Sp R ⟶ X) (u : U ⟶ X) [IsOpenImmersion u]
    (p : Sp R) (h : y p ∈ Set.range u) : ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R') (a : Sp R' ⟶ U),
      IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧ spMap φ ≫ y = a ≫ u := by
  obtain ⟨q, hq⟩ := h
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := y) (g := u) p q hq.symm
  obtain ⟨i, r, hr⟩ := (pullback y u).affineOpenCover.openCover.exists_eq z
  let C := (pullback y u).affineOpenCover.X i
  let w : Sp C ⟶ pullback y u := (pullback y u).affineOpenCover.f i
  have : IsOpenImmersion w := (pullback y u).affineOpenCover.map_prop i
  obtain ⟨φ, hφ⟩ := exists_spMap (w ≫ pullback.fst y u)
  refine ⟨C, inferInstance, φ, w ≫ pullback.snd y u, ?_, ?_, ?_⟩
  · rw [← hφ]; infer_instance
  · rw [← hφ]; refine ⟨r, ?_⟩
    rw [← hz, ← hr]; rfl
  · rw [← hφ, Category.assoc, Category.assoc, pullback.condition]

set_option backward.isDefEq.respectTransparency false in
theorem exists_map_of_coord : ∀ (R σ : Type) [CommRing R] (I : Ideal (MvPolynomial σ R)) (Z Y : Scheme.{0}) (s : Z ⟶ Sp R) (sY : Y ⟶ Sp R) (M : LB Z) (N : LB Y) (th : σ → M.Sec) (ty : σ → N.Sec), ProjRep I s M th → N.IsLB → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (y : Sp R' ⟶ Y) (v : σ → R'), y ≫ sY = spMap β → SecCoord N ty y v → Ideal.span (Set.range v) = ⊤ ∧ ∀ F ∈ I, MvPolynomial.eval₂ β v F = 0) → ∃ f : Y ⟶ Z, f ≫ s = sY ∧ LBIso N (M.pull f) ∧ (∀ (R' : Type) [CommRing R'] (y : Sp R' ⟶ Y) (v : σ → R'), SecCoord N ty y v ↔ SecCoord M th (y ≫ f) v) ∧ ∀ f' : Y ⟶ Z, f' ≫ s = sY → (∀ (R' : Type) [CommRing R'] (y : Sp R' ⟶ Y) (v : σ → R'), SecCoord N ty y v → SecCoord M th (y ≫ f') v) → f' = f := by
  intro R σ _ I Z Y s sY M N th ty ⟨hM, hloc, hpts⟩ hN hY
  have uniq : ∀ (T : Type) [CommRing T] (x x' : Sp T ⟶ Z) (v : σ → T), x ≫ s = x' ≫ s → SecCoord M th x v →
      SecCoord M th x' v → x = x' := by
    intro T _ x x' v e h h'
    obtain ⟨β, hβ⟩ := exists_spMap (x ≫ s)
    obtain ⟨h₁, h₂⟩ := hloc T β x v hβ h
    exact (hpts T β v h₁ h₂).unique ⟨hβ, h⟩ ⟨e.symm.trans hβ, h'⟩
  have uni : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (v : σ → T), SecCoord N ty y v →
      Ideal.span (Set.range v) = ⊤ ∧ ∃ x : Sp T ⟶ Z, x ≫ s = y ≫ sY ∧ SecCoord M th x v := by
    intro T _ y v h
    obtain ⟨β, hβ⟩ := exists_spMap (y ≫ sY)
    obtain ⟨h₁, h₂⟩ := hY T β y v hβ h
    obtain ⟨x, hx, hx'⟩ := (hpts T β v h₁ h₂).exists
    exact ⟨h₁, x, hx.trans hβ.symm, hx'⟩
  choose A iA u v hu hp hv using (GlobalTheory.T.sectionCoordinateVector_exists_locally Y N σ ty hN).2.2
  choose g hg hgv using fun p => (uni (A p) (u p) (v p) (hv p)).2
  have key : ∀ (p : Y) (T : Type) [CommRing T] (a : Sp T ⟶ Sp (A p)), (∃ w, SecCoord N ty (a ≫ u p) w) ∧
      ∀ w, SecCoord N ty (a ≫ u p) w ↔ SecCoord M th (a ≫ g p) w := by
    intro p T _ a
    obtain ⟨φ, rfl⟩ := exists_spMap a
    have h₁ := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N σ ty _ _ _ hN (hv p)).1 T φ
    have h₂ := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Z M σ th _ _ _ hM (hgv p)).1 T φ
    refine ⟨⟨_, h₁⟩, fun w => ⟨fun h => ?_, fun h => ?_⟩⟩
    · obtain ⟨c, hc⟩ := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N σ ty _ _ _ hN h₁).2.2 w h
      rw [show w = _ from funext hc]
      exact (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Z M σ th _ _ _ hM h₂).2.1 c
    · obtain ⟨c, hc⟩ := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Z M σ th _ _ _ hM h₂).2.2 w h
      rw [show w = _ from funext hc]
      exact (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N σ ty _ _ _ hN h₁).2.1 c
  let 𝒰 : Y.OpenCover := Scheme.Cover.mkOfCovers Y (fun p => Sp (A p)) u (fun p => ⟨p, hp p⟩) hu
  have hglue : ∀ p q : Y, pullback.fst (u p) (u q) ≫ g p = pullback.snd (u p) (u q) ≫ g q := by
    intro p q
    refine Scheme.Cover.hom_ext (pullback (u p) (u q)).affineOpenCover.openCover _ _ fun i => ?_
    let C := (pullback (u p) (u q)).affineOpenCover.X i
    let r : Sp C ⟶ pullback (u p) (u q) := (pullback (u p) (u q)).affineOpenCover.f i
    have e : (r ≫ pullback.fst _ _) ≫ u p = (r ≫ pullback.snd _ _) ≫ u q := by
      rw [Category.assoc, Category.assoc, pullback.condition]
    obtain ⟨⟨w, hw⟩, h⟩ := key p C (r ≫ pullback.fst _ _)
    have := uniq C _ _ w (by rw [Category.assoc, hg, ← Category.assoc, e, Category.assoc _ (g q), hg, Category.assoc _ (u q)])
      ((h w).1 hw) (((key q C (r ≫ pullback.snd _ _)).2 w).1 (e ▸ hw))
    rw [Category.assoc, Category.assoc] at this
    exact this
  let f : Y ⟶ Z := 𝒰.glueMorphisms g hglue
  have hf : ∀ p, u p ≫ f = g p := fun p => Scheme.Cover.ι_glueMorphisms 𝒰 _ hglue p
  have hfs : f ≫ s = sY := by
    refine Scheme.Cover.hom_ext 𝒰 _ _ fun p => ?_
    change u p ≫ _ = u p ≫ _
    rw [← Category.assoc, hf, hg]
  refine ⟨f, hfs, ?_, fun T _ y w => ⟨fun h => ?_, fun h => ?_⟩, fun f' hf' h => ?_⟩
  · refine lbIso_of_coord N (M.pull f) ty (fun i => RepBC.secPull M f (th i)) fun p =>
      ⟨A p, iA p, u p, v p, hu p, hp p, (uni _ _ _ (hv p)).1, hv p, (RepBC.secCoord_pull M th f _ _).2 ?_⟩
    rw [hf]; exact hgv p
  · refine GlobalTheory.T.isSectionCoordinateVector_of_locally_on_ring Z M σ th T _ w hM (uni T y w h).1 fun q => ?_
    have := hu (y q)
    obtain ⟨T', _, φ, a, h₁, h₂, e⟩ := exists_factor y (u (y q)) q (hp _)
    refine ⟨T', inferInstance, φ, h₁, h₂, ?_⟩
    rw [← Category.assoc, e, Category.assoc, hf, ← (key _ T' a).2, ← e]
    exact (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N σ ty _ _ _ hN h).1 T' φ
  · obtain ⟨β, hβ⟩ := exists_spMap ((y ≫ f) ≫ s)
    refine GlobalTheory.T.isSectionCoordinateVector_of_locally_on_ring Y N σ ty T _ w hN (hloc T β _ w hβ h).1 fun q => ?_
    have := hu (y q)
    obtain ⟨T', _, φ, a, h₁, h₂, e⟩ := exists_factor y (u (y q)) q (hp _)
    refine ⟨T', inferInstance, φ, h₁, h₂, ?_⟩
    rw [e, (key _ T' a).2, ← hf, ← Category.assoc, ← e, Category.assoc]
    exact (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Z M σ th _ _ _ hM h).1 T' φ
  · refine Scheme.Cover.hom_ext 𝒰 _ _ fun p => ?_
    change u p ≫ _ = u p ≫ _
    rw [hf]
    exact uniq _ _ _ (v p) (by rw [Category.assoc, hf', hg]) (h _ _ _ (hv p)) (hgv p)

end GlobalTheory.ZM.RepMap
end
