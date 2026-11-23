import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AgreeOfCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ArcData

theorem unit_ext_field {K F : Type} [Field K] [Field F] (ρ : Sp F ⟶ Sp K) (z : Sp F) {U : (Sp K).Opens}
    {a b : Γ(Sp K, U)ˣ} (h : ρ z ∈ U → gm ρ z U a = gm ρ z U b) : a = b := by
  have sK : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  by_cases hz : ρ z ∈ U
  · obtain rfl : U = ⊤ := top_le_iff.1 fun y _ => by rw [Subsingleton.elim y (ρ z)]; exact hz
    have e := congrArg Units.val (h hz)
    rw [gm_val ρ z ⊤ hz, gm_val ρ z ⊤ hz] at e
    have hK : IsField Γ(Sp K, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField K)
    letI := hK.toField
    exact Units.ext (RingHom.injective
      (((Sp F).presheaf.germ (ρ ⁻¹ᵁ ⊤) z hz).hom.comp (ρ.app ⊤).hom) e)
  · exact unit_ext fun y hy => absurd (by rw [Subsingleton.elim (ρ z) y]; exact hy) hz

variable {R : Type} [CommRing R] [IsDomain R]

theorem mapsAt_of_genRel {D D' : DegPre R} {B₀ : Scheme.{0}} {M₀ : LB B₀} (hM₀ : M₀.IsLB) {φ : D.P.A.left ⟶ B₀}
    {Φ : D'.P.A.left ⟶ D.P.A.left} {w : LB.Iso D.P.L (M₀.pull φ)} {wD : LB.Iso D'.P.L (D.P.L.pull Φ)}
    {w' : LB.Iso D'.P.L (M₀.pull (Φ ≫ φ))} (T : Tri w wD w') {F : Type} [Field F] (ρ : Sp F ⟶ (TK R).left)
    (x : D'.X) (y : D.X) (hx : D'.xK x ≫ Φ = D.xK y) {pt₀ : PUnit → (Sp F ⟶ B₀)}
    (t₀ : LB.Gen (LB.LinComb M₀ pt₀ (fun _ => -1))) (s : F)
    (h : GenRel w (LB.pullGen _ _ _ (D.psi y) ρ) t₀ s) (h' : GenRel w' (LB.pullGen _ _ _ (D'.psi x) ρ) t₀ s) :
    ∃ b : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => D'.xK x ≫ Φ) (fun _ => -1)),
      GeneratorPullback.MapsAt D.P.L D'.P.L (J := PUnit) (fun _ => Φ) wD (D'.xK x) (-1) (D'.psi x) b ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (z : Z) (J), Good D.P.L z J → val b r z J = val (D.psi y) r z J := by
  obtain ⟨b, -, vb⟩ := exists_gen D.P.isLB (K' := PUnit) (φ' := fun _ => D'.xK x ≫ Φ) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) hx.symm) (D.psi y) (D.psi_gen y)
  refine ⟨b, fun jN jL => ?_, vb⟩
  have z : Sp F := (default : PrimeSpectrum F)
  refine unit_ext_field (K := FractionRing R) ρ z fun hz => ?_
  have mN : Φ (D'.xK x (ρ z)) ∈ D.P.L.U (jN PUnit.unit) := mem_pull.1 hz.1
  have mL : D'.xK x (ρ z) ∈ D'.P.L.U jL := hz.2
  have hp : (ρ ≫ D'.xK x) ≫ Φ = ρ ≫ D.xK y := by rw [Category.assoc, hx]
  have mN' : (ρ ≫ D.xK y) z ∈ D.P.L.U (jN PUnit.unit) := by rw [← hp]; exact mN
  obtain ⟨J, hJ, eJ⟩ := exists_good D.P.L D.P.isLB z (K := PUnit) (fun _ => ρ ≫ D.xK y) jN (fun _ _ _ => rfl)
    (fun _ => mN')
  obtain ⟨j₀, hj₀⟩ := exists_chart hM₀ (φ (Φ (D'.xK x (ρ z))))
  have hj₀' : φ ((ρ ≫ D.xK y) z) ∈ M₀.U j₀ := by rw [← hp]; exact hj₀
  have e := ((genRel_iff w _ t₀ s z).1 h).2 jN (fun _ => j₀) (fun _ => hj₀') (fun _ => mN')
  have e' := ((genRel_iff w' _ t₀ s z).1 h').2 (fun _ => jL) (fun _ => j₀) (fun _ => hj₀) (fun _ => mL)
  have E := Units.ext (e.trans e'.symm)
  rw [Fintype.prod_unique, Fintype.prod_unique, T _ (ρ ≫ D'.xK x) z j₀ (jN PUnit.unit) jL hj₀ mN mL, hp, mul_zpow,
    _root_.mul_assoc] at E
  have E' := mul_left_cancel E
  have a₁ := gm_pullGen D.P.L (fun _ : PUnit => D.xK y) _ (D.psi y) ρ (𝟙 _) z jN (Set.mem_iInter.2 fun _ => mN')
  have a₂ := gm_pullGen D'.P.L (fun _ : PUnit => D'.xK x) _ (D'.psi x) ρ (𝟙 _) z (fun _ => jL)
    (Set.mem_iInter.2 fun _ => mL)
  rw [Category.id_comp] at a₁ a₂
  have v := vb _ ρ z J hJ
  rw [val_of b ρ z J jN (fun k => by rw [hx]; exact eJ k), val_of (D.psi y) ρ z J jN eJ] at v
  refine (gm_res _ z _ hz _).trans (v.trans (a₁.symm.trans (E'.trans (Eq.symm ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) ?_ ((gm_res _ z _ hz _).trans a₂.symm)))))))
  exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull ρ _ z _ hz _))

theorem exists_isPullDeg_id (D D' : DegPre R) {S₀ : Scheme.{0}} {A₀ : Over S₀} [GrpObj A₀] {M₀ : LB A₀.left}
    (hM₀ : M₀.IsLB) (rig₀ : LB.Gen (M₀.pull (eSec A₀))) {f : Sp R ⟶ S₀} {φ : D.P.A.left ⟶ A₀.left}
    {φ' : D'.P.A.left ⟶ A₀.left} (p : IsGrpPullback D.P.A A₀ f φ) (p' : IsGrpPullback D'.P.A A₀ f φ')
    (w : LB.Iso D.P.L (M₀.pull φ)) (w' : LB.Iso D'.P.L (M₀.pull φ')) (g : PGen w) (g' : PGen w')
    (r : PMaps w (K := PUnit) (fun _ => eSec D.P.A) (fun _ => eSec A₀) (fun _ => 1) D.rig rig₀ f)
    (r' : PMaps w' (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec A₀) (fun _ => 1) D'.rig rig₀ f)
    (xe : D'.X ≃+ D.X) (hc : ∀ x, (D'.c x).left ≫ φ' = (D.c (xe x)).left ≫ φ)
    (Wo : (Spec (CommRingCat.of R)).Opens) (hWo : genericPoint (Spec (CommRingCat.of R)) ∈ Wo) (ψW : PsiOn D Wo)
    {F : Type} [Field F] (ρ : Sp F ⟶ (TK R).left)
    (hψ : ∀ x, ∃ (pt₀ : PUnit → (Sp F ⟶ A₀.left)) (t₀ : LB.Gen (LB.LinComb M₀ pt₀ (fun _ => -1))) (s : F),
      GenRel w (LB.pullGen _ _ _ (D.psi (xe x)) ρ) t₀ s ∧ GenRel w' (LB.pullGen _ _ _ (D'.psi x) ρ) t₀ s) :
    ∃ hD : IsPullDeg (RingHom.id R) D D',
      (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R))) ≫ φ = φ' ∧ (∀ x, hD.xe x = xe x) ∧
      ∃ w₁ : LB.Iso D'.P.L (M₀.pull ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R))) ≫ φ)),
        HEq w₁ w' ∧ Tri w hD.w w₁ := by
  have hs := specOf_id R
  have hsf : specOf (RingHom.id R) ≫ f = f := by rw [hs, Category.id_comp]
  obtain ⟨e, me, he⟩ := grpPullback_iso p'
    (((isGrpPullback_pullback D.P.A (specOf (RingHom.id R))).comp p).congr hsf rfl)
  rw [← Category.assoc] at he
  subst he
  have gp : IsGrpPullback D'.P.A D.P.A (specOf (RingHom.id R))
      (e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R))) :=
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback D.P.A (specOf (RingHom.id R)))).congr
      (Category.id_comp _) rfl
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)) =
      specOf (RingHom.id R) ≫ eSec D.P.A := (cubeMapOf gp).e_comm
  obtain ⟨wD, T⟩ := exists_cancel hM₀ w w' g g' D.P.isLB D'.P.isLB
  have hc' : ∀ x, (D'.c x).left ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)) =
      (D.c (xe x)).left := fun x => by
    apply p.1.hom_ext
    · rw [Category.assoc]; exact hc x
    · rw [Category.assoc, gp.1.w, ← Category.assoc, Over.w, Over.w, hs]; exact Category.comp_id _
  obtain ⟨gW, hgW⟩ : ∃ gW : (TK R).left ⟶ (TW Wo).left, gW ≫ Wo.ι = jK R :=
    ⟨IsOpenImmersion.lift Wo.ι (jK R) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      have hy : jK R y = genericPoint (Spec (CommRingCat.of R)) := by
        rw [genericPoint_eq_bot_of_affine]
        apply PrimeSpectrum.ext
        show Ideal.comap (algebraMap R (FractionRing R)) (PrimeSpectrum.asIdeal y) = ⊥
        rw [@Ideal.eq_bot_of_prime _ _ (PrimeSpectrum.asIdeal y) (PrimeSpectrum.isPrime y)]
        exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R))
      show jK R y ∈ Wo
      rw [hy]; exact hWo), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨lam, l₁, l₂⟩ : ∃ lam : (TK R).left ⟶ (jK R ⁻¹ᵁ Wo).toScheme, lam ≫ (jK R ⁻¹ᵁ Wo).ι = 𝟙 _ ∧
      lam ≫ (jK R ∣_ Wo) = gW :=
    ⟨(isPullback_morphismRestrict (jK R) Wo).lift _ _ (hgW.trans (Category.id_comp _).symm),
      (isPullback_morphismRestrict (jK R) Wo).lift_snd _ _ _,
      (isPullback_morphismRestrict (jK R) Wo).lift_fst _ _ _⟩
  refine ⟨⟨e, me, wD, (isGen_iff _).2 (T.pgen_cancel hM₀ g g'), hE, ?_, xe,
    fun x => (hc' x).trans (by rw [hs, Category.id_comp]), Wo, ψW, gW, hgW.trans (by rw [hs, Category.comp_id]),
    fun x => ?_⟩, rfl, fun _ => rfl, w', HEq.rfl, T⟩
  · refine (maps_iff wD _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf (RingHom.id R)) _
      (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf (RingHom.id R)) hE D.P.L) (fun _ => rfl)).2 ?_
    exact T.pmaps_cancel hM₀ (fun _ => hE) r (by rw [hsf]; exact r')
  · obtain ⟨pt₀, t₀, s, h, h'⟩ := hψ x
    obtain ⟨b, hb, vb⟩ := mapsAt_of_genRel hM₀ T ρ x (xe x)
      ((Category.assoc _ _ _).trans (congrArg (jK R ≫ ·) (hc' x))) t₀ s h h'
    refine ⟨b, hb, corr_of_val D.P.isLB fun y J hJ => (vb _ _ y J hJ).trans ?_⟩
    have v := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq (xe x)) lam).trans (val_pull hJ _ _ _))
    rw [l₁, l₂] at v
    exact v.symm.trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp])).symm

end GlobalTheory.ArcData

namespace GlobalTheory

theorem arcWit_data_iso : Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (χ : Sp (PowerSeries k) ⟶ Y.X) (χ' : Sp (PowerSeries k) ⟶ Y'.X) (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ) (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ'), ∃ (hD : IsPullDeg (RingHom.id (PowerSeries k)) W'.P.D.toPre W.P.D.toPre), ((hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ = W.φ ∧ (∀ x, hD.xe (W.e x) = W'.e x) ∧ ∃ w₁ : LB.Iso W.P.D.toPre.P.L (a.D₀.P.L.pull ((hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ)), HEq w₁ W.w ∧ Tri W'.w hD.w w₁) := by
  intro h5 E _ _ _ H D l c₀ c k _ bF a O O' _ _ β β' Y Y' χ χ' W W'
  obtain ⟨s1, s2, s3, -, s5, s6⟩ := W.spec
  obtain ⟨t1, t2, t3, -, t5, t6⟩ := W'.spec
  obtain ⟨Wo, hWo, ⟨ψW⟩⟩ := h5.psiOnExists _ _ (admissibleBase_powerSeries k) W'.P.D
  let F := AlgebraicClosure (FractionRing (PowerSeries k))
  let κ : k →+* F := ((algebraMap (FractionRing (PowerSeries k)) F).comp (algebraMap (PowerSeries k) _)).comp
    (PowerSeries.C (R := k))
  letI : Algebra (FractionRing k) F := (IsFractionRing.lift (K := FractionRing k) (g := κ) κ.injective).toAlgebra
  have ha : ∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
      algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C (R := k) x)) :=
    fun x => IsFractionRing.lift_algebraMap (K := FractionRing k) (g := κ) κ.injective x
  have k₁ := (s6 F _ ha rfl).1
  have k₂ := (t6 F _ ha rfl).1
  let xe : W.P.D.toPre.X ≃+ W'.P.D.toPre.X := W.e.symm.toAddEquiv.trans W'.e.toAddEquiv
  have hxe : ∀ y, xe (W.e y) = W'.e y := fun y => congrArg W'.e (W.e.symm_apply_apply y)
  obtain ⟨hD, h₁, h₂, h₃⟩ := ArcData.exists_isPullDeg_id W'.P.D.toPre W.P.D.toPre a.D₀.P.isLB a.D₀.rig t1 s1 W'.w W.w
    ((isGen_iff _).1 t2) ((isGen_iff _).1 s2)
    ((maps_iff W'.w _ (fun _ => eSec a.D₀.P.A) _ W'.P.D.toPre.rig a.D₀.rig _ _
      (rigPull_le W'.φ _ W'.he a.D₀.P.L) (fun _ => rfl)).1 t3)
    ((maps_iff W.w _ (fun _ => eSec a.D₀.P.A) _ W.P.D.toPre.rig a.D₀.rig _ _
      (rigPull_le W.φ _ W.he a.D₀.P.L) (fun _ => rfl)).1 s3)
    xe (fun x => by
      obtain ⟨y, rfl⟩ := W.e.surjective x
      rw [hxe]
      exact (s5 y).trans (t5 y).symm) Wo hWo ψW (F := F) (jFK (R := PowerSeries k) F) (fun x => by
      obtain ⟨y, rfl⟩ := W.e.surjective x
      rw [hxe]
      exact ⟨_, _, _, k₂ y, k₁ y⟩)
  exact ⟨hD, h₁, fun x => (h₂ _).trans (hxe x), h₃⟩

end GlobalTheory
