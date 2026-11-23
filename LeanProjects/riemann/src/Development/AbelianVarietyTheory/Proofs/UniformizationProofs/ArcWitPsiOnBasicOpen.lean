import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ArcPsiOn

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ArcPull

theorem genRel_iff_val {F : Type} [Field F] {B B₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀} (hM : M.IsLB) (hM₀ : M₀.IsLB)
    {φ : B ⟶ B₀} (w : LB.Iso M (M₀.pull φ)) {pt : PUnit → (Sp F ⟶ B)} {pt₀ : PUnit → (Sp F ⟶ B₀)} {ε : PUnit → ℤ}
    (t : LB.Gen (LB.LinComb M pt ε)) (t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)) (x : F) (z : Sp F) :
    GenRel w t t₀ x ↔ pt PUnit.unit ≫ φ = pt₀ PUnit.unit ∧ ∀ J₀ J, Good M₀ z J₀ → Good M z J →
      (om w z J₀ J (pt PUnit.unit) ^ ε PUnit.unit * val t (𝟙 _) z J).val = toStk z x * (val t₀ (𝟙 _) z J₀).val := by
  rw [genRel_iff w t t₀ x z]
  constructor
  · rintro ⟨hp, H⟩
    refine ⟨hp _, fun J₀ J hJ₀ hJ => ?_⟩
    have e := H (fun k => J (pt k)) (fun k => J₀ (pt k ≫ φ)) (fun k => hJ₀ (pt k ≫ φ)) (fun k => hJ (pt k))
    rw [Fintype.prod_unique] at e
    rw [val_of t _ z J (fun k => J (pt k)) (fun k => by rw [Category.id_comp]),
      val_of t₀ _ z J₀ (fun k => J₀ (pt k ≫ φ)) (fun k => by rw [Category.id_comp, hp])]
    exact e
  · rintro ⟨hp, H⟩
    refine ⟨fun _ => hp, fun j j₀ h₀ h₁ => ?_⟩
    obtain ⟨J, hJ, eJ⟩ := exists_good M hM z pt j (fun _ _ _ => rfl) h₁
    obtain ⟨J₀, hJ₀, eJ₀⟩ := exists_good M₀ hM₀ z (fun k => pt k ≫ φ) j₀ (fun _ _ _ => rfl) h₀
    have e := H J₀ J hJ₀ hJ
    rw [val_of t _ z J j (fun k => by rw [Category.id_comp]; exact eJ k),
      val_of t₀ _ z J₀ j₀ (fun k => by rw [Category.id_comp, ← eJ₀ k]; exact congrArg J₀ hp.symm), om, eJ,
      eJ₀ PUnit.unit] at e
    rw [Fintype.prod_unique]
    exact e

theorem exists_unit_basicOpen {R : Type} [CommRing R] (u : R) :
    ∃ c : Γ((TW (R := R) (PrimeSpectrum.basicOpen u)).left, ⊤)ˣ, ∀ (F : Type) [Field F] (r : R →+* F)
      (z : Sp F ⟶ (TW (R := R) (PrimeSpectrum.basicOpen u)).left),
      z ≫ (TW (R := R) (PrimeSpectrum.basicOpen u)).hom = specOf r → ∀ (p : Sp F) (n : ℤ),
      (gm z p ⊤ (c ^ n)).val = toStk p (r u ^ n) := by
  let U : (Spec (CommRingCat.of R)).Opens := PrimeSpectrum.basicOpen u
  let s : Γ(Spec (CommRingCat.of R), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom u
  have hc : IsUnit ((U.ι.app ⊤).hom s) := by
    apply U.toScheme.toRingedSpace.isUnit_of_isUnit_germ
    intro y hy
    have : y ∈ U.toScheme.basicOpen ((U.ι.app ⊤).hom s) := by
      rw [← Scheme.preimage_basicOpen]
      show U.ι y ∈ (Spec (CommRingCat.of R)).basicOpen s
      rw [basicOpen_eq_of_affine]
      exact y.2
    exact (Scheme.mem_basicOpen _ _ y hy).1 this
  refine ⟨hc.unit, fun F _ r z hz p n => ?_⟩
  have e : (gm z p ⊤ hc.unit).val = toStk p (r u) := by
    have e₁ : (gm z p ⊤ hc.unit).val = gs (z ≫ U.ι) p ⊤ s :=
      (gs_unit z p ⊤ trivial hc.unit).symm.trans (gs_pull z U.ι p ⊤ trivial s)
    have hz' : z ≫ U.ι = specOf r := hz
    rw [e₁, hz', gs_eq _ p ⊤ trivial]
    have nat := congrArg (fun q => q.hom u) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom r))
    exact congrArg ((Sp F).presheaf.germ ⊤ p trivial).hom nat.symm
  have h0 : r u ≠ 0 := fun h => by
    rw [h, map_zero] at e
    exact (gm z p ⊤ hc.unit).ne_zero e
  have e' : Units.map (toStk p).toMonoidHom (Units.mk0 _ h0) = gm z p ⊤ hc.unit := Units.ext e.symm
  refine (congrArg Units.val ((map_zpow (gm z p ⊤) hc.unit n).trans ((congrArg (· ^ n) e'.symm).trans
    (map_zpow _ _ n).symm))).trans ?_
  show toStk p _ = _
  rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]

theorem val_scale' {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)ˣ) (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val (scaleGen c t) r z J = gm r z ⊤ c * val t r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ (hJ.mem φ r) _) rfl)

variable {O' R : Type} [CommRing O'] [IsDomain O'] [CommRing R] [IsDomain R] {D₀ : DegPre O'} {D : DegPre R}

theorem exists_gen_on (f : O' →+* R) (u : R) {φ : D.P.A.left ⟶ D₀.P.A.left} (w : LB.Iso D.P.L (D₀.P.L.pull φ))
    (hw : w.IsGen) (y : D₀.X) (x : D.X) (hc : (D.c x).left ≫ φ = spMap f ≫ (D₀.c y).left)
    (hy : PsiUnitOn D₀ y Set.univ) (n : ℤ) :
    ∃ s : LB.Gen (LB.LinComb D.P.L (K := PUnit)
        (fun _ => (toUnit (TW (R := R) (PrimeSpectrum.basicOpen u)) ≫ D.c x).left) (fun _ => -1)), s.IsGen ∧
      ∀ (F : Type) [Field F] (r : R →+* F) (z : Sp F ⟶ (TW (R := R) (PrimeSpectrum.basicOpen u)).left),
        z ≫ (TW (R := R) (PrimeSpectrum.basicOpen u)).hom = specOf r → ∀ j : Sp F ⟶ (TK O').left,
        j ≫ jK O' = specOf r ≫ spMap f →
        GenRel w (LB.pullGen _ _ _ s z) (LB.pullGen _ _ _ (D₀.psi y) j) (r u ^ n) := by
  obtain ⟨t, ht, H⟩ := (psiUnitOn_univ_iff D₀ y).1 hy
  obtain ⟨c, hcu⟩ := exists_unit_basicOpen u
  have hψ : (toUnit (TW (R := R) (PrimeSpectrum.basicOpen u)) ≫ D.c x).left ≫ φ =
      ((TW (R := R) (PrimeSpectrum.basicOpen u)).hom ≫ spMap f) ≫ (D₀.c y).left := by
    show ((TW (R := R) (PrimeSpectrum.basicOpen u)).hom ≫ (D.c x).left) ≫ φ = _
    rw [Category.assoc, hc, Category.assoc]
  obtain ⟨a, ha, va⟩ := exists_down_om hw D₀.P.isLB D.P.isLB (K := PUnit)
    (φ' := fun _ => (toUnit (TW (R := R) (PrimeSpectrum.basicOpen u)) ≫ D.c x).left)
    ((TW (R := R) (PrimeSpectrum.basicOpen u)).hom ≫ spMap f) (fun _ => hψ) t ht
  refine ⟨scaleGen (c ^ n) a, scaleGen_isGen _ _ ha, fun F _ r z hz j hj => ?_⟩
  have p : Sp F := (default : PrimeSpectrum F)
  have hzj : z ≫ (TW (R := R) (PrimeSpectrum.basicOpen u)).hom ≫ spMap f = j ≫ jK O' := by
    rw [← Category.assoc, hz, hj]
  refine (genRel_iff_val D.P.isLB D₀.P.isLB w _ _ _ p).2 ⟨?_, fun J₀ J hJ₀ hJ => ?_⟩
  · show (z ≫ (toUnit (TW (R := R) (PrimeSpectrum.basicOpen u)) ≫ D.c x).left) ≫ φ = j ≫ jK O' ≫ (D₀.c y).left
    rw [Category.assoc, hψ, ← Category.assoc, hzj, Category.assoc]
  · have e := va _ z p J₀ J hJ₀ hJ
    rw [Fintype.prod_unique, hzj, ← val_pull hJ₀, val_corr hJ₀ H] at e
    rw [val_pull hJ, val_pull hJ₀, Category.id_comp, Category.id_comp, val_scale' _ _ _ hJ, e, ← hcu F r z hz p n,
      ← Units.val_mul, mul_left_comm]

theorem val_eq_of_genRel {F : Type} [Field F] {B B₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀} (hM : M.IsLB) (hM₀ : M₀.IsLB)
    {φ : B ⟶ B₀} {w : LB.Iso M (M₀.pull φ)} {pt pt' : PUnit → (Sp F ⟶ B)} {pt₀ : PUnit → (Sp F ⟶ B₀)} {ε : PUnit → ℤ}
    {t : LB.Gen (LB.LinComb M pt ε)} {t' : LB.Gen (LB.LinComb M pt' ε)} {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)} {x : F}
    (hp : pt PUnit.unit = pt' PUnit.unit) (h : GenRel w t t₀ x) (h' : GenRel w t' t₀ x) (z : Sp F) {J} (hJ : Good M z J) :
    val t (𝟙 _) z J = val t' (𝟙 _) z J := by
  obtain ⟨J₀, hJ₀⟩ := DegPull.exists_good' hM₀ z
  have e := ((genRel_iff_val hM hM₀ w _ _ _ z).1 h).2 J₀ J hJ₀ hJ
  have e' := ((genRel_iff_val hM hM₀ w _ _ _ z).1 h').2 J₀ J hJ₀ hJ
  rw [hp, ← e'] at e
  exact mul_left_cancel (Units.ext e)

theorem corr_of_geom (U : (Spec (CommRingCat.of R)).Opens) (hU : (U : Set (Spec (CommRingCat.of R))).Nonempty)
    (x : D.X) (s : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (toUnit (TW U) ≫ D.c x).left) (fun _ => -1)))
    (F : Type) [Field F] [Algebra (FractionRing R) F]
    (H : ∀ z : Sp F ⟶ (TW U).left, z ≫ (TW U).hom = jFK (R := R) F ≫ jK R → ∀ p J, Good D.P.L p J →
      val s z p J = val (D.psi x) (jFK (R := R) F) p J) :
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ s (jK R ∣_ U)) (LB.pullGen D.P.L _ _ (D.psi x) (jK R ⁻¹ᵁ U).ι) := by
  have sep : D.P.A.left.IsSeparated := by
    have := D.P.isAb.proper
    refine ⟨?_⟩
    rw [← terminal.comp_from D.P.A.hom]
    infer_instance
  obtain ⟨lam, hl⟩ : ∃ lam : Sp F ⟶ (jK R ⁻¹ᵁ U).toScheme, lam ≫ (jK R ⁻¹ᵁ U).ι = jFK (R := R) F :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact TauPull.jK_mem _ U hU), IsOpenImmersion.lift_fac _ _ _⟩
  have hκ : (lam ≫ jK R ∣_ U) ≫ U.ι = jFK (R := R) F ≫ jK R := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hl]
  have p : Sp F := (default : PrimeSpectrum F)
  have hss : Subsingleton (Spec (CommRingCat.of (FractionRing R))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))
  refine TauPull.corr_of_dense D.P.isLB lam p (fun V ⟨y, hy⟩ => ?_) fun J hJ => ?_
  · rw [show lam p = y from Subtype.ext (Subsingleton.elim _ _)]
    exact hy
  · rw [val_pull hJ, val_pull hJ, hl]
    exact H _ hκ p J hJ

end GlobalTheory.ArcPsiOn

open GlobalTheory.ArcPsiOn GlobalTheory.ArcPull ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem GlobalTheory.arcWit_psiOn_basicOpen : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (Dm : Geo.Tor.Datum H) (l : Geo.Tor.Level H) (Xo : Geo.Tor.Moduli Dm l) (c : Geo.Tor.Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Geo.Tor.Model Xo c β) (O' : Type) [CommRing O'] [IsDomain O'] (b : O →+* O') (a : Geo.Tor.ArcIn Dm l β O' b) (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (f : O' →+* R), Function.Injective f → ∀ (u : R), u ≠ 0 → ∀ (χ : Geo.Tor.Sp R ⟶ Y.X) (W : Geo.Tor.ArcWit Y a I f u χ), ∃ ψW : PsiOn W.P.D.toPre (PrimeSpectrum.basicOpen u), ∀ (F : Type) [Field F] [Algebra (FractionRing O') F] (r : R →+* F) (z : Spec (CommRingCat.of F) ⟶ (TW (R := R) (PrimeSpectrum.basicOpen u)).left), z ≫ (TW (R := R) (PrimeSpectrum.basicOpen u)).hom = specOf r → (∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) = r (f x)) → ∀ y, Geo.Tor.GenRel W.w (LB.pullGen _ _ _ (ψW.psi (W.e y)) z) (LB.pullGen _ _ _ (a.D₀.psi y) (jFK (R := O') F)) (r u ^ (a.be y y / 2)) := by
  intro E _ _ _ H Dm l Xo c O _ β Y O' _ _ b a R _ _ I f hf u hu χ W
  obtain ⟨-, s2, -, -, s5, s6⟩ := W.spec
  choose s hs H using fun x : W.P.D.toPre.X => exists_gen_on f u W.w s2 (W.e.symm x) x
    (by simpa only [LinearEquiv.apply_symm_apply] using s5 (W.e.symm x)) (a.gen _)
    (a.be (W.e.symm x) (W.e.symm x) / 2)
  refine ⟨⟨s, hs, fun x => ?_⟩, fun F _ _ r z hz hr y => ?_⟩
  · let F := AlgebraicClosure (FractionRing R)
    letI : Algebra (FractionRing O') F := ((algebraMap (FractionRing R) F).comp (fracMap hf)).toAlgebra
    have hF : ∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) =
        algebraMap (FractionRing R) F (algebraMap R _ (f x)) := fun x =>
      congrArg (algebraMap (FractionRing R) F) (fracMap_algebraMap hf x)
    refine corr_of_geom _ ⟨⟨⊥, Ideal.isPrime_bot⟩, hu⟩ x (s x) F fun z hz p J hJ => ?_
    have hj : jFK (R := R) F ≫ jK R = specOf ((algebraMap (FractionRing R) F).comp (algebraMap R _)) :=
      (spMap_comp _ _).symm
    have k := H x F _ z (hz.trans hj) (jFK (R := O') F) ((spMap_comp _ _).symm.trans
      ((congrArg spMap (RingHom.ext hF)).trans (spMap_comp f _)))
    have k' := (s6 F _ hF rfl).1 (W.e.symm x)
    rw [LinearEquiv.apply_symm_apply] at k'
    have e := val_eq_of_genRel W.P.D.toPre.P.isLB a.D₀.P.isLB (by
      show z ≫ (TW (R := R) (PrimeSpectrum.basicOpen u)).hom ≫ (W.P.D.toPre.c x).left =
        jFK (R := R) F ≫ jK R ≫ (W.P.D.toPre.c x).left
      rw [← Category.assoc, hz, Category.assoc]) k k' p hJ
    rwa [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp] at e
  · have k := H (W.e y) F r z hz (jFK (R := O') F) ((spMap_comp _ _).symm.trans
      ((congrArg spMap (RingHom.ext hr)).trans (spMap_comp f r)))
    rw [LinearEquiv.symm_apply_apply] at k
    exact k
