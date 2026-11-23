import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.QkExtExistsSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

theorem uwRQe_gen {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {Y Y' : Scheme.{0}} {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} {ε : K → ℤ} (g : Y' ⟶ Y) (hφ : ∀ k, φ' k = g ≫ φ k)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ t' : LB.Gen (LB.LinComb L φ' ε), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
        val t' r z J = val t (r ≫ g) z J := by
  obtain rfl : φ' = fun k => g ≫ φ k := funext hφ
  refine ⟨LB.pullGen L φ ε t g, LB.isGen_pullGen (φ := φ) (ε := ε) (c := t) (hc := ht) (h := g), ?_⟩
  intro Z r z J hg
  first
    | exact val_pull hg t g r
    | exact val_pull t g r

section QkExt

variable {R : Type} [CommRing R] [IsDomain R] (D : Out.DegPre R) {F F' : Type} [Field F]
  [Algebra (FractionRing R) F] [Field F'] [Algebra (FractionRing R) F'] (f : F →+* F')
  (hf : ∀ r : FractionRing R, f (algebraMap _ F r) = algebraMap _ F' r)

include hf

theorem uwRQe_e : CommRingCat.ofHom (algebraMap (FractionRing R) F) ≫ CommRingCat.ofHom f =
    CommRingCat.ofHom (algebraMap (FractionRing R) F') := by
  ext x
  first
    | exact hf x
    | simpa using hf x

theorem uwRQe_rho_jFK : spMap f ≫ Out.jFK (R := R) F = Out.jFK (R := R) F' := by
  first
    | rw [← Spec.map_comp, uwRQe_e f hf]
    | (simp only [spMap, Out.jFK]; rw [← Spec.map_comp, uwRQe_e f hf])

def uwRQe_rho : Out.TF (R := R) F' ⟶ Out.TF (R := R) F :=
  Over.homMk (spMap f) (by
    show spMap f ≫ (Out.jFK (R := R) F ≫ Out.jK R) = Out.jFK (R := R) F' ≫ Out.jK R
    rw [← Category.assoc, uwRQe_rho_jFK f hf])

theorem uwRQe_cF (χ : D.X) : Out.DegPre.cF D F' χ = uwRQe_rho f hf ≫ Out.DegPre.cF D F χ := by
  first
    | simp [Out.DegPre.cF]
    | (show toUnit _ ≫ D.c χ = uwRQe_rho f hf ≫ toUnit _ ≫ D.c χ
       rw [← Category.assoc, CartesianMonoidalCategory.comp_toUnit])

theorem uwRQe_zeroF : Out.DegPre.zeroF D F' = uwRQe_rho f hf ≫ Out.DegPre.zeroF D F := by
  first
    | simp [Out.DegPre.zeroF]
    | (show toUnit _ ≫ η[D.P.A] = uwRQe_rho f hf ≫ toUnit _ ≫ η[D.P.A]
       rw [← Category.assoc, CartesianMonoidalCategory.comp_toUnit])

theorem uwRQe_padd (x y : Out.TF (R := R) F ⟶ D.P.A) :
    padd D.P.A (uwRQe_rho f hf ≫ x) (uwRQe_rho f hf ≫ y) = uwRQe_rho f hf ≫ padd D.P.A x y := by
  simp only [padd]
  rw [← Category.assoc, CartesianMonoidalCategory.comp_lift]

theorem uwRQe_gtφ (b : Out.TF (R := R) F ⟶ D.P.A) (χ : D.X) (k : Fin 4) :
    Out.DegPre.gtφ D F' (uwRQe_rho f hf ≫ b) χ k = spMap f ≫ Out.DegPre.gtφ D F b χ k := by
  have e : ∀ m : Out.TF (R := R) F ⟶ D.P.A, (uwRQe_rho f hf ≫ m).left = spMap f ≫ m.left :=
    fun _ => rfl
  fin_cases k
  · change (padd D.P.A (Out.DegPre.cF D F' χ) (uwRQe_rho f hf ≫ b)).left =
      spMap f ≫ (padd D.P.A (Out.DegPre.cF D F χ) b).left
    rw [uwRQe_cF D f hf χ, uwRQe_padd D f hf]
    all_goals exact e _
  · change (Out.DegPre.cF D F' χ).left = spMap f ≫ (Out.DegPre.cF D F χ).left
    rw [uwRQe_cF D f hf χ]
    all_goals exact e _
  · exact e b
  · change (Out.DegPre.zeroF D F').left = spMap f ≫ (Out.DegPre.zeroF D F).left
    rw [uwRQe_zeroF D f hf]
    all_goals exact e _

theorem uwRQe_sgen (g : Out.GtPtF D F) (χ : D.X) :
    ∃ t' : LB.Gen (LB.LinComb D.P.L (Out.DegPre.gtφ D F' (uwRQe_rho f hf ≫ g.b) χ) Out.DegPre.gtε), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.TF (R := R) F').left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι),
        Good D.P.L z J → val t' r z J = val (g.s χ) (r ≫ spMap f) z J :=
  uwRQe_gen D.P.isLB (spMap f) (fun k => uwRQe_gtφ D f hf g.b χ k) (g.s χ) (g.isGen χ)

theorem uwRQe_cub {Z : Scheme.{0}} {z : Z} {J : (Z ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J)
    (x x' y : Out.TF (R := R) F' ⟶ D.P.A) (u u' v : Out.TF (R := R) F ⟶ D.P.A) (hx : x = uwRQe_rho f hf ≫ u)
    (hx' : x' = uwRQe_rho f hf ≫ u') (hy : y = uwRQe_rho f hf ≫ v) (r : Z ⟶ (Out.TF (R := R) F').left) :
    val (Out.DegPre.cubAt D F' x x' y) r z J = val (Out.DegPre.cubAt D F u u' v) (r ≫ spMap f) z J := by
  subst hx hx' hy
  have e : lift (uwRQe_rho f hf ≫ u) (lift (uwRQe_rho f hf ≫ u') (uwRQe_rho f hf ≫ v)) =
      uwRQe_rho f hf ≫ lift u (lift u' v) := by
    rw [CartesianMonoidalCategory.comp_lift, CartesianMonoidalCategory.comp_lift]
  simp only [Out.DegPre.cubAt]
  rw [e]
  first
    | exact (val_pull D.cub.t _ r).trans ((congrArg (fun q => val D.cub.t q z J)
        (Category.assoc r (spMap f) _).symm).trans (val_pull D.cub.t _ (r ≫ spMap f)).symm)
    | exact (val_pull hJ D.cub.t _ r).trans ((congrArg (fun q => val D.cub.t q z J)
        (Category.assoc r (spMap f) _).symm).trans (val_pull hJ D.cub.t _ (r ≫ spMap f)).symm)

def uwRQe_ext (g : Out.GtPtF D F) : Out.GtPtF D F' where
  b := uwRQe_rho f hf ≫ g.b
  s χ := (uwRQe_sgen D f hf g χ).choose
  isGen χ := (uwRQe_sgen D f hf g χ).choose_spec.1
  s_zero := corr_of_val D.P.isLB fun y J hJ => by
    rw [(uwRQe_sgen D f hf g 0).choose_spec.2 _ _ y J hJ, val_corr hJ g.s_zero, val_one, val_one]
  mult χ χ' := corr_of_val D.P.isLB fun y J hJ =>
    (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) ((uwRQe_sgen D f hf g (χ + χ')).choose_spec.2 _ _ y J hJ)
      (uwRQe_cub D f hf hJ _ _ _ _ _ _ (uwRQe_cF D f hf χ) (uwRQe_cF D f hf χ') rfl (𝟙 _))).trans
      ((val_mul hJ _ _ _).symm.trans ((val_corr hJ (g.mult χ χ') _).trans ((val_mul hJ _ _ _).trans
        ((congrArg₂ (· * ·) ((uwRQe_sgen D f hf g χ).choose_spec.2 _ _ y J hJ)
          ((uwRQe_sgen D f hf g χ').choose_spec.2 _ _ y J hJ)).symm.trans (val_mul hJ _ _ _).symm)))))

theorem uwRQe_val (g : Out.GtPtF D F) (χ : D.X) {Z : Scheme.{0}} (r : Z ⟶ (Out.TF (R := R) F').left) (z : Z)
    (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (hJ : Good D.P.L z J) :
    val ((uwRQe_ext D f hf g).s χ) r z J = val (g.s χ) (r ≫ spMap f) z J :=
  (uwRQe_sgen D f hf g χ).choose_spec.2 Z r z J hJ

theorem uwRQe_isZero {g : Out.GtPtF D F} (h : g.IsZero) : (uwRQe_ext D f hf g).IsZero := by
  unfold Out.GtPtF.IsZero at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun χ => corr_of_val D.P.isLB fun p J hJ => ?_⟩
  · show uwRQe_rho f hf ≫ g.b = _
    rw [h1, uwRQe_zeroF D f hf]
  · rw [uwRQe_val D f hf g χ _ p J hJ, val_corr hJ (h2 χ), val_one, val_one]

theorem uwRQe_isAdd {g g' g'' : Out.GtPtF D F} (h : g.IsAdd g' g'') :
    (uwRQe_ext D f hf g).IsAdd (uwRQe_ext D f hf g') (uwRQe_ext D f hf g'') := by
  unfold Out.GtPtF.IsAdd at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun χ => corr_of_val D.P.isLB fun p J hJ => ?_⟩
  · show uwRQe_rho f hf ≫ g''.b = padd D.P.A (uwRQe_rho f hf ≫ g.b) (uwRQe_rho f hf ≫ g'.b)
    rw [h1, uwRQe_padd D f hf]
  · refine (val_mul hJ _ _ _).trans ?_
    refine Eq.trans ?_ (val_mul hJ _ _ _).symm
    rw [uwRQe_val D f hf g'' χ _ p J hJ, uwRQe_val D f hf g χ _ p J hJ, uwRQe_val D f hf g' χ _ p J hJ]
    refine (congrArg₂ (· * ·) rfl
      (uwRQe_cub D f hf hJ _ _ _ _ _ _ (uwRQe_cF D f hf χ) rfl rfl (𝟙 _))).trans ?_
    exact (val_mul hJ _ _ _).symm.trans ((val_corr hJ (h2 χ) _).trans (val_mul hJ _ _ _))

theorem uwRQe_isIota {y : D.X} {g : Out.GtPtF D F} (h : g.IsIota y) : (uwRQe_ext D f hf g).IsIota y := by
  unfold Out.GtPtF.IsIota at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun χ => corr_of_val D.P.isLB fun p J hJ => ?_⟩
  · show uwRQe_rho f hf ≫ g.b = _
    rw [h1, uwRQe_cF D f hf y]
  · rw [uwRQe_val D f hf g χ _ p J hJ, val_corr hJ (h2 χ)]
    first
      | exact (val_pull _ _ _).trans ((congrArg (fun q => val (D.io y χ) q p J)
          (by rw [Category.assoc, uwRQe_rho_jFK f hf])).trans (val_pull _ _ _).symm)
      | exact (val_pull hJ _ _ _).trans ((congrArg (fun q => val (D.io y χ) q p J)
          (by rw [Category.assoc, uwRQe_rho_jFK f hf])).trans (val_pull hJ _ _ _).symm)

theorem uwRQe_isNsmul {k : ℕ} {g h : Out.GtPtF D F} (H : Out.GtPtF.IsNsmul k g h) :
    Out.GtPtF.IsNsmul k (uwRQe_ext D f hf g) (uwRQe_ext D f hf h) := by
  unfold Out.GtPtF.IsNsmul at H ⊢
  obtain ⟨gs, h0, hs, hl⟩ := H
  exact ⟨fun i => uwRQe_ext D f hf (gs i), uwRQe_isZero D f hf h0, fun i => uwRQe_isAdd D f hf (hs i),
    congrArg (uwRQe_ext D f hf) hl⟩

end QkExt

theorem qkExtExists : QkExtExistsSt := by
  unfold QkExtExistsSt
  intro R _ _ D F F' _ _ _ _ f hf k p
  obtain ⟨h, hn, hi⟩ := p.eq
  refine ⟨⟨p.y, uwRQe_ext D f hf p.g, ⟨uwRQe_ext D f hf h, uwRQe_isNsmul D f hf hn, uwRQe_isIota D f hf hi⟩⟩, ?_⟩
  unfold QkExt
  dsimp only
  refine ⟨rfl, rfl, fun χ => corr_of_val D.P.isLB fun q J hJ => ?_⟩
  rw [uwRQe_val D f hf p.g χ _ q J hJ]
  first
    | exact (val_pull _ _ _).symm
    | exact (val_pull hJ _ _ _).symm

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
