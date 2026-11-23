import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.QkRelQkScaleEquiv

noncomputable section

namespace GlobalTheory.TauTwist

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorusExt

section Sections

variable {X Y Z : Scheme.{0}} {L : LB X} {K K₁ K₂ K₃ : Type} [Fintype K] [Fintype K₁] [Fintype K₂] [Fintype K₃]

def scaleSec {M : LB Y} (c : Γ(Y, ⊤)ˣ) (s : LB.Sec M) : LB.Sec M where
  f j := (res (le_top : M.U j ≤ ⊤) c).val * s.f j
  compat i j := by
    have e : ∀ {W W' : Y.Opens} (h : W' ≤ W), (Y.presheaf.map (homOfLE h).op).hom (res (le_top : W ≤ ⊤) c).val =
        (res (le_top : W' ≤ ⊤) c).val := fun h => congrArg Units.val (res_res' _ _ c)
    rw [map_mul, map_mul, s.compat i j, e, e, mul_left_comm]

theorem sval_scaleSec {φ : K → (Y ⟶ X)} {ε : K → ℤ} (c : Γ(Y, ⊤)ˣ) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) {z : Z}
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) : sval (scaleSec c s) r z J = (gm r z ⊤ c).val * sval s r z J :=
  (gs_mul r z _ (hJ.mem φ r) _ _).trans (congrArg₂ (· * ·) ((gs_unit r z _ (hJ.mem φ r) _).trans
    (congrArg Units.val (gm_res r z le_top (hJ.mem φ r) c))) rfl)

variable {F : Type} [Field F]

def constUnit (p : Y ⟶ Sp F) (a : Fˣ) : Γ(Y, ⊤)ˣ := pullU p ⊤ (unitOn a)

theorem gm_constUnit (p : Y ⟶ Sp F) (a : Fˣ) (r : Z ⟶ Y) (z : Z) : gm r z ⊤ (constUnit p a) = unitAt (r ≫ p) z a :=
  gm_pull r p z ⊤ trivial (unitOn a)

theorem secRel_scale (hL : L.IsLB) (p : Y ⟶ Sp F) {h : Y ⟶ Y} (hp : h ≫ p = p) {e : Sp F ⟶ Y} (he : e ≫ p = 𝟙 _)
    {φ₁ : K₁ → (Y ⟶ X)} {ε₁ : K₁ → ℤ} {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {φ₃ : K₃ → (Y ⟶ X)} {ε₃ : K₃ → ℤ}
    {φ : K → (Sp F ⟶ X)} {ε : K → ℤ} (s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)) (s₂ : LB.Sec (LB.LinComb L φ₂ ε₂))
    {v v' : LB.Gen (LB.LinComb L φ ε)} {a b c : Fˣ} (habc : a = b * c)
    (hv : ∀ y J, Good L y J → val v' (𝟙 _) y J = unitAt (𝟙 _) y c * val v (𝟙 _) y J)
    (H : ∀ u : LB.Gen (LB.LinComb L φ₃ ε₃), u.IsGen → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u e) v →
      GeneratorPullback.SecRel L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h φ₃ ε₃ u)
    (u : LB.Gen (LB.LinComb L φ₃ ε₃)) (hu : u.IsGen) (hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u e) v') :
    GeneratorPullback.SecRel L φ₁ ε₁ (scaleSec (constUnit p a) s₁) φ₂ ε₂ (scaleSec (constUnit p b) s₂) h φ₃ ε₃ u := by
  have H₀ := (secRel_iff hL _ _ _ _ _ _ _ _ _ _).1 (H (scaleGen (constUnit p c⁻¹) u) (scaleGen_isGen _ _ hu)
    (corr_of_val hL fun y J hJ => by
      have e₁ := (val_pull hJ _ _ _).symm.trans ((val_corr hJ hc (𝟙 _)).trans (hv y J hJ))
      rw [val_pull hJ, val_scaleGen _ _ _ hJ, gm_constUnit, e₁, Category.assoc, he, Category.id_comp, map_inv,
        inv_mul_cancel_left]))
  refine (secRel_iff hL _ _ _ _ _ _ _ _ _ _).2 fun y J hJ => ?_
  rw [sval_scaleSec _ _ _ hJ, sval_scaleSec _ _ _ hJ, H₀ _ _ y J hJ, val_scaleGen _ _ _ hJ, gm_constUnit, gm_constUnit,
    gm_constUnit, Category.assoc, hp, habc, map_mul, map_inv, Units.val_mul, Units.val_mul]
  have := (unitAt (𝟙 Y ≫ p) y c).mul_inv
  linear_combination ((unitAt (𝟙 Y ≫ p) y b).val * sval s₂ (𝟙 Y ≫ h) y J * (val u (𝟙 Y) y J).val) * this

end Sections

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {ψ : PsiFam D} {hψ : ∀ χ, (ψ χ).IsGen}
  {F : Type} [Field F] [Algebra (FractionRing R) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.X] {w : O} {t : D.X → D.X → (FractionRing R)ˣ} {k : ℕ}
  {r : D.X → D.X → Fˣ}

def famScale (hw : w + star w = 1) (ht : IsScalarForm O t) (hq : PsiRel D ψ fun y => t y (w • y))
    (hr : IsRootForm O k t r) (hψ : ∀ χ, (ψ χ).IsGen) (s : Fam D F k) : Fam (withPsi D ψ hψ) F k where
  s α := scaleSec (constUnit (fst (TF (R := R) F) D.P.A).left (r α (w • α))) (s.s α)
  fe mu α := by
    refine secRel_scale D.P.isLB (fst (TF (R := R) F) D.P.A).left
      (congrArg (fun q => q.left) (lift_fst _ _ : DegPre.trF D F mu ≫ _ = _))
      (congrArg (fun q => q.left) (lift_fst _ _ : DegPre.zF D F ≫ _ = _)) _ _
      (c := Units.map (algebraMap (FractionRing R) F).toMonoidHom (t mu α * t mu (w • mu) ^ k)) ?_
      (fun y J hJ => ?_) (s.fe mu α)
    · rw [hr.1.refine_add hw, map_mul, map_pow, ← hr.2, ← hr.2, smul_comm w k mu, hr.1.nsmul_left, hr.1.nsmul_right,
        hr.1.nsmul_right, hr.1.symm α mu]
      ac_rfl
    · have key : ∀ (y : (TF (R := R) F).left) J, Good D.P.L y J →
          val (DegPre.famMult (withPsi D ψ hψ) F k mu α) (𝟙 (TF (R := R) F) :).left y J =
          unitAt ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) y (t mu α * t mu (w • mu) ^ k) *
            val (DegPre.famMult D F k mu α) (𝟙 (TF (R := R) F) :).left y J := fun y J hJ => by
        rw [val_famMult (D := D) (𝟙 (TF (R := R) F)) hJ k mu α]
        refine (val_famMult (D := withPsi D ψ hψ) (𝟙 (TF (R := R) F)) hJ k mu α).trans ?_
        refine (congrArg₂ (· * ·) (hq.val_tau (ht.refine_add hw mu α) _ hJ) (congrArg₂ (· * ·)
          ((val_powGen _ _ _ _ _).trans (congrArg (· ^ k) (hq mu _ _ y J hJ))) rfl)).trans ?_
        rw [map_mul, map_pow, mul_pow, val_powGen (D.psi mu), _root_.mul_assoc (_ ^ k), _root_.mul_mul_mul_comm]
        rfl
      exact (key y J hJ).trans (congrArg₂ (· * ·) (unitAt_spMap _ (algebraMap (FractionRing R) F) y _) rfl)

variable (hw : w + star w = 1) (ht : IsScalarForm O t) (hq : PsiRel D ψ fun y => t y (w • y)) (hr : IsRootForm O k t r)

theorem phiRel_famScale (p : QkPt D F k)
    (v : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k))) {s s' : Fam D F k}
    (h : PhiRel D F k p v s s') :
    PhiRel (withPsi D ψ hψ) F k (qkScale hw ht hq hr hψ p) (scaleGen (unitOn (r p.y (w • p.y))) v)
      (famScale hw ht hq hr hψ s) (famScale hw ht hq hr hψ s') := fun α => by
  refine secRel_scale D.P.isLB (fst (TF (R := R) F) D.P.A).left
    (congrArg (fun q => q.left) (lift_fst _ _ : DegPre.trPt D F p.g.b ≫ _ = _))
    (congrArg (fun q => q.left) (lift_fst _ _ : DegPre.zF D F ≫ _ = _)) _ _
    (c := r p.y α * r p.y (w • p.y)) ?_ (fun y J hJ => ?_) (h α)
  · show r (α + p.y) (w • (α + p.y)) = _
    rw [hr.1.refine_add hw, hr.1.symm α p.y]
    ac_rfl
  · refine (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) (val_scale (r p.y α) (p.g.s α) _ hJ)
      (val_scale (r p.y (w • p.y)) v _ hJ)).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_mul hJ _ _ _).symm)))
    rw [map_mul, _root_.mul_mul_mul_comm]

include hw ht hq hr

theorem QkRel.weilQkIs_of {p q : QkPt D F k} {p' q' : QkPt (withPsi D ψ hψ) F k} (hp : QkRel r p p') (hq' : QkRel r q q')
    {ζ : F} (h : WeilQkIs (withPsi D ψ hψ) F k p' q' ζ) : WeilQkIs D F k p q ζ := by
  obtain rfl := (qkRel_qkScale hw ht hq hr p).unique hp
  obtain rfl := (qkRel_qkScale hw ht hq hr q).unique hq'
  intro v v' hv hv' s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄ α j
  have e := h _ _ (scaleGen_isGen _ _ hv) (scaleGen_isGen _ _ hv') _ _ _ _ _ (phiRel_famScale hw ht hq hr q v' h₁)
    (phiRel_famScale hw ht hq hr p v h₂) (phiRel_famScale hw ht hq hr p v h₃) (phiRel_famScale hw ht hq hr q v' h₄) α j
  exact (Units.mul_right_inj _).1 (e.trans (mul_left_comm _ _ _))

theorem QkRel.weilQkIs_iff {p q : QkPt D F k} {p' q' : QkPt (withPsi D ψ hψ) F k} (hp : QkRel r p p')
    (hq' : QkRel r q q') (ζ : F) : WeilQkIs (withPsi D ψ hψ) F k p' q' ζ ↔ WeilQkIs D F k p q ζ :=
  ⟨hp.weilQkIs_of hw ht hq hr hq',
    QkRel.weilQkIs_of (D := withPsi D ψ hψ) hw ht.inv hq.symm hr.inv hp.symm hq'.symm⟩

end GlobalTheory.TauTwist
