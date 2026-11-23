import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RatTors
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescOfPoints
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

noncomputable section

namespace GlobalTheory.LevelField

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ArcDataDescent

theorem qkExt_trans {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F₀ F₁ F₂ : Type} [Field F₀] [Field F₁]
    [Field F₂] [Algebra (FractionRing R) F₀] [Algebra (FractionRing R) F₁] [Algebra (FractionRing R) F₂]
    {f : F₀ →+* F₁} {g : F₁ →+* F₂} {k : ℕ} {p₀ : QkPt D F₀ k} {p₁ : QkPt D F₁ k} {p₂ : QkPt D F₂ k}
    (h : QkExt f p₀ p₁) (h' : QkExt g p₁ p₂) : QkExt (g.comp f) p₀ p₂ := by
  refine ⟨h'.1.trans h.1, ?_, fun χ => corr_of_val D.P.isLB fun (y : Sp F₂) J hJ => ?_⟩
  · exact h'.2.1.trans ((congrArg (spMap g ≫ ·) h.2.1).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ p₀.g.b.left) (spMap_comp f g).symm)))
  · refine (val_corr hJ (h'.2.2 χ) _).trans ((val_pull hJ _ _ _).trans ((val_corr hJ (h.2.2 χ) _).trans
      ((val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))))
    exact congrArg (fun q => val (p₀.g.s χ) q y J) ((Category.assoc _ _ _).trans
      (congrArg (𝟙 (Sp F₂) ≫ ·) (spMap_comp f g).symm))

theorem val_eq_of_genRel {F : Type} [Field F] {B B₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀} (hM₀ : M₀.IsLB)
    {φ : B ⟶ B₀} {w : LB.Iso M (M₀.pull φ)} {K : Type} [Fintype K] {pt pt' : K → (Sp F ⟶ B)} {pt₀ : K → (Sp F ⟶ B₀)}
    {ε : K → ℤ} {t : LB.Gen (LB.LinComb M pt ε)} {t' : LB.Gen (LB.LinComb M pt' ε)}
    {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)} {x : F} (hp : pt = pt') (h : GenRel w t t₀ x) (h' : GenRel w t' t₀ x)
    (z : Sp F) {J} (hJ : Good M z J) : val t (𝟙 _) z J = val t' (𝟙 _) z J := by
  subst hp
  choose J₀ hJ₀ using fun χ : Sp F ⟶ B₀ => exists_chart hM₀ (χ z)
  have e := ((genRel_iff w t t₀ x z).1 h).2 (fun k => J (pt k)) (fun k => J₀ (pt k ≫ φ))
    (fun k => hJ₀ (pt k ≫ φ)) (fun k => hJ (pt k))
  have e' := ((genRel_iff w t' t₀ x z).1 h').2 (fun k => J (pt k)) (fun k => J₀ (pt k ≫ φ))
    (fun k => hJ₀ (pt k ≫ φ)) (fun k => hJ (pt k))
  rw [val_of t _ z J (fun k => J (pt k)) (fun k => by rw [Category.id_comp]),
    val_of t' _ z J (fun k => J (pt k)) (fun k => by rw [Category.id_comp])]
  exact mul_left_cancel (Units.ext (e.trans e'.symm))

variable {R O' : Type} [CommRing R] [IsDomain R] [CommRing O'] [IsDomain O'] {D : DegPre R} {D₀ : DegPre O'}
  {ψ : D.P.A.left ⟶ D₀.P.A.left} {w : LB.Iso D.P.L (D₀.P.L.pull ψ)} {k : ℕ}

theorem genRel_ext {F F' : Type} [Field F] [Field F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F']
    [Algebra (FractionRing O') F] [Algebra (FractionRing O') F'] {σ : F →+* F'}
    (hσ : σ.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')
    (hσ₀ : σ.comp (algebraMap (FractionRing O') F) = algebraMap (FractionRing O') F')
    {q : QkPt D F k} {q' : QkPt D F' k} {q₀ : QkPt D₀ F k} {q₀' : QkPt D₀ F' k} (h : QkExt σ q q')
    (h₀ : QkExt σ q₀ q₀') {χ : D.X} {χ₀ : D₀.X} {x : F} (H : GenRel w (q.g.s χ) (q₀.g.s χ₀) x) :
    GenRel w (q'.g.s χ) (q₀'.g.s χ₀) (σ x) :=
  (genRel_congr D.P.isLB D₀.P.isLB w (gtφ_ext hσ h χ) (gtφ_ext hσ₀ h₀ χ₀) (q'.g.isGen _)
    (pullGen_isGen _ _ _ _ (q.g.isGen _) _) (q₀'.g.isGen _) (pullGen_isGen _ _ _ _ (q₀.g.isGen _) _)
    (fun _ _ hJ => val_corr hJ (h.2.2 χ) _) (fun _ _ hJ => val_corr hJ (h₀.2.2 χ₀) _) _).2
    ((genRel_pull_iff σ w _ _ x).2 H)

theorem eq_of_genRel {F : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F] {f : O' →+* R}
    (gp : IsGrpPullback D.P.A D₀.P.A (spMap f) ψ) (e : D₀.X ≃+ D.X) {q q' : QkPt D F k} {q₀ : QkPt D₀ F k}
    {x : D₀.X → F} (hy : q.y = q'.y) (H : ∀ χ, GenRel w (q.g.s (e χ)) (q₀.g.s χ) (x χ))
    (H' : ∀ χ, GenRel w (q'.g.s (e χ)) (q₀.g.s χ) (x χ)) : q = q' := by
  have hb : q.g.b = q'.g.b :=
    Over.OverMorphism.ext (gp.1.hom_ext (((H 0).1 2).trans ((H' 0).1 2).symm) (by rw [Over.w, Over.w]))
  refine TorusExt.qk_ext hy (TorusExt.gt_ext hb fun χ => corr_of_val D.P.isLB fun y J hJ => ?_)
  obtain ⟨χ, rfl⟩ := e.surjective χ
  exact val_eq_of_genRel D₀.P.isLB (by rw [hb]) (H χ) (H' χ) y hJ

theorem toA_of_toA : GlobalTheory.UT.LL → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R O' : Type) [CommRing R] [IsDomain R] [CharZero R] [CommRing O'] [IsDomain O'] (I : Ideal R), AdmBase R I → ∀ (t : SAB H (Sp R)) (P : PELUnif I t) (D₀ : DegPre O'), D₀.TauBimult → ∀ (f : O' →+* R) (ψ : P.D.toPre.P.A.left ⟶ D₀.P.A.left) (w : LB.Iso P.D.toPre.P.L (D₀.P.L.pull ψ)) (e : D₀.X ≃+ P.D.toPre.X), IsGrpPullback P.D.toPre.P.A D₀.P.A (spMap f) ψ → w.IsGen → ∀ k : ℕ, 1 ≤ k → ∀ (p₀ : QkPt D₀ (FractionRing O') k) (s : D₀.X → FractionRing R) (x₀ : Sp (FractionRing R) ⟶ P.A.A.left) (C : Type) [Field C] [IsAlgClosed C] [Algebra (FractionRing R) C] [Algebra (FractionRing O') C], Along f C → ∀ (q₀ : QkPt D₀ C k) (q : QkPt P.D.toPre C k) (x : TFK (R := R) C ⟶ P.A.A), QkExt (algebraMap _ C) p₀ q₀ → q.y = e q₀.y → (∀ χ, GenRel w (q.g.s (e χ)) (q₀.g.s χ) (algebraMap _ C (s χ))) → x.left = jFK (R := R) C ≫ x₀ → P.ToA C k q x → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F], Along f F → ∀ (q₀' : QkPt D₀ F k) (q' : QkPt P.D.toPre F k) (x' : TFK (R := R) F ⟶ P.A.A), QkExt (algebraMap _ F) p₀ q₀' → q'.y = e q₀'.y → (∀ χ, GenRel w (q'.g.s (e χ)) (q₀'.g.s χ) (algebraMap _ F (s χ))) → x'.left = jFK (R := R) F ≫ x₀ → P.ToA F k q' x' := by
  intro hL E _ _ _ H R O' _ _ _ _ _ I _ t P D₀ hB f ψ w e gp _ k hk p₀ s x₀ C _ _ _ _ hC q₀ q x h₀ hy hg hx hA
    F _ _ _ _ hF q₀' q' x' h₀' hy' hg' hx'
  obtain ⟨F', _, _, σ, τ, hστ⟩ := exists_common_field (algebraMap (FractionRing R) C) (algebraMap (FractionRing R) F)
  letI : Algebra (FractionRing R) F' := (σ.comp (algebraMap _ C)).toAlgebra
  letI : Algebra (FractionRing O') F' := (σ.comp (algebraMap _ C)).toAlgebra
  have hσ : σ.comp (algebraMap (FractionRing R) C) = algebraMap (FractionRing R) F' := rfl
  have hσ₀ : σ.comp (algebraMap (FractionRing O') C) = algebraMap (FractionRing O') F' := rfl
  have hτ : τ.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' := hστ.symm
  have hτ₀ : τ.comp (algebraMap (FractionRing O') F) = algebraMap (FractionRing O') F' :=
    IsLocalization.ringHom_ext (nonZeroDivisors O') (RingHom.ext fun a =>
      (congrArg τ (hF a).symm).trans ((RingHom.congr_fun hστ _).symm.trans (congrArg σ (hC a))))
  obtain ⟨r, hr, -⟩ := TorusExt.existsUnique_qkExt P.D.tau_bimult σ hσ q
  obtain ⟨r', hr', -⟩ := TorusExt.existsUnique_qkExt P.D.tau_bimult τ hτ q'
  obtain ⟨r₀, hr₀, -⟩ := TorusExt.existsUnique_qkExt hB σ hσ₀ q₀
  obtain ⟨r₀', hr₀', -⟩ := TorusExt.existsUnique_qkExt hB τ hτ₀ q₀'
  have a := qkExt_trans h₀ hr₀
  have a' := qkExt_trans h₀' hr₀'
  rw [hσ₀] at a
  rw [hτ₀] at a'
  obtain rfl : r₀ = r₀' :=
    (TorusExt.existsUnique_qkExt hB (algebraMap (FractionRing O') F') (RingHom.ext fun _ => rfl) p₀).unique a a'
  obtain rfl : r = r' := eq_of_genRel gp e (q₀ := r₀) (x := fun χ => algebraMap (FractionRing R) F' (s χ))
    (by rw [hr.1, hr'.1, hy, hy', h₀.1, h₀'.1]) (fun χ => genRel_ext hσ hσ₀ hr hr₀ (hg χ))
    (fun χ => by
      have b := genRel_ext hτ hτ₀ hr' hr₀' (hg' χ)
      rwa [show τ (algebraMap (FractionRing R) F (s χ)) = algebraMap (FractionRing R) F' (s χ) from
        RingHom.congr_fun hτ _] at b)
  letI : Algebra C F' := σ.toAlgebra
  letI : Algebra F F' := τ.toAlgebra
  haveI : IsScalarTower (FractionRing R) C F' := IsScalarTower.of_algebraMap_eq' hσ.symm
  haveI : IsScalarTower (FractionRing R) F F' := IsScalarTower.of_algebraMap_eq' hτ.symm
  have hj : spMap σ ≫ jFK (R := R) C = jFK (R := R) F' := (spMap_comp _ _).symm.trans (congrArg spMap hσ)
  have hj' : spMap τ ≫ jFK (R := R) F = jFK (R := R) F' := (spMap_comp _ _).symm.trans (congrArg spMap hτ)
  have ex : TorsionExt.fieldMap (R := R) C F' ≫ x = TorsionExt.fieldMap (R := R) F F' ≫ x' := by
    refine Over.OverMorphism.ext ?_
    show spMap σ ≫ x.left = spMap τ ≫ x'.left
    rw [hx, hx', ← Category.assoc, ← Category.assoc, hj, hj']
  refine (TorsionExt.qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow P.U hk hr' x').2 ?_
  rw [← ex]
  exact (TorsionExt.qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow P.U hk hr x).1 hA

end GlobalTheory.LevelField
end
