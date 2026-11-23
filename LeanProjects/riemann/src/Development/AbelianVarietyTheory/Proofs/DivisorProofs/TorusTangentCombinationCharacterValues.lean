import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationPointsAddPullTangent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorLiftsToDegenerationPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationTangentPointUniqueLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentRelationAdditiveScaling
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsPointOfIffThick
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TorusVals

variable {R : Type} [CommRing R]

theorem dual_mul (a b : R) : ((1 : DualNumber R) + TrivSqZeroExt.inr a) * (1 + TrivSqZeroExt.inr b) = 1 + TrivSqZeroExt.inr (a + b) := by
  ext <;> simp [add_comm]

theorem epsScaleR_one_add (c a : R) : epsScaleR c (1 + TrivSqZeroExt.inr a) = 1 + TrivSqZeroExt.inr (c * a) := by
  ext <;> simp [epsScaleR, mul_comm]

section Gs

variable {Z : Scheme.{0}} (q : Z ⟶ (epsR R).left) (z : Z)

theorem gs_one_add_zero : gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr 0)) = 1 := by
  rw [gs_eq q z ⊤ trivial, TrivSqZeroExt.inr_zero, add_zero, map_one, map_one, map_one]

theorem gs_dual_mul (a b : R) :
    gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr a)) *
      gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr b)) =
    gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (a + b))) := by
  rw [← gs_mul q z ⊤ trivial, ← map_mul, dual_mul]

theorem gs_scale (c a : R) :
    gs (q ≫ (epsScale R c).left) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr a)) =
    gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (c * a))) := by
  rw [← gs_pull q (epsScale R c).left z ⊤ trivial, ← epsScaleR_one_add]
  have e := congrArg (fun f => f.hom (1 + TrivSqZeroExt.inr a : DualNumber R))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (epsScaleR c)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  rw [e]
  rfl

end Gs

variable [IsDomain R] {D : DegPre R} {H : Over (Sp R)} [GrpObj H] [IsCommMonObj H] {Φ : ∀ T, (T ⟶ H) ≃ GtPt D T}

def HasVals (Φ : ∀ T, (T ⟶ H) ≃ GtPt D T) (y : epsR R ⟶ H) (a : D.X → R) : Prop :=
  (Φ _ y).b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z)
    (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
    (val ((Φ _ y).s χ) q z J).val = gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (a χ)))

theorem hasVals_one (hΦ : TorusModel.Represents Φ) : HasVals Φ 1 (fun _ => 0) := by
  have hz : (Φ (epsR R) 1).IsZero := GtVec.isZero_of_isAdd (by simpa using hΦ.2 (epsR R) 1 1)
  refine ⟨hz.1, fun χ Z q z J hJ => ?_⟩
  rw [val_corr hJ (hz.2 χ) q, val_one, gs_one_add_zero]
  rfl

theorem hasVals_scale (hΦ : TorusModel.Represents Φ) {y : epsR R ⟶ H} {a : D.X → R} (h : HasVals Φ y a) (c : R) :
    HasVals Φ (epsScale R c ≫ y) (fun χ => c * a χ) := by
  have hp := hΦ.1 (epsR R) (epsR R) (epsScale R c) y
  refine ⟨?_, fun χ Z q z J hJ => ?_⟩
  · rw [((TorusModel.isPull_iff _ _ _).1 hp).1, h.1]
    simp only [DegPre.zeroT, ← Category.assoc]
    congr 1
    exact toUnit_unique _ _
  · rw [val_corr hJ (hp.2 χ) q, val_pull hJ, h.2 χ Z _ z J hJ, gs_scale]

theorem hasVals_mul (hΦ : TorusModel.Represents Φ) {y y' : epsR R ⟶ H} {a a' : D.X → R} (h : HasVals Φ y a)
    (h' : HasVals Φ y' a') : HasVals Φ (y * y') (fun χ => a χ + a' χ) := by
  have hs := hΦ.2 (epsR R) y y'
  refine ⟨?_, fun χ Z q z J hJ => ?_⟩
  · rw [((TorusModel.isAdd_iff _ _ _).1 hs).1, h.1, h'.1]
    exact _root_.mul_one _
  · have e := (val_mul hJ _ _ q).symm.trans ((val_corr hJ (hs.2 χ) q).trans (val_mul hJ _ _ q))
    let T' : Over (Sp R) := Over.mk (q ≫ (epsR R).hom)
    let ρ : T' ⟶ epsR R := Over.homMk q rfl
    have hc : val (DegPre.cubAtT D (epsR R) (DegPre.cT D (epsR R) χ) (Φ _ y).b (Φ _ y').b) q z J = 1 := by
      have := val_cub D.cub ρ hJ (DegPre.cT D (epsR R) χ) (Φ _ y).b (Φ _ y').b
      refine this.trans ?_
      rw [h'.1]
      have e1 : ρ ≫ DegPre.zeroT D (epsR R) = (1 : T' ⟶ D.P.A) := by
        simp only [DegPre.zeroT, ← Category.assoc]
        rw [Hom.one_def]
        congr 1
      rw [e1]
      exact (isCub_cubV D.cub hJ).face₃ _ _
    rw [hc, _root_.mul_one] at e
    rw [e, Units.val_mul, h.2 χ Z q z J hJ, h'.2 χ Z q z J hJ, gs_dual_mul]

end GlobalTheory.MBLow.TorusVals

namespace GlobalTheory.MBLow.TorusVals

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {H : Over (Sp R)} [GrpObj H] [IsCommMonObj H]
  {Φ : ∀ T, (T ⟶ H) ≃ GtPt D T}

theorem hasVals_tanComb (hΦ : TorusModel.Represents Φ) : ∀ (r : ℕ) (a : Fin r → D.X → R) (x : Fin r → (epsR R ⟶ H)),
    (∀ l, HasVals Φ (x l) (a l)) → ∀ d : Fin r → R, HasVals Φ (tanComb d x) (fun χ => ∑ l, d l * a l χ)
  | 0, a, x, _, d => by
    have e : tanComb d x = 1 := by simp [tanComb]
    have ef : (fun χ => ∑ l : Fin 0, d l * a l χ) = fun _ => 0 := funext fun _ => by simp
    rw [e, ef]
    exact hasVals_one hΦ
  | r + 1, a, x, hx, d => by
    have e : tanComb d x = (epsScale R (d 0) ≫ x 0) * tanComb (fun i => d i.succ) (fun i => x i.succ) := by
      simp only [tanComb, List.ofFn_succ, List.prod_cons]
    have key := hasVals_mul hΦ (hasVals_scale hΦ (hx 0) (d 0))
      (hasVals_tanComb hΦ r (fun i => a i.succ) (fun i => x i.succ) (fun l => hx l.succ) (fun i => d i.succ))
    have ef : (fun χ => ∑ l, d l * a l χ) = fun χ => d 0 * a 0 χ + ∑ l : Fin r, d l.succ * a l.succ χ :=
      funext fun χ => Fin.sum_univ_succ _
    rw [e, ef]
    exact key

theorem tanComb_vals : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (H : Over (Sp R)) [GrpObj H] [IsCommMonObj H] (Φ : ∀ T, (T ⟶ H) ≃ GtPt D T), GlobalTheory.TorusModel.Represents Φ → ∀ (r : ℕ) (a : Fin r → D.X → R) (x : Fin r → (epsR R ⟶ H)), (∀ l, (Φ _ (x l)).b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val ((Φ _ (x l)).s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (a l χ)))) → ∀ d : Fin r → R, (Φ _ (tanComb d x)).b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val ((Φ _ (tanComb d x)).s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (∑ l, d l * a l χ))) :=
  fun _ _ _ _ _ _ _ _ hΦ r a x hx d => hasVals_tanComb hΦ r a x hx d

end GlobalTheory.MBLow.TorusVals

end
