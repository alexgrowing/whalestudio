import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CommGroupCommonFactorQuotientCancel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MumfordTowerRepWtUnique
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MumfordTowerRepWtMulAdd
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasWtGenPullIff

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.WeightPoint

theorem w_of_isCPPullback {S S' : Scheme.{0}} {B' : Over S'} {B : Over S} [GrpObj B'] [IsCommMonObj B'] [GrpObj B]
    [IsCommMonObj B] {M' : CP B'} {M : CP B} {f : S' ⟶ S} {β : B'.left ⟶ B.left} (h : IsCPPullback M' M f β) :
    β ≫ B.hom = B'.hom ≫ f := by
  obtain ⟨h, -⟩ := h
  exact h.1.w

section Tower
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {P : CP G} {X : Type} [AddCommGroup X]
  {T : TowerR I P X} (a : T.Alg)

omit [IsDomain R] [IsLocalRing R] [IsCommMonObj G] in

theorem isGrpPullback_thickMap (e : ℕ) :
    IsGrpPullback (thickObj R I e G) (thickObj R I (e + 1) G) (thickTrans R I e) (thickMap R I e G) :=
  (isGrpPullback_pullback G (thick R I (e + 1))).cancel ((isGrpPullback_pullback G (thick R I e)).congr
    (thickTrans_comp R I e).symm ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).symm)
    (pullback.lift_snd _ _ _)

omit [IsDomain R] in

theorem exists_section [IsAdicComplete I R] {B : Over (Spec (CommRingCat.of R))}
    (x : ∀ e : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ B.left) (hx : ∀ e, x e ≫ B.hom = thick R I e)
    (hc : ∀ e, thickTrans R I e ≫ x (e + 1) = x e) : ∃ c : 𝟙_ _ ⟶ B, ∀ e, thick R I e ≫ c.left = x e := by
  obtain ⟨c, ⟨h₁, h₂⟩, -⟩ := existsUnique_over_of_isAdicFamily (I := I) (f := x) (𝟙 _) B.hom hc
    fun e => (hx e).trans (Category.comp_id _).symm
  exact ⟨Over.homMk c h₁, h₂⟩

theorem isGrpPullback_level (e : ℕ) : IsGrpPullback (T.l e).Q.B a.B (thick R I e) (a.b e) := by
  obtain ⟨h, -⟩ := a.b_pb e
  exact h

theorem exists_rep_level (hP : PicardZeroDegenerationCondition) [IsNoetherianRing R] (hI : I ≠ ⊤) (hK : KTriv a.B a.M.L.L) (χ : X) (e : ℕ) :
    ∃ x, x ≫ a.B.hom = thick R I e ∧ Rep (T.l e).Q a.M.L.L (a.b e) x χ :=
  have := isLocalRing_quotient_pow hI e
  exists_rep hP a.M a.ample hK (T.l e).Q (isGrpPullback_level a e) χ

theorem rep_level_pull {χ : X} {e : ℕ} {x} (h : Rep (T.l (e + 1)).Q a.M.L.L (a.b (e + 1)) x χ) :
    Rep (T.l e).Q a.M.L.L (a.b e) (thickTrans R I e ≫ x) χ :=
  Rep.pull (Q := (T.l (e + 1)).Q) (Q' := (T.l e).Q) (isGrpPullback_thickMap e) (T.tor e)
    (w_of_isCPPullback (T.β_pb e)) (T.β_q e) (a.b_β e) h

theorem exists_repWt (hP : PicardZeroDegenerationCondition) [IsNoetherianRing R] [IsAdicComplete I R] (hK : KTriv a.B a.M.L.L) (χ : X) :
    ∃ c : 𝟙_ _ ⟶ a.B, ∀ e, a.RepWt c χ e := by
  choose x hx hr using exists_rep_level a hP (ne_top_of_isHausdorff I) hK χ
  obtain ⟨c, hc⟩ := exists_section x hx fun e => Rep.unique a.M.L.isLB hK (isGrpPullback_level a e).1
    (by rw [Category.assoc, hx, thickTrans_comp]) (hx e) (rep_level_pull a (hr (e + 1))) (hr e)
  refine ⟨c, fun e => Rep.section (isGrpPullback_level a e).1.w c ?_⟩
  rw [hc]
  exact hr e

theorem repWt_unique [IsHausdorff I R] (hK : KTriv a.B a.M.L.L) {χ : X} {c c' : 𝟙_ _ ⟶ a.B}
    (hc : ∀ e, a.RepWt c χ e) (hc' : ∀ e, a.RepWt c' χ e) : c = c' := by
  refine Over.OverMorphism.ext (GlobalTheory.hom_ext_of_isHausdorff I fun e => ?_)
  obtain ⟨pb, -⟩ := a.b_pb e
  have k := section_eq_of_isWt a.M.L.isLB hK c c' (T.l e).Q pb.1 χ (hc e) (hc' e)
  rw [Over.comp_left, Over.comp_left, Rosenlicht.toUnit_left] at k
  exact k

theorem repWt_add {χ χ' : X} {c c' : 𝟙_ _ ⟶ a.B} {e : ℕ} (h : a.RepWt c χ e) (h' : a.RepWt c' χ' e) :
    a.RepWt (c * c') (χ + χ') e := by
  refine exists_genWt_add (fun Z x g => ?_) a.M.L.isLB (GlobalTheory.Square.triv_inv (triv_square_sections a.M.c c c'))
    (fun U _ f => ?_) h h'
  · rw [← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, TQ.mul_comp_q]
  · simp only [Fin.prod_univ_two, Fin.prod_univ_four, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow]
    module

end Tower

theorem exists_weightPoints : Laws → Laws2 → Ega → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G) (X : Type) [AddCommGroup X] (T : TowerR I P X) (a : T.Alg), KTriv a.B a.M.L.L → ∃ c : X → (𝟙_ _ ⟶ a.B), (∀ χ χ', c (χ + χ') = c χ * c χ') ∧ ∀ χ e, a.RepWt (c χ) χ e := by
  intro _ _ hE R _ _ _ I hR G _ _ P X _ T a hK
  have := hR.1.1
  have := hR.1.2.2.2
  choose c hc using exists_repWt a hE.2.2.2 hK
  exact ⟨c, fun χ χ' => repWt_unique a hK (hc _) fun e => repWt_add a (hc χ e) (hc χ' e), hc⟩

end GlobalTheory.WeightPoint
end
