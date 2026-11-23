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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueTorusExtensionPointOfGroupPointStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtCoordAdditive
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionQk

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T : Over (Spec (CommRingCat.of R))}
  {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem val_cubAtT {T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T) {y : T'.left} {J} (hJ : Good D.P.L y J)
    (χ : D.X) (x w : T ⟶ D.P.A) :
    val (DegPre.cubAtT D T (DegPre.cT D T χ) x w) ρ.left y J = th D y J (cP D _ χ) (ρ ≫ x) (ρ ≫ w) := by
  have := val_cub D.cub ρ hJ (cP D T χ) x w
  rwa [comp_cP] at this

theorem exists_pull (ρ : TF (R := R) F ⟶ T) (g : GtPt D T) :
    ∃ g' : GtPtF D F, g'.b = ρ ≫ g.b ∧
      ∀ χ y J, Good D.P.L y J → val (g'.s χ) (𝟙 _) y J = val (g.s χ) ρ.left y J := by
  have vp : ∀ χ y J, Good D.P.L y J →
      val (LB.pullGen D.P.L _ _ (g.s χ) ρ.left) (𝟙 _) y J = val (g.s χ) ρ.left y J := fun χ y J hJ => by
    rw [val_pull hJ, Category.id_comp]
  obtain ⟨g', hb, hv⟩ := exists_gt (D := D) (F := F) (ρ ≫ g.b) (fun χ => LB.pullGen D.P.L _ _ (g.s χ) ρ.left)
    (fun χ => pullGen_isGen _ _ _ _ (g.isGen χ) _) (fun χ U _ h => by
      refine Finset.prod_congr rfl fun i _ => congrArg (fun q => h q ^ DegPre.gtε i) ?_
      fin_cases i
      · exact congrArg (fun q : TF (R := R) F ⟶ D.P.A => q.left)
          ((MonObj.comp_mul ρ (cP D T χ) g.b).trans (congrArg (· * (ρ ≫ g.b)) (comp_cP D ρ χ)))
      · exact congrArg (fun q : TF (R := R) F ⟶ D.P.A => q.left) (comp_cP D ρ χ)
      · rfl
      · exact congrArg (fun q : TF (R := R) F ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) ρ))
    (fun y J hJ => (vp 0 y J hJ).trans ((val_corr hJ g.s_zero _).trans (val_one _)))
    (fun χ χ' y J hJ => by
      rw [vp _ y J hJ, vp _ y J hJ, vp _ y J hJ]
      have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (g.mult χ χ') ρ.left).trans (val_mul hJ _ _ _))
      refine Eq.trans (congrArg₂ (· * ·) rfl ?_) e
      refine Eq.trans ?_ (val_cubAtT ρ hJ χ (cP D T χ') g.b).symm
      rw [comp_cP])
  exact ⟨g', hb, fun χ y J hJ => (hv χ y J hJ).trans (vp χ y J hJ)⟩

theorem isIota_zero (hB : D.TauBimult) {h : GtPtF D F} (hh : h.IsZero) : GtPtF.IsIota 0 h := by
  obtain ⟨hb, hv⟩ := (isZero_iff h).1 hh
  refine (isIota_iff 0 h).2 ⟨hb.trans (cPoint_zero _).symm, fun χ y J hJ => ?_⟩
  have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
  have t := tau_mul (𝟙 (TF (R := R) F)) hJ hB 0 0 χ
  rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t
  exact (hv χ y J hJ).trans (mul_eq_left.1 t.symm).symm

theorem exists_qk (hB : D.TauBimult) (ρ : TF (R := R) F ⟶ T) (k : ℕ) (g : GtPt D T) (gs : ℕ → GtPt D T)
    (h₀ : (gs 0).IsZero) (hs : ∀ i, GtPt.IsAdd (gs i) g (gs (i + 1))) (hk : (gs k).IsZero) :
    ∃ p : QkPt D F k, p.y = 0 ∧ GtPt.IsPullF F ρ.left g p.g := by
  choose pl hb hv using fun g : GtPt D T => exists_pull ρ g
  have zero : ∀ g : GtPt D T, g.IsZero → (pl g).IsZero := fun g hg =>
    (isZero_iff _).2 ⟨by rw [hb, hg.1]; exact MonObj.comp_one (M := D.P.A) ρ, fun χ y J hJ =>
      (hv g χ y J hJ).trans ((val_corr hJ (hg.2 χ) _).trans (val_one _))⟩
  have add : ∀ g g' g'' : GtPt D T, g.IsAdd g' g'' → (pl g).IsAdd (pl g') (pl g'') := fun g g' g'' h =>
    (isAdd_iff _ _ _).2 ⟨by rw [hb, hb, hb, h.1]; exact MonObj.comp_mul ρ g.b g'.b, fun χ y J hJ => by
      rw [hv _ _ y J hJ, hv _ _ y J hJ, hv _ _ y J hJ, hb, hb]
      have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (h.2 χ) ρ.left).trans (val_mul hJ _ _ _))
      exact Eq.trans (congrArg₂ (· * ·) rfl (val_cubAtT ρ hJ χ g.b g'.b).symm) e⟩
  refine ⟨⟨0, pl g, pl (gs k), ⟨fun i => pl (gs i), zero _ h₀, fun i => add _ _ _ (hs i), rfl⟩,
    isIota_zero hB (zero _ hk)⟩, rfl, congrArg (fun q : TF (R := R) F ⟶ D.P.A => q.left) (hb g),
    fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  refine (hv g χ y J hJ).trans ?_
  rw [val_pull hJ, Category.id_comp]

theorem base_pow (g : GtPt D T) (gs : ℕ → GtPt D T)
    (h₀ : (gs 0).IsZero) (hs : ∀ i, GtPt.IsAdd (gs i) g (gs (i + 1))) (i : ℕ) : (gs i).b = g.b ^ i := by
  induction i with
  | zero => rw [pow_zero]; exact h₀.1
  | succ i ih => rw [pow_succ, ← ih]; exact (hs i).1

theorem torsionPoint_qk : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ) (x : (𝟙_ (Over (Spec (CommRingCat.of R)))) ⟶ G) (gp : GtPt D.toPre (𝟙_ (Over (Spec (CommRingCat.of R))))), x ^ k = 1 → (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ x ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R I e))).left)) → gp.b ^ k = 1 ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], ∃ p : QkPt D.toPre F k, p.y = 0 ∧ GtPt.IsPullF F (toUnit (TF (R := R) F)).left gp p.g := by
  intro hG R _ _ _ I hI hne D A G _ _ U k x gp hx hm
  obtain ⟨hadd, hzero⟩ := GlobalTheory.gtCoord_additive hG R I hI hne D A G U
  choose gs hgs using fun i : ℕ => (GlobalTheory.T.existsUnique_torusExtensionPoint_of_groupPoint R I hI hne D A G U (x ^ i)).exists
  have h₀ : (gs 0).IsZero := hzero _ (by simpa only [pow_zero] using hgs 0)
  have hk : (gs k).IsZero := hzero _ (by simpa only [hx] using hgs k)
  have hs : ∀ i, GtPt.IsAdd (gs i) gp (gs (i + 1)) := fun i =>
    hadd (x ^ i) x _ _ _ (hgs i) hm (by simpa only [pow_succ] using hgs (i + 1))
  exact ⟨(base_pow gp gs h₀ hs k).symm.trans hk.1,
    fun F _ _ => exists_qk D.tau_bimult (toUnit _) k gp gs h₀ hs hk⟩

end GlobalTheory.TorsionQk
