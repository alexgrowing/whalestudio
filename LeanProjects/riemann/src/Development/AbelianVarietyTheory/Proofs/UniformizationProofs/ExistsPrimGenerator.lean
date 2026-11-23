import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT.PrimGen

open GlobalTheory.FieldBaseChange

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]
  {F : Type} [Field F] [Algebra (FractionRing V) F]

theorem exists_lower (v : AddValuation F (WithTop ℚ)) {n : ℕ} (c : Fin n → F) :
    ∃ r : ℚ, ∀ i, (r : WithTop ℚ) ≤ v (c i) := by
  obtain ⟨m, hm⟩ := (Set.finite_range fun i => (v (c i)).untopD 0).bddBelow
  refine ⟨m, fun i => ?_⟩
  have h := hm ⟨i, rfl⟩
  cases e : v (c i) with
  | top => exact le_top
  | coe y =>
    simp only [e, WithTop.untopD_coe] at h
    exact WithTop.coe_le_coe.2 h

theorem exists_vge (U : UnifPre (maximalIdeal V) D A G) (v : AddValuation F (WithTop ℚ)) {k : ℕ}
    {σ : U.SecGF F k} {s : Fam D.toPre F k} (h : U.ExpandsG F k σ s) (α : D.toPre.X) :
    ∃ r : ℚ, VGe D F v k α (s.s α) r := by
  obtain ⟨n, c, x, -, -, hs⟩ := (expandsG_iff U F k σ s).1 h
  obtain ⟨r, hr⟩ := exists_lower v c
  refine ⟨r, n, c, fun i => (x i).2 α,
    fun i => termPull D.toPre (FractionRing V) F k α (genericTerm D k α ((x i).2 α)), fun i => ?_, hr, fun j => ?_⟩
  · exact SectionScalarValuation.secScal_of_sval D.toPre.P.isLB fun y J hJ =>
      ((sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
        (congrArg (fun q => sval ((x i).2 α) q y J) ((Category.assoc _ _ _).trans (congrArg (𝟙 _ ≫ ·)
          (congrArg (fun q => q.left) (famMap_snd D.toPre (FractionRing V) F))))))).symm
  · exact (congrArg (chartLin (famBase D.toPre F) _ j) (hs α)).trans (map_sum (chartLin (famBase D.toPre F) _ j) _ _)

theorem exists_prim_span (hU : UUStatement) {ϖ : V} (hϖ : Irreducible ϖ) {Q : D.toPre.X → ℤ}
    (hQ : QForm.IsQ D.toPre ϖ Q) [IsAlgClosed F] {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v) :
    ∃ ϑ : Fam D.toPre F 1, Prim D Q v ϑ ∧
      ∀ s : Fam D.toPre F 1, (∃ r : ℚ, VGe D F v 1 0 (s.s 0) r) → ∃ c : F, s = c • ϑ := by
  classical
  obtain ⟨b, hli, hb, hsp⟩ := hU V ϖ hϖ D Q hQ F v hv (Or.inl inferInstance) 1 le_rfl
  have : Subsingleton (Fin (1 ^ (D.toPre.rank + D.toPre.P.g))) := by rw [one_pow]; infer_instance
  let i₀ : Fin (1 ^ (D.toPre.rank + D.toPre.P.g)) := ⟨0, by rw [one_pow]; exact one_pos⟩
  have hsp' : ∀ s, NuGe D Q F v 1 s 0 → ∃ c : F, (0 : WithTop ℚ) ≤ v c ∧ s = c • b i₀ := fun s hs => by
    obtain ⟨c, hc, e⟩ := (hsp s).1 hs
    exact ⟨c i₀, hc i₀, e.trans (Fintype.sum_subsingleton _ i₀)⟩
  refine ⟨b i₀, ⟨hb i₀, fun r hr h => ?_⟩, ?_⟩
  · obtain ⟨ζ, s', hζ, hs', e⟩ := (n1c V ϖ hϖ D Q hQ F v hv 1 le_rfl (b i₀) (hb i₀)).1 ⟨r, hr, h⟩
    obtain ⟨c, hc, rfl⟩ := hsp' s' hs'
    rw [isSmul_iff, smul_smul] at e
    have e1 : ζ * c = 1 := smul_left_injective F (hli.ne_zero i₀) (e.symm.trans (one_smul F _).symm)
    have h0 : (0 : WithTop ℚ) < v (ζ * c) := by
      rw [AddValuation.map_mul]
      exact lt_add_of_lt_of_nonneg hζ hc
    rw [e1, AddValuation.map_one] at h0
    exact lt_irrefl _ h0
  · rintro s ⟨r, hr⟩
    have h1 : NuGe D Q F v 1 s (-(|r| + 1)) := by
      rw [n1a V ϖ hϖ D Q hQ F v hv 1 le_rfl {0} (fun χ => ⟨0, Finset.mem_singleton_self _, χ, by simp⟩) s]
      intro α hα
      obtain rfl := Finset.mem_singleton.1 hα
      refine hr.mono ?_
      rw [QForm.Q_zero hϖ D hQ]
      have := neg_abs_le r
      simp only [Int.cast_zero, zero_div, add_zero]
      linarith
    obtain ⟨ζ, hζ0, hζ⟩ := exists_val_eq hv (r := |r| + 1) (by positivity)
    have h2 := NuGe.smul Q hζ.ge ((isSmul_iff ζ s _).2 rfl) h1
    rw [neg_add_cancel] at h2
    obtain ⟨c, -, e⟩ := hsp' _ h2
    exact ⟨ζ⁻¹ * c, by rw [mul_smul, ← e, inv_smul_smul₀ hζ0]⟩

end GlobalTheory.UT.PrimGen

namespace GlobalTheory.UT

open GlobalTheory.FieldBaseChange

theorem exists_prim_generator : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ : W0 U.toUnifPre, w₀.IsGen → ∃ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ ∧ Prim D Q v ϑ ∧ IsGenSec A.A A.L 1 th := by
  intro hL _ _ _ hU V _ _ _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ _ U w₀ hw
  obtain ⟨ϑ, hp, hsp⟩ := PrimGen.exists_prim_span hU hϖ hQ hv
  obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hL.1.globalFns U F (k := 1) le_rfl w₀ hw
  refine ⟨e.symm ϑ, ϑ, (he _ _).2 (e.apply_symm_apply ϑ), hp, fun t => ?_⟩
  obtain ⟨σ, -, hσ⟩ := (he t _).2 rfl
  obtain ⟨c, hc⟩ := hsp _ (PrimGen.exists_vge U.toUnifPre v hσ 0)
  have ht : t = (c • e.symm ϑ : SecOver (abelianBase A F) _) :=
    e.injective (hc.trans (by rw [map_smul, e.apply_symm_apply]))
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c, fun j => ?_⟩
  rw [ht]
  rfl

end GlobalTheory.UT
