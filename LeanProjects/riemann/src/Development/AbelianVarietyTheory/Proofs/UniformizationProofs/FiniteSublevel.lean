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
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTwistBasisOffPrime
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralFamilyOfStrictMin
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsRepresentativesModNsmul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOfIsMinInClassTwoOfSameClassFour

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefVal
open TWM TWO SectionScalarValuation

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {D : DegData V (maximalIdeal V)}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)

theorem isPullback_jO : IsPullback (jO hϖ hv (D := D)).left (fst (TF (R := V) F) D.toPre.P.A).left
    (fst (TO hϖ hv) D.toPre.P.A).left (Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F))) := by
  have H₁ : IsPullback (snd (TO hϖ hv) D.toPre.P.A).left (fst (TO hϖ hv) D.toPre.P.A).left D.toPre.P.A.hom
      (TO hϖ hv).hom := (IsPullback.of_hasPullback (TO hϖ hv).hom D.toPre.P.A.hom).flip
  have H₀ : IsPullback (DegPre.prB D.toPre F).left (fst (TF (R := V) F) D.toPre.P.A).left D.toPre.P.A.hom
      (TF (R := V) F).hom := (IsPullback.of_hasPullback (TF (R := V) F).hom D.toPre.P.A.hom).flip
  rw [← jO_snd hϖ hv, ← Over.w (ιS hϖ hv)] at H₀
  exact H₀.of_right (jO_fst hϖ hv) H₁

include hϖ hv in

theorem exists_vge (hTW : TwistBCSpanStatement) {k : ℕ} (hk : 1 ≤ k) {α : D.toPre.X}
    (s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))) : ∃ r : ℚ, VGe D F v k α s r := by
  have hL := D.toPre.P.isLB
  have := D.toPre.P.isAb.proper
  have hp : IsProper (fst (TO hϖ hv) D.toPre.P.A).left :=
    inferInstanceAs (IsProper (pullback.fst (TO hϖ hv).hom D.toPre.P.A.hom))
  have : CompactSpace (TO hϖ hv).left := inferInstanceAs (CompactSpace (Spec (CommRingCat.of (Ov v))))
  have : QuasiSeparatedSpace (TO hϖ hv).left := inferInstanceAs (QuasiSeparatedSpace (Spec (CommRingCat.of (Ov v))))
  have : CompactSpace (TO hϖ hv ⊗ D.toPre.P.A).left :=
    QuasiCompact.compactSpace_of_compactSpace (fst (TO hϖ hv) D.toPre.P.A).left
  have : QuasiSeparatedSpace (TO hϖ hv ⊗ D.toPre.P.A).left :=
    (quasiSeparated_iff_quasiSeparatedSpace (fst (TO hϖ hv) D.toPre.P.A).left).mp inferInstance
  obtain ⟨s₁, hs₁⟩ := exists_sec hL (φ' := fun i => (jO hϖ hv (D := D)).left ≫
      (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB α i) (ε' := DegPre.famε k)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by
      rw [GC.famφ_eq, ← jO_snd hϖ hv, Category.assoc]) s
  obtain ⟨t, ht, S, hS⟩ := TwistLoc.exists_clear_denominator (nonZeroDivisors (Ov v)) (isPullback_jO hϖ hv (D := D)) hL
    (fun i => (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k) s₁
  obtain ⟨n, rr, σ, hσ⟩ := hTW V D.toPre k hk α (Ov v) (fO v hϖ hv) inferInstance S
  choose σF hσF using fun i => FamInt.exists_pull (D := D) (F := F) (σ i)
  have ht0 : (t : F) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := F) ht
  obtain ⟨r, hr⟩ := wt_coe_of_ne (v := v) (inv_ne_zero ht0)
  refine ⟨r, n, fun i => (t : F)⁻¹ * ιr (v := v) (rr i), σ, σF, hσF, fun i => ?_, fun j => ?_⟩
  · rw [AddValuation.map_mul, hr]
    exact le_add_of_nonneg_right (v_ιr _)
  refine (sec_ext_val hL (s' := FamInt.secLin (fun i => gF D.toPre F ((t : F)⁻¹ * ιr (v := v) (rr i))) σF)
    (fun y J hJ => ?_) j).trans rfl
  rw [sval_lin (s := FamInt.secLin _ _) (fun i => gF D.toPre F ((t : F)⁻¹ * ιr (v := v) (rr i))) σF (fun _ => rfl) _ y hJ]
  have e₁ : sval S (𝟙 _ ≫ (jO hϖ hv (D := D)).left) y J = gs (𝟙 _) y ⊤ (gF D.toPre F t) * sval s (𝟙 _) y J := by
    rw [← hs₁ _ _ y J hJ, sval_of S (𝟙 _ ≫ (jO hϖ hv (D := D)).left) y J (fun a => J (𝟙 _ ≫ (jO hϖ hv (D := D)).left ≫
      (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB α a)) (fun a => by rw [Category.assoc])]
    refine (hS _ (𝟙 _) y _ (hJ.mem (fun a => (jO hϖ hv (D := D)).left ≫
      (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB α a) (𝟙 _))).trans (congrArg₂ (· * ·) ?_ rfl)
    have e := gs_jO hϖ hv (D := D) (𝟙 _) y ((Scheme.ΓSpecIso (CommRingCat.of (Ov v))).inv.hom t)
    rw [show ιr (v := v) ((Scheme.ΓSpecIso (CommRingCat.of (Ov v))).inv.hom t) = (t : F) by simp [ιr]] at e
    rw [← e, ← Category.assoc]
    exact (gs_pull _ _ y ⊤ trivial _).symm
  have e₂ := sval_lin (fun l => (fst (TO hϖ hv) D.toPre.P.A).left.appTop.hom (rr l))
      (fun l => pullSec D.toPre.P.L _ _ (σ l) (snd (TO hϖ hv) D.toPre.P.A).left) (fun j => hσ j)
      (𝟙 _ ≫ (jO hϖ hv).left) y hJ
  have g : ∀ a b : F, gs (𝟙 _) y ⊤ (gF D.toPre F (a * b)) =
      gs (𝟙 _) y ⊤ (gF D.toPre F a) * gs (𝟙 _) y ⊤ (gF D.toPre F b) := fun a b => by
    rw [map_mul, gs_mul _ y ⊤ trivial]
  have g₁ : gs (𝟙 _) y ⊤ (gF D.toPre F (t : F)⁻¹) * gs (𝟙 _) y ⊤ (gF D.toPre F t) = 1 := by
    rw [← g, inv_mul_cancel₀ ht0, map_one, gs_eq _ _ ⊤ trivial, map_one, map_one]
  rw [← _root_.one_mul (sval s _ y J), ← g₁, _root_.mul_assoc, ← e₁, e₂, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [g, gs_jO, sval_pullSec _ _ _ _ _ y hJ, Category.assoc, jO_snd, secScal_sval (hσF i) _ y hJ, _root_.mul_assoc]

include hϖ hv in

theorem exists_nuGe (hTW : TwistBCSpanStatement) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q) {k : ℕ} (hk : 1 ≤ k)
    (s : Fam D.toPre F k) : ∃ r : ℚ, NuGe D Q F v k s r := by
  classical
  obtain ⟨-, e, he⟩ := exists_representatives_mod_nsmul D.toPre.X k hk
  choose r hr using fun i => exists_vge hϖ hv hTW hk (s.s (e i))
  obtain ⟨m, hm⟩ := (Set.finite_range fun i => (Q (e i) : ℚ) / k - r i).bddAbove
  refine ⟨-m, ?_⟩
  rw [n1a V ϖ hϖ D Q hQ _ _ hv k hk (Finset.univ.image e) (fun χ => by
    obtain ⟨i, hi, -⟩ := he χ
    exact ⟨e i, Finset.mem_image_of_mem _ (Finset.mem_univ i), hi⟩) s]
  intro α hα
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hα
  have := hm ⟨i, rfl⟩
  exact VGe.mono (hr i) (by linarith)

include hϖ in

theorem finite_sublevel {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q) {k : ℕ} (hk : 1 ≤ k) (l : D.toPre.X →+ ℚ)
    (q : ℚ) : {χ | (Q χ : ℚ) / k + l χ ≤ q}.Finite := by
  let β : LinearMap.BilinForm ℤ D.toPre.X := LinearMap.mk₂ ℤ (fun a b => QForm.bHom hϖ D hQ a b)
    (fun a a' b => by simp) (fun c a b => by simp) (fun a b b' => by simp) (fun c a b => by simp)
  have hβ : ∀ a, β a a = 2 * Q a := fun a => (QForm.two_Q_eq hϖ D hQ a).symm
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  refine (ClassMin.finite_affine_sublevel (ClassMin.realExtension_ofIntBilin_posDef (β := β)
    (fun a b => QForm.bOf_comm D a b) (fun a ha => by have := QForm.Q_pos hϖ D hQ ha; rw [hβ]; omega))
    (inv_pos.2 hk') ((Rat.castHom ℝ).toAddMonoidHom.comp l) q).subset fun χ hχ => ?_
  have h : (((Q χ : ℚ) / k + l χ : ℚ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hχ
  show (k : ℝ)⁻¹ * ClassMin.ofIntBilin β χ + (l χ : ℝ) ≤ q
  rw [ClassMin.ofIntBilin_apply, hβ]
  push_cast at h ⊢
  refine le_of_eq_of_le ?_ h
  field_simp

end GlobalTheory.UT.CoefVal
end
