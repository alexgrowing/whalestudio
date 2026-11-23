import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstPtsAddSmul

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ConstFrame

theorem valR_g_self {A : Type} [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} {L : LB Z} (hL : L.IsLB) (x : Sp A ⟶ Z)
    (j : L.ι) (h : ⊤ ≤ x ⁻¹ᵁ L.U j) : valR x (L.U j ⊓ L.U j) (L.g j j).val = 1 := by
  apply toStkA_injective
  rw [toStkA_valR x (L.U j ⊓ L.U j) _ (fun _ hz => ⟨h hz, h hz⟩), map_one]
  exact congrArg Units.val (gm_self hL x _ (h trivial))

theorem valR_rig {A A₀ : Type} [CommRing A] [IsLocalRing A] [CommRing A₀] {B : Over (Sp A)} {B₀ : Over (Sp A₀)}
    [GrpObj B] [IsCommMonObj B] [GrpObj B₀] [IsCommMonObj B₀] {M : LB B.left} {M₀ : LB B₀.left} (f : A₀ →+* A)
    {φ : B.left ⟶ B₀.left} (he : eSec B ≫ φ = spMap f ≫ eSec B₀) (w : LB.Iso M (M₀.pull φ))
    (r : LB.Gen (M.pull (eSec B))) (r₀ : LB.Gen (M₀.pull (eSec B₀)))
    (h : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec B) (fun _ => 1)) r (rigPullOf φ (spMap f) he M₀ r₀))
    (j : M.ι) (j₀ : M₀.ι) (hj : ⊤ ≤ (show Sp A ⟶ _ from eSec B) ⁻¹ᵁ (LB.div (M₀.pull φ) M).U (fun _ => j₀, j))
    (hj₀ : ⊤ ≤ (M₀.pull (eSec B₀)).U (fun _ => j₀)) :
    f (valR (𝟙 (Sp A₀)) ((M₀.pull (eSec B₀)).U (fun _ => j₀)) (r₀.s (fun _ => j₀)).val) =
      valR (A := A) (eSec B) _ (w.s (fun _ => j₀, j)).val *
        valR (𝟙 (Sp A)) ((M.pull (eSec B)).U (fun _ => j)) (r.s (fun _ => j)).val := by
  have hc := hj (show cpt A ∈ (⊤ : (Sp A).Opens) from trivial)
  have e := gm_maps_pt h (𝟙 (Sp A)) (cpt A) (fun _ => j₀) j hc.1 hc.2
  have hr : ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ (M.pull (eSec B)).U (fun _ => j) := fun z hz => mem_pull.2 (hj hz).2
  have h₀ : ⊤ ≤ (𝟙 (Sp A₀)) ⁻¹ᵁ (M₀.pull (eSec B₀)).U (fun _ => j₀) := hj₀
  have h₁ := FormalValue.top_le_comp h₀ (spMap f)
  apply toStkA_injective
  refine Eq.trans ?_ ((congrArg Units.val e).trans ?_)
  · refine (congrArg _ (FormalValue.valR_spMap f _ _ h₀ _).symm).trans ((toStkA_valR _ _ _ h₁ _).trans
      (congrArg Units.val ?_))
    have hm : (𝟙 (Sp A) : Sp A ⟶ Sp A) (cpt A) ∈ ((M₀.pull φ).pull (eSec B)).U (fun _ _ => j₀) := mem_pull.2 hc.1
    refine Eq.trans ?_ ((gm_res (𝟙 (Sp A)) _ _ hm _).trans (gm_pull (𝟙 (Sp A)) (spMap f) _ _ (hj₀ trivial) _)).symm
    rw [Category.id_comp, Category.comp_id]
  · refine Eq.trans ?_ (map_mul _ _ _).symm
    exact (Units.val_mul _ _).trans (congrArg₂ (· * ·) (toStkA_valR (A := A) (eSec B) _ _ hj _).symm
      (toStkA_valR _ _ _ hr _).symm)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable [Algebra (FractionRing ℂ) ℂ] {Y : Model Xo c β} {b : O →+* ℂ} {a : ArcIn D l β ℂ b} {χ : Sp ℂ⟦X⟧ ⟶ Y.X}
  {W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ} {Λ : GtAn a}
  (Ξ : ConstPts W Λ)

omit [Algebra (FractionRing ℂ) ℂ] in

theorem complete : IsAdicComplete ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) ℂ⟦X⟧ := by
  rw [Algebra.algebraMap_self, Ideal.map_id]
  infer_instance

theorem base_comp (v : Λ.A.V) :
    (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) ≫ W.φ = spMap (PowerSeries.C (R := ℂ)) ≫ (Λ.u.ex v.2).left :=
  ((Ξ.g_rel v 0).1 2).trans (congrArg (spMap (PowerSeries.C (R := ℂ)) ≫ ·) (Λ.ex0_b v))

theorem exists_charts (v : Λ.A.V) : ∃ (jM : W.P.D.toPre.P.L.ι) (j₀ : a.D₀.P.L.ι),
    ⊤ ≤ (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, jM) ∧
    ⊤ ≤ (Λ.u.ex v.2).left ⁻¹ᵁ a.D₀.P.L.U j₀ := by
  obtain ⟨jM, hM⟩ := exists_chart W.P.D.toPre.P.isLB ((show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) (cpt ℂ⟦X⟧))
  have h₀ := FrameValue.le_chartAt a.D₀.P.isLB (Λ.u.ex v.2).left
  refine ⟨jM, _, (top_le_iff_cpt _ _).2 ⟨mem_pull.2 ?_, hM⟩, h₀⟩
  exact (congrArg (fun q => q (cpt ℂ⟦X⟧) ∈ a.D₀.P.L.U _) (base_comp Ξ v)).mpr (FormalValue.top_le_comp h₀ _ trivial)

theorem isFrm (v : Λ.A.V) : IsFrm W.P.U.LG.L (Ξ.x v).left (Ξ.τ v) := by
  haveI := complete
  obtain ⟨jM, j₀, hj, h₀⟩ := exists_charts Ξ v
  have hw := FormalValue.isUnit_valR (A := ℂ⟦X⟧) (Ξ.g v).b.left _ hj (W.w.s (fun _ => j₀, jM))
  have hM : ⊤ ≤ FormalValue.basePt (Ξ.g v) ⁻¹ᵁ W.P.D.toPre.P.L.U jM := fun z hz => (hj hz).2
  refine ⟨fun j h => ?_, fun j j' h => ?_⟩
  · refine isUnit_of_mul_isUnit_right ((congrArg IsUnit (Ξ.τ_eq v j jM j₀ h hj)).mpr ?_)
    exact (Units.isUnit _).mul ((Ne.isUnit (Λ.u.fr_ne j₀ v.2 h₀)).map _)
  · have h₁ : ⊤ ≤ (Ξ.x v).left ⁻¹ᵁ W.P.U.LG.L.U j := fun z hz => (h hz).1
    have h₂ : ⊤ ≤ (Ξ.x v).left ⁻¹ᵁ W.P.U.LG.L.U j' := fun z hz => (h hz).2
    have t := FormalValue.tau_trans (Ξ.x_fm v) h₁ h₂ hM hM
    rw [valR_g_self W.P.D.toPre.P.isLB _ jM hM, _root_.mul_one] at t
    have e₁ := Ξ.τ_eq v j jM j₀ h₁ hj
    have e₂ := Ξ.τ_eq v j' jM j₀ h₂ hj
    refine hw.mul_left_cancel (e₁.trans ?_)
    refine (congrArg (· * _) t).trans ?_
    rw [_root_.mul_assoc, mul_left_comm]
    exact (mul_left_comm _ _ _).trans ((congrArg (_ * ·) e₂.symm).trans (mul_left_comm _ _ _))

theorem tau_zero (hx : Ξ.x 0 = 1) (j : W.P.U.LG.L.ι) (h : ⊤ ≤ (Ξ.x 0).left ⁻¹ᵁ W.P.U.LG.L.U j) :
    Ξ.τ 0 j = valR (𝟙 (Sp ℂ⟦X⟧)) ((W.P.U.LG.L.pull (eSec W.t.G)).U (fun _ => j))
      (W.P.U.LG.rig.s (fun _ => j)).val := by
  haveI := complete
  have hs : spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) = 𝟙 _ := Spec.map_id _
  obtain ⟨jM, j₀, hj, h₀⟩ := exists_charts Ξ 0
  have hw := FormalValue.isUnit_valR (A := ℂ⟦X⟧) (Ξ.g 0).b.left _ hj (W.w.s (fun _ => j₀, jM))
  have hM : ⊤ ≤ FormalValue.basePt (Ξ.g 0) ⁻¹ᵁ W.P.D.toPre.P.L.U jM := fun z hz => (hj hz).2
  have hx' : (Ξ.x 0).left = spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) ≫ eSec W.t.G := by
    refine (congrArg Over.Hom.left hx).trans ?_
    exact congrArg (· ≫ eSec W.t.G) ((Category.comp_id _).symm.trans (Over.w (toUnit selfR)))
  have hu : (Λ.u.ex (0 : Λ.A.V).2).left = eSec a.D₀.P.A := by
    refine (congrArg Over.Hom.left ((Λ.u.ker 0).2 Λ.u.Λ.zero_mem)).trans ?_
    rw [Hom.one_def]; simp [eSec]
  have hb : FormalValue.basePt (Ξ.g 0) = eSec W.P.D.toPre.P.A := by
    refine W.spec.1.1.hom_ext ?_ ?_
    · exact (base_comp Ξ 0).trans ((congrArg (_ ≫ ·) hu).trans W.he.symm)
    · exact (Over.w (Ξ.g 0).b).trans (hs.trans (Over.w η[W.P.D.toPre.P.A]).symm)
  have hb' : FormalValue.basePt (Ξ.g 0) = spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) ≫ eSec W.P.D.toPre.P.A :=
    hb.trans ((Category.id_comp _).symm.trans (congrArg (· ≫ _) hs.symm))
  have hf := Ξ.x_fm 0
  have e := Ξ.τ_eq 0 j jM j₀ h hj
  rw [hx'] at hf h e
  have t := FormalValue.tau_rig hf hb' h hM
  have hj₀ : ⊤ ≤ (a.D₀.P.L.pull (eSec a.D₀.P.A)).U (fun _ => j₀) := fun z hz =>
    mem_pull.2 ((congrArg (fun q => q z ∈ a.D₀.P.L.U j₀) hu).mp (h₀ hz))
  have r := valR_rig (PowerSeries.C (R := ℂ)) W.he W.w W.P.D.toPre.rig a.D₀.rig W.spec.2.2.1 jM j₀ (hb ▸ hj) hj₀
  have f := (congrArg (PowerSeries.C (R := ℂ)) (Λ.rig (fun _ => j₀) hj₀)).trans r
  replace f := f.trans (congrArg (fun q => valR (A := ℂ⟦X⟧) q _ (W.w.s (fun _ => j₀, jM)).val * _) hb.symm)
  refine hw.mul_left_cancel (e.trans ((congrArg (_ * ·) f).trans ((mul_left_comm _ _ _).trans (congrArg (_ * ·) ?_))))
  have t' := t
  generalize FormalValue.tau W.P.U.toUnifPre ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧))
    (spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) ≫ eSec W.t.G) j jM = q at t' ⊢
  rw [hs] at t'
  exact t'

omit [Algebra (FractionRing ℂ) ℂ] in

theorem main : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) , (∀ v, IsFrm W.P.U.LG.L (Ξ.x v).left (Ξ.τ v)) ∧ ∀ j, ⊤ ≤ (Ξ.x 0).left ⁻¹ᵁ W.P.U.LG.L.U j → Ξ.τ 0 j = valR (𝟙 (Sp ℂ⟦X⟧)) ((W.P.U.LG.L.pull (eSec W.t.G)).U (fun _ => j)) (W.P.U.LG.rig.s (fun _ => j)).val := by
  intro h₁ h₂ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ
  refine ⟨isFrm Ξ, tau_zero Ξ ?_⟩
  have h := (GlobalTheory.ArcPts.constPts_add_smul h₁ h₂ E H D l Xo c O β Y b a χ W Λ Ξ).1 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

end GlobalTheory.ConstFrame
