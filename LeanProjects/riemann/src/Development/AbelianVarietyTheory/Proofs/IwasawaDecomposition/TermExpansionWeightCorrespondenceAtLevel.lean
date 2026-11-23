import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.CancelSecAct
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.TorusInj
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTransport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusCoordSecondPresentationWeightEqStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationExpansionSumsEqTransportStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TermMatch

theorem gs_sub' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a - b) = gs f y U a - gs f y U b := by simp only [gs_eq f y U h, map_sub]

theorem gs_sum' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {κ : Type} (S : Finset κ)
    (a : κ → Γ(X, U)) : gs f y U (∑ i ∈ S, a i) = ∑ i ∈ S, gs f y U (a i) := by
  simp only [gs_eq f y U h, map_sum]

theorem gs_zero' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) : gs f y U 0 = 0 := by
  simp only [gs_eq f y U h, map_zero]

theorem exists_good_ext {X Z : Scheme.{0}} (L : LB X) (hL : L.IsLB) (z : Z) (c : (Z ⟶ X) → L.ι) :
    ∃ J, Good L z J ∧ ∀ ψ, ψ z ∈ L.U (c ψ) → J ψ = c ψ := by
  classical
  choose d hd using fun ψ : Z ⟶ X => exists_chart hL (ψ z)
  refine ⟨fun ψ => if ψ z ∈ L.U (c ψ) then c ψ else d ψ, fun ψ => ?_, fun ψ h => if_pos h⟩
  by_cases h : ψ z ∈ L.U (c ψ)
  · simpa only [if_pos h] using h
  · simpa only [if_neg h] using hd ψ

theorem pull_inv {P Y B : Scheme.{0}} {a b : P ⟶ Y} {p : Y ⟶ B} (h : a ≫ p = b ≫ p) {W : B.Opens}
    {V : Y.Opens} (hV : V ≤ p ⁻¹ᵁ W) (ha : b ⁻¹ᵁ V ≤ a ⁻¹ᵁ V) (x : Γ(B, W)) :
    (a.appLE V (b ⁻¹ᵁ V) ha).hom ((Y.presheaf.map (homOfLE hV).op).hom ((p.app W).hom x)) =
      (b.app V).hom ((Y.presheaf.map (homOfLE hV).op).hom ((p.app W).hom x)) := by
  have m : p.app W ≫ Y.presheaf.map (homOfLE hV).op ≫ a.appLE V _ ha =
      p.app W ≫ Y.presheaf.map (homOfLE hV).op ≫ b.app V := by
    rw [Scheme.Hom.app_eq_appLE b, Scheme.Hom.map_appLE, Scheme.Hom.map_appLE,
      Scheme.Hom.app_eq_appLE p, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE,
      Semi.TorusInj.appLE_of_eq h]
  exact congrArg (fun φ => φ.hom x) m

end GlobalTheory.TermMatch

open GlobalTheory.TermMatch ReciprocityTheory.ChartRestriction.G.Out.WeightPf in
set_option maxHeartbeats 4000000 in

theorem GlobalTheory.termMatch_at_level : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)) (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen → wL.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG (maximalIdeal R) e G).left (r z) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U'.LG.L.U jL' → gw w (r ≫ (U'.gt e).pG.left) z (fun _ => jM) (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 = gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL')) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, val ((U.gt e).t (xe x)) r z J = val ((U'.gt e).t x) r z J') → ∀ (σ : H0 U.LG.L 2) (σ' : H0 U'.LG.L 2) (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ e : ℕ, U.ExpandsAt e 2 σ f) → (∀ e : ℕ, U'.ExpandsAt e 2 σ' f') → (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ G.left) → U.LG.L.ι) (J' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z J → Good U'.LG.L z J' → sval σ r z J = (gv wL r z (fun _ => J r) (fun _ => J' r)).val * sval σ' r z J') → ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → ∀ α' : D'.toPre.X, sval (f (xe α')) (r ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (xe α')) r z J).val = (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left)).val * sval (f' α') (r ≫ (U'.gt e).pG.left) z J' * (val ((U'.gt e).t α') r z J').val := by
  intro R _ _ _ hCN G _ _ hSA D D' A A' U U' Φ w wL hw hwL hΦ hlev xe hM σ σ' f f' hE hE' hσ e Z r z J J'
    hJ hJ' α'
  classical
  obtain ⟨S, hS⟩ := GlobalTheory.T.uniformisationExpansion_sums_eq_transport R hCN G hSA D D' A A' U U' Φ w wL hw hwL hΦ hlev xe hM σ σ' f f' hE hE' hσ e
  obtain ⟨h0, h0', -⟩ := hS Z r z J J' hJ hJ'
  by_cases hα : α' ∉ S
  · rw [h0 α' hα, h0' α' hα, zero_mul, mul_zero, zero_mul]
  push_neg at hα

  have hq : (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left := (hlev e).1
  let c : ((thickObj R (maximalIdeal R) e G).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι := fun ψ => J (r ≫ ψ)
  let c' : ((thickObj R (maximalIdeal R) e G).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι := fun ψ => J' (r ≫ ψ)
  let jf : D'.toPre.X → Fin 4 → D.toPre.P.L.ι := fun β k => c ((U.gt e).pG.left ≫ D.toPre.famφB (xe β) k)
  let jt : D'.toPre.X → Fin 4 → D.toPre.P.L.ι := fun β k => c (D.toPre.Oφ (U.gt e).pG (xe β) k)
  let jf' : D'.toPre.X → Fin 4 → D'.toPre.P.L.ι := fun β k => c' ((U'.gt e).pG.left ≫ D'.toPre.famφB β k)
  let jt' : D'.toPre.X → Fin 4 → D'.toPre.P.L.ι := fun β k => c' (D'.toPre.Oφ (U'.gt e).pG β k)
  let jM : Fin 1 → D.toPre.P.L.ι := fun _ => c ((U'.gt e).pG.left ≫ Φ.hom.left)
  let jM' : Fin 1 → D'.toPre.P.L.ι := fun _ => c' (U'.gt e).pG.left
  let Wo : D'.toPre.P.A.left.Opens :=
    ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left).U
      (fun _ => jM) ⊓ (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)).U jM'
  let Vst : (thickObj R (maximalIdeal R) e G).left.Opens :=
    ((U'.gt e).pG.left ⁻¹ᵁ Wo ⊓ (((U'.gt e).pG.left ≫ Φ.hom.left) ⁻¹ᵁ D.toPre.P.L.U (jM 0) ⊓
      (U'.gt e).pG.left ⁻¹ᵁ D'.toPre.P.L.U (jM' 0))) ⊓
    S.inf (fun β => ((U.gt e).pG.left ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB (xe β)) (jf β) ⊓
      LB.wchart D.toPre.P.L (D.toPre.Oφ (U.gt e).pG (xe β)) (jt β)) ⊓
      ((U'.gt e).pG.left ⁻¹ᵁ LB.wchart D'.toPre.P.L (D'.toPre.famφB β) (jf' β) ⊓
      LB.wchart D'.toPre.P.L (D'.toPre.Oφ (U'.gt e).pG β) (jt' β)))
  have hVo : Vst ≤ (U'.gt e).pG.left ⁻¹ᵁ Wo := inf_le_left.trans inf_le_left
  have hVm : Vst ≤ ((U'.gt e).pG.left ≫ Φ.hom.left) ⁻¹ᵁ D.toPre.P.L.U (jM 0) :=
    inf_le_left.trans (inf_le_right.trans inf_le_left)
  have hVm' : Vst ≤ (U'.gt e).pG.left ⁻¹ᵁ D'.toPre.P.L.U (jM' 0) :=
    inf_le_left.trans (inf_le_right.trans inf_le_right)
  have hVf : ∀ β ∈ S, Vst ≤ (U.gt e).pG.left ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB (xe β)) (jf β) :=
    fun β hβ => inf_le_right.trans ((Finset.inf_le hβ).trans (inf_le_left.trans inf_le_left))
  have hVt : ∀ β ∈ S, Vst ≤ LB.wchart D.toPre.P.L (D.toPre.Oφ (U.gt e).pG (xe β)) (jt β) :=
    fun β hβ => inf_le_right.trans ((Finset.inf_le hβ).trans (inf_le_left.trans inf_le_right))
  have hVf' : ∀ β ∈ S, Vst ≤ (U'.gt e).pG.left ⁻¹ᵁ LB.wchart D'.toPre.P.L (D'.toPre.famφB β) (jf' β) :=
    fun β hβ => inf_le_right.trans ((Finset.inf_le hβ).trans (inf_le_right.trans inf_le_left))
  have hVt' : ∀ β ∈ S, Vst ≤ LB.wchart D'.toPre.P.L (D'.toPre.Oφ (U'.gt e).pG β) (jt' β) :=
    fun β hβ => inf_le_right.trans ((Finset.inf_le hβ).trans (inf_le_right.trans inf_le_right))
  have hx0 : r z ∈ Vst := by
    have hc : ∀ ψ, ψ (r z) ∈ D.toPre.P.L.U (c ψ) := fun ψ => by
      have := hJ (r ≫ ψ); rwa [Scheme.Hom.comp_apply] at this
    have hc' : ∀ ψ, ψ (r z) ∈ D'.toPre.P.L.U (c' ψ) := fun ψ => by
      have := hJ' (r ≫ ψ); rwa [Scheme.Hom.comp_apply] at this
    refine ⟨⟨⟨mem_pull.2 (Set.mem_iInter.2 fun _ => ?_), Set.mem_iInter.2 fun _ => ?_⟩, ?_, ?_⟩,
      mem_finset_inf _ _ _ fun β _ => ⟨⟨Set.mem_iInter.2 fun k => ?_, Set.mem_iInter.2 fun k => ?_⟩,
        ⟨Set.mem_iInter.2 fun k => ?_, Set.mem_iInter.2 fun k => ?_⟩⟩⟩
    · have := hc ((U'.gt e).pG.left ≫ Φ.hom.left); rwa [Scheme.Hom.comp_apply] at this
    · exact hc' (U'.gt e).pG.left
    · exact hc _
    · exact hc' _
    · have := hc ((U.gt e).pG.left ≫ D.toPre.famφB (xe β) k); rwa [Scheme.Hom.comp_apply] at this
    · exact hc _
    · have := hc' ((U'.gt e).pG.left ≫ D'.toPre.famφB β k); rwa [Scheme.Hom.comp_apply] at this
    · exact hc' _

  let Fv : ∀ β ∈ S, Γ((thickObj R (maximalIdeal R) e G).left, Vst) := fun β hβ =>
    ((thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE (hVf β hβ)).op).hom (((U.gt e).pG.left.app _).hom ((f (xe β)).f (jf β)))
  let Tv : ∀ β ∈ S, Γ((thickObj R (maximalIdeal R) e G).left, Vst) := fun β hβ =>
    ((thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE (hVt β hβ)).op).hom (((U.gt e).t (xe β)).s (jt β)).val
  let Fv' : ∀ β ∈ S, Γ((thickObj R (maximalIdeal R) e G).left, Vst) := fun β hβ =>
    ((thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE (hVf' β hβ)).op).hom (((U'.gt e).pG.left.app _).hom ((f' β).f (jf' β)))
  let Tv' : ∀ β ∈ S, Γ((thickObj R (maximalIdeal R) e G).left, Vst) := fun β hβ =>
    ((thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE (hVt' β hβ)).op).hom (((U'.gt e).t β).s (jt' β)).val
  let Ωv : Γ((thickObj R (maximalIdeal R) e G).left, Vst) :=
    ((thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE hVo).op).hom (((U'.gt e).pG.left.app Wo).hom (w.s (fun _ => jM, jM')).val)
  let Hv : ∀ β ∈ S, Γ((thickObj R (maximalIdeal R) e G).left, Vst) := fun β hβ => Fv β hβ * Tv β hβ - Ωv * Fv' β hβ * Tv' β hβ
  have hterm : ∀ (Z0 : Scheme.{0}) (r0 : Z0 ⟶ (thickObj R (maximalIdeal R) e G).left) (z0 : Z0) (J0 : (Z0 ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι)
      (J0' : (Z0 ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), r0 z0 ∈ Vst →
      (∀ ψ, ψ (r0 z0) ∈ D.toPre.P.L.U (c ψ) → J0 (r0 ≫ ψ) = c ψ) →
      (∀ ψ, ψ (r0 z0) ∈ D'.toPre.P.L.U (c' ψ) → J0' (r0 ≫ ψ) = c' ψ) → ∀ β (hβ : β ∈ S),
      gs r0 z0 Vst (Hv β hβ) = sval (f (xe β)) (r0 ≫ (U.gt e).pG.left) z0 J0 * (val ((U.gt e).t (xe β)) r0 z0 J0).val -
        (ExpTrans.om w z0 (fun q _ => J0 q) (fun q _ => J0' q) (r0 ≫ (U'.gt e).pG.left)).val *
          sval (f' β) (r0 ≫ (U'.gt e).pG.left) z0 J0' * (val ((U'.gt e).t β) r0 z0 J0').val := by
    intro Z0 r0 z0 J0 J0' hz0 hc0 hc0' β hβ
    have hjf : ∀ k, J0 ((r0 ≫ (U.gt e).pG.left) ≫ D.toPre.famφB (xe β) k) = jf β k := fun k => by
      rw [Category.assoc]
      refine hc0 _ ?_
      have := Set.mem_iInter.1 (hVf β hβ hz0) k
      rwa [← Scheme.Hom.comp_apply] at this
    have hjf' : ∀ k, J0' ((r0 ≫ (U'.gt e).pG.left) ≫ D'.toPre.famφB β k) = jf' β k := fun k => by
      rw [Category.assoc]
      refine hc0' _ ?_
      have := Set.mem_iInter.1 (hVf' β hβ hz0) k
      rwa [← Scheme.Hom.comp_apply] at this
    have eF : gs r0 z0 Vst (Fv β hβ) = sval (f (xe β)) (r0 ≫ (U.gt e).pG.left) z0 J0 :=
      (gs_res r0 z0 (hVf β hβ) hz0 _).trans ((gs_pull r0 (U.gt e).pG.left z0 _ (hVf β hβ hz0) _).trans
        (sval_of _ _ _ _ (jf β) hjf).symm)
    have eT : gs r0 z0 Vst (Tv β hβ) = (val ((U.gt e).t (xe β)) r0 z0 J0).val :=
      (gs_res r0 z0 (hVt β hβ) hz0 _).trans ((gs_unit r0 z0 _ (hVt β hβ hz0) _).trans
        (congrArg Units.val (val_of _ r0 z0 J0 (jt β) (fun k => hc0 _ (Set.mem_iInter.1 (hVt β hβ hz0) k))).symm))
    have eF' : gs r0 z0 Vst (Fv' β hβ) = sval (f' β) (r0 ≫ (U'.gt e).pG.left) z0 J0' :=
      (gs_res r0 z0 (hVf' β hβ) hz0 _).trans ((gs_pull r0 (U'.gt e).pG.left z0 _ (hVf' β hβ hz0) _).trans
        (sval_of _ _ _ _ (jf' β) hjf').symm)
    have eT' : gs r0 z0 Vst (Tv' β hβ) = (val ((U'.gt e).t β) r0 z0 J0').val :=
      (gs_res r0 z0 (hVt' β hβ) hz0 _).trans ((gs_unit r0 z0 _ (hVt' β hβ hz0) _).trans
        (congrArg Units.val (val_of _ r0 z0 J0' (jt' β) (fun k => hc0' _ (Set.mem_iInter.1 (hVt' β hβ hz0) k))).symm))
    have ej : (fun (_ : Fin 1) => J0 ((r0 ≫ (U'.gt e).pG.left) ≫ Φ.hom.left)) = jM := funext fun _ => by
      rw [Category.assoc]
      exact hc0 _ (hVm hz0)
    have ek : (fun (_ : Fin 1) => J0' (r0 ≫ (U'.gt e).pG.left)) = jM' := funext fun _ => hc0' _ (hVm' hz0)
    have eO : (ExpTrans.om w z0 (fun q _ => J0 q) (fun q _ => J0' q) (r0 ≫ (U'.gt e).pG.left)) =
        gm (r0 ≫ (U'.gt e).pG.left) z0 Wo (w.s (fun _ => jM, jM')) := by
      have key : ∀ (j1 : Fin 1 → D.toPre.P.L.ι) (k1 : Fin 1 → D'.toPre.P.L.ι), j1 = jM → k1 = jM' →
          gw w (r0 ≫ (U'.gt e).pG.left) z0 j1 k1 = gm (r0 ≫ (U'.gt e).pG.left) z0 Wo (w.s (fun _ => jM, jM')) := by
        rintro _ _ rfl rfl; rfl
      exact key _ _ ej ek
    have eΩ : gs r0 z0 Vst Ωv = (ExpTrans.om w z0 (fun q _ => J0 q) (fun q _ => J0' q) (r0 ≫ (U'.gt e).pG.left)).val :=
      (gs_res r0 z0 hVo hz0 _).trans ((gs_pull r0 (U'.gt e).pG.left z0 Wo (hVo hz0) _).trans
        ((gs_unit (r0 ≫ (U'.gt e).pG.left) z0 Wo (hVo hz0) _).trans (congrArg Units.val eO.symm)))
    have e1 : gs r0 z0 Vst (Hv β hβ) = gs r0 z0 Vst (Fv β hβ) * gs r0 z0 Vst (Tv β hβ) -
        gs r0 z0 Vst Ωv * gs r0 z0 Vst (Fv' β hβ) * gs r0 z0 Vst (Tv' β hβ) := by
      simp only [Hv, gs_sub' r0 z0 Vst hz0, gs_mul r0 z0 Vst hz0]
    rw [e1, eF, eT, eF', eT', eΩ]

  have hsum0 : ∑ β ∈ S.attach, Hv β.1 β.2 = 0 := by
    refine fn_ext fun y hy => ?_
    obtain ⟨Jy, hJy, eJy⟩ := exists_good_ext D.toPre.P.L D.toPre.P.isLB y c
    obtain ⟨J'y, hJ'y, eJ'y⟩ := exists_good_ext D'.toPre.P.L D'.toPre.P.isLB y c'
    obtain ⟨-, -, E⟩ := hS _ (𝟙 _) y Jy J'y hJy hJ'y
    have ht := hterm _ (𝟙 _) y Jy J'y hy (fun ψ h => by rw [Category.id_comp]; exact eJy ψ h)
      (fun ψ h => by rw [Category.id_comp]; exact eJ'y ψ h)
    rw [gs_sum' _ y _ hy, gs_zero' _ y _ hy, Finset.sum_congr rfl (fun β _ => ht β.1 β.2),
      Finset.sum_attach S (fun β => sval (f (xe β)) (𝟙 (thickObj R (maximalIdeal R) e G).left ≫ (U.gt e).pG.left) y Jy * (val ((U.gt e).t (xe β)) (𝟙 (thickObj R (maximalIdeal R) e G).left) y Jy).val -
        (ExpTrans.om w y (fun q _ => Jy q) (fun q _ => J'y q) (𝟙 (thickObj R (maximalIdeal R) e G).left ≫ (U'.gt e).pG.left)).val *
          sval (f' β) (𝟙 (thickObj R (maximalIdeal R) e G).left ≫ (U'.gt e).pG.left) y J'y * (val ((U'.gt e).t β) (𝟙 (thickObj R (maximalIdeal R) e G).left) y J'y).val),
      Finset.sum_sub_distrib]
    rw [Finset.mul_sum] at E
    rw [E, ← Finset.sum_sub_distrib]
    exact Finset.sum_eq_zero fun β _ => by rw [_root_.mul_assoc, sub_self]
  have hpG : (act (U.gt e)).left ≫ (U.gt e).pG.left =
      (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left ≫ (U.gt e).pG.left :=
    act_left_pG (U.gt e)
  have hinv : Φ.hom.left ≫ Φ.inv.left = 𝟙 _ := by rw [← Over.comp_left, Φ.hom_inv_id, Over.id_left]
  have hq' : (U'.gt e).pG.left = (U.gt e).pG.left ≫ Φ.inv.left := by
    rw [← hq, Category.assoc, hinv, Category.comp_id]
  have hpG' : (act (U.gt e)).left ≫ (U'.gt e).pG.left =
      (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left ≫ (U'.gt e).pG.left := by
    rw [hq', ← Category.assoc, hpG, Category.assoc]
  have hpGΦ : (act (U.gt e)).left ≫ (U'.gt e).pG.left ≫ Φ.hom.left =
      (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left ≫ (U'.gt e).pG.left ≫ Φ.hom.left := by
    rw [← Category.assoc, hpG', Category.assoc]
  have hOφ' : ∀ β k, (act (U.gt e)).left ≫ D'.toPre.Oφ (U'.gt e).pG β k =
      (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left ≫ D'.toPre.Oφ (U'.gt e).pG β k := by
    intro β k
    have hm : (Over.map (thick R (maximalIdeal R) e)).map (act (U.gt e)) ≫ (U'.gt e).pG =
        (Over.map (thick R (maximalIdeal R) e)).map (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)) ≫
          (U'.gt e).pG :=
      Over.OverMorphism.ext (by simpa only [Over.comp_left, Over.map_map_left] using hpG')
    have h1 := Oφ_comp ((Over.map (thick R (maximalIdeal R) e)).map (act (U.gt e))) (U'.gt e).pG β k
    have h2 := Oφ_comp ((Over.map (thick R (maximalIdeal R) e)).map
      (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G))) (U'.gt e).pG β k
    simp only [Over.map_map_left] at h1 h2
    rw [h1, h2, hm]
  let W' : (Te D.toPre (maximalIdeal R) e ⊗ thickObj R (maximalIdeal R) e G).left.Opens :=
    (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left ⁻¹ᵁ Vst
  have mv : ∀ {B : Scheme.{0}} (ψ : (thickObj R (maximalIdeal R) e G).left ⟶ B) (O : B.Opens),
      (act (U.gt e)).left ≫ ψ = (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left ≫ ψ →
      ∀ y, (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left y ∈ ψ ⁻¹ᵁ O →
        (act (U.gt e)).left y ∈ ψ ⁻¹ᵁ O :=
    fun ψ O h y hy => (congrArg (· ∈ O) (comp_base_eq h y)).mpr hy
  have mw : ∀ {L : LB D'.toPre.P.A.left} {φ : Fin 4 → ((thickObj R (maximalIdeal R) e G).left ⟶ D'.toPre.P.A.left)}
      (j : Fin 4 → L.ι), (∀ k, (act (U.gt e)).left ≫ φ k =
        (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left ≫ φ k) →
      ∀ y, (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left y ∈ LB.wchart L φ j →
        (act (U.gt e)).left y ∈ LB.wchart L φ j :=
    fun {L φ} j h y hy => Set.mem_iInter.2 fun k => by
      have := Set.mem_iInter.1 hy k
      simp only [Set.mem_preimage] at this ⊢
      rw [comp_base_eq (h k) y]; exact this
  have mw0 : ∀ {L : LB D.toPre.P.A.left} {φ : Fin 4 → ((thickObj R (maximalIdeal R) e G).left ⟶ D.toPre.P.A.left)}
      (j : Fin 4 → L.ι), (∀ k, (act (U.gt e)).left ≫ φ k =
        (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left ≫ φ k) →
      ∀ y, (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left y ∈ LB.wchart L φ j →
        (act (U.gt e)).left y ∈ LB.wchart L φ j :=
    fun {L φ} j h y hy => Set.mem_iInter.2 fun k => by
      have := Set.mem_iInter.1 hy k
      simp only [Set.mem_preimage] at this ⊢
      rw [comp_base_eq (h k) y]; exact this
  have ha : W' ≤ (act (U.gt e)).left ⁻¹ᵁ Vst := by
    intro y hy
    refine ⟨⟨mv _ _ hpG' y hy.1.1, mv _ _ hpGΦ y hy.1.2.1, mv _ _ hpG' y hy.1.2.2⟩,
      mem_finset_inf _ _ _ fun β hβ => ⟨⟨mv _ _ hpG y (mem_of_finset_inf hy.2 hβ).1.1,
        mw0 _ (fun k => act_Oφ (U.gt e) (xe β) k) y (mem_of_finset_inf hy.2 hβ).1.2⟩,
        ⟨mv _ _ hpG' y (mem_of_finset_inf hy.2 hβ).2.1, mw _ (hOφ' β) y (mem_of_finset_inf hy.2 hβ).2.2⟩⟩⟩

  have keyF : ∀ β (hβ : β ∈ S), ((act (U.gt e)).left.appLE Vst W' ha).hom (Fv β hβ) =
      ((snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.app Vst).hom (Fv β hβ) :=
    fun β hβ => pull_inv hpG (hVf β hβ) ha _
  have keyF' : ∀ β (hβ : β ∈ S), ((act (U.gt e)).left.appLE Vst W' ha).hom (Fv' β hβ) =
      ((snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.app Vst).hom (Fv' β hβ) :=
    fun β hβ => pull_inv hpG' (hVf' β hβ) ha _
  have keyΩ : ((act (U.gt e)).left.appLE Vst W' ha).hom Ωv =
      ((snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.app Vst).hom Ωv :=
    pull_inv hpG' hVo ha _
  let chi : D.toPre.X → Γ((Te D.toPre (maximalIdeal R) e ⊗ thickObj R (maximalIdeal R) e G).left, W') := fun χ =>
    ((Te D.toPre (maximalIdeal R) e ⊗ thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE le_top).op).hom
      (TorusInj.chiP D.toPre.X (thickObj R (maximalIdeal R) e G) χ)
  have keyT : ∀ β (hβ : β ∈ S), ((act (U.gt e)).left.appLE Vst W' ha).hom (Tv β hβ) =
      chi (xe β) * ((snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.app Vst).hom (Tv β hβ) := by
    intro β hβ
    have hs : W' ≤ (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left ⁻¹ᵁ
        LB.wchart D.toPre.P.L (D.toPre.Oφ (U.gt e).pG (xe β)) (jt β) := fun z hz => hVt β hβ hz
    have ha' : W' ≤ (act (U.gt e)).left ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.Oφ (U.gt e).pG (xe β)) (jt β) :=
      fun z hz => hVt β hβ (ha hz)
    have T := t_act (U.gt e) (xe β) (jt β) (fun k1 k2 h => congrArg c h) W' hs ha'
    have m1 : (thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE (hVt β hβ)).op ≫
        (act (U.gt e)).left.appLE Vst W' ha = (act (U.gt e)).left.appLE _ W' ha' := Scheme.Hom.map_appLE _ _ _
    have m2 : (thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE (hVt β hβ)).op ≫
        (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.app Vst =
        (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.appLE _ W' hs := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE]
    exact (congrArg (fun φ => φ.hom (((U.gt e).t (xe β)).s (jt β)).val) m1).trans
      (T.trans (congrArg (_ * ·) (congrArg (fun φ => φ.hom (((U.gt e).t (xe β)).s (jt β)).val) m2).symm))
  have keyT' : ∀ β (hβ : β ∈ S), ((act (U.gt e)).left.appLE Vst W' ha).hom (Tv' β hβ) =
      chi (xe β) * ((snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.app Vst).hom (Tv' β hβ) := by
    intro β hβ
    have hs : W' ≤ (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left ⁻¹ᵁ
        LB.wchart D'.toPre.P.L (D'.toPre.Oφ (U'.gt e).pG β) (jt' β) := fun z hz => hVt' β hβ hz
    have ha' : W' ≤ (act (U.gt e)).left ⁻¹ᵁ LB.wchart D'.toPre.P.L (D'.toPre.Oφ (U'.gt e).pG β) (jt' β) :=
      fun z hz => hVt' β hβ (ha hz)
    have T := GlobalTheory.T.torusCoord_secondPresentation_weight_eq R hCN G hSA D D' A A' U U' e xe (hM e) β (jt' β) (fun k1 k2 h => congrArg c' h) W' hs ha'
    have m1 : (thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE (hVt' β hβ)).op ≫
        (act (U.gt e)).left.appLE Vst W' ha = (act (U.gt e)).left.appLE _ W' ha' := Scheme.Hom.map_appLE _ _ _
    have m2 : (thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE (hVt' β hβ)).op ≫
        (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.app Vst =
        (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.appLE _ W' hs := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE]
    exact (congrArg (fun φ => φ.hom (((U'.gt e).t β).s (jt' β)).val) m1).trans
      (T.trans (congrArg (_ * ·) (congrArg (fun φ => φ.hom (((U'.gt e).t β).s (jt' β)).val) m2).symm))
  have hact : ∀ β (hβ : β ∈ S), ((act (U.gt e)).left.appLE Vst W' ha).hom (Hv β hβ) =
      chi (xe β) * ((snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.app Vst).hom (Hv β hβ) := by
    intro β hβ
    have e1 : Hv β hβ = Fv β hβ * Tv β hβ - Ωv * Fv' β hβ * Tv' β hβ := rfl
    rw [e1, map_sub, map_mul, map_mul, map_mul, keyF β hβ, keyT β hβ, keyF' β hβ, keyT' β hβ, keyΩ, map_sub,
      map_mul, map_mul, map_mul]
    ring
  have hZ : ∑ β ∈ S.attach, chi (xe β.1) *
      ((snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.app Vst).hom (Hv β.1 β.2) = 0 :=
    (Finset.sum_congr rfl fun β _ => (hact β.1 β.2).symm).trans
      ((map_sum _ _ _).symm.trans ((congrArg _ hsum0).trans (map_zero _)))
  let hfun : D'.toPre.X → Γ((thickObj R (maximalIdeal R) e G).left, Vst) := fun β =>
    if hβ : β ∈ S then Hv β hβ else 0
  have hd : ∀ β (hβ : β ∈ S), hfun β = Hv β hβ := fun β hβ => dif_pos hβ
  have hsum : ∑ β ∈ S, chi (xe β) *
      ((snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.app Vst).hom (hfun β) = 0 :=
    (Finset.sum_attach S (fun β => chi (xe β) *
      ((snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.app Vst).hom (hfun β))).symm.trans
      ((Finset.sum_congr rfl fun β _ => congrArg (fun z => chi (xe β.1) *
        ((snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.app Vst).hom z) (hd β.1 β.2)).trans hZ)
  have hs' : ∑ χ ∈ S.map xe.toEquiv.toEmbedding, chi χ *
      ((snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.app Vst).hom (hfun (xe.symm χ)) = 0 := by
    rw [Finset.sum_map]
    refine (Finset.sum_congr rfl fun β _ => ?_).trans hsum
    exact congrArg (fun t => chi (xe β) *
      ((snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.app Vst).hom (hfun t))
      (xe.symm_apply_apply β)
  have h0 := TorusInj.eq_zero_of_sum D.toPre.X (thickObj R (maximalIdeal R) e G) (S.map xe.toEquiv.toEmbedding)
    (fun χ => hfun (xe.symm χ)) hs' (xe α') (Finset.mem_map_of_mem _ hα)
  have h1 : hfun α' = 0 := by simpa only [AddEquiv.symm_apply_apply] using h0
  have hH : Hv α' hα = 0 := (hd α' hα).symm.trans h1
  have fin := hterm Z r z J J' hx0 (fun ψ _ => rfl) (fun ψ _ => rfl) α' hα
  rw [hH, gs_zero' r z Vst hx0] at fin
  exact sub_eq_zero.1 fin.symm
