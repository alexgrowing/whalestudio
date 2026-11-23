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
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR in
set_option maxHeartbeats 1600000 in

theorem expansion_sums_transport : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)) (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen → wL.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG (maximalIdeal R) e G).left (r z) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U'.LG.L.U jL' → gw w (r ≫ (U'.gt e).pG.left) z (fun _ => jM) (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 = gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL')) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, val ((U.gt e).t (xe x)) r z J = val ((U'.gt e).t x) r z J') → ∀ (σ : H0 U.LG.L 2) (σ' : H0 U'.LG.L 2) (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ e : ℕ, U.ExpandsAt e 2 σ f) → (∀ e : ℕ, U'.ExpandsAt e 2 σ' f') → (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ G.left) → U.LG.L.ι) (J' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z J → Good U'.LG.L z J' → sval σ r z J = (gv wL r z (fun _ => J r) (fun _ => J' r)).val * sval σ' r z J') → ∀ e : ℕ, ∃ S : Finset D'.toPre.X, ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → (∀ α' ∉ S, sval (f (xe α')) (r ≫ (U.gt e).pG.left) z J = 0) ∧ (∀ α' ∉ S, sval (f' α') (r ≫ (U'.gt e).pG.left) z J' = 0) ∧ ∑ α' ∈ S, sval (f (xe α')) (r ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (xe α')) r z J).val = (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left)).val * ∑ α' ∈ S, sval (f' α') (r ≫ (U'.gt e).pG.left) z J' * (val ((U'.gt e).t α') r z J').val := by
  intro R _ _ _ _ G _ _ _ D D' A A' U U' Φ w wL _ _ _ hlev xe _ σ σ' f f' hE hE' hσ e
  classical
  obtain ⟨S₁, hS₁⟩ := expandsAt_val U.toUnifPre e 2 σ f (hE e)
  obtain ⟨S₂, hS₂⟩ := expandsAt_val U'.toUnifPre e 2 σ' f' (hE' e)
  refine ⟨S₁.map xe.symm.toEquiv.toEmbedding ∪ S₂, fun Z r z J J' hJ hJ' => ?_⟩
  obtain ⟨A₁, B₁⟩ := hS₁ Z r z J hJ
  obtain ⟨A₂, B₂⟩ := hS₂ Z r z J' hJ'
  have z₁ : ∀ α' ∉ S₁.map xe.symm.toEquiv.toEmbedding ∪ S₂,
      sval (f (xe α')) (r ≫ (U.gt e).pG.left) z J = 0 := by
    intro α' hα
    refine A₁ _ fun hc => hα (Finset.mem_union_left _ (Finset.mem_map.2 ⟨xe α', hc, xe.symm_apply_apply α'⟩))
  have z₂ : ∀ α' ∉ S₁.map xe.symm.toEquiv.toEmbedding ∪ S₂,
      sval (f' α') (r ≫ (U'.gt e).pG.left) z J' = 0 := by
    intro α' hα
    exact A₂ _ fun hc => hα (Finset.mem_union_right _ hc)
  refine ⟨z₁, z₂, ?_⟩

  have E₁ : ∑ α' ∈ S₁.map xe.symm.toEquiv.toEmbedding ∪ S₂,
      sval (f (xe α')) (r ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (xe α')) r z J).val =
      ∑ α ∈ S₁, sval (f α) (r ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t α) r z J).val := by
    rw [← Finset.sum_subset (Finset.subset_union_left) (fun α' _ hα => by
      rw [A₁ (xe α') fun hc => hα (Finset.mem_map.2 ⟨xe α', hc, xe.symm_apply_apply α'⟩), zero_mul]),
      Finset.sum_map]
    refine Finset.sum_congr rfl fun α _ => ?_
    have h₀ : xe (xe.symm.toEquiv.toEmbedding α) = α := xe.apply_symm_apply α
    rw [h₀]
  have E₂ : ∑ α' ∈ S₁.map xe.symm.toEquiv.toEmbedding ∪ S₂,
      sval (f' α') (r ≫ (U'.gt e).pG.left) z J' * (val ((U'.gt e).t α') r z J').val =
      ∑ α' ∈ S₂, sval (f' α') (r ≫ (U'.gt e).pG.left) z J' * (val ((U'.gt e).t α') r z J').val :=
    (Finset.sum_subset (Finset.subset_union_right) (fun α' _ hα => by rw [A₂ α' hα, zero_mul])).symm
  rw [E₁, E₂]
  obtain ⟨jL, hL⟩ := exists_chart U.LG.isLB ((fstG (maximalIdeal R) e G).left (r z))
  obtain ⟨jL', hL'⟩ := exists_chart U'.LG.isLB ((fstG (maximalIdeal R) e G).left (r z))
  rw [← B₁ jL hL, ← B₂ jL' hL']
  obtain ⟨J₀, hJ₀, k₀⟩ := exists_good U.LG.L U.LG.isLB z (fun _ : PUnit => r ≫ (fstG (maximalIdeal R) e G).left)
    (fun _ => jL) (fun _ _ _ => rfl) (fun _ => hL)
  obtain ⟨J₀', hJ₀', k₀'⟩ := exists_good U'.LG.L U'.LG.isLB z (fun _ : PUnit => r ≫ (fstG (maximalIdeal R) e G).left)
    (fun _ => jL') (fun _ _ _ => rfl) (fun _ => hL')
  have c₀ : J₀ (r ≫ (fstG (maximalIdeal R) e G).left) = jL := k₀ PUnit.unit
  have c₀' : J₀' (r ≫ (fstG (maximalIdeal R) e G).left) = jL' := k₀' PUnit.unit
  have hS : sv U.toUnifPre 2 σ (r ≫ (fstG (maximalIdeal R) e G).left) z jL =
      (gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL')).val *
        sv U'.toUnifPre 2 σ' (r ≫ (fstG (maximalIdeal R) e G).left) z jL' := by
    have H := hσ Z (r ≫ (fstG (maximalIdeal R) e G).left) z J₀ J₀' hJ₀ hJ₀'
    rw [sval_of σ _ z J₀ (fun _ => jL) (fun _ => by rw [Category.comp_id]; exact c₀),
      sval_of σ' _ z J₀' (fun _ => jL') (fun _ => by rw [Category.comp_id]; exact c₀'), c₀, c₀'] at H
    exact H
  have W : gw w (r ≫ (U'.gt e).pG.left) z (fun _ => J (r ≫ (U.gt e).pG.left)) (fun _ => J' (r ≫ (U'.gt e).pG.left)) *
        wv U'.toUnifPre e r z (J' (r ≫ (U'.gt e).pG.left)) jL' ^ 2 =
      wv U.toUnifPre e r z (J (r ≫ (U.gt e).pG.left)) jL ^ 2 *
        gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL') :=
    (hlev e).2 Z r z (J (r ≫ (U.gt e).pG.left)) (J' (r ≫ (U'.gt e).pG.left)) jL jL' (hJ _) (hJ' _) hL hL'
  have hO : ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left) =
      gw w (r ≫ (U'.gt e).pG.left) z (fun _ => J (r ≫ (U.gt e).pG.left)) (fun _ => J' (r ≫ (U'.gt e).pG.left)) := by
    show gw w (r ≫ (U'.gt e).pG.left) z (fun _ => J ((r ≫ (U'.gt e).pG.left) ≫ Φ.hom.left))
      (fun _ => J' (r ≫ (U'.gt e).pG.left)) = _
    rw [Category.assoc, (hlev e).1]
  rw [hS, hO, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul, W]

end GlobalTheory
