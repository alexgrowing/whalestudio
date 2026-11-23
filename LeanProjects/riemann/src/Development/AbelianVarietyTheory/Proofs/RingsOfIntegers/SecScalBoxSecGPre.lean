import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecScalBoxSecGProd
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecScalOfPointwise
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PreboxExpansionWeight

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ExpandsBoxPre

set_option maxHeartbeats 2000000 in

theorem secScal_boxSecG_pre : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pG : IsPowGrp G' G j) (U' : UnifPre I D' A' G') (U : UnifPre I D A G) (wL : LB.Iso U'.LG.L (boxLB U.LG.L pG.pr)) (hw : wL.IsGen) (k : ℕ) (s : Fin j → U.SecK k) (σ : Fin j → H0 U.LG.L k) (r : Fin j → R), (∀ i, GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ)) (s i) (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) (σ i) (pullback.fst G.hom (jK R)) (scal (pullback.snd G.hom (jK R) ≫ jK R) (r i))) → ∀ s' : U'.SecK k, IsBoxSecK pG wL k s' s → GeneratorPullback.SecScal U'.LG.L (fun _ : Fin 1 => pullback.fst G'.hom (jK R)) (fun _ => (k : ℤ)) s' (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => (k : ℤ)) (boxSecG pG wL hw U.LG.isLB U'.LG.isLB k σ) (pullback.fst G'.hom (jK R)) (scal (pullback.snd G'.hom (jK R) ≫ jK R) (∏ i, r i)) := by
  intro R _ _ I j D D' A A' G G' _ _ _ _ pG U' U wL hw k s σ r hσ s' hs'
  intro j₁ j₂ hcoh
  have hj0 : j₁ 0 = j₂ 0 := hcoh (Sum.inl 0) (Sum.inr 0) (by simp)
  obtain ⟨jL, rfl⟩ : ∃ jL, j₁ = fun _ => jL := ⟨j₁ 0, funext fun x => by fin_cases x; rfl⟩
  obtain rfl : j₂ = fun _ => jL := funext fun x => by fin_cases x; exact hj0.symm
  set fst' := pullback.fst G'.hom (jK R) with hfst'
  set W := LB.wchart U'.LG.L (fun _ : Fin 1 => fst') (fun _ => jL) ⊓
    LB.wchart U'.LG.L (fun k => fst' ≫ (fun _ : Fin 1 => 𝟙 G'.left) k) (fun _ => jL) with hWdef
  have hcov : W ≤ ⨆ jN : Fin j → U.LG.L.ι, W ⊓ fst' ⁻¹ᵁ (boxLB U.LG.L pG.pr).U jN := by
    intro y hy
    have : fst'.base y ∈ (⨆ jN, (boxLB U.LG.L pG.pr).U jN : G'.left.Opens) := by
      rw [(linComb_isLB _ U.LG.isLB _ _).cover]; trivial
    obtain ⟨jN, hjN⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨jN, hy, hjN⟩
  apply sec_ext_cover W (fun jN => W ⊓ fst' ⁻¹ᵁ (boxLB U.LG.L pG.pr).U jN) (fun _ => inf_le_left) hcov
  intro jN
  apply ReciprocityTheory.ChartRestriction.G.Geo.Tor.fn_ext
  intro y hy
  have hyW : y ∈ W := hy.1
  have hyB : fst'.base y ∈ (boxLB U.LG.L pG.pr).U jN := hy.2
  have hyL : fst'.base y ∈ U'.LG.L.U jL := Set.mem_iInter.1 hyW.1 0
  have hyV : fst'.base y ∈ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jN, jL) := ⟨hyB, hyL⟩
  set snd' := pullback.snd G'.hom (jK R) ≫ jK R with hsnd'

  set u := Geo.Tor.gs fst' y ((LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jN, jL)) ((wL.s (jN, jL)) ^ k).val with hu
  set Lσ := Geo.Tor.gs fst' y (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL))
    ((boxSecG pG wL hw U.LG.isLB U'.LG.isLB k σ).f (fun _ => jL)) with hLσ
  set S := Geo.Tor.gs (𝟙 _) y (LB.wchart U'.LG.L (fun _ : Fin 1 => fst') (fun _ => jL)) (s'.f (fun _ => jL)) with hS
  set C := Geo.Tor.gs (𝟙 _) y ⊤ (scal snd' (∏ i, r i)) with hC
  have hA : u * Lσ = ∏ i, Geo.Tor.gs (fst' ≫ (pG.pr i).left) y (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jN i))
      ((σ i).f (fun _ => jN i)) := by
    have E := congrArg (Geo.Tor.gs fst' y ((LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jN, jL)))
      (isBoxSecG_boxSecG pG wL hw U.LG.isLB U'.LG.isLB k σ jN jL)
    refine (congrArg (u * ·) (Geo.Tor.gs_res _ _ (boxG_le_b pG jN jL) hyV _).symm).trans ?_
    refine (Geo.Tor.gs_mul _ _ _ hyV _ _).symm.trans (E.trans ?_)
    refine (gs_prod _ _ _ hyV _ _).trans (Finset.prod_congr rfl fun i _ => ?_)
    exact (Geo.Tor.gs_res _ _ _ hyV _).trans
      (Geo.Tor.gs_pull _ _ _ _ (Set.mem_iInter.2 fun _ => by simpa using Set.mem_iInter.1 hyB i) _)
  have hB : ∀ i, Geo.Tor.gs (fst' ≫ (pG.pr i).left) y (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jN i))
      ((σ i).f (fun _ => jN i)) = Geo.Tor.gs (𝟙 _) y ⊤ (scal snd' (r i)) *
        Geo.Tor.gs (prK pG i) y (LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => jN i))
          ((s i).f (fun _ => jN i)) := by
    intro i
    have hcoh_i : LB.Coh U.LG.L (Sum.elim (fun _ : Fin 1 => pullback.fst G.hom (jK R))
        (fun k => pullback.fst G.hom (jK R) ≫ (fun _ : Fin 1 => 𝟙 G.left) k))
        (Sum.elim (fun _ : Fin 1 => jN i) (fun _ : Fin 1 => jN i)) := by
      intro a b _; rcases a with a | a <;> rcases b with b | b <;> rfl
    have hmemK : (pullback.fst G.hom (jK R)).base ((prK pG i).base y) ∈ U.LG.L.U (jN i) := by
      rw [← Scheme.Hom.comp_apply, prK_fst, Scheme.Hom.comp_apply]
      exact Set.mem_iInter.1 hyB i
    have hyi : (prK pG i).base y ∈ LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => jN i) ⊓
        LB.wchart U.LG.L (fun k => pullback.fst G.hom (jK R) ≫ (fun _ : Fin 1 => 𝟙 G.left) k) (fun _ => jN i) :=
      ⟨Set.mem_iInter.2 fun _ => hmemK, Set.mem_iInter.2 fun _ => by simpa using hmemK⟩
    have E := congrArg (Geo.Tor.gs (prK pG i) y _) (hσ i (fun _ => jN i) (fun _ => jN i) hcoh_i)
    rw [← prK_fst]
    refine (Geo.Tor.gs_pull _ _ _ _ ?_ _).symm.trans ?_
    · exact Set.mem_iInter.2 fun _ => by simpa using hmemK
    refine (Geo.Tor.gs_res _ _ _ hyi _).symm.trans (E.trans ?_)
    refine (Geo.Tor.gs_mul _ _ _ hyi _ _).trans ?_
    congr 1
    · refine (Geo.Tor.gs_res _ _ _ hyi _).trans ?_
      show Geo.Tor.gs (prK pG i) y ⊤ (((pullback.snd G.hom (jK R) ≫ jK R).app ⊤).hom _) =
        Geo.Tor.gs (𝟙 _) y ⊤ ((snd'.app ⊤).hom _)
      refine (Geo.Tor.gs_pull (prK pG i) (pullback.snd G.hom (jK R) ≫ jK R) y ⊤ (by trivial) _).trans ?_
      refine Eq.trans ?_ (Geo.Tor.gs_pull (𝟙 _) snd' y ⊤ (by trivial) _).symm
      rw [← Category.assoc, boxScal_prK_snd, Category.id_comp]
    · exact Geo.Tor.gs_res _ _ _ hyi _
  have hCc : u * S = ∏ i, Geo.Tor.gs (prK pG i) y
      (LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => jN i)) ((s i).f (fun _ => jN i)) := by
    have hyV' : (𝟙 (pullback G'.hom (jK R)) : _ ⟶ _) y ∈ fst' ⁻¹ᵁ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jN, jL) := hyV
    have E := congrArg (Geo.Tor.gs (𝟙 _) y (fst' ⁻¹ᵁ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jN, jL))) (hs' jN jL)
    have hu' : Geo.Tor.gs (𝟙 _) y (fst' ⁻¹ᵁ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jN, jL))
        ((pullU (Y := pullback G'.hom (jK R)) fst' _ (wL.s (jN, jL))) ^ k).val = u := by
      have e1 : ((pullU (Y := pullback G'.hom (jK R)) fst' _ (wL.s (jN, jL))) ^ k).val =
          (fst'.app _).hom ((wL.s (jN, jL)) ^ k).val := by
        rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow]; rfl
      rw [e1]
      exact (Geo.Tor.gs_pull _ _ _ _ hyV _).trans (by rw [Category.id_comp])
    refine (congrArg₂ (· * ·) hu'.symm (Geo.Tor.gs_res _ _ (boxSec_le_a pG jN jL) hyV' _).symm).trans ?_
    refine (Geo.Tor.gs_mul _ _ _ hyV' _ _).symm.trans (E.trans ?_)
    refine (gs_prod _ _ _ hyV' _ _).trans (Finset.prod_congr rfl fun i _ => ?_)
    refine (Geo.Tor.gs_res _ _ _ hyV' _).trans
      ((Geo.Tor.gs_pull (𝟙 _) (prK pG i) y
        (LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => jN i))
        (boxSec_le_b pG jN jL i hyV') _).trans ?_)
    rw [Category.id_comp]
  have hD : C = ∏ i, Geo.Tor.gs (𝟙 _) y ⊤ (scal snd' (r i)) := by
    rw [hC, show scal snd' (∏ i, r i) = ∏ i, scal snd' (r i) by simp [scal, map_prod],
      gs_prod _ _ _ (by trivial)]
  have hU : IsUnit u := by
    rw [hu, Geo.Tor.gs_unit _ _ _ hyV]; exact Units.isUnit _
  have hmain : Lσ = C * S := by
    apply hU.mul_left_cancel
    rw [hA, Finset.prod_congr rfl (fun i _ => hB i), Finset.prod_mul_distrib, ← hD, ← hCc]
    ring
  have hLg : Geo.Tor.gs (𝟙 _) y (W ⊓ fst' ⁻¹ᵁ (boxLB U.LG.L pG.pr).U jN) (rs (inf_le_left : W ⊓ fst' ⁻¹ᵁ (boxLB U.LG.L pG.pr).U jN ≤ W)
      (rs (inf_le_right.trans (fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k) :
        W ≤ fst' ⁻¹ᵁ LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL))
        ((fst'.app (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL))).hom
          ((boxSecG pG wL hw U.LG.isLB U'.LG.isLB k σ).f (fun _ => jL))))) = Lσ := by
    refine (Geo.Tor.gs_res _ _ _ hy _).trans ((Geo.Tor.gs_res _ _ _ hyW _).trans
      ((Geo.Tor.gs_pull _ _ _ _ ?_ _).trans ?_))
    · exact Set.mem_iInter.2 fun _ => by simpa using hyL
    · rw [Category.id_comp]
  have hRg : Geo.Tor.gs (𝟙 _) y (W ⊓ fst' ⁻¹ᵁ (boxLB U.LG.L pG.pr).U jN) (rs (inf_le_left : W ⊓ fst' ⁻¹ᵁ (boxLB U.LG.L pG.pr).U jN ≤ W)
      (resTop W (scal snd' (∏ i, r i)) * rs (inf_le_left : W ≤ LB.wchart U'.LG.L (fun _ : Fin 1 => fst') (fun _ => jL))
        (s'.f (fun _ => jL)))) = C * S := by
    refine (Geo.Tor.gs_res _ _ _ hy _).trans ((Geo.Tor.gs_mul _ _ _ hyW _ _).trans ?_)
    congr 1
    · exact Geo.Tor.gs_res _ _ _ hyW _
    · exact Geo.Tor.gs_res _ _ _ hyW _
  exact hLg.trans (hmain.trans hRg.symm)

set_option maxHeartbeats 1000000 in

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U' : UnifPre I D' A' G') (U : UnifPre I D A G) (wL : LB.Iso U'.LG.L (boxLB U.LG.L pG.pr)), (∀ i, U'.gen.hom ≫ pA.pr i = (Over.pullback (jK R)).map (pG.pr i) ≫ U.gen.hom) ∧ wL.IsGen ∧ (∃ b : LB.Gen (LB.LinComb U.LG.L (K := Fin j) (fun i => eSec G' ≫ (pG.pr i).left) (fun _ => 1)), GeneratorPullback.MapsAt U.LG.L U'.LG.L (fun i => (pG.pr i).left) wL (eSec G') 1 U'.LG.rig b ∧ LB.Gen.Corr U.LG.L _ _ _ _ b (GeneratorPullback.finProdGen U.LG.L (J := Fin j) (fun _ _ => eSec G) (fun _ _ => 1) (fun _ => U.LG.rig))) ∧ (∀ (e : ℕ) (i : Fin j), (U'.gt e).q ≫ (Over.pullback (thick R I e)).map (pD.pw.pr i) = (Over.pullback (thick R I e)).map (pG.pr i) ≫ (U.gt e).q) ∧ (∀ (e : ℕ) (x : D'.toPre.X), ∃ hψ : ∀ (i : Fin j) (k : Fin 4), D'.toPre.Oφ ((Over.map (thick R I e)).map (U'.gt e).q ≫ D'.toPre.prBe I e) x k ≫ (pD.pw.pr i).left = ((Over.pullback (thick R I e)).map (pG.pr i)).left ≫ D.toPre.Oφ ((Over.map (thick R I e)).map (U.gt e).q ≫ D.toPre.prBe I e) (pD.xe x i) k, LB.Gen.Maps (LB.linCombIso pD.w _ Oinvε) ((U'.gt e).t x) (GeneratorPullback.boxGen D.toPre.P.L (fun i => (pD.pw.pr i).left) _ Oinvε (fun i => GeneratorPullback.pullAlong D.toPre.P.L (pD.pw.pr i).left ((Over.pullback (thick R I e)).map (pG.pr i)).left _ Oinvε _ (hψ i) ((U.gt e).t (pD.xe x i))))) ∧ (∀ (e : ℕ) (jNM : Fin j → D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL' : U'.LG.L.ι) (jNL : Fin j → U.LG.L.ι), res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_left) : (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM') ⊓ (LB.div (D'.toPre.P.L.pull (U'.gt e).pG.left) (U'.LG.L.pull (fstG I e G').left)).U (fun _ => jM', fun _ => jL') ⊓ (⨅ i, ((Over.pullback (thick R I e)).map (pG.pr i)).left ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left) (U.LG.L.pull (fstG I e G).left)).U (fun _ => jNM i, fun _ => jNL i)) ⊓ (fstG I e G').left ⁻¹ᵁ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jNL, jL') ≤ (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM')) (pullU (U'.gt e).pG.left _ (pD.w.s (jNM, jM'))) * res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_right)) ((U'.w e).s (fun _ => jM', fun _ => jL')) = (∏ i, res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_right.trans (iInf_le _ i))) (pullU ((Over.pullback (thick R I e)).map (pG.pr i)).left _ ((U.w e).s (fun _ => jNM i, fun _ => jNL i)))) * res (X := (thickObj R I e G').left) inf_le_right (pullU (Y := (thickObj R I e G').left) (fstG I e G').left _ (wL.s (jNL, jL')))) → ∀ (k : ℕ) (s : Fin j → U.SecK k) (Fs : Fin j → Fam D.toPre (FractionRing R) k), (∀ i, U.Expands k (s i) (Fs i)) → ∀ (s' : U'.SecK k) (F' : Fam D'.toPre (FractionRing R) k), IsBoxSecK pG wL k s' s → IsBoxFam pD (FractionRing R) k F' Fs → U'.Expands k s' F' := by
  intro R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG U' U wL h k s Fs hs s' F' hs' hF'
  choose r hr σ f hσ hf hE using hs
  refine ⟨∏ i, r i, Finset.prod_ne_zero_iff.2 fun i _ => hr i,
    boxSecG pG wL h.2.1 U.LG.isLB U'.LG.isLB k σ, boxFamB pD k f,
    secScal_boxSecG_pre R I j D D' A A' G G' pG U' U wL h.2.1 k s σ r hσ s' hs',
    fun α' => GlobalTheory.BoxFamScalar.main R I j D D' pD k Fs f r hf F' hF' α', fun e => ?_⟩
  exact GlobalTheory.BoxExpPre.expandsAt_box_unifPre R I j D D' A A' G G' pD pA pG U' U wL h k e σ f (fun i => hE i e) _ _
    (isBoxSecG_boxSecG pG wL h.2.1 U.LG.isLB U'.LG.isLB k σ) (isBoxFamB_boxFamB pD k f)

end GlobalTheory.ExpandsBoxPre
