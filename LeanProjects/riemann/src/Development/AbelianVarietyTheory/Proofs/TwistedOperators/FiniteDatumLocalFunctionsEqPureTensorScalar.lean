import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianDatumFlippedFiniteTensorBigRoute

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section

namespace GlobalTheory.FlipMatch

open GlobalTheory.BigDat GlobalTheory.WeilM

set_option maxHeartbeats 1600000 in

theorem datum_placesA : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t) (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
    (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → IsTied t i j e Bs Γ X →
    ∀ f₀, IsDatumA (t := t) W e Γ (Finsupp.single (((), ρ.vX i (j + 1)), ρ.vT (i + 1) j) 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ Γ.M.vac) →
    ∀ ι : ∀ w : Pl D.host.E, ((Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank) → Fv D.host.F (w.under (𝓞 D.host.F))) → ℂ) →ₗ[ℂ]
      (Matrix (Fin ((locGrid G t w).rank (i + 1, j + 1))) ((locGrid G t w).Cols i j) (Kw w) → ℂ),
    (∀ w ∈ locPl G t, IsLagrModel Γ.M W.ψ (w.under (𝓞 D.host.F)) (mixHalf e (atPl w 1)) (mixHalf e (cA D (atPl w 1))) (mixCo B t e w) (ι w)) →
    ∃ s : ℂ, s ≠ 0 ∧ ∀ ε, IsIdemSum ε (locPl G t) → ∀ (n : Pl D.host.E → ℕ) Ψ (τ : TotT G (routeBig t i j)),
      (∀ w ∈ locPl G t, IsNatDatum (unifAt w) (n w) (Ψ w)) →
      HasLocal B t ε (X := (i, j + 1)) (M := (i + 1, j + 1)) (Y := (i + 1, j)) ⟨i.2.le, j.2⟩ ⟨i.2, j.2⟩ ⟨i.2, j.2.le⟩
        (IsLocVec W (.chi i (j + 1)) ε (ρ.vX i (j + 1))) (IsLocVec W (.mu t (i + 1) j) ε (ρ.vT (i + 1) j)) τ Ψ →
      ∀ φ, IsFinPart Γ.M X.T φ → (∀ w ∈ locPl G t, ι w (φ (w.under (𝓞 D.host.F))) = Ψ w) →
        IsDatumA W e Γ τ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (s • f₀) φ) := by
  intro D T L sc G μ₀ hL W B ρ t i j M _ e Bs Γ X om om' h hT hti f₀ hdat ι hι
  classical
  have h₁ := ρ.vX_is i (j + 1) i.2 j.2
  have h₂ := ρ.vT_is t (i + 1) j i.2 j.2
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd W.ψ := h.ψ ▸ hT.base.std
  have hG : Γ.M.IsGood W.ψ := h.ψ ▸ hT.geo.hM
  obtain ⟨hadd, -, -⟩ := GlobalTheory.BigDat.ThBox.thetaPt_box W M t i j e Bs Γ X om om' h hT
  have hf : thetaPt Γ W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ Γ.M.vac) = box e (ρ.vX i (j + 1)) (ρ.vT (i + 1) j) := by
    funext u
    have := hdat.2 u
    exact this.trans ((Finsupp.sum_single_index (zero_mul _)).trans (one_mul _))
  obtain ⟨hid, hsumid⟩ := GlobalTheory.IdemAtPl.main hL (G := G) t
  have hh := fun w hw => GlobalTheory.BigDat.halves_split hL W i j e Γ h.JW h.JWW _ _ (hid w hw).1 (hid w hw).2
  have hco := GlobalTheory.BigDat.mixCo_spec B t i j e
  have hv := fun w hw => lagr_vac (hι w hw) (hG.vac _).1 (hG.vac _).2.1 (latPt e (w.under (𝓞 D.host.F)) : Set _)
    (fun γ hγ hγ' => GlobalTheory.BigDat.VacFix.vac_fixed W M t i j e Bs Γ X om om' h hT _ (GlobalTheory.BigDat.latPt_le_latAtV t i j e Bs Γ X hti _) γ (.inr ⟨hγ, hγ'.elim
      (fun h => ⟨_, (hid w hw).1, h⟩) fun h => ⟨_, splitIdem_conj (hid w hw).1, h⟩⟩)) (hco w).2.1 (hh w hw).2.2.2.1
  set c := ∏ w ∈ locPl G t, ι w (Γ.M.vac _) 0 with hc
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun w hw => (hv w hw).1
  refine ⟨c, hc0, ?_⟩
  intro ε hε n Ψ τ _ hloc φ hφ hΨ
  obtain ⟨φ₁, φ₂, hmem, hsum⟩ := hloc
  have sW := (node_isV G hL (X := .grid (i + 1) (j + 1)) ⟨i.2, j.2⟩).sd
  obtain ⟨T₁, hT₁⟩ := (GlobalTheory.PlaceModelSum.placeModelExistsSum D W.ψ W.ψ_std _ _ _ _ (isSelfDualC_neg sW)
    (node_isV G hL (X := .grid i (j + 1)) ⟨i.2.le, j.2⟩).sd _ ε hε _ h₁.2.theta h₁.2.lat).1
  obtain ⟨T₂, hT₂⟩ := (GlobalTheory.PlaceModelSum.placeModelExistsSum D W.ψ W.ψ_std _ _ _ _
    (node_isV G hL (X := .grid (i + 1) j) ⟨i.2, j.2.le⟩).sd sW _ ε hε _ h₂.2.theta h₂.2.lat).1
  obtain ⟨g0, g1, g2⟩ := GlobalTheory.BigDat.boxGraph_graph_heis hL W i j e Γ h.JW h.JWW ε _ hε _ _ T₁ T₂ hT₁ hT₂
  obtain ⟨hεs, hεw⟩ := hsumid ε hε
  have hb : thetaPt Γ W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • f₀) Γ.M.vac) = c • box e (ρ.vX i (j + 1)) (ρ.vT (i + 1) j) := by
    rw [← hf]
    exact funext fun u => (congrArg (thetaPt Γ W.ψ · u) (funext fun _ => mul_assoc _ _ _)).trans (thetaPt_smul _ _ _ _ u)
  let R : Submodule ℂ ((Pt G i j → ℂ) × ((Ix G i j → AF D.host.F) → ℂ)) :=
    { carrier := {p | p.2 ∈ schA D.host.F _ ∧ (p.1, thetaPt Γ W.ψ p.2) ∈ boxGraph e ε T₁ T₂}
      zero_mem' := ⟨zero_mem _, by
        have : thetaPt Γ W.ψ 0 = 0 := funext fun u => by simpa using thetaPt_smul Γ W.ψ 0 0 u
        rw [Prod.snd_zero, this]; exact zero_mem _⟩
      add_mem' := fun {p q} hp hq => ⟨add_mem hp.1 hq.1, by
        rw [Prod.snd_add, hadd _ hp.1 _ hq.1]; exact add_mem hp.2 hq.2⟩
      smul_mem' := fun a p hp => ⟨Submodule.smul_mem _ a hp.1, by
        rw [Prod.smul_snd, show thetaPt Γ W.ψ (a • p.2) = a • thetaPt Γ W.ψ p.2 from funext (thetaPt_smul _ _ _ _)]
        exact Submodule.smul_mem _ a hp.2⟩ }
  have hA : ∀ w ∈ locPl G t, ∀ x ∈ mixHalf e (atPl w 1), x ∈ mixHalf e ε := fun w hw x hx =>
    ⟨isHalf_mono (hεw w hw) hx.1, isHalf_mono (hεw w hw) hx.2⟩
  have hA' : ∀ w ∈ locPl G t, ∀ x ∈ mixHalf e (cA D (atPl w 1)), x ∈ mixHalf e (cA D ε) := fun w hw x hx =>
    have : cA D ε * cA D (atPl w 1) = cA D (atPl w 1) := by rw [← RingHom.map_mul, hεw w hw]
    ⟨isHalf_mono this hx.1, isHalf_mono this hx.2⟩
  have hbase : (Set.indicator (halfPt e ε : Set _) fun u => ∏ w ∈ locPl G t, ι w (Γ.M.vac _) (mixCo B t e w u)) =
      c • box e (halfInd ε (latV G i j)) (halfInd ε (latW G i j)) := by
    funext u
    rw [Pi.smul_apply, smul_eq_mul, box, halfInd, halfInd]
    by_cases hu : u ∈ mixHalf e ε
    · rw [Set.indicator_of_mem (mem_halfPt.2 hu), Finset.prod_congr rfl fun w hw =>
        (congrArg _ ((hco w).2.2.1 u).symm).trans ((hv w hw).2 _ ((hh w hw).2.2.2.2 u).1)]
      by_cases hl : mapV e u ∈ latV G i j ∧ mapW e u ∈ latW G i j
      · rw [if_pos ⟨hl.1, hu.1⟩, if_pos ⟨hl.2, hu.2⟩, mul_one, mul_one]
        exact Finset.prod_congr rfl fun w hw => Set.indicator_of_mem (((hh w hw).2.2.2.2 u).2.2 hl.1 hl.2) _
      · have : ∃ w ∈ locPl G t, ofMaps e (atPl w 1 • mapV e u, atPl w 1 • mapW e u) ∉ latPt e (w.under (𝓞 D.host.F)) := by
          by_contra! hall
          exact hl ⟨mem_of_sum_smul (hεs ▸ hu.1) fun w hw => (mapV_ofMaps e _ ▸ (hall w hw).2.1 :),
            mem_of_sum_smul (hεs ▸ hu.2) fun w hw => (mapW_ofMaps e _ ▸ (hall w hw).2.2 :)⟩
        obtain ⟨w, hw, hn⟩ := this
        rw [Finset.prod_eq_zero hw (Set.indicator_of_notMem hn _)]
        rcases not_and_or.1 hl with hl | hl
        · rw [if_neg fun h => hl h.1, zero_mul, mul_zero]
        · rw [if_neg fun h : _ ∧ IsHalf ε (mapW e u) => hl h.1, mul_zero, mul_zero]
    · rw [Set.indicator_of_notMem (mt mem_halfPt.1 hu)]
      rcases not_and_or.1 hu with hl | hl
      · rw [if_neg fun h => hl h.2, zero_mul, mul_zero]
      · rw [if_neg fun h : _ ∧ IsHalf ε (mapW e u) => hl h.2, mul_zero, mul_zero]
  have hR := GlobalTheory.InductLagr.rel_of_vac Γ.M W.ψ hstd hG (locPl G t) (fun w => w.under (𝓞 D.host.F)) (Good.under_injOn hL G t) _
    (fun w => mixHalf e (atPl w 1)) (fun w => mixHalf e (cA D (atPl w 1))) (mixCo B t e) ι (halfPt e ε) R (c • f₀)
    (fun w hw => hι w hw) (fun w hw u hu => ⟨(hh w hw).1 u hu, mem_halfPt.2 (hA w hw u hu)⟩) (fun w hw => (hh w hw).2.1)
    (fun w hw => (hh w hw).2.2.1) (fun w _ x _ u => (hco w).1 u x)
    (fun w _ w' _ hne x hx u => by rw [(hco w').1, (hco w').2.2.2 w hne.symm x hx, add_zero])
    (fun w hw u => ⟨_, ((hh w hw).2.2.2.2 u).1, (hco w).2.2.1 u, ((hh w hw).2.2.2.2 u).2.1⟩)
    (fun w hw x hx p hp => ⟨GlobalTheory.HeisSchA.rho_mem_schA Γ.M W.ψ hstd x _ hp.1, by
      have := g1 x (hA w hw x hx) _ hp.2
      rwa [← thetaPt_rho] at this⟩)
    (fun w hw x hx p hp => ⟨GlobalTheory.HeisSchA.rho_mem_schA Γ.M W.ψ hstd x _ hp.1, by
      have := g2 x (hA' w hw x hx) _ hp.2
      rwa [← thetaPt_rho] at this⟩)
    ⟨(isFinPart_vac hG ∅).fam.mem hG _, by
      have := (boxGraph e ε T₁ T₂).smul_mem c (Submodule.subset_span
        ⟨_, _, GlobalTheory.isSBHalf_halfInd ε _, GlobalTheory.isSBHalf_halfInd ε _, rfl⟩)
      rw [(congrArg T₁ (one_smul ℂ _).symm).trans hT₁.vac, (congrArg T₂ (one_smul ℂ _).symm).trans hT₂.vac] at this
      show (_, thetaPt Γ W.ψ _) ∈ _
      rw [hbase, hb]
      exact this⟩
    φ hφ.1 fun v hv => hφ.2 v fun hm => let ⟨w, hw, e⟩ := (hti.2.2.1 v).1 hm; hv w hw e
  have hτ : (∑ d ∈ τ.support, τ d • (box e (φ₁ d) (φ₂ d), box e d.1.2 d.2)) ∈ boxGraph e ε T₁ T₂ :=
    sum_mem fun d hd => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, (hmem d hd).1.1, (hmem d hd).2.1, by
      rw [← (hmem d hd).1.2.2 T₁ hT₁, ← (hmem d hd).2.2.2 T₂ hT₂]⟩)
  have hfst : (Set.indicator (halfPt e ε : Set _) fun u => ∏ w ∈ locPl G t, ι w (φ _) (mixCo B t e w u)) =
      (∑ d ∈ τ.support, τ d • (box e (φ₁ d) (φ₂ d), box e d.1.2 d.2)).1 := by
    funext u
    rw [Prod.fst_sum, Finset.sum_apply]
    by_cases hu : u ∈ mixHalf e ε
    · rw [Set.indicator_of_mem (mem_halfPt.2 hu), Finset.prod_congr rfl fun w hw => congrFun (hΨ w hw) _]
      exact (hsum _ _ hu.1 hu.2).symm
    · rw [Set.indicator_of_notMem (mt mem_halfPt.1 hu)]
      refine (Finset.sum_eq_zero fun d hd => mul_eq_zero_of_right _ ?_).symm
      by_contra hne
      exact hu ⟨(hmem d hd).1.1.1 _ (left_ne_zero_of_mul hne), (hmem d hd).2.1.1 _ (right_ne_zero_of_mul hne)⟩
  refine ⟨hR.1, fun u => ?_⟩
  have := g0 _ (by
    have := sub_mem hR.2 hτ
    rwa [← Prod.mk.eta (p := Finset.sum _ _), Prod.mk_sub_mk, ← hfst, sub_self] at this)
  have := congrFun (sub_eq_zero.1 this) u
  rw [Prod.snd_sum, Finset.sum_apply] at this
  exact this

end GlobalTheory.FlipMatch

end
