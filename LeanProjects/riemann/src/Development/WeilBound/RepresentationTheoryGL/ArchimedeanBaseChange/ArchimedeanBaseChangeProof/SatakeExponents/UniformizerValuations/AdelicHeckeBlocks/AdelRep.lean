import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelRep
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.HasCompactSupportOfSection
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PSplit
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.PAdelEqOf

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcN.F2 (mconv)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelH

namespace Adel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

omit [IsCMField E] in
theorem cpt_eq (w : Pl E) (u : GL (Fin n) E) (x : GA E n) :
    cpt w u x = GeneralLinearGroup.map (pLoc E w) (gFin x * (ratF E n u)⁻¹) := by
  rw [cpt, adeleqof_map_cW, map_mul, map_inv, adeleqof_pFin_ratGL]; rfl

theorem cpt'_eq (w : Pl E) (u : GL (Fin n) E) (x : GA E n) :
    cpt' w u x = GeneralLinearGroup.map (pLoc E w) (thF E n (gFin x * (ratF E n u)⁻¹)) := by
  rw [cpt', adeleqof_map_cW, adeleqof_pFin_thetaGL, map_mul, map_inv, adeleqof_pFin_ratGL]; rfl

end Adel

theorem rtAlg (hS : SizeBasic) : RtAlg := by
  intro E _ _ _ B u₁ u₂
  refine ⟨?_, ?_, ?_⟩
  · intro ψ ψ'
    funext x y g
    simp only [mulF, rt, mul_assoc]
  · intro t ht
    refine ⟨t.r + B.c + |logSize (finGL E B.a (ratF E B.a u₁))| + |logSize (finGL E B.b (ratF E B.b u₂))|, ?_⟩
    refine ⟨ht.T, add_nonneg (add_nonneg (add_nonneg ht.r B.c_nonneg) (abs_nonneg _)) (abs_nonneg _), ht.ka, ht.kb,
      fun x y => ⟨(ht.ψ x y).1.comp (continuous_mul_const _),
        (ht.ψ x y).2.comp_homeomorph (Homeomorph.mulRight (ratF E B.a u₁, ratF E B.b u₂)⁻¹)⟩, ?_⟩
    intro x y h hne
    have hh := ht.size x y _ hne
    simp only [Prod.fst_mul, Prod.fst_inv, Prod.snd_mul, Prod.snd_inv] at hh
    obtain ⟨h1, h2⟩ := hh
    have e1 : finGL E B.a h.1 = finGL E B.a (h.1 * (ratF E B.a u₁)⁻¹) * finGL E B.a (ratF E B.a u₁) := by
      rw [← map_mul, inv_mul_cancel_right]
    have e2 : finGL E B.b h.2 = finGL E B.b (h.2 * (ratF E B.b u₂)⁻¹) * finGL E B.b (ratF E B.b u₂) := by
      rw [← map_mul, inv_mul_cancel_right]
    have c1 := B.ca (finGL E B.a (h.1 * (ratF E B.a u₁)⁻¹)) (finGL E B.a (ratF E B.a u₁))
    have c2 := B.cb (finGL E B.b (h.2 * (ratF E B.b u₂)⁻¹)) (finGL E B.b (ratF E B.b u₂))
    have a1 := le_abs_self (logSize (finGL E B.a (ratF E B.a u₁)))
    have a2 := le_abs_self (logSize (finGL E B.b (ratF E B.b u₂)))
    have p1 := abs_nonneg (logSize (finGL E B.a (ratF E B.a u₁)))
    have p2 := abs_nonneg (logSize (finGL E B.b (ratF E B.b u₂)))
    rw [e1, e2]
    constructor <;> · dsimp only; linarith
  · intro ψ hψ
    choose ra hra using fun x y => (hS E B.a).1 _
      ((hψ x y).2.image ((continuous_finGL' (E := E) B.a).comp continuous_fst))
    choose rb hrb using fun x y => (hS E B.b).1 _
      ((hψ x y).2.image ((continuous_finGL' (E := E) B.b).comp continuous_snd))
    refine ⟨∑ x, ∑ y, (|ra x y| + |rb x y|), Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity, ?_⟩
    intro x y h hne
    have key : |ra x y| + |rb x y| ≤ ∑ x, ∑ y, (|ra x y| + |rb x y|) :=
      (Finset.single_le_sum (f := fun y' => |ra x y'| + |rb x y'|) (fun _ _ => by positivity) (Finset.mem_univ y)).trans
        (Finset.single_le_sum (f := fun x' => ∑ y', (|ra x' y'| + |rb x' y'|))
          (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ x))
    have hm : h ∈ tsupport (ψ x y) := subset_tsupport _ hne
    have b1 : logSize (finGL E B.a h.1) ≤ ra x y := hra x y _ ⟨h, hm, rfl⟩
    have b2 : logSize (finGL E B.b h.2) ≤ rb x y := hrb x y _ ⟨h, hm, rfl⟩
    have := le_abs_self (ra x y)
    have := le_abs_self (rb x y)
    have := abs_nonneg (ra x y)
    have := abs_nonneg (rb x y)
    exact ⟨by linarith, by linarith⟩

theorem adelRep (h1 : FmAlg) (h2 : FmTr) (h3 : RtAlg) : AdelRep := by
  intro E _ _ _ κ _ S P B e hS hP hne u₁ u₂ Ta Tb N Lo w t₀ L₀ hLo hL₀ ht₀
  have key : (lmWd Lo w L₀).Ok P ∧ (BGen.wd w t₀).ψ = rt u₁ u₂ (fm S P B e (lmWd Lo w L₀)) := by
    induction w with
    | nil => exact ⟨hL₀, ht₀⟩
    | cons g w ih =>
      have ih' := ih (fun s hs => hLo s (List.mem_cons_of_mem _ hs))
      rcases g with c | s
      · exact ih'
      · obtain ⟨hs1, hs2⟩ := hLo s (by simp)
        obtain ⟨-, hB, hC, -, -⟩ := h1 E κ S P B e hS hP (Lo s) (lmWd Lo w L₀) hs1 ih'.1
        refine ⟨hB, ?_⟩
        show mulF B.ν s.ψ (BGen.wd w t₀).ψ = rt u₁ u₂ (fm S P B e ((Lo s).mul (lmWd Lo w L₀)))
        rw [ih'.2, hs2, (h3 E B u₁ u₂).1, hC]
  refine ⟨key.1, key.2, ?_⟩
  funext g
  obtain ⟨-, hT⟩ := h2 E κ S P B e hP hne (lmWd Lo w L₀) N key.1
  have hT3 : F.trM (BGen.wd w t₀).Φ (opM Ta Tb (tenN P B e N)) g = _ :=
    tensTr E B.a B.b B.Ma B.Mb B.κ (BGen.wd w t₀).ka (BGen.wd w t₀).kb Ta Tb (BGen.wd w t₀).ψ (tenN P B e N) g
  have hA : ∏ v, (BGen.wd w t₀).arch Ta Tb v (GeneralLinearGroup.map (cV v) g.1, GeneralLinearGroup.map (cV v) g.2) =
      (∏ v, phiOf (B.Ma v) (Ta v) ((BGen.wd w t₀).ka v) (gInf v g.1)) *
        ∏ v, phiOf (B.Mb v) (Tb v) ((BGen.wd w t₀).kb v) (gInf v g.2) := by
    simp only [PT.arch]
    exact Finset.prod_mul_distrib
  have hF : finFn S ((lmWd Lo w L₀).tr P N) (lmWd Lo w L₀).t (hFin g * (ratF E B.a u₁, ratF E B.b u₂)⁻¹) =
      ∏ᶠ v ∈ S, (lmWd Lo w L₀).tr P N v (cpt v u₁ g.1, cpt v u₂ g.2) *
        if IsSplitAt v then (lmWd Lo w L₀).t v (cpt' v u₁ g.1, cpt' v u₂ g.2) else 1 := by
    simp only [finFn, Adel.cpt_eq, Adel.cpt'_eq]
    rfl
  rw [hT3, key.2]
  simp only [rt]
  rw [hT, Pi.smul_apply, smul_eq_mul, adel, hA, hF]
  ring

end PositivityTheory.Rg.BcB.F

end
