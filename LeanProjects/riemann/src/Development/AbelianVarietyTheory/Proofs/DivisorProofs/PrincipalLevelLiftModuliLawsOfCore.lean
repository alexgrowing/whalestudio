import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishingStatement
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.LevCore

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem dict_transport {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
    {X : Comp → Data E r} {V W : HSp D} (h : V = W) (dict : GA D V → Σ k, Frame (X k).Ψ r)
    (d : GA D W → Σ k, Frame (X k).Ψ r) (hdd : ∀ g (h' : V = W), d g = dict (h' ▸ g))
    (Kf : Subgroup (GA D V)) (th : ∀ k, (X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hr : V.rank = r)
    (N : ℕ) (hl : IsLevelK V N Kf) (hd : DictIsUnif V dict Kf th hr)
    (hu : ∀ g τ i, ‖dmin (X (dict g).1).Gm (dict g).2 τ i‖ = 1) :
    ∃ (Kf' : Subgroup (GA D W)) (hr' : W.rank = r), IsLevelK W N Kf' ∧ DictIsUnif W d Kf' th hr' ∧
      ∀ g τ i, ‖dmin (X (d g).1).Gm (d g).2 τ i‖ = 1 := by
  subst h
  obtain rfl : d = dict := funext fun g => hdd g rfl
  exact ⟨Kf, hr, hl, hd, hu⟩

end GlobalTheory.LevCore

open GlobalTheory.LevCore in

theorem GlobalTheory.LevGeo.laws_of_coreJ : ∀ (D : D7) (T : CoreJ D) (j : ℕ), LawsJ T → InR D j → Laws D j (T.Q.Xo j) T.Q.c (T.U j) (coreDict T.toCore j) ∧ ∀ (G : WTZ D.host.E) (σ : T.Q.c.F →+* ℂ) (f : cuspW (T.Q.Xo j) T.Q.c (T.U j) G), normW (T.U j) (xiR D) (fun _ => D.sp.W j) (coreDict T.toCore j) G σ f = normW (T.U j) (xiR D) (T.V j) (T.dict j) G σ f := by
  intro D T j hT hj
  obtain ⟨hH, hL, _, hDat⟩ := hT.pins
  refine ⟨⟨hj, hH, hDat j hj, hL.2, hT.unf j hj, hT.chiTriv j hj, ?_, ?_⟩, ?_⟩
  · intro σ hσ
    obtain ⟨th, hr, hinf, hdu⟩ := hT.dictU j hj σ hσ
    obtain ⟨Kf', hr', h1, h2, h3⟩ := dict_transport (hT.spaceW j hj σ hσ) (T.dict j σ) (coreDict T.toCore j σ)
      (fun g h' => by unfold coreDict; rw [dif_pos h']) (T.Kf j σ) th hr _
      (hL.1 ▸ hT.levelK j hj σ hσ) hdu (hT.muUnit j hj σ hσ).2.2.2
    exact ⟨Kf', th, hr', h1, hinf, h2, h3⟩
  · intro σ hσ
    have h := hT.modelW j hj σ hσ
    rw [hT.spaceW j hj σ hσ] at h
    exact h
  · intro G σ f
    have hg := Formalism.L2.Pj.goodEmb_goodOf (c := T.Q.c) σ
    have key : ∀ (W : HSp D) (h : T.V j (Formalism.L2.Pj.goodOf T.Q.c σ) = W)
        (d : GA D W → Σ k, Frame ((T.U j (Formalism.L2.Pj.goodOf T.Q.c σ)).X k).Ψ D.R.r),
        (∀ g (h' : T.V j (Formalism.L2.Pj.goodOf T.Q.c σ) = W), d g = T.dict j _ (h' ▸ g)) →
        petAt (T.U j (Formalism.L2.Pj.goodOf T.Q.c σ)) (xiR D) W d (muQ1 W) G f =
          petAt (T.U j (Formalism.L2.Pj.goodOf T.Q.c σ)) (xiR D) (T.V j _) (T.dict j _) (muQ1 _) G f := by
      intro W h
      subst h
      intro d hdd
      obtain rfl : d = _ := funext fun g => hdd g rfl
      rfl
    exact key _ (hT.spaceW j hj _ hg) _ (fun g h' => by unfold coreDict; rw [dif_pos h'])
