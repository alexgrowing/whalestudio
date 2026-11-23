import Formalism.LocalToGlobal.ProjectiveLattices.MapRingEquivTransApply

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions MeasureTheory
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem levelK_unique {V : HSp D} {N : ℕ} {Kf Kf' : Subgroup (GA D V)} (h : IsLevelK V N Kf)
    (h' : IsLevelK V N Kf') : Kf = Kf' :=
  Subgroup.ext fun k => (h k).trans (h' k).symm

def RdUIndep (D : D7) : Prop :=
  ∀ (Q : Par D) (j : ℕ) (σ : Q.c.F →+* ℂ), GoodEmb Q.c σ →
    ∀ (U U' : Unf (Q.Xo j) Q.c σ D.R.r), IsUnf U → IsUnf U' →
    ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ sec (Q.Xo j) Q.c a n,
      (rdU U f ∈ holSub U.X (laU U a n) ↔ rdU U' f ∈ holSub U'.X (laU U' a n)) ∧
      (rdU U f ∈ holSub U.X (laU U a n) →
        supN U.X (laU U a n) (rdU U f) = supN U'.X (laU U' a n) (rdU U' f))

def L2Independence (D : D7) : Prop :=
  ∀ (Q : Par D) (j : ℕ) (U U' : ∀ σ : Q.c.F →+* ℂ, Unf (Q.Xo j) Q.c σ D.R.r),
    (∀ σ, GoodEmb Q.c σ → IsUnf (U σ)) → (∀ σ, GoodEmb Q.c σ → IsUnf (U' σ)) →
    ∀ (σ : Q.c.F →+* ℂ), GoodEmb Q.c σ → ∀ (V : HSp D), V = D.sp.W j → ∀ (Kf : Subgroup (GA D V)),
      IsLevelK V (D.host.g 0 * D.host.g 1) Kf → FinVol V →
    ∀ (dict : GA D V → Σ k, Frame ((U σ).X k).Ψ D.R.r) (dict' : GA D V → Σ k, Frame ((U' σ).X k).Ψ D.R.r)
      (mu mu' : GA D V → ℂ),
      (∃ th hr, (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif V dict Kf th hr) →
      (∃ th hr, (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif V dict' Kf th hr) →
      MuUnit V dict mu → MuUnit V dict' mu' → Continuous mu → Continuous mu' →
    ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n →
    ∀ (hl : JMemL2 V σ (rdC U σ a n) dict mu) (hl' : JMemL2 V σ (rdC U' σ a n) dict' mu')
      (f : Rul (Q.Xo j) Q.c), f ∈ cusp (Q.Xo j) Q.c U a n → f ∈ cusp (Q.Xo j) Q.c U' a n →
      l2C U σ V dict mu (xiR D) a n hl f = l2C U' σ V dict' mu' (xiR D) a n hl' f

theorem l2_independent_two_spaces (hL : L2Independence D) (Q : Par D) (j : ℕ) (U U' : ∀ σ : Q.c.F →+* ℂ, Unf (Q.Xo j) Q.c σ D.R.r)
    (hU : ∀ σ, GoodEmb Q.c σ → IsUnf (U σ)) (hU' : ∀ σ, GoodEmb Q.c σ → IsUnf (U' σ))
    (σ : Q.c.F →+* ℂ) (hσ : GoodEmb Q.c σ) (V1 V2 : HSp D) (hV1 : V1 = D.sp.W j) (hV2 : V2 = D.sp.W j)
    (Kf1 : Subgroup (GA D V1)) (Kf2 : Subgroup (GA D V2))
    (hK1 : IsLevelK V1 (D.host.g 0 * D.host.g 1) Kf1) (hK2 : IsLevelK V2 (D.host.g 0 * D.host.g 1) Kf2)
    (hF : FinVol V1)
    (dict : GA D V1 → Σ k, Frame ((U σ).X k).Ψ D.R.r) (dict' : GA D V2 → Σ k, Frame ((U' σ).X k).Ψ D.R.r)
    (mu : GA D V1 → ℂ) (mu' : GA D V2 → ℂ)
    (hd : ∃ th hr, (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif V1 dict Kf1 th hr)
    (hd' : ∃ th hr, (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif V2 dict' Kf2 th hr)
    (hm : MuUnit V1 dict mu) (hm' : MuUnit V2 dict' mu') (hc : Continuous mu) (hc' : Continuous mu')
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hdom : Dom a n)
    (hl : JMemL2 V1 σ (rdC U σ a n) dict mu) (hl' : JMemL2 V2 σ (rdC U' σ a n) dict' mu')
    (f : Rul (Q.Xo j) Q.c) (hf : f ∈ cusp (Q.Xo j) Q.c U a n) (hf' : f ∈ cusp (Q.Xo j) Q.c U' a n) :
    l2C U σ V1 dict mu (xiR D) a n hl f = l2C U' σ V2 dict' mu' (xiR D) a n hl' f := by
  subst hV1
  subst hV2
  obtain rfl := levelK_unique hK1 hK2
  exact hL Q j U U' hU hU' σ hσ _ rfl Kf1 hK1 hF dict dict' mu mu' hd hd' hm hm' hc hc' a n hdom hl hl' f hf hf'

theorem cusp_eq_of_rd (hR : RdUIndep D) (Q : Par D) (j : ℕ) (U U' : ∀ σ : Q.c.F →+* ℂ, Unf (Q.Xo j) Q.c σ D.R.r)
    (hU : ∀ σ, GoodEmb Q.c σ → IsUnf (U σ)) (hU' : ∀ σ, GoodEmb Q.c σ → IsUnf (U' σ))
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hdom : Dom a n) :
    cusp (Q.Xo j) Q.c U a n = cusp (Q.Xo j) Q.c U' a n := by
  ext f
  rw [mem_cusp, mem_cusp]
  refine and_congr_right fun hf => forall_congr' fun σ => forall_congr' fun hσ => ?_
  exact (hR Q j σ hσ (U σ) (U' σ) (hU σ hσ) (hU' σ hσ) a n hdom f hf).1

theorem cxIndep_of (hR : RdUIndep D) (hL : L2Independence D) : CxIndep D := by
  intro T U V dict mu Kf h h' j hj w
  have hU : ∀ σ, GoodEmb T.Q.c σ → IsUnf (T.U j σ) := h.unf j hj
  have hU' : ∀ σ, GoodEmb T.Q.c σ → IsUnf (U j σ) := h'.unf j hj
  have hC : T.C j w = Core.C { T with U := U, V := V, dict := dict, mu := mu, Kf := Kf } j w :=
    cusp_eq_of_rd hR T.Q j (T.U j) (U j) hU hU' (wtA w) w.n (dom_wtA w)
  refine ⟨hC, fun σ f hf => ⟨?_, ?_⟩⟩
  · have hσ := goodEmb_goodOf T.Q.c σ
    have hmem := ((mem_cusp _ _ _ _ _ f).1 hf).2 _ hσ
    have hsec := ((mem_cusp _ _ _ _ _ f).1 hf).1
    have e := (hR T.Q j _ hσ (T.U j _) (U j _) (hU _ hσ) (hU' _ hσ) (wtA w) w.n (dom_wtA w) f hsec).2 hmem
    show supC (T.Q.Xo j) T.Q.c (T.U j) (xiR D) (goodOf T.Q.c σ) (wtA w) w.n f =
      supC (T.Q.Xo j) T.Q.c (U j) (xiR D) (goodOf T.Q.c σ) (wtA w) w.n f
    unfold supC
    rw [e]
  · have hσ := goodEmb_goodOf T.Q.c σ
    have hf' : f ∈ Core.C { T with U := U, V := V, dict := dict, mu := mu, Kf := Kf } j w := hC ▸ hf
    unfold NlM
    rw [dif_pos hj, dif_pos hj]
    exact l2_independent_two_spaces hL T.Q j (T.U j) (U j) hU hU' _ hσ _ _ (h.spaceW j hj _ hσ) (h'.spaceW j hj _ hσ)
      _ _ (h.levelK j hj _ hσ) (h'.levelK j hj _ hσ) (h.finVol j hj _ hσ) _ _ _ _
      (h.dictU j hj _ hσ) (h'.dictU j hj _ hσ) (h.muUnit j hj _ hσ) (h'.muUnit j hj _ hσ)
      (h.muCont j hj _ hσ) (h'.muCont j hj _ hσ) (wtA w) w.n (dom_wtA w) _ _ f hf hf'

end Formalism.L2.Pj
