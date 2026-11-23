import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InclEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexifyStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShort.SysHyp

variable {F : Type} [Field F] [NumberField F]

theorem mulW_comm (G : Geo F) (j : ℕ) (u v : Fin G.N → F) (m : G.Sec j) :
    G.mulW (j + 1) u (G.mulW j v m) = G.mulW (j + 1) v (G.mulW j u m) := by
  simp only [Geo.mulW_apply]
  refine tw_ext (isLB_tens G.K.isLB G.isLBA) G.isLB fun i c y hy hi hc => ?_
  rw [germ_mulSec _ _ _ _ _ _ _ _ _ hi hc, germ_mulSec _ _ _ _ _ _ _ _ _ hi hc,
    germ_mulSec _ _ _ _ _ _ _ _ _ hi hc, germ_mulSec _ _ _ _ _ _ _ _ _ hi hc]
  exact mul_left_comm _ _ _

theorem shift_comm (G : Geo F) (u v : Fin G.N → F) : shift G u * shift G v = shift G v * shift G u := by
  refine LinearMap.ext fun x => funext fun j => ?_
  rcases j with _ | _ | j
  · rfl
  · change G.mulW 0 u 0 = G.mulW 0 v 0
    rw [map_zero, map_zero]
  · exact mulW_comm G j u v (x j)

theorem shift_single (G : Geo F) (j : ℕ) (u : Fin G.N → F) (m : G.Sec j) :
    shift G u (Pi.single j m) = Pi.single (j + 1) (G.mulW j u m) := by
  funext l
  rcases l with _ | l
  · rw [Pi.single_eq_of_ne (Nat.succ_ne_zero j).symm]
    rfl
  · change G.mulW l u ((Pi.single j m : Tot G) l) = _
    by_cases h : l = j
    · subst h
      rw [Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne (fun e => h (Nat.succ_injective e)), map_zero]

variable (X : Data F)

theorem coe_inclEquiv (j : ℕ) (x : X.V j) :
    (inclEquiv X j x : Tot X.toGeo) = Pi.single j (x : X.Sec j) := rfl

theorem coe_eq_single (j : ℕ) (x : LinearMap.range (incl X j)) :
    (x : Tot X.toGeo) = Pi.single j ((inclEquiv X j).symm x : X.Sec j) := by
  rw [← coe_inclEquiv, LinearEquiv.apply_symm_apply]

theorem isFull (Λ₀ : ℝ) (j : ℕ) : IsFull ((sysOf X Λ₀).M j) := by
  refine ⟨(X.full j).fg.map _, ?_⟩
  change Submodule.span F ((inclEquiv X j).toLinearMap '' (X.M j : Set (X.V j))) = ⊤
  rw [← Submodule.map_span, (X.full j).span, Submodule.map_top, LinearEquiv.range]

theorem short (Λ₀ : ℝ) {j : ℕ} {Λ : ℝ} (h : X.ShortFamily j Λ) : (sysOf X Λ₀).Short j Λ := by
  obtain ⟨v, hm, hi, hn⟩ := h
  have hs : ⊤ ≤ Submodule.span F (Set.range v) :=
    (hi.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, X.latRank_M])).ge
  refine ⟨_, (Module.Basis.mk hi hs).map (inclEquiv X j), fun i => ?_⟩
  have e : (Module.Basis.mk hi hs).map (inclEquiv X j) i = inclEquiv X j (v i) := by
    rw [Module.Basis.map_apply, Module.Basis.mk_apply]
  refine e ▸ ⟨⟨v i, hm i, rfl⟩, fun σ => ?_⟩
  change (X.nm j).nrm σ ((inclEquiv X j).symm (inclEquiv X j (v i))) ≤ Λ
  rw [LinearEquiv.symm_apply_apply]
  exact hn i σ

end GlobalTheory.HSShort.SysHyp

namespace GlobalTheory.HSShort

open SysHyp

theorem GeoHyp.sysOf_hyp : ∀ (F : Type) [Field F] [NumberField F] (X : Data F) (Λ₀ : ℝ),
    GeoHyp X Λ₀ → (sysOf X Λ₀).Hyp := by
  intro F _ _ X Λ₀ h
  have := h.totallyComplex
  refine ⟨X.geom.alg.variety.one_le, X.le_T, ⟨?_, X.geom.alg.spans, X.herm, fun k σ => h.normsLe k σ, h.one_le_Lam⟩,
    shift_comm X.toGeo, fun j _ => isFull X Λ₀ j, ?_, ?_, X.one_le_beta, h.hermSysHyp_one_le_lambdaZero, X.one_le_LamD, X.one_le_LamT,
    short X Λ₀ h.short0, short X Λ₀ h.shortD, short X Λ₀ h.shortT⟩
  · obtain ⟨j, -⟩ := TopologicalSpace.Opens.mem_iSup.1 (X.geom.alg.bpf.ge (Set.mem_univ (genericPoint X.Y)))
    exact j.pos
  · rintro j hj k _ ⟨f, hf, rfl⟩
    obtain ⟨g, hg, e⟩ := h.mulStable j hj (X.w.col k) (Submodule.subset_span ⟨k, rfl⟩) f hf
    refine ⟨inclEquiv X (j + 1) g, ⟨g, hg, rfl⟩, ?_⟩
    exact ((shift_single X.toGeo j _ f).trans (congrArg (Pi.single (M := fun l => X.Sec l) (j + 1)) e.symm)).symm
  · intro σ j hj u m c f g e
    refine h.mulBound.mulBoundAt σ j hj u m c (fun i => (inclEquiv X j).symm (f i))
      (fun t => (inclEquiv X (j + 1)).symm (g t)) fun k i => ?_
    have e₁ := (coe_eq_single X (j + 1) (g (k, i))).symm.trans ((e k i).trans
      ((congrArg (shift X.toGeo (Pi.single k 1)) (coe_eq_single X j (f i))).trans (shift_single X.toGeo j _ _)))
    exact Pi.single_injective (M := fun l => X.Sec l) (j + 1) e₁

end GlobalTheory.HSShort
