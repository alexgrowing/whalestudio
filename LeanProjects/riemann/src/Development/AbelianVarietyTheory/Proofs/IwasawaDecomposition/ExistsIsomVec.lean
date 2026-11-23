import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousActP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdSideUnique
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresBasic
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.GsdIso

open Formalism.L2.Col Formalism.IndefR.Bridge

theorem exists_isom_vec : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] (S : Formalism.L2.Col.GSD K) (ok : S.Ok) {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ι : Γ →* G) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (P : Bridge.ClassPres ι (S.toCSD ok) σ ρ J χ) (c : S.V →ₛₗ[σ] W) (d : G → S.D),
  (∀ (φ : S.EqFun) (h : G), P.extL (S.res ok φ) h = c (φ.1 (d h))) → (∃ φ : S.EqFun, φ ≠ 0) → ∃ v : S.V, c v ≠ 0 ∧ inner ℂ (c v) (c v) = σ (S.pair v v) := by
  classical
  intro K _ _ _ S ok G Γ W _ _ _ _ ι σ ρ J χ P c d H hne
  obtain ⟨φ, hφ⟩ := hne
  obtain ⟨k, hk⟩ : ∃ k, φ.1 (S.outSec.rep k) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ ((S.res ok).map_eq_zero_iff.1 (Subtype.ext (funext h)))
  set x := φ.1 (S.outSec.rep k) with hx
  have vi := (S.res ok φ).2 k
  let f : (S.toCSD ok).Forms := ⟨Pi.single k x, fun c' γ => by
    by_cases h : c' = k
    · subst h
      rw [Pi.single_eq_same]
      exact vi γ
    · rw [Pi.single_eq_of_ne h, map_zero]⟩
  have H1 := H ((S.res ok).symm f) (P.y k)
  rw [ClassPres.extL_apply, LinearEquiv.apply_symm_apply, GlobalTheory.PresBasic.ext_y] at H1
  have e2 : ((S.res ok).symm f).1 (d (P.y k)) =
      S.ρ (S.outSec.mv (d (P.y k))) ((Pi.single k x : S.Cl → S.V) (S.cls (d (P.y k)))) := rfl
  rw [e2] at H1
  have hfk : ((f : S.Cl → S.V)) k = x := by simp [f]
  rw [hfk] at H1
  have hc0 : P.coef x ≠ 0 := fun h => hk (GlobalTheory.PresBasic.coef_injective P (h.trans (map_zero _).symm))
  have hc : S.cls (d (P.y k)) = k := by
    by_contra h
    rw [Pi.single_eq_of_ne h, map_zero, map_zero] at H1
    exact hc0 H1
  rw [hc, Pi.single_eq_same] at H1
  refine ⟨S.ρ (S.outSec.mv (d (P.y k))) x, H1 ▸ hc0, ?_⟩
  rw [← H1, P.coef_pair, ok.inv]

end GlobalTheory.Mem.GsdIso
