import Formalism.SharpRestriction.LevelLetterCocycles.KillWinFromCut
import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi
import Formalism.SharpRestriction.LevelLetterCocycles.PrecompConst
import Formalism.SharpRestriction.LevelLetterCocycles.LocalInputsFromLiterature

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.InvW

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

structure LevEv (W : LocWach PD LL O v n) (a : ZMod n) (s : ℕ) where
  F : Type
  fF : Field F
  algOF : Algebra O F
  hp : ((PD.p : ℕ) : F) ≠ 0
  ev : Rs F PD.p s → LetA O n →+* F
  ev_O : ∀ ζ (x : O), ev ζ (algebraMap O (LetA O n) x) = algebraMap O F x
  ev_letE : ∀ ζ, ev ζ (letE a) = 1
  ev_ps : ∀ ζ, ev ζ (ps W s) = 0
  ev_pt : ∀ t, t ≠ s → ∀ ζ, ev ζ (ps W t) ≠ 0
  σ : W.Gam → (ZMod (PD.p ^ (s + 1)))ˣ
  ev_γ : ∀ g ζ x, ev ζ (W.γA g x) = ev (powR F PD.p s (σ g) ζ) x
  gen : Subgroup.closure (insert (σ W.gam) (σ '' (W.DelF : Set W.Gam))) = ⊤
  div : ∀ g ∈ W.AΔ, (∀ ζ, ev ζ g = 0) → ∃ (κ : ℕ) (w : LetA O n), w ∈ W.AΔ ∧
    ((PD.p : ℕ) : LetA O n) ^ κ * (letE a * g) = ps W s * w
  rat : ∀ g ∈ W.AΔ, ∀ d ∈ W.AΔ, (∀ ζ, ev ζ d ≠ 0) → ∀ c : F, (∀ ζ, ev ζ g = c * ev ζ d) →
    ∃ (κ : ℕ) (x : O), ((PD.p : ℕ) : F) ^ κ * c = algebraMap O F x

attribute [instance] LevEv.fF LevEv.algOF

theorem invLevCore_of (W : LocWach PD LL O v n) (hπ : W.π₀ ∈ W.AΔ) (hL : ∀ a s, LevEv W a s)
    (hPC : InvCut.PrecompConst) : CutU.InvLevCore W := by
  intro _hA _hp a s T e hsT f hf hγ
  obtain ⟨u, hu, hfu⟩ := hf
  obtain ⟨κ, v, hv, hfv⟩ := hγ
  let L := hL a s
  letI : Field L.F := L.fF
  letI : Algebra O L.F := L.algOF
  set D : LetA O n := ∏ t ∈ T, ps W t ^ e t with hDdef
  set U : LetA O n := letE a * 1 * u with hUdef
  have hDΔ : D ∈ W.AΔ := Subalgebra.prod_mem _ fun t _ => Subalgebra.pow_mem _ (RatW.ps_mem W hπ t) _
  have hUΔ : U ∈ W.AΔ := W.AΔ.mul_mem (W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W a) (W.AΔ.one_mem)) hu
  have hUe : letE a * U = U := by rw [hUdef, ← mul_assoc, ← mul_assoc, RatW.letE_idem]

  have hp0 : ((PD.p : ℕ) : L.F) ≠ 0 := L.hp
  have hγE' : algebraMap (LetA O n) W.EE (W.γA W.gam D) * W.γE W.gam f =
      algebraMap (LetA O n) W.EE (W.γA W.gam U) := by
    have h1 : W.γE W.gam (algebraMap (LetA O n) W.EE D * f) = W.γE W.gam (algebraMap (LetA O n) W.EE U) := by
      rw [hfu]
    rw [map_mul, W.γE_ext, W.γE_ext] at h1
    exact h1
  have hA : ((PD.p : ℕ) : LetA O n) ^ κ * (D * W.γA W.gam U - W.γA W.gam D * U) =
      W.γA W.gam D * (letE a * ps W s * v) := by
    apply W.EE_inj
    simp only [lE] at hfv
    simp only [map_mul, map_sub, map_pow, map_natCast] at hfv ⊢
    linear_combination (-(((PD.p : ℕ) : W.EE) ^ κ * algebraMap (LetA O n) W.EE D)) * hγE' +
      (((PD.p : ℕ) : W.EE) ^ κ * algebraMap (LetA O n) W.EE (W.γA W.gam D)) * hfu +
      algebraMap (LetA O n) W.EE (W.γA W.gam D) * hfv
  have hevD : ∀ ζ, L.ev ζ D ≠ 0 := fun ζ => by
    rw [hDdef, map_prod]
    exact Finset.prod_ne_zero_iff.2 fun t ht => by
      rw [map_pow]; exact pow_ne_zero _ (L.ev_pt t (fun h => hsT (h ▸ ht)) ζ)
  have hevA : ∀ ζ, L.ev ζ D * L.ev ζ (W.γA W.gam U) = L.ev ζ (W.γA W.gam D) * L.ev ζ U := fun ζ => by
    have h1 := congrArg (L.ev ζ) hA
    simp only [map_mul, map_sub, map_pow, map_natCast, L.ev_ps, mul_zero, zero_mul] at h1
    exact sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ hp0))
  let h : Rs L.F PD.p s → L.F := fun ζ => L.ev ζ U / L.ev ζ D
  have hinvΔ : ∀ δ ∈ W.DelF, ∀ ζ, h (powR L.F PD.p s (L.σ δ) ζ) = h ζ := fun δ hδ ζ => by
    simp only [h]
    rw [← L.ev_γ, ← L.ev_γ, hUΔ δ hδ, hDΔ δ hδ]
  have hinvγ : ∀ ζ, h (powR L.F PD.p s (L.σ W.gam) ζ) = h ζ := fun ζ => by
    simp only [h]
    rw [← L.ev_γ, ← L.ev_γ]
    have hγD : L.ev ζ (W.γA W.gam D) ≠ 0 := by rw [L.ev_γ]; exact hevD _
    rw [div_eq_div_iff hγD (hevD ζ)]
    linear_combination hevA ζ
  obtain ⟨c, hc⟩ := hPC L.F PD.p s _ L.gen h (by
    rintro x (rfl | ⟨δ, hδ, rfl⟩)
    · funext ζ; rw [precomp_apply]; exact hinvγ ζ
    · funext ζ; rw [precomp_apply]; exact hinvΔ δ hδ ζ)
  have hUc : ∀ ζ, L.ev ζ U = c * L.ev ζ D := fun ζ => by
    have := hc ζ
    simp only [h] at this
    rw [div_eq_iff (hevD ζ)] at this
    exact this
  obtain ⟨κ1, x, hx⟩ := L.rat U hUΔ D hDΔ hevD c hUc
  set g : LetA O n := ((PD.p : ℕ) : LetA O n) ^ κ1 * U - algebraMap O (LetA O n) x * D with hgdef
  have hgΔ : g ∈ W.AΔ := W.AΔ.sub_mem (W.AΔ.mul_mem (W.AΔ.pow_mem (W.AΔ.natCast_mem _) _) hUΔ)
    (W.AΔ.mul_mem (W.AΔ.algebraMap_mem x) hDΔ)
  have hg0 : ∀ ζ, L.ev ζ g = 0 := fun ζ => by
    rw [hgdef, map_sub, map_mul (L.ev ζ) (((PD.p : ℕ) : LetA O n) ^ κ1) U,
      map_mul (L.ev ζ) (algebraMap O (LetA O n) x) D, map_pow, map_natCast, L.ev_O, hUc ζ, ← hx]
    ring
  obtain ⟨κ2, w, hw, hgw⟩ := L.div g hgΔ hg0
  refine ⟨κ1 + κ2, ((PD.p : ℕ) : O) ^ κ2 * x, w, hw, ?_⟩
  have hlw : letE a * ps W s * w = ps W s * w := by
    calc letE a * ps W s * w = letE a * (ps W s * w) := mul_assoc _ _ _
      _ = letE a * (((PD.p : ℕ) : LetA O n) ^ κ2 * (letE a * g)) := by rw [hgw]
      _ = ((PD.p : ℕ) : LetA O n) ^ κ2 * ((letE a * letE a) * g) := by ring
      _ = ps W s * w := by rw [RatW.letE_idem, hgw]
  rw [hlw, ← hgw]
  have hO : algebraMap O W.EE (((PD.p : ℕ) : O) ^ κ2 * x) =
      algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) (((PD.p : ℕ) : O) ^ κ2 * x)) :=
    IsScalarTower.algebraMap_apply O (LetA O n) W.EE _
  rw [hO]
  simp only [lE, hgdef]
  have hUe' : letE a * (((PD.p : ℕ) : LetA O n) ^ κ1 * U - algebraMap O (LetA O n) x * D) =
      ((PD.p : ℕ) : LetA O n) ^ κ1 * U - letE a * algebraMap O (LetA O n) x * D := by
    rw [mul_sub, mul_left_comm, hUe, mul_assoc]
  rw [hUe']
  simp only [map_mul, map_sub, map_pow, map_natCast] at hfu ⊢
  linear_combination (((PD.p : ℕ) : W.EE) ^ (κ1 + κ2)) * hfu

end Core

end Formalism.MainNotions.UnusedSlot80.InvW
