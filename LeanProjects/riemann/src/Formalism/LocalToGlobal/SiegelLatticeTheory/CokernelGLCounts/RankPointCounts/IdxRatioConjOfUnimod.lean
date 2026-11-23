import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ConjSecondFactor

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape Formalism.L2.SG.Pf.ProdE
  Formalism.L2.SG.Pf.ProdEP2Core Formalism.L2.SG.Pf.IndexCocycleOrbits

namespace Formalism.L2.SG.Pf.ProdEP2Cut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem idxRatio_conj_of_unimod {G : Type} [Group G] (A B : Subgroup G) (s : G) (hBA : B ≤ A) (hf : B.relIndex A ≠ 0)
    (hU : IdxRatio A (cj s A) = 1) : IdxRatio A (cj s B) = (B.relIndex A : ℝ) := by
  rw [idxCocycle G A (cj s B) (cj s A) (cj_le hBA) (by rw [relIndex_cj]; exact hf), hU, relIndex_cj, mul_one]

theorem unimod_of_sub {G : Type} [Group G] (A B' : Subgroup G) (s : G) (hAB' : A ≤ B') (hs : s ∈ B')
    (hf : A.relIndex B' ≠ 0) : IdxRatio A (cj s A) = 1 := by
  have h := idxRatio_conj_sub A A B' s le_rfl hAB' hs hf
  rw [h, Subgroup.relIndex_self, Nat.cast_one]

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) {p : PlF D}

def UnimodAt (w : Point D.host.E (D.R.rS + 1)) : Prop :=
  ∀ s ∈ StP M δ u u' w p, IdxRatio (Ag M δ u u' (p := p) w) (cj s (Ag M δ u u' (p := p) w)) = 1

theorem unimod_of_over (w : Point D.host.E (D.R.rS + 1)) (h : OverAt M δ u u' (p := p) w) : UnimodAt M δ u u' (p := p) w := by
  intro s hs
  obtain ⟨B', hAB', hsB', hf⟩ := h s hs
  exact unimod_of_sub _ B' s hAB' hsB' hf

theorem locIdx_at' (w : Point D.host.E (D.R.rS + 1)) (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D)
    (hL : IsLoUni L) (hU : IsUpUni U) (v : ℝ) (hN : CountAt M δ u u' w hA L U hL hU v)
    (hO : UnimodAt M δ u u' (p := p) w) :
    IdxRatio (AP M δ u u' w p) (CPL M δ u u' w hA L U hL hU) = v := by
  rw [idxRatio_map]
  obtain ⟨N, π, hR, hHN, hg, hBA, hfA, hv⟩ := hN
  have hC := cShape M δ u u' hA L U hL hU w
  have hCS : cj (g0 M δ hA L U hL hU) (KP M p ⊓ StabX p (XP M δ u u' w L U)) ≤ StP M δ u u' w p := by
    rw [← hC]
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  show IdxRatio (Ag M δ u u' w) (Cg M δ u u' w hA L U hL hU) = v
  rw [hC, cj_eq_cj_img hR hHN hg hCS, idxRatio_conj_of_unimod _ _ _ hBA hfA (hO _ (hR.mem _ hg)), hv]

variable (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def StepsU : Prop :=
  ∀ (γ : Formalism.L2.SG.TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D)
    (hE : Formalism.L2.SG.Pf.ZsVolCut.HypE M δ u u' F0 what₂ γ w F' L U) (p : PlF D),
    CountAt M δ u u' w (hE.1 p) L U hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2.1
      (Formalism.L2.SG.LsDatumB.wtL M δ (D.mem u).A.T (D.mem u').A.T p w
        (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * Formalism.L2.SG.LsDatumB.sgnP p)) ∧
    UnimodAt M δ u u' (p := p) w

theorem locIdxC_of_count (h : StepsU M δ u u' F0 what₂) : LocIdxC M δ u u' F0 what₂ := by
  intro γ w F' L U hE p
  obtain ⟨hN, hO⟩ := h γ w F' L U hE p
  exact locIdx_at' M δ u u' w _ L U _ _ _ hN hO

end Formalism.L2.SG.Pf.ProdEP2Cut
