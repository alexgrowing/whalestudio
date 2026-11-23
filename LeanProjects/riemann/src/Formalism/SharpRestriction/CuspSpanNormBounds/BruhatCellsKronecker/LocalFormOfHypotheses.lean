import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem frm_stdLat_isOrtho (K : Type) [Field K] [NumberField K] [StarRing K] (j : ℕ) :
    Formalism.HermitianLatticesTheory.IsOrthoLattice (Cnt.stdH K j) (stdLat K j) j := by
  classical
  refine ⟨fun i => Pi.single i (1 : K), Pi.linearIndependent_single_one (Fin j) K, ?_, rfl, ?_⟩
  · have h := (Pi.basisFun K (Fin j)).span_eq
    have e : (fun i : Fin j => Pi.single i (1 : K)) = ⇑(Pi.basisFun K (Fin j)) := by
      funext i
      simp [Pi.basisFun_apply]
    rw [e]
    exact h
  · intro a c
    simp [Cnt.stdH, LinearMap.mk₂'ₛₗ_apply, Pi.single_apply, apply_ite star, eq_comm]

theorem frm_stdH_isSymm (K : Type) [Field K] [NumberField K] [StarRing K] (j : ℕ) : (Cnt.stdH K j).IsSymm := by
  constructor
  intro x y
  simp only [Cnt.stdH, LinearMap.mk₂'ₛₗ_apply, map_sum, map_mul, starRingEnd_apply, star_star]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem formAt_of (D : D7) (u : D.what₂.Word) (hR : LocalBesselAndTopKernel.FamilyMidVolume D) (hL : UnitaryVolumeMass.stLem3L0 D u)
    (hW : ∀ τ, (dimPiU D.R.k (uS D u τ) : ℝ) = vand (uS D u τ) / ∏ i ∈ Finset.range D.R.k, (i.factorial : ℝ))
    (h3 : 3 ≤ Tu D u) (hs : SplitsE D (D.mem u).A.T) : UnitaryVolumeMass.FormAt D u := by
  intro F0 he hz what₂ hrows
  have h1 := (hL (D.mem u).A.T_prime h3 hs F0 he hz what₂ hrows).1
  have h2 := (hR (Fin D.R.k → D.host.E) (Cnt.stdH D.host.E D.R.k) (stdLat D.host.E D.R.k)
    (frm_stdH_isSymm D.host.E D.R.k)).1 (frm_stdLat_isOrtho D.host.E D.R.k) u
  have h4 : dimPi (hc := D.hcW) u =
      ∏ τ, vand (uS D u τ) / ∏ i ∈ Finset.range D.R.k, (i.factorial : ℝ) :=
    Finset.prod_congr rfl (fun τ _ => hW τ)
  rw [h1, h2, h4]
  simp only [massS, massU, Tr, Tu]
  ring

theorem three_le_Tu (D : D7) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (h : Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (u : D.what₂.Word) : 3 ≤ Tu D u := by
  obtain ⟨hH, hD, _⟩ := h
  have hg1 : ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ (D.host.g 0 : ℝ) := hH.2.2.2.2.2.2.2.2.2.2.2.1
  have hg2 : ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ (D.host.g 1 : ℝ) := hH.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmod := (hD.2.2.2.2.2.2.2.2.1 u).2
  have hk : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hb : (1 : ℝ) < large₂.sc.b := by
    unfold Scale.b Scale.L
    exact Real.one_lt_exp_iff.2 (Real.rpow_pos_of_pos (lt_trans one_pos large₂.sc.one_lt_alt) _)
  have hkb : (1 : ℝ) < ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := by
    apply one_lt_pow₀ _ (by norm_num)
    nlinarith
  have h0 : 2 ≤ D.host.g 0 := by
    have : (1 : ℝ) < (D.host.g 0 : ℝ) := lt_of_lt_of_le hkb hg1
    exact_mod_cast this
  have h1 : 2 ≤ D.host.g 1 := by
    have : (1 : ℝ) < (D.host.g 1 : ℝ) := lt_of_lt_of_le hkb hg2
    exact_mod_cast this
  have hM : 16 ≤ (D.host.g 0 * D.host.g 1) ^ 2 := by
    have : 4 ≤ D.host.g 0 * D.host.g 1 := by nlinarith
    nlinarith
  have hp := (D.mem u).A.T_prime.two_le
  unfold Tu
  by_contra hlt
  have h2 : (D.mem u).A.T = 2 := by omega
  rw [h2, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
  omega

theorem local_form_of_hypotheses (D : D7) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (h : Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (hR : LocalBesselAndTopKernel.FamilyMidVolume D) (hL : ∀ u, UnitaryVolumeMass.stLem3L0 D u)
    (hW : VanishingOnXAndXPlus.PlaneWaveIsometry D large₂ C' Cl Cg cb Cu cT CT C0) (u : D.what₂.Word) : UnitaryVolumeMass.FormAt D u :=
  formAt_of D u hR (hL u) (fun τ => hW h u τ) (three_le_Tu D large₂ h u) (h.2.1.2.2.2.2.2.2.2.2.1 u).1

section Family

variable {eps : ℝ} (Fm : FamP eps)

theorem formAt_family (Cg cb Cu cT CT C0 : ℝ) (hR : PX.RanksF Fm C0 Cg cb Cu cT CT) (hL : VanishingOnXAndXPlusMass.Conclusion3Family Fm)
    (hW : VanishingOnXAndXPlus.FamilyWeylDimensionVandermondeQuotient Fm Cg cb Cu cT CT C0) :
    OwnEv Fm fun C' Cl x i => Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 →
      ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u := by
  obtain ⟨a, ha⟩ := hR
  obtain ⟨b, hb⟩ := hW
  refine ownEv_intro Fm (max a b) (fun x hx hx1 i h u => ?_)
  exact local_form_of_hypotheses _ _ h (ha x (le_trans (le_max_left _ _) hx) i ⟨h.2.1, h.1, h.2.2⟩)
    (fun u => hL x hx1 i u) (hb x (le_trans (le_max_right _ _) hx) i) u

end Family

end Formalism.MainNotions.BridgeLemma

end
