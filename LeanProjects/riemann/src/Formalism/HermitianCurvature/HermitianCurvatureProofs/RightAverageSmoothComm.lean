import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableCsmul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DegLiftOfParts

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.ChartIntegralLocal Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section local_

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem foldT_congr_open {U : Set (Mat k r)} (hU : IsOpen U) :
    ∀ (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) {f₁ f₂ : Mat k r → E},
      (∀ x ∈ U, x ∈ GV k r → f₁ x = f₂ x) →
      ∀ x ∈ U, x ∈ GV k r → Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.foldT ts f₁ x = Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.foldT ts f₂ x
  | [], _, _, h => h
  | t :: ts, f₁, f₂, h => by
    intro x hx hxG
    have ih := foldT_congr_open hU ts h
    show Top (Q.EH k r) t.1 t.2.1 t.2.2 (Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.foldT ts f₁) x =
      Top (Q.EH k r) t.1 t.2.1 t.2.2 (Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.foldT ts f₂) x
    rw [Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.top_apply', Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.top_apply', Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.EH_apply,
      Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.EH_apply, ih x hx hxG,
      Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.rdV_congr hU hx hxG (Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Xa_unit _ _).1 ih,
      Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.rdV_congr hU hx hxG (Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Xb_unit _ _).1 ih]

theorem AA_congr_open {U : Set (Mat k r)} (hU : IsOpen U) {f₁ f₂ : Mat k r → E}
    (h : ∀ x ∈ U, x ∈ GV k r → f₁ x = f₂ x) (m : ℕ) (hm : m ≤ r) (u ell : ℂ) {x : Mat k r} (hx : x ∈ U)
    (hxG : x ∈ GV k r) :
    C3.AAop k r m hm u f₁ x = C3.AAop k r m hm u f₂ x ∧ C3.AAvop k r m hm ell f₁ x = C3.AAvop k r m hm ell f₂ x := by
  refine ⟨?_, ?_⟩
  · simp only [C3.AAop]
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · rw [qminor_foldT, qminor_foldT]
      congr 1
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [foldT_congr_open hU _ h x hx hxG]
    · rfl
  · simp only [C3.AAvop]
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · rw [qminor_foldT, qminor_foldT]
      congr 1
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [foldT_congr_open hU _ h x hx hxG]
    · rfl

end local_

section hyp

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem kr_smul (Bs : RealPlaceData k r Wp Wq) (a : Mat k r → ℂ) (G : Mat k r → (Wq →L[ℂ] Wp)) (y : Mat k r)
    (ha : ∀ ξ, InR Bs ξ → a (y * Matrix.of ξ.2 * Matrix.of ξ.1) = a y) :
    Kr Bs (fun g => a g • G g) y = a y • Kr Bs G y := by
  rw [kr_eq, kr_eq, ← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [ae_inR Bs] with ξ hξ
  simp only [rho_pR, ha ξ hξ, ContinuousLinearMap.smul_comp]
  rw [smul_comm]

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem kr_zero (Bs : RealPlaceData k r Wp Wq) (y : Mat k r) : Kr Bs (fun _ => (0 : Wq →L[ℂ] Wp)) y = 0 := by
  simp [Kr]

theorem kr_AA_loc (Bs : RealPlaceData k r Wp Wq) (l : Fin (r + 2)) {H : Mat k r → (Wq →L[ℂ] Wp)}
    (hH : ∀ g ∈ GV k r, Dmin k r Bs.z Bs.z' g l ≠ 0 → Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc ⊤ H g)
    {C : Set (Mat k r)} (hC : IsCompact C) (hz : ∀ g ∈ GV k r, g ∉ C → H g = 0) (m : ℕ) (hm : m ≤ r) (u ell : ℂ)
    {y : Mat k r} (hy : y ∈ GV k r) (hD : Dmin k r Bs.z Bs.z' y l ≠ 0) :
    Kr Bs (C3.AAop k r m hm u H) y = C3.AAop k r m hm u (Kr Bs H) y ∧
      Kr Bs (C3.AAvop k r m hm ell H) y = C3.AAvop k r m hm ell (Kr Bs H) y := by
  set c₀ := Dmin k r Bs.z Bs.z' y l with hc₀
  have hc0 : 0 < ‖c₀‖ := norm_pos_iff.mpr hD
  obtain ⟨χD, ⟨hχs, -, -⟩, hχ1, hχsupp⟩ := Formalism.FourierDecayAlt.P.JCTx6.Pos.bump_exists hD
  have hDc : Continuous (fun g : Mat k r => Dmin k r Bs.z Bs.z' g l) :=
    (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin Bs.z Bs.z' l).continuous
  set Ht : Mat k r → (Wq →L[ℂ] Wp) := fun g => χD (Dmin k r Bs.z Bs.z' g l) • H g with hHtdef
  have hHt : CkOn ⊤ (GV k r) Ht := by
    intro g0 hg0
    by_cases hmem : Dmin k r Bs.z Bs.z' g0 l ∈ tsupport χD
    · have hne : Dmin k r Bs.z Bs.z' g0 l ≠ 0 := by
        intro h0
        have := (hχsupp _ hmem).1
        rw [h0, norm_zero] at this
        linarith
      obtain ⟨U, f', hU, hgU, hf', he⟩ := hH g0 hg0 hne
      refine ⟨U, fun g => χD (Dmin k r Bs.z Bs.z' g l) • f' g, hU, hgU, ?_, fun g hg hgG => ?_⟩
      · exact ((hχs.comp (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin Bs.z Bs.z' l)).contDiffOn).smul hf'
      · show χD (Dmin k r Bs.z Bs.z' g l) • H g = χD (Dmin k r Bs.z Bs.z' g l) • f' g
        rw [he g hg hgG]
    · refine ⟨(fun g => Dmin k r Bs.z Bs.z' g l) ⁻¹' (tsupport χD)ᶜ, fun _ => 0,
        (isClosed_tsupport χD).isOpen_compl.preimage hDc, hmem, contDiffOn_const, fun g hg _ => ?_⟩
      show χD (Dmin k r Bs.z Bs.z' g l) • H g = 0
      rw [image_eq_zero_of_notMem_tsupport hg, zero_smul]
  have hzt : ∀ g ∈ GV k r, g ∉ C → Ht g = 0 := fun g hg hgC => by
    show χD (Dmin k r Bs.z Bs.z' g l) • H g = 0
    rw [hz g hg hgC, smul_zero]
  set V := {x : Mat k r | dist (Dmin k r Bs.z Bs.z' x l) c₀ < ‖c₀‖ / 4} with hV
  have hVo : IsOpen V := isOpen_lt (hDc.dist continuous_const) continuous_const
  have hyV : y ∈ V := by show dist c₀ c₀ < ‖c₀‖ / 4; rw [dist_self]; positivity
  have hHV : ∀ x ∈ V, x ∈ GV k r → H x = Ht x := by
    intro x hx _
    show H x = χD (Dmin k r Bs.z Bs.z' x l) • H x
    rw [hχ1 _ (le_of_lt hx), one_smul]
  have hKV : ∀ x ∈ V, x ∈ GV k r → Kr Bs H x = Kr Bs Ht x := by
    intro x hx _
    rw [kr_eq, kr_eq]
    refine integral_congr_ae ?_
    filter_upwards [ae_inR Bs] with ξ hξ
    simp only [rho_pR, hHtdef, dmin_pR Bs hξ x l]
    rw [hχ1 _ (le_of_lt hx), one_smul]
  have hqV : ∀ ξ, InR Bs ξ → y * Matrix.of ξ.2 * Matrix.of ξ.1 ∈ V := by
    intro ξ hξ
    show dist (Dmin k r Bs.z Bs.z' (y * Matrix.of ξ.2 * Matrix.of ξ.1) l) c₀ < ‖c₀‖ / 4
    rw [dmin_pR Bs hξ y l, dist_self]; positivity
  have hqG : ∀ ξ, InR Bs ξ → y * Matrix.of ξ.2 * Matrix.of ξ.1 ∈ GV k r := fun ξ hξ =>
    Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hy hξ.2.1) hξ.1.1
  obtain ⟨hA, hAv⟩ := kr_AA_cpt Bs hHt hC hzt m hm u ell hy
  refine ⟨?_, ?_⟩
  · have e1 : Kr Bs (C3.AAop k r m hm u H) y = Kr Bs (C3.AAop k r m hm u Ht) y := by
      rw [kr_eq, kr_eq]
      refine integral_congr_ae ?_
      filter_upwards [ae_inR Bs] with ξ hξ
      simp only [rho_pR]
      rw [(AA_congr_open hVo hHV m hm u ell (hqV ξ hξ) (hqG ξ hξ)).1]
    rw [e1, hA, (AA_congr_open hVo hKV m hm u ell hyV hy).1]
  · have e1 : Kr Bs (C3.AAvop k r m hm ell H) y = Kr Bs (C3.AAvop k r m hm ell Ht) y := by
      rw [kr_eq, kr_eq]
      refine integral_congr_ae ?_
      filter_upwards [ae_inR Bs] with ξ hξ
      simp only [rho_pR]
      rw [(AA_congr_open hVo hHV m hm u ell (hqV ξ hξ) (hqG ξ hξ)).2]
    rw [e1, hAv, (AA_congr_open hVo hKV m hm u ell hyV hy).2]

end hyp

theorem right_average_smooth_comm : KrHyp := by
  intro k r Wp Wq _ _ _ _ _ _ Bs j hj H hH hRb y hy hD
  obtain ⟨R, hR⟩ := hRb
  have hC := Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k r R
  have hz : ∀ g ∈ B.GV k r, g ∉ {g : B.Mat k r | B.gN g ≤ R} → H g = 0 := by
    intro g hg hgC
    by_contra h
    exact hgC (hR g hg h)
  refine ⟨kr_loc Bs ⟨j, by omega⟩ hH hC hz y hy hD, fun le e => ?_⟩
  by_cases h0 : e = 1 ∧ j = 0
  · have e1 : D.vLet k r Bs.z Bs.z' j hj le e H = fun _ => 0 := by
      funext g; simp [D.vLet, h0]
    rw [e1, kr_zero]
    simp [D.vLet, h0]
  · have hm : j - e ≤ r := by omega
    obtain ⟨hA, hAv⟩ := kr_AA_loc Bs ⟨j, by omega⟩ hH hC hz (j - e) hm ((le.2 : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2)
      ((le.2 : ℂ) - ((2 * r + k : ℕ) : ℂ) / 2) hy hD
    rcases le with ⟨b, Y⟩
    cases b
    · have e1 : D.vLet k r Bs.z Bs.z' j hj (false, Y) e H = fun g =>
          (conj (Dmin k r Bs.z Bs.z' g ⟨j, by omega⟩))⁻¹ •
            C3.AAvop k r (j - e) hm ((Y : ℂ) - ((2 * r + k : ℕ) : ℂ) / 2) H g := by
        funext g; simp [D.vLet, h0]
      rw [e1, kr_smul Bs _ _ y (fun ξ hξ => by rw [dmin_pR Bs hξ y]), hAv]
      simp [D.vLet, h0]
    · have e1 : D.vLet k r Bs.z Bs.z' j hj (true, Y) e H = fun g =>
          (Dmin k r Bs.z Bs.z' g ⟨j, by omega⟩)⁻¹ •
            C3.AAop k r (j - e) hm ((Y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) H g := by
        funext g; simp [D.vLet, h0]
      rw [e1, kr_smul Bs _ _ y (fun ξ hξ => by rw [dmin_pR Bs hξ y]), hA]
      simp [D.vLet, h0]

end Formalism.FourierDecayAlt.P.PBG
