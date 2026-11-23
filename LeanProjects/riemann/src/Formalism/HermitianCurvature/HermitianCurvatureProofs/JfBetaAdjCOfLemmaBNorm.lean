import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactSupportFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.FormalDegreeBessel.FinalG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingExistence

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

section gen

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem cptInCC_G {F : Mat k r → E} {C : Set (Mat k r)} (hF : CkOn ⊤ (GV k r) F) (hC : IsCompact C)
    (hz : ∀ g ∈ GV k r, g ∉ C → F g = 0) (A : ℝ) (m : ℕ) : InCC A m F := by
  classical
  set F₂ : Mat k r → E := fun g => if g ∈ GV k r then F g else 0 with hF₂
  have he : ∀ g ∈ GV k r, F₂ g = F g := fun g hg => by simp [hF₂, hg]
  have hF₂c : CkOn ⊤ (GV k r) F₂ := by
    intro g₀ hg₀
    obtain ⟨U, F', hU, hgU, hc, hff⟩ := hF g₀ hg₀
    exact ⟨U, F', hU, hgU, hc, fun g hg hgG => (he g hgG).trans (hff g hg hgG)⟩
  obtain ⟨c, hc1, hc2⟩ := Formalism.FourierDecayAlt.P.compact_support_finite_class k r E F₂ C hF₂c hC (fun g hg => by
    by_cases hgG : g ∈ GV k r
    · rw [he g hgG]; exact hz g hgG hg
    · simp [hF₂, hgG]) A m
  refine ⟨c, B5.ckOn_mono le_top hF, fun u v hu hv hl g hg => ?_⟩
  have := hc2 u v hu hv hl g hg
  rwa [dLR_eq, W_congr (lr u v) (fun y hy => by
      simp only [lr, List.mem_append, List.mem_map] at hy
      rcases hy with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
      · exact (hu X hX).1
      · exact (hv X hX).1) he g hg, ← dLR_eq] at this

theorem ckOn_Rw_top {f : Mat k r → E} (h : CkOn ⊤ (GV k r) f) :
    ∀ (w : List (Mat k r)), (∀ X ∈ w, inLie k r X) → CkOn ⊤ (GV k r) (Rw w f) := by
  intro w
  induction w with
  | nil => intro _; exact h
  | cons X w ih =>
    intro hw
    show CkOn ⊤ (GV k r) (RdV X (Rw w f))
    have h1 : CkOn (⊤ + 1) (GV k r) (Rw w f) := by
      rw [top_add]; exact ih fun Y hY => hw Y (List.mem_cons_of_mem _ hY)
    exact B5.ckOn_RdV (hw X List.mem_cons_self) h1

end gen

theorem om_stable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq) :
    IsStableOpen D (Om k r D.z D.z') := by
  refine ⟨⟨Q.OmPlus k r D.z D.z', PositiveOrbitOpen.omPlus_open D.z D.z', Set.inter_comm _ _⟩, ?_⟩
  intro s hs s' hs' g hg
  refine ⟨BetaSesquilinearity.gv_mul (BetaSesquilinearity.gv_mul (BetaSesquilinearity.Sset_sub hs) hg.1) (BetaSesquilinearity.Sset_sub hs'), fun l hl => ?_, ?_⟩
  · rw [dInv k r D.z D.z' D.z_mem D.z'_mem s hs s' hs' g l]; exact hg.2.1 l hl
  · show 0 < Gf k r D.z D.z' (s * g * s')
    rw [gInv k r D.z D.z' D.z_mem D.z'_mem s hs s' hs' g]; exact hg.2.2

end Formalism.FourierDecayAlt.P.JFxG

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.JFxG

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jf_betaAdjC_of_lemmaBNorm : Formalism.FourierDecayAlt.B2.LemmaBNorm → Formalism.FourierDecayAlt.P.JFxG.BetaAdjC := by
  intro hL k r Wp Wq _ _ _ _ _ _ D Θ F F' hI hS hC hF hF' hFc hF'c
  obtain ⟨C, hCc, hCO, hCF⟩ := hFc
  obtain ⟨C', hC'c, hC'O, hC'F⟩ := hF'c
  have hL3 := (hL k r Wp Wq D (AB k r) le_rfl hI).2.2.1
  have supp : ∀ {φ : Mat k r → (Wq →L[ℂ] Wp)} {K : Set (Mat k r)}, IsCompact K → K ⊆ Om k r D.z D.z' →
      (∀ g ∈ GV k r, g ∉ K → φ g = 0) → closure {g | g ∈ GV k r ∧ φ g ≠ 0} ⊆ Om k r D.z D.z' :=
    fun hK hKO hz => (closure_minimal (fun g hg => by
      by_contra hgK
      exact hg.2 (hz g hg.1 hgK)) hK.isClosed).trans hKO
  have rwz : ∀ {φ : Mat k r → (Wq →L[ℂ] Wp)} {K : Set (Mat k r)}, IsCompact K →
      (∀ g ∈ GV k r, g ∉ K → φ g = 0) → ∀ w : List (Mat k r), (∀ X ∈ w, inLie k r X) →
        ∀ g ∈ GV k r, g ∉ K → Rw w φ g = 0 :=
    fun hK hz w hw g hg hgK => BetaSesquilinearity.Rw_vanish hK.isClosed.isOpen_compl hw (fun x hx hxK => hz x hx hxK) g hg hgK
  have hFz : ∀ g ∈ GV k r, g ∉ C → F g = 0 := fun g _ h => hCF g h
  have hF'z : ∀ g ∈ GV k r, g ∉ C' → F' g = 0 := fun g _ h => hC'F g h
  have hap : ∀ T ∈ Θ, CkOn ⊤ (GV k r) (fun x => T.coefAdj x (F' x)) ∧
      ∀ g ∈ GV k r, g ∉ C' → T.coefAdj g (F' g) = 0 := fun T hT =>
    ⟨B5.ckOn_coef (hS T hT).2 hF' (supp hC'c hC'O hF'z), fun g hg hgK => by rw [hF'z g hg hgK, map_zero]⟩
  have hrev : ∀ T ∈ Θ, ∀ X ∈ T.word.reverse, inLie k r X := fun T _ X hX => T.word_lie X (List.mem_reverse.1 hX)

  have hΘF : InCC (AB k r) 5 (opApply Θ F) := by
    show InCC _ 5 (fun g => (Θ.map fun T => T.coef g (Rw T.word F g)).sum)
    refine BetaSesquilinearity.InCC_opsum Θ (fun T g => T.coef g (Rw T.word F g)) fun T hT => ?_
    exact cptInCC_G (B5.ckOn_coef (hS T hT).1 (ckOn_Rw_top hF T.word T.word_lie)
        (supp hCc hCO (rwz hCc hFz T.word T.word_lie))) hCc
      (fun g hg hgK => by
        show T.coef g (Rw T.word F g) = 0
        rw [rwz hCc hFz T.word T.word_lie g hg hgK, map_zero]) _ 5
  have hΘF' : InCC (AB k r) 5 (opAdj Θ F') := by
    show InCC _ 5 (fun g => (Θ.map fun T =>
      ((-1 : ℂ) ^ T.word.length) • Rw T.word.reverse (fun x => T.coefAdj x (F' x)) g).sum)
    refine BetaSesquilinearity.InCC_opsum Θ (fun T g => ((-1 : ℂ) ^ T.word.length) • Rw T.word.reverse (fun x => T.coefAdj x (F' x)) g)
      fun T hT => ?_
    exact cptInCC_G (B4.ckOn_smul ((-1 : ℂ) ^ T.word.length) (ckOn_Rw_top (hap T hT).1 _ (hrev T hT))) hC'c
      (fun g hg hgK => by
        show ((-1 : ℂ) ^ T.word.length) • Rw T.word.reverse (fun x => T.coefAdj x (F' x)) g = 0
        rw [rwz hC'c (hap T hT).2 _ (hrev T hT) g hg hgK, smul_zero]) _ 5

  have hIC : IntClause D Θ F F' := by
    intro p hp T hT i j hij hj
    have hlie1 : ∀ X ∈ (T.word.take i).reverse, inLie k r X := fun X hX =>
      T.word_lie X (List.mem_of_mem_take (List.mem_reverse.mp hX))
    have hlie2 : ∀ X ∈ T.word.drop j, inLie k r X := fun X hX => T.word_lie X (List.mem_of_mem_drop hX)
    set f₁ : Mat k r → (Wq →L[ℂ] Wp) := Rw (T.word.take i).reverse (fun x => T.coefAdj x (F' x)) with hf₁
    set f₂ : Mat k r → (Wq →L[ℂ] Wp) := Rw (T.word.drop j) (rho D p F) with hf₂
    have hf₁c : CkOn ⊤ (GV k r) f₁ := ckOn_Rw_top (hap T hT).1 _ hlie1
    have hf₁z : ∀ g ∈ GV k r, g ∉ C' → f₁ g = 0 := rwz hC'c (hap T hT).2 _ hlie1
    obtain ⟨K₁, hK₁⟩ := cptInCC_G hf₁c hC'c hf₁z 0 0
    have hb₁ : ∀ g ∈ GV k r, ‖f₁ g‖ ≤ K₁ := by
      intro g hg
      have := hK₁.2 [] [] (by simp) (by simp) (by simp) g hg
      simpa [Real.rpow_zero, dLR, Rw] using this
    have hf₂c : ContinuousOn f₂ (GV k r) :=
      BetaSesquilinearity.CkOn_cont subset_rfl (B5.ckOn_mono bot_le (ckOn_Rw_top (B5.ckOn_rho D hp hF) _ hlie2))
    have hf₁cont : ContinuousOn f₁ (GV k r) := BetaSesquilinearity.CkOn_cont subset_rfl (B5.ckOn_mono bot_le hf₁c)
    obtain ⟨K₂, hK₂⟩ := (hC'c.inter_right B5.GV_closed).exists_bound_of_continuousOn (hf₂c.mono Set.inter_subset_right)
    set G : Mat k r → (Wq →L[ℂ] Wp) := fun g => ((‖f₂ g‖ : ℝ) : ℂ) • f₁ g with hG
    have hGn : ∀ g, ‖G g‖ = ‖f₁ g‖ * ‖f₂ g‖ := by
      intro g
      simp only [hG, norm_smul, Complex.norm_real, norm_norm]
      ring
    have hGc : ContinuousOn G (GV k r) := (Complex.continuous_ofReal.comp_continuousOn hf₂c.norm).smul hf₁cont
    have hGm := BetaSesquilinearity.aesm_of_continuousOn D hGc
    have hfin : D.μG (C' : Set (Mt k r)) ≠ ⊤ := (D.haarG.finite_compact C' hC'c).ne
    have hind : Integrable ((C' : Set (Mt k r)).indicator fun _ => K₁ * K₂) D.μG :=
      (integrableOn_const hfin).integrable_indicator (IsClosed.measurableSet (α := Mt k r) hC'c.isClosed)
    have hint : Integrable (fun g : Mt k r => G (Matrix.of g)) D.μG := by
      refine hind.mono' hGm ?_
      filter_upwards [B5.haar_ae D.haarG] with x hx
      by_cases hxC : x ∈ (C' : Set (Mt k r))
      · rw [Set.indicator_of_mem hxC, hGn]
        have h1 := hb₁ (Matrix.of x) hx
        have h2 := hK₂ (Matrix.of x) ⟨hxC, hx⟩
        exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
      · rw [Set.indicator_of_notMem hxC, hGn, hf₁z (Matrix.of x) hx hxC, norm_zero, zero_mul]
    exact hint.norm.congr (Filter.Eventually.of_forall fun g => hGn _)
  exact hL3 (Om k r D.z D.z') Θ (om_stable D) hS hC F F' (B5.ckOn_mono le_top hF) (B5.ckOn_mono le_top hF')
    (supp hCc hCO hFz) (supp hC'c hC'O hF'z) (cptInCC_G hF hCc hFz _ 5) (cptInCC_G hF' hC'c hF'z _ 5) hΘF hΘF' hIC

theorem jf_radAdj_of_parts2 : Formalism.FourierDecayAlt.P.JFxG.Exhaust → Formalism.FourierDecayAlt.JF.JDom → Formalism.FourierDecayAlt.P.JFxG.JThetaAdjC →
    Formalism.FourierDecayAlt.B2.LemmaBNorm → Formalism.FourierDecayAlt.JF.RadAdj := fun hE hD hA hL =>
  jf_radAdj_of_parts hE hD hA (jf_betaAdjC_of_lemmaBNorm hL)

theorem jf_radAdj_of_parts3 : Formalism.FourierDecayAlt.P.JFxG.Exhaust → Formalism.FourierDecayAlt.JF.JDom → Formalism.FourierDecayAlt.P.JFxG.JThetaAdjC →
    Formalism.FourierDecayAlt.B.XiExists → Formalism.FourierDecayAlt.JF.RadAdj := fun hE hD hA hX =>
  jf_radAdj_of_parts2 hE hD hA (Formalism.FourierDecayAlt.P.lemma_b_from_xi hX).1

end Formalism.FourierDecayAlt.P
