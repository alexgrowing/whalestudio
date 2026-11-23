import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfBetaAdjCOfLemmaBNorm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BXiAsm

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CompactSupportClassLemmas

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.JFxG

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem compact_support_in_class_general (D : RealPlaceData k r Wp Wq) (Θ : DiffOp k r Wp Wq) (hS : SmoothCoef (GPos D) Θ)
    (hC : Commutes D (GPos D) Θ) (F F' : Mat k r → (Wq →L[ℂ] Wp))
    (hF : CkOn ⊤ (GV k r) F) (hFc : HasCompactSupport F) (hFO : ∀ g ∈ tsupport F, g ∈ GV k r → g ∈ GPos D)
    (hF' : CkOn ⊤ (GV k r) F') (hF'c : HasCompactSupport F') (hF'O : ∀ g ∈ tsupport F', g ∈ GV k r → g ∈ GPos D) :
    InCC (AB k r) 5 F ∧ InCC (AB k r) 5 F' ∧ InCC (AB k r) 5 (opApply Θ F) ∧ InCC (AB k r) 5 (opAdj Θ F') ∧
      beta D (opApply Θ F) F' = beta D F (opAdj Θ F') := by
  set C : Set (Mat k r) := tsupport F with hCdef
  set C' : Set (Mat k r) := tsupport F' with hC'def
  have hCc : IsCompact C := hFc
  have hC'c : IsCompact C' := hF'c
  obtain ⟨_, _, _, _, _, hL3, _⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi k r Wp Wq D (AB k r) le_rfl
  have supp : ∀ {φ : Mat k r → (Wq →L[ℂ] Wp)} {K : Set (Mat k r)}, IsCompact K →
      (∀ g ∈ K, g ∈ GV k r → g ∈ GPos D) →
      (∀ g ∈ GV k r, g ∉ K → φ g = 0) → closure {g | g ∈ GV k r ∧ φ g ≠ 0} ⊆ GPos D :=
    by
    intro φ K hK hKO hz
    exact (closure_minimal (s := {g | g ∈ GV k r ∧ φ g ≠ 0}) (t := K ∩ GV k r) (fun g hg => by
      refine ⟨?_, hg.1⟩
      by_contra hgK
      exact hg.2 (hz g hg.1 hgK)) (hK.isClosed.inter Formalism.FourierDecayAlt.P.B5.GV_closed)).trans (fun g hg => hKO g hg.1 hg.2)
  have rwz : ∀ {φ : Mat k r → (Wq →L[ℂ] Wp)} {K : Set (Mat k r)}, IsCompact K →
      (∀ g ∈ GV k r, g ∉ K → φ g = 0) → ∀ w : List (Mat k r), (∀ X ∈ w, inLie k r X) →
        ∀ g ∈ GV k r, g ∉ K → Rw w φ g = 0 :=
    fun hK hz w hw g hg hgK => Formalism.FourierDecayAlt.P.BetaSesquilinearity.Rw_vanish hK.isClosed.isOpen_compl hw (fun x hx hxK => hz x hx hxK) g hg hgK
  have hFz : ∀ g ∈ GV k r, g ∉ C → F g = 0 := fun g _ h => image_eq_zero_of_notMem_tsupport h
  have hF'z : ∀ g ∈ GV k r, g ∉ C' → F' g = 0 := fun g _ h => image_eq_zero_of_notMem_tsupport h
  have hap : ∀ T ∈ Θ, CkOn ⊤ (GV k r) (fun x => T.coefAdj x (F' x)) ∧
      ∀ g ∈ GV k r, g ∉ C' → T.coefAdj g (F' g) = 0 := fun T hT =>
    ⟨Formalism.FourierDecayAlt.P.B5.ckOn_coef (hS T hT).2 hF' (supp hC'c hF'O hF'z), fun g hg hgK => by rw [hF'z g hg hgK, map_zero]⟩
  have hrev : ∀ T ∈ Θ, ∀ X ∈ T.word.reverse, inLie k r X := fun T _ X hX => T.word_lie X (List.mem_reverse.1 hX)
  have hΘF : InCC (AB k r) 5 (opApply Θ F) := by
    show InCC _ 5 (fun g => (Θ.map fun T => T.coef g (Rw T.word F g)).sum)
    refine Formalism.FourierDecayAlt.P.BetaSesquilinearity.InCC_opsum Θ (fun T g => T.coef g (Rw T.word F g)) fun T hT => ?_
    exact cptInCC_G (Formalism.FourierDecayAlt.P.B5.ckOn_coef (hS T hT).1 (ckOn_Rw_top hF T.word T.word_lie)
        (supp hCc hFO (rwz hCc hFz T.word T.word_lie))) hCc
      (fun g hg hgK => by
        show T.coef g (Rw T.word F g) = 0
        rw [rwz hCc hFz T.word T.word_lie g hg hgK, map_zero]) _ 5
  have hΘF' : InCC (AB k r) 5 (opAdj Θ F') := by
    show InCC _ 5 (fun g => (Θ.map fun T =>
      ((-1 : ℂ) ^ T.word.length) • Rw T.word.reverse (fun x => T.coefAdj x (F' x)) g).sum)
    refine Formalism.FourierDecayAlt.P.BetaSesquilinearity.InCC_opsum Θ
      (fun T g => ((-1 : ℂ) ^ T.word.length) • Rw T.word.reverse (fun x => T.coefAdj x (F' x)) g) fun T hT => ?_
    exact cptInCC_G (ckOn_smul ((-1 : ℂ) ^ T.word.length) (ckOn_Rw_top (hap T hT).1 _ (hrev T hT))) hC'c
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
      Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_cont subset_rfl (Formalism.FourierDecayAlt.P.B5.ckOn_mono bot_le
        (ckOn_Rw_top (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp hF) _ hlie2))
    have hf₁cont : ContinuousOn f₁ (GV k r) :=
      Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_cont subset_rfl (Formalism.FourierDecayAlt.P.B5.ckOn_mono bot_le hf₁c)
    obtain ⟨K₂, hK₂⟩ := (hC'c.inter_right Formalism.FourierDecayAlt.P.B5.GV_closed).exists_bound_of_continuousOn
      (hf₂c.mono Set.inter_subset_right)
    set G : Mat k r → (Wq →L[ℂ] Wp) := fun g => ((‖f₂ g‖ : ℝ) : ℂ) • f₁ g with hG
    have hGn : ∀ g, ‖G g‖ = ‖f₁ g‖ * ‖f₂ g‖ := by
      intro g
      simp only [hG, norm_smul, Complex.norm_real, norm_norm]
      ring
    have hGc : ContinuousOn G (GV k r) := (Complex.continuous_ofReal.comp_continuousOn hf₂c.norm).smul hf₁cont
    have hGm := Formalism.FourierDecayAlt.P.BetaSesquilinearity.aesm_of_continuousOn D hGc
    have hfin : D.μG (C' : Set (Mt k r)) ≠ ⊤ := (D.haarG.finite_compact C' hC'c).ne
    have hind : Integrable ((C' : Set (Mt k r)).indicator fun _ => K₁ * K₂) D.μG :=
      (integrableOn_const hfin).integrable_indicator (IsClosed.measurableSet (α := Mt k r) hC'c.isClosed)
    have hint : Integrable (fun g : Mt k r => G (Matrix.of g)) D.μG := by
      refine hind.mono' hGm ?_
      filter_upwards [Formalism.FourierDecayAlt.P.B5.haar_ae D.haarG] with x hx
      by_cases hxC : x ∈ (C' : Set (Mt k r))
      · rw [Set.indicator_of_mem hxC, hGn]
        have h1 := hb₁ (Matrix.of x) hx
        have h2 := hK₂ (Matrix.of x) ⟨hxC, hx⟩
        exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
      · rw [Set.indicator_of_notMem hxC, hGn, hf₁z (Matrix.of x) hx hxC, norm_zero, zero_mul]
    exact hint.norm.congr (Filter.Eventually.of_forall fun g => hGn _)
  have hIF := cptInCC_G hF hCc hFz (AB k r) 5
  have hIF' := cptInCC_G hF' hC'c hF'z (AB k r) 5
  exact ⟨hIF, hIF', hΘF, hΘF', hL3 (GPos D) Θ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gPos_stable D) hS hC F F'
    (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hF) (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hF')
    (supp hCc hFO hFz) (supp hC'c hF'O hF'z) hIF hIF' hΘF hΘF' hIC⟩

end Formalism.FourierDecayAlt.P.CompactSupportClassLemmas

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

theorem compact_support_lemma_three : CompactSupportClassMembership := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ _hB v Θ hΘ F F' hF hFc hFO hF' hF'c hF'O
  exact Formalism.FourierDecayAlt.P.CompactSupportClassLemmas.compact_support_in_class_general (T v).base Θ hΘ.1 hΘ.2 F F' hF hFc
    (fun g hg hgG => ⟨hgG, (hFO hg).1⟩) hF' hF'c (fun g hg hgG => ⟨hgG, (hF'O hg).1⟩)

end Formalism.FourierDecayAlt.P.CutMP.JA.SA

end
