import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GenericAdmissibleFamilyOfSteps
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FibreCountOfFirstSteps

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals
open scoped ENNReal

section GenG

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}
  {Λ : Submodule (𝓞 E) S.V} {g : ℕ} {T T' : E} {F : LFlag S r T} {F' : LFlag S r T'}

theorem frame_mem_localization (F₁ : LFlag S r T) (UUm : Submodule (𝓞 E) S.V) (hX : XLam Λ F₁ ≤ UUm) (hzm : F₁.fl.z ∈ UUm)
    (hc : IsFixedConv Λ g F₁) (P : HeightOneSpectrum (𝓞 E)) (hP : (g : 𝓞 E) ∈ P.asIdeal) (b : Fin (r + 1)) :
    frame F₁ b ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal UUm) := by
  have := P.isPrime
  induction b using Fin.lastCases with
  | last => rw [a_frame_last]; exact c3eqv_le_loc _ hzm
  | cast b =>
    rw [a_frame_castSucc]
    obtain ⟨c, -, hc1, heq⟩ := hc.1 P
    have h1 : F₁.fl.e b ∈ Submodule.span (𝓞 E) (Set.range fun a => c a • F₁.fl.e a) :=
      Submodule.subset_span ⟨b, by simp [hc1 hP b]⟩
    have h2 : F₁.fl.e b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F₁) := by
      rw [heq]; exact c3eqv_le_loc _ h1
    exact c3eqv_loc_mono hX h2

end GenG

section GenG2

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}
  {Λ : Submodule (𝓞 E) S.V} {g : ℕ} {T T' : E} {F : LFlag S r T} {F' : LFlag S r T'}

theorem generic_kills_B (hg : g ≠ 0) (hz : IsLift Λ F) (hz' : IsLift Λ F') (hc : IsFixedConv Λ g F) (hc' : IsFixedConv Λ g F')
    (hgen : IsGeneric Λ g F F') : ∀ w ∈ BLat Λ F F', (g : 𝓞 E) • w ∈ UU Λ F F' := by
  intro w hw
  apply BridgeLemma.lframe_local_global
  intro P
  have := P.isPrime
  obtain ⟨ξ, hξ, hloc⟩ := hgen
  have hA : XLam Λ F ≤ UU Λ F F' := le_sup_of_le_left (le_sup_of_le_left le_sup_left)
  have hB : F.fl.z ∈ UU Λ F F' := by
    rw [← hz.2]
    exact (le_sup_of_le_left (le_sup_of_le_left le_sup_right) : Submodule.span (𝓞 E) {F.zt} ≤ UU Λ F F')
      (Submodule.mem_span_singleton_self _)
  have hC : XLam Λ F' ≤ UU Λ F F' := le_sup_of_le_left le_sup_right
  have hD : F'.fl.z ∈ UU Λ F F' := by
    rw [← hz'.2]
    exact (le_sup_right : Submodule.span (𝓞 E) {F'.zt} ≤ UU Λ F F') (Submodule.mem_span_singleton_self _)
  by_cases hP : (g : 𝓞 E) ∈ P.asIdeal
  · have h1 : w ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Mplus Λ g F F' ξ) := by
      rw [← (hloc P).1 hP]; exact c3eqv_le_loc _ hw
    obtain ⟨s, hs, hsw⟩ := BridgeLemma.lframe_mem_locP.1 h1
    have hle : Mplus Λ g F F' ξ ≤
        (Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (UU Λ F F')).comap (LinearMap.lsmul (𝓞 E) S.V (g : 𝓞 E)) := by
      refine Submodule.span_le.2 ?_
      rintro x ((hx | hx) | ⟨b, rfl⟩)
      · exact c3eqv_le_loc _ (Submodule.smul_mem _ _ (hA hx))
      · have hx' : x = F.zt := hx
        rw [hx', hz.2]
        exact c3eqv_le_loc _ (Submodule.smul_mem _ _ hB)
      · show (g : 𝓞 E) • ((g : E)⁻¹ • (frame F' b - frameAct (frame F) ξ b)) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (UU Λ F F')
        have hgE : (g : E) ≠ 0 := by exact_mod_cast hg
        have e : (g : 𝓞 E) • ((g : E)⁻¹ • (frame F' b - frameAct (frame F) ξ b)) =
            frame F' b - frameAct (frame F) ξ b := by
          rw [← algebraMap_smul E (g : 𝓞 E), map_natCast, smul_smul, mul_inv_cancel₀ hgE, one_smul]
        rw [e]
        refine Submodule.sub_mem _ (frame_mem_localization F' _ hC hD hc' P hP b) ?_
        simp only [frameAct]
        refine Submodule.sum_mem _ fun a _ => ?_
        have := Submodule.smul_mem _ (ξ a b) (frame_mem_localization F _ hA hB hc P hP a)
        rw [← algebraMap_smul E (ξ a b)] at this
        exact this
    have h2 : (g : 𝓞 E) • (s • w) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (UU Λ F F') := hle hsw
    obtain ⟨t, ht, htx⟩ := BridgeLemma.lframe_mem_locP.1 h2
    refine ⟨t * s, fun h => ?_, ?_⟩
    · rcases P.isPrime.mem_or_mem h with h | h
      · exact ht h
      · exact hs h
    · rw [mul_smul, smul_comm s (g : 𝓞 E) w]; exact htx
  · have h1 : w ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (UU Λ F F') := by
      rw [← (hloc P).2 hP]; exact c3eqv_le_loc _ hw
    obtain ⟨s, hs, hsw⟩ := BridgeLemma.lframe_mem_locP.1 h1
    exact ⟨s, hs, by rw [smul_comm]; exact Submodule.smul_mem _ _ hsw⟩

theorem generic_B_eq_bot (hg : g ≠ 0) (hz : IsLift Λ F) (hz' : IsLift Λ F') (hc : IsFixedConv Λ g F)
    (hc' : IsFixedConv Λ g F') (hgen : IsGeneric Λ g F F') : gB Λ g F F' = ⊥ := by
  unfold gB
  rw [eq_bot_iff, Submodule.smul_le]
  intro a ha q _
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [Submodule.mem_bot, mul_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem _ c (generic_kills_B hg hz hz' hc hc' hgen w.1 w.2)

end GenG2

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word)

def GenericIndexOne (C' Cl Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ →
  ∀ F' : FlagU D u', IsTermF D Λ (lf D F0) F' → IsGeneric Λ (gS D) (lf D F0) F' →
    La Λ (gS D) (lf D F0) F' ≤ Thp Λ (lf D F0) F'

theorem generic_index_one (C' Cl Cg cb Cu cT CT C0 A : ℝ) : GenericIndexOne D large₂ u u' C' Cl Cg cb Cu cT CT C0 A := by
  intro hH F0 _ _ Λ hΛr F' hT' hgen x hx
  have hSt : Cnt.Stand D u u' := hH.2.1
  have hPr := Formalism.MainNotions.VanishingOnXAndXPlus.primeHyp_of_stand D u u' hSt
  have hF : FixedHyp D Λ (lf D F0) := hΛr.2.1
  have hg : gS D ≠ 0 := by
    unfold gS
    exact Nat.mul_ne_zero hSt.2.2.2.2.2.2.2.1.ne_zero hSt.2.2.2.2.2.2.2.2.1.ne_zero
  obtain ⟨_, _, _, _, φ, hφ, _⟩ := lemma_one_section D u (Tu D u') Λ (lf D F0) F' hF hPr hT'.1
  have hbot := generic_B_eq_bot hg hF.2.2.1 hT'.1.1 hF.2.2.2 hT'.2.1 hgen
  have h0 : φ (Submodule.Quotient.mk ⟨x, hx⟩) = φ 0 := by
    apply Subtype.ext
    have hall : ∀ y : gB Λ (gS D) (lf D F0) F', (y : BQ Λ (lf D F0) F') = 0 := fun y =>
      (Submodule.mem_bot (𝓞 D.host.E)).1 (hbot.le y.2)
    rw [hall, hall]
  have h3 := hφ h0
  rw [Submodule.Quotient.mk_eq_zero] at h3
  exact h3

end Gen

end Formalism.MainNotions.BridgeLemma₂

end
