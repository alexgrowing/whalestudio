import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLevChiFlagLEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarMapMulRightOfMemCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityInnerProductUnitTwistedRightTranslatStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLiftsStatement

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem finiteGroup_acts_unitarily_hilbertMultiplicityModel : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S), ∀ (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) J χ, ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (e : H →ₗ[ℂ] MMap M) (d : ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), (∀ x y, inner ℂ x y = d * ipM M μ 𝓕 (e x) (e y)) → Function.Injective e → (∀ x, e x ∈ Mult θ M J χ) → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → ∀ (g0 : G0 L.Pg L.r) (u : H ≃ₗ[ℂ] H), (∀ x v, e (u x) v = actG0 V β L g0 (e x v)) → ∀ x, ‖u x‖ = ‖x‖ := by
  intro D V S θ M β L J χ H _ _ e d μ 𝓕 hin hinj hmem hμ h𝓕 g0 u hact x
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hμ

  have hchoose : ∀ (P Q : ℂ → Prop) (hP : ∃ c, P c) (hQ : ∃ c, Q c), P = Q → hP.choose = hQ.choose := by
    rintro P Q hP hQ rfl; rfl
  have hip : ipM M μ 𝓕 (e (u x)) (e (u x)) = ipM M μ 𝓕 (e x) (e x) := by
    by_cases hk : ∃ κ, IsLevelLift V β L g0 κ
    · obtain ⟨hcpt, hlift⟩ := GlobalTheory.T.isCompact_parahoricLevel_and_contains_lifts V β L
      have hκ : hk.choose ∈ levG V β (flagL L) := hlift g0 _ hk.choose_spec
      have hκi : hk.choose⁻¹ ∈ levG V β (flagL L) := inv_mem hκ
      set a : ℂ := (levChi V β (flagL L) hk.choose)⁻¹ with ha_def
      have ha : ‖a‖ = 1 := by rw [ha_def, norm_inv, GlobalTheory.norm_levChi_flagL_eq_one V β L _ hκ, inv_one]
      have ha0 : a ≠ 0 := by intro h; rw [h, norm_zero] at ha; exact zero_ne_one ha
      have hai : ‖a⁻¹‖ = 1 := by rw [norm_inv, ha, inv_one]
      have hU : ∀ v g, e (u x) v g = a * e x v (g * hk.choose) := by
        intro v g
        rw [hact x v]
        simp only [actG0, dif_pos hk, ha_def]
      have hV : ∀ v g, e x v g = a⁻¹ * e (u x) v (g * hk.choose⁻¹) := by
        intro v g
        rw [hU, mul_assoc g, inv_mul_cancel, mul_one, ← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
      have hm1 := GlobalTheory.haar_map_mul_right_of_mem_compact_subgroup μ _ hcpt _ hκ
      have hm2 := GlobalTheory.haar_map_mul_right_of_mem_compact_subgroup μ _ hcpt _ hκi
      have hiff : ∀ c, IsMultIP M μ 𝓕 (e (u x)) (e (u x)) c ↔ IsMultIP M μ 𝓕 (e x) (e x) c := by
        intro c
        constructor
        · intro hc
          exact GlobalTheory.T.multiplicityInnerProduct_unit_twisted_right_translation θ M J χ μ 𝓕 hμ h𝓕 _ _ hai hm2 _ (hmem (u x)) _ (hmem (u x)) _ _ hV hV c hc
        · intro hc
          exact GlobalTheory.T.multiplicityInnerProduct_unit_twisted_right_translation θ M J χ μ 𝓕 hμ h𝓕 _ _ ha hm1 _ (hmem x) _ (hmem x) _ _ hU hU c hc
      unfold ipM
      split_ifs with h1 h2 h2
      · exact hchoose _ _ h1 h2 (funext fun c => propext (hiff c))
      · exact absurd (let ⟨c, hc⟩ := h1; ⟨c, (hiff c).1 hc⟩) h2
      · exact absurd (let ⟨c, hc⟩ := h2; ⟨c, (hiff c).2 hc⟩) h1
      · rfl
    ·
      have h0 : e (u x) = 0 := by
        ext v g
        rw [hact x v]
        simp only [actG0, dif_neg hk]
        rfl
      have hux : u x = 0 := hinj (by rw [h0, map_zero])
      have hx : x = 0 := by
        have := congrArg u.symm hux
        simpa using this
      rw [hux, hx]
  have hsq' : ‖u x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), hin, hin, hip]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq'

end GlobalTheory
