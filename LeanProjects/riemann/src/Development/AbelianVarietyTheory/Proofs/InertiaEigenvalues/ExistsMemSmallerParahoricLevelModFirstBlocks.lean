import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksW
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelSubgroupRestrictedProductOfLaws
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmallerParahoric

open GlobalTheory.LevelProduct

theorem exists_cut {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (h : GA D V) (hS : Lev.finE V h ∈ St β)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    ∃ k : GA D V, Lev.finE V k ∈ St β ∧ ∀ PP : Pl D.host.E,
      (PP.under (𝓞 D.host.F) ∈ S → redFn β PP (Lev.finE V k) = redFn β PP (Lev.finE V h)) ∧
      (PP.under (𝓞 D.host.F) ∉ S → redFn β PP (Lev.finE V k) = 1) := by
  induction S using Finset.cons_induction_on with
  | empty =>
    refine ⟨1, ?_, fun PP => ⟨fun hh => absurd hh (Finset.notMem_empty _), fun _ => ?_⟩⟩
    · rw [MonoidHom.map_one]; exact Subgroup.one_mem _
    · rw [MonoidHom.map_one]; exact redFn_one PP
  | cons v S hv ih =>
    obtain ⟨k, hk, hr⟩ := ih
    have hc : Lev.finE V (cmp V v h) ∈ St β := by
      rw [finE_cmp]; exact piece_mem_St (phi_idem v) (phi_idem' v) hS
    have hpos : ∀ PP : Pl D.host.E, PP.under (𝓞 D.host.F) = v →
        redFn β PP (Lev.finE V (cmp V v h)) = redFn β PP (Lev.finE V h) := fun PP e => by
      rw [finE_cmp]; exact redFn_piece (phi_idem v) (phi_idem' v) hS PP (resS_phi_pos e)
    have hneg : ∀ PP : Pl D.host.E, ¬ PP.under (𝓞 D.host.F) = v →
        redFn β PP (Lev.finE V (cmp V v h)) = 1 := fun PP e => by
      rw [finE_cmp] at hc ⊢; exact redFn_piece_eq_one (phi_idem' v) hc PP (resS_phi_neg e)
    refine ⟨cmp V v h * k, ?_, fun PP => ?_⟩
    · rw [MonoidHom.map_mul]; exact Subgroup.mul_mem _ hc hk
    · rw [MonoidHom.map_mul, redFn_mul hc hk, Finset.mem_cons]
      by_cases e : PP.under (𝓞 D.host.F) = v
      · refine ⟨fun _ => ?_, fun hn => absurd (Or.inl e) hn⟩
        rw [hpos PP e, (hr PP).2 (e ▸ hv), mul_one]
      · rw [hneg PP e, one_mul]
        exact ⟨fun hh => (hr PP).1 (hh.resolve_left e), fun hh => (hr PP).2 fun h' => hh (Or.inr h')⟩

set_option maxHeartbeats 1600000 in

theorem exists_mem_smaller : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (Q' : Finset (Pl D.host.E)) (xq : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), L.Q ⊆ Q' → (∀ PP ∈ L.Pg, ∀ PP' ∈ Q', PP ≠ PP' ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP PP' ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP' PP) → ∀ g ∈ (levEnv V β L).Q, ∃ g' ∈ (levEnv V β { L with Q := Q', xq := xq }).Q, g⁻¹ * g' ∈ (levEnv V β L).J := by
  classical
  intro D V β Λ _ L Q' xq hQ hoff g hg
  obtain ⟨_, h, rfl⟩ := g
  have hh : Lev.finE V h ∈ lev D.sp.cm V.gram β (Lev.flagL L) := hg
  obtain ⟨-, hS, hP, hq⟩ := mem_parLev.1 (lev_le_parLev hh)
  obtain ⟨k, hk, hr⟩ := exists_cut V β h hS (L.Pg.image fun PP => PP.under (𝓞 D.host.F))
  have h1 : ∀ PP ∈ L.Pg, redFn β PP (Lev.finE V k) = redFn β PP (Lev.finE V h) := fun PP hPP =>
    (hr PP).1 (Finset.mem_image_of_mem _ hPP)
  have h2 : ∀ PP ∈ Q', redFn β PP (Lev.finE V k) = 1 := fun PP' hPP' => (hr PP').2 fun hm => by
    obtain ⟨PP, hPP, e⟩ := Finset.mem_image.1 hm
    obtain ⟨a, b, -⟩ := hoff PP hPP PP' hPP'
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e.symm with e' | e'
    · exact a e'.symm
    · refine b ?_
      rw [e']
      exact fun c hc => ⟨Formalism.DivisionValues.cO _ c, Ideal.mem_map_of_mem _ hc, rfl⟩
  have hS' : Lev.finE V h⁻¹ ∈ St β := by rw [MonoidHom.map_inv]; exact Subgroup.inv_mem _ hS
  have h3 : ∀ PP, redFn β PP (Lev.finE V (h⁻¹ * k)) = (redFn β PP (Lev.finE V h))⁻¹ * redFn β PP (Lev.finE V k) :=
    fun PP => by rw [MonoidHom.map_mul, redFn_mul hS' hk, MonoidHom.map_inv, redFn_inv hS]
  have A : Lev.finE V k ∈ lev D.sp.cm V.gram β (Lev.flagL { L with Q := Q', xq := xq }) := by
    refine mem_lev.2 ⟨mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA V k, hk, fun PP hPP => ?_, fun PP hPP => ?_⟩,
      Subgroup.mem_top _⟩
    · rw [h1 PP hPP]; exact hP PP hPP
    · rw [h2 PP hPP]; exact Subgroup.one_mem _
  have B : Lev.finE V (h⁻¹ * k) ∈ lev D.sp.cm V.gram β (Lev.flag1L L) := by
    refine mem_lev.2 ⟨mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA V _, ?_, fun PP hPP => ?_, fun PP hPP => ?_⟩, ?_⟩
    · rw [MonoidHom.map_mul]; exact Subgroup.mul_mem _ hS' hk
    · rw [h3, h1 PP hPP, inv_mul_cancel]; exact Subgroup.one_mem _
    · rw [h3, h2 PP (hQ hPP), mul_one]; exact Subgroup.inv_mem _ (hq PP hPP)
    · have e : rTup β (Lev.flag1L L) (Lev.finE V (h⁻¹ * k)) = 1 := by
        funext PP
        show upperLeftBlock L.hr (redFn β PP.1 (Lev.finE V (h⁻¹ * k))) = 1
        rw [h3, h1 PP.1 PP.2, inv_mul_cancel]; exact blockDiagonalExtendByOnePrimeField_one _ _
      rw [e]; exact Subgroup.one_mem _
  refine ⟨(finHom V).rangeRestrict k, A, ?_⟩
  have e : (⟨finHom V h, h, rfl⟩ : Bridge.Gf V)⁻¹ * (finHom V).rangeRestrict k = (finHom V).rangeRestrict (h⁻¹ * k) := by
    apply Subtype.ext
    exact ((MonoidHom.map_mul (finHom V) _ _).trans (congrArg (· * finHom V k) (MonoidHom.map_inv (finHom V) h))).symm
  rw [e]
  exact B

end GlobalTheory.SmallerParahoric

end
