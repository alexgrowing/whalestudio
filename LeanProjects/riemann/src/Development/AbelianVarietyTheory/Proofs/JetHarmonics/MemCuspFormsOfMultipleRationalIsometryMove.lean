import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryOfSabMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointMoveCalculus
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsUnitGramFrameBorelChange
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CabsDiagEqOne
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.UnitFramesGeneratorRatioModulusOne
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MeanFundamentalDomainEqOfPeriodic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMeanContinuity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ExponentialGrowthExclusion

noncomputable section

namespace GlobalTheory.LevelCusp.Transport

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LevelCusp
open ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity
open GlobalTheory.Dict (castFr)
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem integral_eq_zero_cast {α : Type} {Ψ Ψ' : Finset α} (h : Ψ = Ψ') {L : AddSubgroup (Ψ → ℝ)}
    {L' : AddSubgroup (Ψ' → ℝ)} [Countable L] [Countable L'] {D : Set (Ψ → ℝ)} {D' : Set (Ψ' → ℝ)}
    {g : (Ψ → ℝ) → ℂ} {g' : (Ψ' → ℝ) → ℂ} {c : ℂ}
    (hg : ∀ s, g s = c * g' (fun τ => s ⟨τ.1, h ▸ τ.2⟩))
    (hD : IsAddFundamentalDomain L D volume) (hD' : IsAddFundamentalDomain L' D' volume)
    (hf : volume D < ⊤) (hf' : volume D' < ⊤) (hp' : 0 < volume D') (hc : Continuous g)
    (hb : ∃ C : ℝ, ∀ s, ‖g s‖ ≤ C) (hL : ∀ p ∈ L, ∀ s, g (p + s) = g s)
    (hL' : ∀ p ∈ L', ∀ s, g' (p + s) = g' s) (h0 : ∫ s in D', g' s = 0) : ∫ s in D, g s = 0 := by
  subst h
  have hg' : ∀ s, g s = c * g' s := hg
  have key := GlobalTheory.mean_fundamentalDomain_eq_of_periodic Ψ L L' D D' g hD hD' hf hf' hc hb (fun p hp s => by rw [add_comm, hL p hp])
    (fun p hp s => by rw [hg', hg', add_comm, hL' p hp])
  have e : ∫ s in D', g s = 0 := by
    simp only [hg']
    rw [integral_const_mul, h0, mul_zero]
  rw [e, mul_zero] at key
  refine (mul_eq_zero.1 key.symm).resolve_left ?_
  exact_mod_cast (ENNReal.toReal_pos hp'.ne' hf'.ne).ne'

variable {X X' : Data E r} {a : GL (Fin r) E}

theorem nfac_eq (h : IsMatch X X' a) {la : Wt X.Ψ r} {la' : Wt X'.Ψ r}
    (hl : ∀ (τ : X'.Ψ) i, la' τ i = la ⟨τ.1, h.mem τ⟩ i) (x : Frame X.Ψ r) :
    X'.nfac la' (lact a (castFr h.psi x)) = X.nfac la x := by
  unfold Data.nfac
  simp only [h.dmin_eq]
  exact (GlobalTheory.Dict.Pull.cast_wt h.psi rfl hl (castFr h.psi x)).symm

theorem isIso_map (h : IsMatch X X' a) {ξ : Fin r → E} (hξ : X.IsIso ξ) :
    X'.IsIso ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) := by
  refine ⟨(h.lat ξ).1 hξ.1, by rw [h.iso, hξ.2.1], fun e => hξ.2.2 ?_⟩
  rw [← GlobalTheory.Dict.Pull.inv_mulVec a ξ, e, Matrix.mulVec_zero]

theorem map_mul_flowMat (h : IsMatch X X' a) (ξ : Fin r → E) (τ : X'.Ψ) (s : ℂ) :
    (a : Matrix (Fin r) (Fin r) E).map τ.1 * X.flowMat ξ ⟨τ.1, h.mem τ⟩ s =
      X'.flowMat ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) τ s * (a : Matrix (Fin r) (Fin r) E).map τ.1 := by
  have he : Data.emb τ.1 ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) =
      (a : Matrix (Fin r) (Fin r) E).map τ.1 *ᵥ Data.emb τ.1 ξ := by
    funext i
    simp [Data.emb, Matrix.mulVec, dotProduct]
  have hc : X'.c τ = X.c ⟨τ.1, h.mem τ⟩ := by simp only [Data.c, h.xi]
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  simp only [Matrix.toLin'_apply]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, flowMat_mulVec, flowMat_mulVec, he, h.hermC_eq, hc,
    Matrix.mulVec_add, Matrix.mulVec_smul]

theorem lact_flow (h : IsMatch X X' a) (ξ : Fin r → E) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) :
    lact a (castFr h.psi (X.flow ξ s x)) =
      X'.flow ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) (fun τ => s ⟨τ.1, h.mem τ⟩) (lact a (castFr h.psi x)) := by
  funext τ
  show (a : Matrix (Fin r) (Fin r) E).map τ.1 * (X.flowMat ξ ⟨τ.1, h.mem τ⟩ (s ⟨τ.1, h.mem τ⟩) *
      mat x ⟨τ.1, h.mem τ⟩) = X'.flowMat ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) τ (s ⟨τ.1, h.mem τ⟩) *
      ((a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x ⟨τ.1, h.mem τ⟩)
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, map_mul_flowMat h]

theorem freq_zero (X : Data E r) (la : Wt X.Ψ r) :
    ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, (0 : X.Ψ → ℝ) τ * p τ = k := fun p _ => ⟨0, by simp⟩

theorem fjI_zero (X : Data E r) (ξ : Fin r → E) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) (s : X.Ψ → ℝ) :
    fjI X ξ 0 P x s = P (X.flow ξ (cR X s) x) := by
  simp [fjI]
  rfl

theorem fj_zero_eq (X : Data E r) (la : Wt X.Ψ r) (ξ : Fin r → E) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.fj la ξ 0 P x = ((volume (ExponentialGrowthExclusion.exists_fd X la).choose).toReal : ℂ)⁻¹ *
      ∫ s in (ExponentialGrowthExclusion.exists_fd X la).choose, fjI X ξ 0 P x s := by
  rw [Data.fj, if_pos (freq_zero X la), dif_pos (ExponentialGrowthExclusion.exists_fd X la)]
  rfl

end GlobalTheory.LevelCusp.Transport

end

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

open GlobalTheory.LevelCusp.Transport ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
  ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity in

theorem GlobalTheory.LevelCusp.mem_SS_of_isMatch : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (a : GL (Fin r) E) (h : IsMatch X X' a) (la : Wt X.Ψ r) (la' : Wt X'.Ψ r), (∀ (τ : X'.Ψ) i, la' τ i = la ⟨τ.1, h.mem τ⟩ i) → ∀ (P : Frame X.Ψ r → ℂ) (Q : Frame X'.Ψ r → ℂ) (c : ℂ), X.IsSec la P → Q ∈ X'.SS la' → (∀ x ∈ X.dom, P x = c * Q (lact a (castFr h.psi x))) → P ∈ X.SS la := by
  intro E _ _ _ r X X' a h la la' hl P Q c hP hQ hPQ
  obtain ⟨⟨hQs, C, hC⟩, hQ0⟩ := hQ
  have hb : ∀ x ∈ X.dom, X.pnorm la P x ≤ ‖c‖ * C := fun x hx => by
    have := hC _ (h.mem_dom hx)
    rw [BoundedSectionAlgebra.pnorm_eq, nfac_eq h hl] at this
    rw [BoundedSectionAlgebra.pnorm_eq, hPQ x hx, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
  refine ⟨⟨hP, _, hb⟩, fun ξ hξ x hx => ?_⟩
  have hξ' := isIso_map h hξ
  have hx' := h.mem_dom hx
  have h0 := hQ0 _ hξ' _ hx'
  obtain ⟨-, hD, -, hf⟩ := (ExponentialGrowthExclusion.exists_fd X la).choose_spec
  obtain ⟨-, hD', hp', hf'⟩ := (ExponentialGrowthExclusion.exists_fd X' la').choose_spec
  rw [fj_zero_eq] at h0 ⊢
  have hne : ((MeasureTheory.volume (ExponentialGrowthExclusion.exists_fd X' la').choose).toReal : ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero (by exact_mod_cast (ENNReal.toReal_pos hp'.ne' hf'.ne).ne')
  have : Countable (X.periods la) := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  have : Countable (X'.periods la') := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  rw [integral_eq_zero_cast h.psi (c := c) (fun s => ?_) hD hD' hf hf' hp'
    (fjI_continuous X la P hP hξ.2.1 0 hx) ⟨‖c‖ * C / X.nfac la x, fun s => ?_⟩
    (fjI_periodic X la P hP hξ.1 hξ.2.1 0 (freq_zero X la) hx)
    (fjI_periodic X' la' Q hQs hξ'.1 hξ'.2.1 0 (freq_zero X' la') hx')
    ((mul_eq_zero.1 h0).resolve_left hne), mul_zero]
  · rw [fjI_zero, fjI_zero, hPQ _ (flow_real_mem_dom X hξ.2.1 s x hx), lact_flow h]
    rfl
  · have hT := hb _ (flow_real_mem_dom X hξ.2.1 s x hx)
    rw [BoundedSectionAlgebra.pnorm_eq, BoundedSectionAlgebra.nfac_flow_real X hξ.2.1] at hT
    rw [fjI_zero, le_div_iff₀ (BoundedSectionAlgebra.nfac_pos X hx la)]
    exact hT
