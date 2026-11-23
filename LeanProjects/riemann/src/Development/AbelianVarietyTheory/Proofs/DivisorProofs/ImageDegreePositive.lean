import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralProjectiveClosureOfLinearSystemPoi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatProjectiveModelOverRingOfIntegersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalArithmeticVarietyModelProjectiveSpacStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackCoordinateCombinationRatioAndVanishStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyCoordinateCombinationsNoCommonZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjugateEmbeddingEqConjMulUnitaryStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

namespace GlobalTheory.ImageModel

theorem exists_isModelOf : Hypotheses2 → ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ), (∀ σ : K →+* ℂ, (starRingEnd ℂ).comp σ ≠ σ) → HasGram Nm → (∀ σ x, Nm ((starRingEnd ℂ).comp σ) x = Nm σ x) → W.FG → Submodule.span K (W : Set V) = ⊤ → GlobalTheory.DegVal.GenRatios ev → 0 < imageDeg ev D → ∃ (X : AlgebraicGeometry.Scheme.{0}) (_ : AlgebraicGeometry.IsIntegral X) (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s := by
  intro _ K V Ω _ _ _ _ _ _ _ _ Nm W ev D hK hG hcj hW hs hR hD
  classical
  obtain ⟨N, n, b, w, A, hF⟩ := GlobalTheory.CompHt.exists_isFrame hK hcj hG hW hs
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    rcases n with _ | m
    · exfalso
      have hW0 : W = ⊥ := by rw [← hF.span]; simp
      have htop : (⊤ : Submodule K V) = ⊥ := by rw [← hs, hW0]; simp
      refine hR.1 (LinearMap.ext fun x => ?_)
      have hx : x ∈ (⊥ : Submodule K V) := htop ▸ Submodule.mem_top
      rw [Submodule.mem_bot] at hx
      simp [hx]
    · exact ⟨m, rfl⟩
  set u : Fin (m + 1) → V := fun k => ∑ j, w j k • b j with hu_def
  have huW : ∀ k, u k ∈ W := fun k => hF.span ▸ Submodule.subset_span ⟨k, rfl⟩
  let gw : Fin (m + 1) → W := fun k => ⟨u k, huW k⟩
  have hspan : Submodule.span K (Set.range u) = ⊤ := by
    rw [← hs, ← hF.span, Submodule.span_span_of_tower]
  choose cc hcc using fun j => (Submodule.mem_span_range_iff_exists_fun K).1
    (hspan ▸ Submodule.mem_top : b j ∈ Submodule.span K (Set.range u))
  let c : Matrix (Fin (m + 1)) (Fin N) K := Matrix.of fun k j => cc j k
  set y : Fin (m + 1) → Ω := fun k => ev (u k) with hy_def
  have hy0 : y ≠ 0 := fun h0 => hR.1 (LinearMap.ext_on_range hspan fun k => by
    simpa using congrFun h0 k)
  obtain ⟨Y, _, q, B₀, hB₀, t, ψ₀, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.exists_integral_projective_closure_of_linearSystem_point K V Ω ev D m u hspan hR hD
  obtain ⟨X₀, _, p₀, g₀, ψ₁, e⟩ := GlobalTheory.T.exists_flat_projective_model_over_ringOfIntegers K Ω D m y Y q B₀ hB₀ t ψ₀ h1 h2 h3 h4 h5 h6
  obtain ⟨X, _, p, g, ψ, hgp, har, hnorm, hbij, hbase, hrat⟩ := GlobalTheory.T.exists_normal_arithmeticVariety_model_projectiveSpace K Ω D m y X₀ p₀ g₀ ψ₁ e
  let B := (ProjSpace.O1 (𝓞 K) m).pull g
  have hB : B.IsLB := LB.isLB_pull (ProjSpace.O1_isLB _ m) g
  let sk : Fin (m + 1) → B.Sec := fun k => secPull (ProjSpace.coord (𝓞 K) m k) g
  obtain ⟨hlin, hrel⟩ := GlobalTheory.T.pulledBack_coordinate_combination_ratio_and_vanish K Ω m y X p g ψ hbase hrat
  have hev : ∀ lam : Fin (m + 1) → 𝓞 K, ev (∑ k, lam k • u k) = ∑ k, algebraMap K Ω (lam k : K) * y k := by
    intro lam
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← algebraMap_smul K (lam k) (u k), LinearMap.map_smul, Algebra.smul_def]
  have hrelV : ∀ lam : Fin (m + 1) → 𝓞 K, ∑ k, lam k • u k = 0 → ∑ k, algX p ⊤ (lam k) • sk k = 0 :=
    fun lam h0 => hrel hy0 lam (by rw [← hev, h0, map_zero])
  choose coef hcoef using fun x : W => (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1
    (hF.span.symm ▸ x.2 : (x : V) ∈ Submodule.span (𝓞 K) (Set.range u))
  let s : W → B.Sec := fun x => ∑ k, algX p ⊤ (coef x k) • sk k
  have sg : ∀ k, s (gw k) = sk k := by
    intro k
    have e1 : ∑ l, (Pi.single k (1 : 𝓞 K) : Fin (m + 1) → 𝓞 K) l • u l = u k := by
      rw [Finset.sum_eq_single k (fun l _ hl => by rw [Pi.single_eq_of_ne hl, zero_smul]) (by simp)]
      rw [Pi.single_eq_same, one_smul]
    have e3 : ∑ l, algX p ⊤ ((Pi.single k (1 : 𝓞 K) : Fin (m + 1) → 𝓞 K) l) • sk l = sk k := by
      rw [Finset.sum_eq_single k (fun l _ hl => by rw [Pi.single_eq_of_ne hl, map_zero, zero_smul]) (by simp)]
      rw [Pi.single_eq_same, map_one, one_smul]
    have h0 := hrelV (coef (gw k) - Pi.single k 1) (by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, hcoef, e1]
      exact sub_eq_zero.2 (hcoef (gw k)))
    simp only [Pi.sub_apply, map_sub, sub_smul, Finset.sum_sub_distrib, e3, sub_eq_zero] at h0
    exact h0
  have hbpf : ⨆ k, nonzeroLocus (sk k) = ⊤ :=
    ProjSpace.iSup_nonzeroLocus_secPull (ProjSpace.iSup_nonzeroLocus_coord (𝓞 K) m) g
  let A' : (𝓞 K →+* ℂ) → Matrix (Fin (m + 1)) (Fin N) ℂ := fun τ =>
    c.map (OfLattice.extEmb τ) * A (OfLattice.extEmb τ)
  have hnz := GlobalTheory.T.fubiniStudy_coordinate_combinations_noCommonZero K V m N X p g u b c A hgp hrelV (fun j => (hcc j).symm) hF.herm
  have hcU : ∀ τ : 𝓞 K →+* ℂ, ∃ U ∈ Matrix.unitaryGroup (Fin N) ℂ,
      A' ((starRingEnd ℂ).comp τ) = (A' τ).map (starRingEnd ℂ) * U := by
    intro τ
    obtain ⟨U, hU, eU⟩ := GlobalTheory.T.frame_conjugate_embedding_eq_conj_mul_unitary K N A hF.conj hF.herm (OfLattice.extEmb τ)
    have he : OfLattice.extEmb ((starRingEnd ℂ).comp τ) = (starRingEnd ℂ).comp (OfLattice.extEmb τ) :=
      OfLattice.extEmb_eq (by rw [RingHom.comp_assoc, OfLattice.extEmb_comp])
    refine ⟨U, hU, ?_⟩
    simp only [A', he, eU, Matrix.map_mul, Matrix.map_map, Matrix.mul_assoc]
    rfl
  let L : HermLB p := OfLattice.combHerm hB sk A' hnz hcU
  refine ⟨X, inferInstance, p, L, ψ, s, har, hnorm, hbij, hbase, ?_, ?_, ?_⟩
  · obtain ⟨k₀, hk₀⟩ : ∃ k, y k ≠ 0 := by
      by_contra! h; exact hy0 (funext h)
    intro x x' i h
    have hψ : ψ (y k₀) ≠ 0 := (map_ne_zero ψ).2 hk₀
    have ha : ψ (y k₀) * fnOf _ h ((s x).f i) = ψ (ev x) * fnOf _ h ((sk k₀).f i) := by
      have := hlin (coef x) k₀ i h
      rwa [← hev, hcoef] at this
    have hb : ψ (y k₀) * fnOf _ h ((s x').f i) = ψ (ev x') * fnOf _ h ((sk k₀).f i) := by
      have := hlin (coef x') k₀ i h
      rwa [← hev, hcoef] at this
    refine mul_left_cancel₀ hψ ?_
    linear_combination (ψ (ev x)) * hb - (ψ (ev x')) * ha
  · refine top_le_iff.1 ?_
    rw [← hbpf]
    exact iSup_le fun k => by
      rw [← sg k]
      exact le_iSup (fun x => nonzeroLocus (s x)) (gw k)
  · refine ⟨N, m + 1, b, w, A, c, gw, hF, fun k => rfl, fun j => (hcc j).symm, fun σ i z => ?_⟩
    have he : OfLattice.extEmb (σ.comp (algebraMap (𝓞 K) K)) = σ := OfLattice.extEmb_eq rfl
    refine (OfLattice.combWeight_φ hB sk _ (hnz _) i z).trans ?_
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sg k]
    simp only [A', he, Matrix.mul_apply, Matrix.map_apply, c, Matrix.of_apply]
    rfl

end GlobalTheory.ImageModel
