import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeEmbeddingMemUnitGroup

open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine

noncomputable section

namespace GlobalTheory.RestrictNorm

theorem hasGram_comp {K V W : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] (N : (K →+* ℂ) → V → ℝ) (φ : W →ₗ[K] V) (hφ : Function.Injective φ) {n : ℕ}
    (b : Module.Basis (Fin n) K V) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hG : IsGram b X N) :
    HasGram (fun σ (x : W) => N σ (φ x)) := by
  haveI : Module.Finite K V := Module.Finite.of_basis b
  let e : W ≃ₗ[K] LinearMap.range φ := LinearEquiv.ofInjective φ hφ
  let c := Module.finBasis K (LinearMap.range φ)
  obtain ⟨Y, hY, hn⟩ := GlobalTheory.Mem.DivInhab.exists_frames_restrict b X (fun v => (hG v).1) (LinearMap.range φ) c
  refine IsGram.hasGram (b := c.map e.symm) (X := Y) fun v => ⟨hY v, fun x => ?_⟩
  have h1 : Formalism.HermitianLatticesTheory.normAt (c.map e.symm) Y v x = Formalism.HermitianLatticesTheory.normAt c Y v (e x) := by
    have hv : Formalism.HermitianLatticesTheory.vecAt (c.map e.symm) v x = Formalism.HermitianLatticesTheory.vecAt c v (e x) := by
      funext i
      simp only [Formalism.HermitianLatticesTheory.vecAt, Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm]
    unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord
    rw [hv]
  rw [h1, hn, (hG v).2]
  rfl

theorem restrict_deg : ∀ (K V : Type) [Field K] [NumberField K] [IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (W : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (N : (K →+* ℂ) → V → ℝ) (φ : W →ₗ[K] V), Function.Injective φ → HasGram N → HasGram (fun σ (x : W) => N σ (φ x)) ∧ ∀ L : Submodule (𝓞 K) W, L.FG → Formalism.HN.rkK (L.map (φ.restrictScalars (𝓞 K))) = Formalism.HN.rkK L ∧ deg N (L.map (φ.restrictScalars (𝓞 K))) = deg (fun σ (x : W) => N σ (φ x)) L := by
  intro K V _ _ _ _ _ _ _ W _ _ _ _ N φ hφ hN
  obtain ⟨⟨n, ⟨b, X⟩, hG⟩⟩ := hN
  have hN' := hasGram_comp N φ hφ b X hG
  refine ⟨hN', fun L hL => ?_⟩
  obtain ⟨⟨m, ⟨c, Y⟩, hG'⟩⟩ := hN'
  letI : StarRing K := starRingOfComm
  have hr := Formalism.HN.rerealize K W (Fin m) V (Fin n) c Y b X φ (fun v => (hG' v).1) (fun v => (hG v).1) hφ
    (fun v x => by rw [(hG v).2, (hG' v).2]) L hL
  have hrk : Formalism.HN.rkK (L.map (φ.restrictScalars (𝓞 K))) = Formalism.HN.rkK L := by
    unfold Formalism.HN.rkK
    have hs : Submodule.span K ((L.map (φ.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V) =
        (Submodule.span K (L : Set W)).map φ := by
      rw [Submodule.map_coe, ← Submodule.span_image]
      rfl
    rw [hs]
    exact (Submodule.equivMapOfInjective φ hφ _).finrank_eq.symm
  refine ⟨hrk, ?_⟩
  unfold GlobalTheory.AllWt.deg GlobalTheory.AllWt.slope
  rw [hrk, slope_sq_eq hG (hL.map _), slope_sq_eq hG' hL]
  unfold Formalism.HN.muDef
  rw [hr.2.2.1]

end GlobalTheory.RestrictNorm
