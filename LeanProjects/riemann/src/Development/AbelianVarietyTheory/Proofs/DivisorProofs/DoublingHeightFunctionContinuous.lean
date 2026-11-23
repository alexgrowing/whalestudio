import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingEmbeddingStabilizers
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot GlobalTheory.ThK.ConeEuler

noncomputable section

namespace GlobalTheory.DblHeightHerm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def Conv {A : Type} [CommRing A] [TopologicalSpace A] {n : ℕ} (H : Subgroup (GL (Fin n) A))
    (G : Subgroup (GL (Fin (n + n)) A)) (ν : Aˣ →* ℝ≥0) (S : Set (GL (Fin (n + n)) A)) : Prop :=
  ∀ i : H × H →* G, (∀ h h', (i (h, h')).1.1 = blkMat finSumFinEquiv h.1.1 h'.1.1) →
    ∀ K : Subgroup G, (∀ g, g ∈ K ↔ g.1 ∈ S) → IwasawaOf finSumFinEquiv G.subtype ν K →
    Continuous (fun g : H => hgtOf finSumFinEquiv G.subtype ν K (i (g, 1))) ∧
    ∃ R : ℝ, ∀ μ : @Measure H (borel H), @Measure.IsHaarMeasure H _ _ (borel H) μ → ∀ t : ℝ, R < t →
      @Integrable _ _ _ _ (borel H) (fun g => ((hgtOf finSumFinEquiv G.subtype ν K (i (g, 1)) : ℝ≥0) : ℝ) ^ t) μ

theorem conv_adelic (hcm : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J)
    {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} (hQ : Q = dblGram finSumFinEquiv J)
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] {a : GL (Fin n) (AF F ⊗[F] E)}
    (ha : IsMajorantFrame σ J a) :
    Conv (HR (AF F) σ J) (HR (AF F) σ Q) (absE F E) ((KAd σ Q L a).map (matHom (AF F) σ Q)) := by
  intro i hi K hK hI
  obtain rfl : K = KAd σ Q L a := Subgroup.ext fun g =>
    (hK g).trans (Subgroup.mem_map_iff_mem (matHom_injective (AF F) σ Q))
  obtain rfl : i = ioH (AF F) σ hQ := MonoidHom.ext fun x => Subtype.ext (Units.ext (hi x.1 x.2))
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := t2Space_adeleRing' (F := F)
  have hI' : HasIwasawa σ Q (KAd σ Q L a) := hI.1
  exact ⟨(hI'.continuous_hgtH continuous_absE (isCompact_KAd hcm)).comp
      ((continuous_ioH _).comp (continuous_id.prodMk continuous_const)),
    GlobalTheory.DblHeightInt.integrable_left hcm hJ hQ L ha hI'⟩

theorem continuous_integrable_hgt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n r s' : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s' →
    ∀ (X₂ : Spc F E (n + n)) (i : UA σ X.J × UA σ X.J →* UA σ X₂.J) (K₂ : Subgroup (UA σ X₂.J)), IsDbl B X X₂ i K₂ →
    Continuous (fun g : UA σ X.J => hgtOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K₂ (i (g, 1))) ∧
    ∃ R : ℝ, ∀ μ : Measure (UA σ X.J), μ.IsHaarMeasure → ∀ t : ℝ, R < t →
      Integrable (fun g : UA σ X.J => ((hgtOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K₂ (i (g, 1)) : ℝ≥0) : ℝ) ^ t) μ := by
  intro F E _ _ _ _ _ σ B n r s' X hB hX X₂ i K₂ hD
  have hcm := hB.cm
  haveI : Submodule.IsLattice E X.L := hX.lat
  have hJt : IsHermND σ X.Jᵀ := ⟨fun i j => hX.herm j i, by
    rw [Matrix.det_transpose]
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    intro hz
    apply GlobalTheory.UnitaryVol.det_ne_zero_of_isCartan (hX.cartan w)
    rw [show X.J.map (B.emb w).1 = ((B.emb w).1).mapMatrix X.J from rfl, ← RingHom.map_det, hz, map_zero]⟩
  have hQ : X₂.Jᵀ = dblGram finSumFinEquiv X.Jᵀ := by
    rw [← GlobalTheory.DblIwasawa.transpose_dblGram, hD.gram]
  obtain ⟨a, hmaj, harch⟩ := GlobalTheory.DblIwasawa.arch hcm B X.J X.θ hX.herm hX.cartan hQ
  have harch' : ∀ (w : InfinitePlace F) (k : GArch σ X₂.Jᵀ w), k ∈ KArch σ X₂.Jᵀ w (Formalism.UG.bc (compInf F E w) a) ↔
      Commute ((matHom w.Completion σ X₂.Jᵀ k).1.map (infEmb (B.emb w))) (X₂.θ w) := fun w k => by
    rw [harch, ← hD.maj]
  have hL₃ : X₂.L = sumLat finSumFinEquiv X.L X.L := hD.lat
  have hL₂' : X₂.L.IsLattice E := by rw [hL₃]; infer_instance
  have key : ∀ g : GAd σ X₂.Jᵀ, GlobalTheory.IwLine.ofGAd σ X₂.J g ∈ GlobalTheory.StabHaar.stabK (σ := σ) B X₂ ↔
      g ∈ KAd σ X₂.Jᵀ X.L a := by
    intro g
    rw [mem_KAd]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := GlobalTheory.T.stabilizer_commutes_majorant F E σ B (n + n) X₂ hL₂' g h
      refine ⟨fun v => ?_, fun w => (harch' w _).2 (h1 w)⟩
      have := h2 v; rwa [hL₃] at this
    · rintro ⟨h2, h1⟩
      refine GlobalTheory.KBridge.ofGAd_mem_stabK F E σ B (n + n) X₂ hL₂' g (fun w => (harch' w _).1 (h1 w)) (fun v => ?_)
      rw [hL₃]; exact h2 v
  have hH : HR (AF F) σ X.Jᵀ = UG (cA σ) (incM F X.J) := (GlobalTheory.IwLine.UG_eq_HR σ _).symm
  have hG : HR (AF F) σ X₂.Jᵀ = UG (cA σ) (incM F X₂.J) := (GlobalTheory.IwLine.UG_eq_HR σ _).symm
  have hC := conv_adelic hcm hJt hQ X.L hmaj
  generalize hS : SetLike.coe ((KAd σ X₂.Jᵀ X.L a).map (matHom (AF F) σ X₂.Jᵀ)) = S at hC
  rw [hH, hG] at hC
  refine hC i hD.emb K₂ (fun g => ?_) hD.iwa
  have hg : g.1 ∈ HR (AF F) σ X₂.Jᵀ := hG.ge g.2
  rw [← hS]
  refine ((GlobalTheory.DblHeightInt.isStab_iff hD.stab g.1 g.2).trans
    (GlobalTheory.DblHeightInt.isStab_iff (GlobalTheory.StabHaar.isStab_stabK (σ := σ) B X₂) g.1 g.2).symm).trans ?_
  exact (key ⟨g.1, hg⟩).trans (Subgroup.mem_map_iff_mem (matHom_injective (AF F) σ X₂.Jᵀ)).symm

end GlobalTheory.DblHeightHerm

end
