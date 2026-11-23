import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneSubIdemQMulSelf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.SetCut

theorem smul_add_one_sub_smul_sub_one {R : Type} [CommRing R] {n : ℕ} (c : R) (M : Matrix (Fin n) (Fin n) R) :
    c • M + (1 - c) • (1 : Matrix (Fin n) (Fin n) R) - 1 = c • (M - 1) := by
  rw [sub_smul, one_smul, smul_sub]; abel

theorem smul_add_one_sub_smul_block {R : Type} [CommRing R] {n m : ℕ} (c : R) (P Q : Matrix (Fin n) (Fin n) R)
    (j : Matrix (Fin n) (Fin m) R) (p : Matrix (Fin m) (Fin n) R) (M : Matrix (Fin m) (Fin m) R)
    (h : P + j * p + Q = 1) :
    c • (P + j * M * p + Q) + (1 - c) • (1 : Matrix (Fin n) (Fin n) R) =
      P + j * (c • M + (1 - c) • (1 : Matrix (Fin m) (Fin m) R)) * p + Q := by
  rw [← h]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_add, sub_smul,
    one_smul, Matrix.mul_sub, Matrix.sub_mul]
  abel

theorem smul_add_one_sub_smul_block₂ {R : Type} [CommRing R] {n m k : ℕ} (c : R)
    (j : Matrix (Fin n) (Fin m) R) (p : Matrix (Fin m) (Fin n) R) (M : Matrix (Fin m) (Fin m) R)
    (j' : Matrix (Fin n) (Fin k) R) (p' : Matrix (Fin k) (Fin n) R)
    (h : j * p + j' * p' = 1) :
    c • (j * M * p + j' * (1 : Matrix (Fin k) (Fin k) R) * p') + (1 - c) • (1 : Matrix (Fin n) (Fin n) R) =
      j * (c • M + (1 - c) • (1 : Matrix (Fin m) (Fin m) R)) * p + j' * (1 : Matrix (Fin k) (Fin k) R) * p' := by
  have := smul_add_one_sub_smul_block c 0 (j' * p') j p M (by rw [zero_add, h])
  simpa only [zero_add, Matrix.mul_one] using this

variable {D : D7}

theorem jac_subOne_cutG (V : HSp D) (ε : AF D.host.F) (hε : ε * ε = ε) (g : GA D V) :
    Formalism.L2.Theta.subOne V (cutG V ε hε g) = algebraMap (AF D.host.F) (AE D) ε • Formalism.L2.Theta.subOne V g :=
  smul_add_one_sub_smul_sub_one (algebraMap (AF D.host.F) (AE D) ε) (Formalism.L2.Theta.mt V g)

theorem jac_cutG_map_NFlag (V : HSp D) {ρ : ℕ} (e : Matrix (Fin V.rank) (Fin ρ) D.host.E) (ε : AF D.host.F)
    (hε : ε * ε = ε) : (NFlag V e).map (cutG V ε hε) ≤ NFlag V e := by
  unfold NFlag
  rw [MonoidHom.map_closure]
  apply Subgroup.closure_mono
  rintro _ ⟨g, ⟨h1, h2⟩, rfl⟩
  refine ⟨fun i => ?_, fun x hx => ?_⟩
  · obtain ⟨a, ha, hb⟩ := h1 i
    refine ⟨algebraMap (AF D.host.F) (AE D) ε • a, fun j hj => ?_, ?_⟩
    · rw [Pi.smul_apply, ha j hj, smul_zero]
    · rw [jac_subOne_cutG, Matrix.smul_mulVec, hb, Matrix.mulVec_smul]
  · obtain ⟨a, hb⟩ := h2 x hx
    refine ⟨algebraMap (AF D.host.F) (AE D) ε • a, ?_⟩
    rw [jac_subOne_cutG, Matrix.smul_mulVec, hb, Matrix.mulVec_smul]

theorem unitaryIdempotentCut_wittHyperbolicEmbedding_comm {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (ε : AF D.host.F) (hε : ε * ε = ε) (h : GA D V₀) :
    cutG V ε hε (d.emb0 h) = d.emb0 (cutG V₀ ε hε h) := by
  apply GlobalTheory.MixModel.mt_injective V
  change Formalism.L2.Theta.mt V (cutG V ε hε (d.emb0 h)) = Formalism.L2.Theta.mt V (d.emb0 (cutG V₀ ε hε h))
  rw [mt_cutG, HypDec.unitaryMatrix_wittCoreEmbedding, HypDec.unitaryMatrix_wittCoreEmbedding, mt_cutG]
  exact smul_add_one_sub_smul_block _ _ _ _ _ _ d.sum_eq_one

theorem jac_cutG_emb_inl {V₀ A L : HSp D} (o : OrthDec V₀ A L) (ε : AF D.host.F) (hε : ε * ε = ε) (h : GA D A) :
    cutG V₀ ε hε (o.emb (h, 1)) = o.emb (cutG A ε hε h, 1) := by
  apply GlobalTheory.MixModel.mt_injective V₀
  change Formalism.L2.Theta.mt V₀ (cutG V₀ ε hε (o.emb (h, 1))) = Formalism.L2.Theta.mt V₀ (o.emb (cutG A ε hε h, 1))
  rw [mt_cutG, OrthDec.mt_emb, OrthDec.mt_emb, mt_cutG, mt_one]
  exact smul_add_one_sub_smul_block₂ _ _ _ _ _ _ o.sum_eq_one

theorem cutG_mem_jacGrp_besGrp (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (ε : AF D.host.F) (hε : ε * ε = ε) :
    (∀ g ∈ jacGrp d, cutG V ε hε g ∈ jacGrp d) ∧
      ∀ (A L : HSp D) (o : OrthDec V₀ A L), ∀ g ∈ besGrp d o, cutG V ε hε g ∈ besGrp d o := by
  refine ⟨fun g hg => ?_, fun A L o g hg => ?_⟩
  · have H : (jacGrp d).map (cutG V ε hε) ≤ jacGrp d := by
      unfold jacGrp
      rw [Subgroup.map_sup]
      refine sup_le_sup (jac_cutG_map_NFlag V d.e ε hε) ?_
      rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
      exact ⟨cutG V₀ ε hε h, (unitaryIdempotentCut_wittHyperbolicEmbedding_comm d ε hε h).symm⟩
    exact H ⟨g, hg, rfl⟩
  · have H : (besGrp d o).map (cutG V ε hε) ≤ besGrp d o := by
      unfold besGrp
      rw [Subgroup.map_sup]
      refine sup_le_sup (jac_cutG_map_NFlag V d.e ε hε) ?_
      rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
      refine ⟨cutG A ε hε h, ?_⟩
      rw [embA_apply, embA_apply, unitaryIdempotentCut_wittHyperbolicEmbedding_comm, jac_cutG_emb_inl]
    exact H ⟨g, hg, rfl⟩

end GlobalTheory.FinPl.SetCut

end
