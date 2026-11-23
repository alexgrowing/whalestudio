import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchLinear

noncomputable section

namespace GlobalTheory.PolKer

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

def PolZero (B : Base F E) (G : Geo σ a a') (X : Chars F E) (R : RealMaps F a a') (Rf : FinMaps F a a')
    (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) : Prop :=
  ∃ T : Finset (Pl F), X.T ⊆ T ∧ ∃ (m : ℕ) (f : Fin m → SInf F (Fin a × Fin (a + a')))
    (φ : Fin m → ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ),
    (∀ i, f i ∈ G.M.Pol B.ψ B.emb ∧ (∀ v, φ i v ∈ SB _) ∧ ∀ v ∉ T, φ i v = G.M.vac v) ∧
    Φ = ∑ i, pure (f i) (φ i) ∧
    ∑ i, R.p (f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p v (φ i v)) = 0

theorem sum_pure_mem_algD {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (ψ : AddChar (AF F) ℂ)
    (emb : ∀ w : InfinitePlace F, EmbOver E w) (T : Finset (Pl F)) {m : ℕ} (f : Fin m → SInf F (Fin n × Fin d))
    (φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ)
    (h : ∀ i, f i ∈ M.Pol ψ emb ∧ (∀ v, φ i v ∈ SB _) ∧ ∀ v ∉ T, φ i v = M.vac v) :
    ∑ i, pure (f i) (φ i) ∈ GlobalTheory.SquareAgree.algD M ψ emb := by
  refine Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, φ i, (h i).1, (h i).2.1, ?_, rfl⟩
  filter_upwards [T.finite_toSet.compl_mem_cofinite] with v hv
  exact (h i).2.2 v hv

theorem algD_of_polZero (B : Base F E) (G : Geo σ a a') (X : Chars F E) (R : RealMaps F a a') (Rf : FinMaps F a a')
    (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) (h : PolZero B G X R Rf Φ) : Φ ∈ GlobalTheory.SquareAgree.algD G.M B.ψ B.emb := by
  obtain ⟨T, -, m, f, φ, hf, rfl, -⟩ := h
  exact sum_pure_mem_algD G.M B.ψ B.emb T f φ hf

end GlobalTheory.PolKer
