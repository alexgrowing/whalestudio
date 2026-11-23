import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBlockNFZeroOne
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Frame

section Gen

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def trM {R : Type} {M n : ℕ} (X : Fin n → Fin M → R) : Matrix (Fin M) (Fin n) R :=
  Matrix.of fun i a => X a i

def framesE (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) :
    Set (Fin n → Fin M → E) :=
  {X | LinearIndependent E X ∧ gramE σ J X = T}

def IsBlockM {n : ℕ} (t : ℕ) (T : Matrix (Fin n) (Fin n) E) : Prop :=
  ∃ h : t < n, (∀ i j : Fin n, (t ≤ i.1 ∨ t ≤ j.1) → T i j = 0) ∧
    (T.submatrix (Fin.castLE h.le) (Fin.castLE h.le)).det ≠ 0

def IsGramFibFree (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n))
    (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) : Prop :=
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val {X | LinearIndependent (R ⊗[F] E) X} ν Set.univ m

end Gen

section Glob

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def SWFree (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E)
    (hT : ∀ a b, σ (T b a) = T a b) : Prop :=
  ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F))
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) →
    ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 →
    ∀ (minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E))
      (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)),
      IsGramFibFree (Ainf F) σ J n (coordW (Ainf F) b laminf n M) (coordHerm (Ainf F) σ b laminf n) minf →
      (∀ v, IsGramFibFree (Fv F v) σ J n (coordW (Fv F v) b (lam v) n M) (coordHerm (Fv F v) σ b (lam v) n) (m v)) →
      IsEulerProd b (thetaMeas σ J μ 𝓕 (framesE σ J T)) 1 (minf (hermOf (Ainf F) σ T hT))
        (fun v => m v (hermOf (Fv F v) σ T hT))

end Glob

section D

open Formalism.BasicNotions Formalism.BasicNotions.TH

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hermE_symm {D : D7} {r : ℕ} (β : PositivityTheory.GramSchwartzFunctions.HermE D r) (a b : Fin r) :
    D.sp.cm.sig (β.1 b a) = β.1 a b := by
  have h := congrFun (congrFun β.2 a) b
  simpa [Matrix.map_apply, Matrix.transpose_apply] using h

theorem trM_mem_framesE_iff {D : D7} (V : HSp D) {r : ℕ} (X : Fin r → Fin V.rank → D.host.E)
    (T : Matrix (Fin r) (Fin r) D.host.E) :
    X ∈ framesE D.sp.cm.sig V.gram T ↔ (trM X).rank = r ∧ PositivityTheory.GramSchwartzFunctions.BC.gramQ V (trM X) = T := by
  have hg : HeckeCharacterZeroLocus.SiegelWeilU.gramE D.sp.cm.sig V.gram X = PositivityTheory.GramSchwartzFunctions.BC.gramQ V (trM X) := by
    refine Matrix.ext fun a b => ?_
    simp only [HeckeCharacterZeroLocus.SiegelWeilU.gramE, HeckeCharacterZeroLocus.SiegelWeilU.hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, PositivityTheory.GramSchwartzFunctions.BC.gramQ, trM,
      Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [mul_assoc]; rfl
  have hr : LinearIndependent D.host.E X ↔ (trM X).rank = r := by
    have h1 : (trM X).rank = (Matrix.of X).rank := by
      have : trM X = Matrix.transpose (Matrix.of X) := rfl
      rw [this, Matrix.rank_transpose]
    rw [h1, Matrix.rank_eq_finrank_span_row]
    have := linearIndependent_iff_card_eq_finrank_span (R := D.host.E) (b := X)
    refine this.trans ?_
    rw [Fintype.card_fin, eq_comm]
    exact Iff.rfl
  simp only [framesE, Set.mem_ofPred_eq, hr, hg]

end D

end GlobalTheory.CompanionTheory.WeilSiegel.Frame
