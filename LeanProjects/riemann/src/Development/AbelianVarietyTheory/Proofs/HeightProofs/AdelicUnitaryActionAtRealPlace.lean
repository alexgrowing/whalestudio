import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder

namespace GlobalTheory.FockCompare.RealAction

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

variable {A B : Type} [CommRing A] [CommRing B] {m n : Type} [Fintype m] [Fintype n]

theorem map_triple (φ : A →+* B) (g : Matrix m m A) (x : Matrix m n A) (h : Matrix n n A) :
    (g * x * hᵀ).map φ = g.map φ * x.map φ * (h.map φ)ᵀ := by
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]

theorem map_triple_zero (φ : A →+* B) (g : Matrix m m A) (x : Matrix m n A) (h : Matrix n n A)
    (hx : x.map φ = 0) : (g * x * hᵀ).map φ = 0 := by
  rw [map_triple, hx, Matrix.mul_zero, Matrix.zero_mul]

omit [Fintype m] in
theorem map_conj (s : A →+* A) (φ : A →+* ℂ) (h : ∀ z, φ (s z) = starRingEnd ℂ (φ z)) (g : Matrix m m A) :
    (g.map s).map φ = (g.map φ).map (starRingEnd ℂ) := by
  ext a b
  exact h _

theorem unitary_map (s : A →+* A) (φ : A →+* ℂ) (h : ∀ z, φ (s z) = starRingEnd ℂ (φ z)) (g J : Matrix m m A)
    (hg : (g.map s)ᵀ * J * g = J) : (g.map φ)ᴴ * J.map φ * g.map φ = J.map φ := by
  have e : (g.map φ)ᴴ = ((g.map s)ᵀ).map φ := by
    ext a b
    exact (h _).symm
  rw [e, ← Matrix.map_mul, ← Matrix.map_mul, hg]

end Generic

variable {D : D7}

theorem infMat_eq (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (V : HSp D) (k : GA D V) :
    infMat D.sp.cm.sig V.gram θ k = (mt V k).map (θ.comp (infPart D)) := rfl

theorem wAt_eq (θ : InfFam D) (V W : HSp D) (τ : D.what₂.Tau) (x : WA V W) :
    wAt θ V W τ x = x.map ((θ τ).comp (infPart D)) := rfl

theorem gramAt_eq {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) :
    gramAt D V τ = (V.gram.map (incA D)).map ((θ τ).comp (infPart D)) := by
  ext a b
  exact (comp_incA hθ τ _).symm

theorem infMat_mem_UH {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (k : GA D V) (τ : D.what₂.Tau) :
    infMat D.sp.cm.sig V.gram (θ τ) k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  rw [infMat_eq, gramAt_eq hθ]
  exact unitary_map (cA D) ((θ τ).comp (infPart D)) (comp_cA hθ τ) _ _ (mt_rel V k)

theorem wAt_actHom {θ : InfFam D} (hθ : IsInfFam θ) (V W : HSp D) (k : GA D V) (k' : GA D W) (x : WA V W)
    (τ : D.what₂.Tau) : wAt θ V W τ (actHom V W k k' x) =
      actC V W (infMat D.sp.cm.sig V.gram (θ τ) k) (infMat D.sp.cm.sig W.gram (θ τ) k') (wAt θ V W τ x) := by
  rw [infMat_eq, infMat_eq, wAt_eq, wAt_eq]
  unfold actHom actC cM
  split_ifs
  · rw [← map_conj (cA D) ((θ τ).comp (infPart D)) (comp_cA hθ τ)]
    exact map_triple _ _ _ _
  · rw [← map_conj (cA D) ((θ τ).comp (infPart D)) (comp_cA hθ τ)]
    exact map_triple _ _ _ _

theorem isRealW_actHom (V W : HSp D) (k : GA D V) (k' : GA D W) (x : WA V W) (hx : IsRealW V W x) :
    IsRealW V W (actHom V W k k' x) := by
  unfold IsRealW actHom
  split_ifs
  · exact map_triple_zero (finPart D) _ _ _ hx
  · exact map_triple_zero (finPart D) _ _ _ hx

theorem real_action : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → (∀ (V : HSp D) (k : GA D V) (τ : D.what₂.Tau), infMat D.sp.cm.sig V.gram (θ τ) k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) ∧ ∀ (V W : HSp D) (k : GA D V) (k' : GA D W) (x : WA V W), (∀ τ, wAt θ V W τ (actHom V W k k' x) = actC V W (infMat D.sp.cm.sig V.gram (θ τ) k) (infMat D.sp.cm.sig W.gram (θ τ) k') (wAt θ V W τ x)) ∧ (IsRealW V W x → IsRealW V W (actHom V W k k' x)) :=
  fun _ _ hθ => ⟨fun V k τ => infMat_mem_UH hθ V k τ, fun V W k k' x =>
    ⟨fun τ => wAt_actHom hθ V W k k' x τ, isRealW_actHom V W k k' x⟩⟩

end GlobalTheory.FockCompare.RealAction

end
