import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVInjective

set_option linter.unusedSectionVars false

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.ParCocompact

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

def rowOf (C : Matrix (Fin n) (Fin r) E) (i : Fin r) : Fin n → E := (cT (σ : E →+* E) C * J) i

def lineProj (C D : Matrix (Fin n) (Fin r) E) (i : Fin r) : Matrix (Fin n) (Fin n) E :=
  Matrix.vecMulVec (fun k => C k i) (rowOf σ J D i)

def projFam (X Y : Matrix (Fin n) (Fin r) E) : Fin r ⊕ Fin r → Matrix (Fin n) (Fin n) E :=
  Sum.elim (lineProj σ J X Y) (lineProj σ J Y X)

def anisoProj (X Y : Matrix (Fin n) (Fin r) E) : Matrix (Fin n) (Fin n) E :=
  1 - ∑ k, projFam σ J X Y k

def normMat (l : Fin n → E) : Matrix (Fin n) (Fin n) E := Matrix.vecMulVec (fun k => σ (l k)) l

def hermFam (X Y : Matrix (Fin n) (Fin r) E) : Option (Fin r ⊕ Fin r) → Matrix (Fin n) (Fin n) E
  | none => cT (σ : E →+* E) (anisoProj σ J X Y) * J * anisoProj σ J X Y
  | some (Sum.inl i) => normMat σ (rowOf σ J Y i)
  | some (Sum.inr i) => normMat σ (rowOf σ J X i)

variable {σ J} {X Y : Matrix (Fin n) (Fin r) E}

theorem leviMin_subset (X Y : Matrix (Fin n) (Fin r) E) : leviMin σ J X Y ⊆ minPar σ J X :=
  fun _ ⟨d, _, e, _⟩ => ⟨_, Matrix.blockTriangular_diagonal _, e⟩

theorem unipMin_subset_minParOne (X : Matrix (Fin n) (Fin r) E) : unipMin σ J X ⊆ minParOne σ J X := by
  rintro u ⟨B, hB, h1, e, -⟩
  exact ⟨B, hB, e, fun i => ⟨1, by rw [h1]; rfl, map_one _⟩⟩

theorem minParOne_props (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    IsClosed (minParOne σ J X) ∧ ∀ p ∈ minParOne σ J X, ∀ q ∈ minParOne σ J X, p * q ∈ minParOne σ J X := by
  obtain ⟨a, ha⟩ := exists_isTorus h hJ hW
  obtain ⟨τ, hc, hm, -, h0, h1⟩ := exists_tau h hJ hW ha
  have ha0 : a 0 = 1 := by
    have e := ha.add 0 0
    rw [add_zero] at e
    exact mul_left_cancel (e.symm.trans (mul_one _).symm)
  have key : ∀ p : minParSub X h hJ hW, p.1 ∈ minParOne σ J X ↔ τ p = 0 := fun p => by
    refine ⟨fun hp => h0 p.1 hp, fun hp => ?_⟩
    have := h1 p
    rwa [hp, ha0, inv_one, mul_one] at this
  constructor
  · have hcl : IsClosed (minPar σ J X) := isClosed_minPar h hJ hW
    have e : minParOne σ J X = Subtype.val '' (τ ⁻¹' {0}) := by
      ext p
      constructor
      · intro hp
        exact ⟨⟨p, minParOne_subset hp⟩, (key _).1 hp, rfl⟩
      · rintro ⟨q, hq, rfl⟩
        exact (key q).2 hq
    rw [e]
    exact (hcl.isClosedEmbedding_subtypeVal.isClosedMap) _ (isClosed_singleton.preimage hc)
  · intro p hp q hq
    have := (key (⟨p, minParOne_subset hp⟩ * ⟨q, minParOne_subset hq⟩)).2 (by
      rw [hm, (key _).1 hp, (key _).1 hq, add_zero])
    exact this

end GlobalTheory.CompanionTheory.ParCocompact

end
