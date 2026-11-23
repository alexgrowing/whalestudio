import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq

noncomputable section

open NumberField IsDedekindDomain Formalism.AUTREP Formalism.UG ReciprocityTheory.Aut

namespace GlobalTheory.SatInd

section Field

variable {K : Type} [Field K]

theorem antiJ_map (g : K →+* K) (n : ℕ) : (antiJ K n).map g = antiJ K n := by
  ext i j
  simp only [antiJ, Matrix.map_apply]
  split_ifs <;> simp

theorem cT_map (g σ σ' : K →+* K) (hg : ∀ x, g (σ x) = σ' (g x)) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) : cT σ' (M.map g) = (cT σ M).map g := by
  ext i j
  simp [cT, hg]

def guMap (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)) (n : ℕ) :
    GU σ n →* GU σ' n :=
  ((bc (n := Fin n) (g : K →+* K)).comp (GU σ n).subtype).codRestrict (GU σ' n) (fun y => by
    have hy : cT σ ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * antiJ K n *
        ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = antiJ K n := y.2
    show cT σ' (((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map (g : K →+* K)) * antiJ K n *
        ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map (g : K →+* K) = antiJ K n
    rw [cT_map (g : K →+* K) σ σ' hg, ← antiJ_map (g : K →+* K) n]
    rw [← Matrix.map_mul, ← Matrix.map_mul, hy])

theorem guMap_val (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)) {n : ℕ}
    (y : GU σ n) :
    (((guMap g hg n y : GU σ' n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map g := rfl

end Field

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}

def gEquiv (D D' : InertDatum L n v w) : w.adicCompletion L ≃+* w.adicCompletion L :=
  D.e.symm.trans D'.e

theorem gEquiv_e (D D' : InertDatum L n v w) (y) : gEquiv D D' (D.e y) = D'.e y := by
  simp [gEquiv]

theorem gEquiv_comm (D D' : InertDatum L n v w) :
    ∀ x, gEquiv D D' (D.σw x) = D'.σw (gEquiv D D' x) := by
  intro x
  obtain ⟨y, rfl⟩ := D.e.surjective x
  rw [← D.comm, gEquiv_e, gEquiv_e, D'.comm]

theorem gEquiv_intL (D D' : InertDatum L n v w) :
    ∀ x, x ∈ intL (w.adicCompletion L) ↔ gEquiv D D' x ∈ intL (w.adicCompletion L) := by
  intro x
  obtain ⟨y, rfl⟩ := D.e.surjective x
  rw [gEquiv_e, ← D.integ, ← D'.integ]

end GlobalTheory.SatInd
