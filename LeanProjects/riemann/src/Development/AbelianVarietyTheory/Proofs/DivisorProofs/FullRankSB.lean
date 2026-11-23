import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

noncomputable section

open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.WeilM

namespace GlobalTheory.RankFibre

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

def fullRankSB (a d : ℕ) : Submodule ℂ (Matrix (Fin a) (Fin d) k → ℂ) where
  carrier := {Ψ | Ψ ∈ SB (Matrix (Fin a) (Fin d) k) ∧ ∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Ψ Y = 0}
  zero_mem' := ⟨(SB _).zero_mem, fun _ _ => rfl⟩
  add_mem' := fun hΦ hΨ => ⟨(SB _).add_mem hΦ.1 hΨ.1, fun Y hY => by simp [hΦ.2 Y hY, hΨ.2 Y hY]⟩
  smul_mem' := fun c Φ hΦ => ⟨(SB _).smul_mem c hΦ.1, fun Y hY => by simp [hΦ.2 Y hY]⟩

def coinv (ν β : kˣ →* ℂˣ) (a d : ℕ) : Submodule ℂ (Matrix (Fin a) (Fin d) k → ℂ) :=
  Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
    Ψ ∈ SB (Matrix (Fin a) (Fin d) k) ∧ z = omA ν β g 1 Ψ - Ψ}

abbrev blocks (a b : ℕ) : (Σ x, Two (Fin a) (Fin b) x) ≃ Fin (a + b) := two (stdSum (rfl : a + b = a + b))

def parChar (ν β : kˣ →* ℂˣ) (a b : ℕ) : parab k (blocks a b) →* ℂˣ :=
  (deltaHalf k (Two (Fin a) (Fin b)) * ((detChar (Fin a) (ν * β)).comp (MonoidHom.fst _ _)).comp
      (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom *
    ((detChar (Fin b) β).comp (MonoidHom.snd _ _)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom).comp
    (leviProj k (blocks a b))

def indScal (ν β : kˣ →* ℂˣ) (a b : ℕ) : Submodule ℂ (GL (Fin (a + b)) k → ℂ) :=
  smoothPart (rightReg ℂ (GL (Fin (a + b)) k) ℂ) ⊓ indSpace (parab k (blocks a b)) (ofChar (parChar ν β a b))

variable [MeasurableSpace k] [BorelSpace k]

def fibre (ν β : kˣ →* ℂˣ) (a b : ℕ) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ) (x : GL (Fin (a + b)) k) : ℂ :=
  ∫ g : GL (Fin a) k, omA ν β 1 x Φ (g.val * X0 k finSumFinEquiv) * (ν (gdet g) : ℂ) *
    apow (gdet g) (((a + b : ℕ) : ℂ) / 2) ∂(haarVol (GlobalTheory.SplitWeil.KO k (Fin a)))

theorem fibre_omA (ν β : kˣ →* ℂˣ) (a b : ℕ) (h : GL (Fin (a + b)) k) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ)
    (x : GL (Fin (a + b)) k) : fibre ν β a b (omA ν β 1 h Φ) x = fibre ν β a b Φ (x * h) := by
  unfold fibre
  congr 1
  funext g
  rw [← omA_mul, one_mul]

end GlobalTheory.RankFibre
