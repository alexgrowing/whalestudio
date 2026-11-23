import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings

namespace Formalism.FourierDecayAlt.P.PBJ

open MeasureTheory Formalism.FourierDecayAlt

def KCls {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (Ψ : G.Mat n → V) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) Ψ ∧ HasCompactSupport Ψ ∧ ∀ Z ∈ tsupport Ψ, G.detM Z ≠ 0

def FubTop : Prop :=
  ∀ (β : ℂ) (p s : ℕ) (σ : Equiv.Perm (Fin (p + s))) (d : Fin (p + s) → ℂ) (σh : Equiv.Perm (Fin p))
    (dh : Fin p → ℂ) (σb : Equiv.Perm (Fin s)) (db : Fin s → ℂ) (V : Type) [NormedAddCommGroup V]
    [NormedSpace ℂ V] [CompleteSpace V] (Ψ : G.Mat (p + s) → V),
    (∀ i, dh i ≠ 0) → (∀ i, db i ≠ 0) → U.hMat σ d = U.blk2 (U.hMat σh dh) 0 0 (U.hMat σb db) → KCls Ψ →
    U.PhiTop (p := p + s) (s := 0) β σ d Ψ (fun x => x.elim0) =
      U.PhiTop (p := s) (s := 0) β σb db (U.PhiTop (p := p) (s := s) β σh dh Ψ) (fun x => x.elim0)

def FreezeLast : Prop :=
  ∀ (β : ℂ) (p : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (Ψ : G.Mat (p + 1) → V), KCls Ψ → ∀ c : ℂ, c ≠ 0 →
    ∃ Ψc : G.Mat p → V, KCls Ψc ∧ ∀ (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ), (∀ i, d i ≠ 0) →
      U.PhiTop (p := p) (s := 1) β σ d Ψ (fun _ _ => c) = U.PhiTop (p := p) (s := 0) β σ d Ψc (fun x => x.elim0)

def OmLongTop : Prop :=
  ∀ β : ℂ, β ≠ 0 → ∀ n : ℕ, ∃ κ : ℂ, κ ≠ 0 ∧
    ∀ (σ : Equiv.Perm (Fin (n + 1))) (d : Fin (n + 1) → ℂ) (z : ℂ) (V : Type) [NormedAddCommGroup V]
      [NormedSpace ℂ V] [CompleteSpace V] (Φ : G.Mat (n + 1) → V),
      z ≠ 0 → U.hMat σ d = G.ptLong (n + 1) z →
      G.OmLong β n Φ z = κ • U.PhiTop (p := n + 1) (s := 0) β σ d Φ (fun x => x.elim0)

def OmBlockTop : Prop :=
  ∀ β : ℂ, β ≠ 0 → ∀ n : ℕ, ∃ κ : ℂ, κ ≠ 0 ∧
    ∀ (σ : Equiv.Perm (Fin (n + 1))) (d : Fin (n + 1) → ℂ) (t c : ℂ) (V : Type) [NormedAddCommGroup V]
      [NormedSpace ℂ V] [CompleteSpace V] (Φ : G.Mat (n + 1) → V),
      t ≠ 0 → c ≠ 0 → U.hMat σ d = G.ptBlock n t c →
      G.OmBlock β n Φ t c = κ • U.PhiTop (p := n + 1) (s := 0) β σ d Φ (fun x => x.elim0)

def KloostDensOfParts : Prop := FubTop → FreezeLast → OmLongTop → OmBlockTop → KB.KloostDens

end Formalism.FourierDecayAlt.P.PBJ
