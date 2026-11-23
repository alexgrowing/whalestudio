import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries GlobalTheory.Prism GlobalTheory.BKReal
open scoped NNReal

namespace GlobalTheory.BSP.Height

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ}
  {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]} {τ : Ainf l} {s : Seed bk d ρ τ} (ht : Height s)

def bas : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀) := s.X.map (toDisc l (X : bk.S) bk.ρ₀) * ht.Z

def Rel {B : Obj l ↥(OL K)} (u : B.A) (f g : Hom bk.prism B)
    (ε : Matrix (Fin d) (Fin d) (Disc l u bk.ρ₀)) : Prop :=
  ∀ Ff Fg : bk.DS bk.ρ₀ →+* Disc l u bk.ρ₀, IsDiscMap (BK.hf f) Ff → IsDiscMap (BK.hf g) Fg →
    toDisc l u bk.ρ₀ (BK.hf g bk.E) ^ s.N • (ht.bas.map Ff * ε) =
      toDisc l u bk.ρ₀ (BK.hf f bk.E) ^ s.N • ht.bas.map Fg

theorem rel_one {B : Obj l ↥(OL K)} (u : B.A) (f : Hom bk.prism B) : ht.Rel u f f 1 := fun Ff Fg hf hg => by
  rw [hf.unique hg, mul_one]

end GlobalTheory.BSP.Height
