import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.RatActGOf
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ProdMemSpan

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.MainNotions.G.LatticeSystems

variable {p : ℕ} (G : GAtP p) {E LL : Type} [Field E] [Field LL] (e : LL →+* G.Kf)
  (iw : ∀ v : Fin G.P.nV, E →+* G.P.Qq v) (t : ∀ v : Fin G.P.nV, Fin (G.P.n' v) → E →+* LL)

def PosCompat : Prop :=
  ∀ (v : Fin G.P.nV) (s : Fin (G.P.n' v)) (x : E), e (t v s x) = G.P.ι v ((G.P.σ v ^ s.val) (iw v x))

def ActE : Prop :=
  ∀ (i : G.comp) (γ : (G.lev i).Γ), ∃ a : GL (Fin (G.P.m + 1)) E,
    ∀ v, (G.lev i).act v γ = Matrix.GeneralLinearGroup.map (iw v) a

def ChiRat : Prop :=
  ∀ (i : G.comp) (γ : (G.lev i).Γ), ∃ a : LL, e a = algebraMap G.O G.Kf ((G.lev i).χ γ : G.O)

def RatTup : Prop :=
  ∀ L : G.P.Tup, G.P.IsLatTup L → ∃ a : GL (Fin (G.P.m + 1)) E,
    ∀ v, L v = colSpan (G.P.W v) ((a : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) E).map (iw v))

theorem ratLev_of (hp : PosCompat G e iw t) (ha : ActE G iw) (hc : ChiRat G e) : RatLev G e := by
  refine ⟨fun i γ v s => ?_, hc⟩
  obtain ⟨a, ha⟩ := ha i γ
  refine ⟨Matrix.GeneralLinearGroup.map (t v s) a, ?_⟩
  rw [ha v]
  ext j k
  simp [gPosGL, hp v s]

theorem ratBasis_of (hp : PosCompat G e iw t) (hr : RatTup G iw) : RatBasis G e := by
  intro L hL v s
  obtain ⟨a, ha⟩ := hr L hL
  refine ⟨Matrix.GeneralLinearGroup.map (t v s) a, ?_⟩
  rw [ha v, Formalism.MainNotions.G.LatticeSystems.la_extO_G]
  congr 1
  ext j k
  simp [Formalism.MainNotions.G.LatticeSystems.la_tw, hp v s]

end Formalism.L2.G.Cmp
