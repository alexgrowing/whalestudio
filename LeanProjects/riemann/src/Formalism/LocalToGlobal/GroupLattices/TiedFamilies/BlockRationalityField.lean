import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieEvR
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.RecAct

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG Formalism.L2.G.Cmp Matrix

namespace Formalism.L2.G

def BlockRationalityField : Prop :=
  ∀ {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (P : Places p O Kf) {Tau : Type} [Fintype Tau] {n : ℕ} {LL : Type} [Field LL] (h : P.m + 1 = n)
    (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (G M : Tau → Matrix (Fin n) (Fin n) ℂ) (embLL : LL →+* ℂ)
    (lam : Tau → DomWeight n), WtTie P h pos lam → (∀ τ, ∃ M0 : GL (Fin n) LL, M τ = M0.1.map embLL) →
    BlockRational P h pos G M embLL lam

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

set_option maxHeartbeats 4000000 in

theorem blkRatRec_of_stmt (hS : BlockRationalityField) (X : Formalism.L2.Herm.Herm0 D) (Gt : GatTies D) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (B : GL (Fin D.R.k) D.host.E) :
    BlockRationalityAtPlace X Gt u w hg B := by
  refine hS (D.gat u w hg).P (locAt X u w hg B).rk (Gt.gat_pos u w hg) _ _ D.what₂.embLL ((D.fm u).lam 0) ?_ ?_
  · intro v s i
    exact Gt.gat_lam u w hg v s i
  · intro τ
    refine ⟨bc (tEL D τ) ((locAt X u w hg B).B)⁻¹, ?_⟩
    ext a b
    exact (tEL_emb D τ _).symm

end Formalism.L2.G
