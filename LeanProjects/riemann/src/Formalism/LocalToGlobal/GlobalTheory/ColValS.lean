import Formalism.LocalToGlobal.GlobalTheory.MemIffOfLocBasisG
import Formalism.SharpRestriction.GlobalSchurBounds.StandardIntegralLatticeExists
import Formalism.SharpRestriction.GlobalSchurBounds.LinkGLOBAL7Tied4

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree Formalism.MainNotions.GlobalTheoryTheory.Inhab

def ColTieW {D : D7} {u : D.what₂.Word} (B : ColBase D u) : Prop :=
  Nonempty ((D.mem u).C.cls 0) ∧
  (∀ c, LatT (D.sp.X 0) (Tu D u ^ (2 * D.R.f)) (D.clsLat u 0 c)) ∧
  ∃ co : ((D.fm u).lat 0).V →ₗ[D.what₂.LL]
      ((D.mem u).C.cls 0 → MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) D.what₂.LL),
    Function.Injective co ∧
    (∀ F, (∃ x, co x = F) ↔ ∀ c, F c ∈ TSpan D.what₂.LL ((D.fm u).lam 0)) ∧
    (∀ w : D.what₂.places.Pl, ∃ γ : (D.mem u).C.cls 0 → D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL,
      (∀ c τ, LocBasis D w (B.Q c τ) (B.eQ c τ) (γ c τ)) ∧
      ∀ x, x ∈ locW D.what₂.places w ((D.fm u).lat 0).L ↔
        ∀ c, actAll ((D.fm u).lam 0) (fun τ => (γ c τ)⁻¹) (co x c) ∈ IntSpanAt D w ((D.fm u).lam 0)) ∧
    ∀ (v : NumberField.InfinitePlace D.what₂.LL) x,
      (Formalism.HermitianLatticesTheory.majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x x).re =
        ∑ c, (nfAll ((D.fm u).lam 0)
          (actAll ((D.fm u).lam 0) (fun τ => Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹)
            (MvPolynomial.map v.embedding (co x c)))
          (actAll ((D.fm u).lam 0) (fun τ => Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹)
            (MvPolynomial.map v.embedding (co x c)))).re

theorem colTie_of_colTieW {D : D7} {u : D.what₂.Word} (B : ColBase D u) (h : ColTieW B) : ColTie B := by
  obtain ⟨h1, h2, co, hinj, hspan, hloc, hinf⟩ := h
  refine ⟨h1, h2, co, hinj, hspan, fun w γ hγ x => ?_, hinf⟩
  obtain ⟨γ0, hγ0, hx⟩ := hloc w
  rw [hx]
  exact forall_congr' fun c => mem_iff_of_locBasis D w ((D.fm u).lam 0) (B.Q c) (B.eQ c) (γ0 c) (γ c)
    (hγ0 c) (hγ c) (co x c)

theorem colTieW_of {D : D7} {u : D.what₂.Word} (B : ColBase D u) (h : ColTie B) : ColTieW B := by
  obtain ⟨h1, h2, co, hinj, hspan, hloc, hinf⟩ := h
  refine ⟨h1, h2, co, hinj, hspan, fun w => ?_, hinf⟩
  have hex : ∀ c τ, ∃ g, LocBasis D w (B.Q c τ) (B.eQ c τ) g := fun c τ =>
    Formalism.L2.GlobalTheoryTheory.TraceIntegrality.exists_locBasis w (B.Q c τ) (B.Q_good c τ) (B.eQ c τ)
  choose γ hγ using hex
  exact ⟨γ, hγ, hloc w γ hγ⟩

theorem colTieW_iff {D : D7} {u : D.what₂.Word} (B : ColBase D u) : ColTieW B ↔ ColTie B :=
  ⟨colTie_of_colTieW B, colTieW_of B⟩

theorem column_value_nonempty_iff (D : D7) (u : D.what₂.Word) :
    Nonempty (ColVal D u) ↔ ∃ B : ColBase D u, ColTieW B := by
  rw [ColVal_nonempty_iff]
  exact exists_congr fun B => (colTieW_iff B).symm

theorem column_value_of_tie_local_bases
    (h : ∀ D : D7, Formalism.L2.Forms.ColsTiedSym D → adm3 D → ∀ u : D.what₂.Word, ∃ B : ColBase D u, ColTieW B) :
    Formalism.MainNotions.RT.ColumnValuationFromTwistCompatibility := by
  intro D h1 h2 u
  exact (column_value_nonempty_iff D u).mpr (h D h1 h2 u)

end Formalism.L2.GlobalTheoryTheory.ColValS
