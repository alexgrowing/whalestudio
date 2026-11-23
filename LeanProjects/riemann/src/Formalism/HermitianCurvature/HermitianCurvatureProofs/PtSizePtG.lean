import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceOmBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FormModel

namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt

noncomputable section

def ptG (h' : C.LPt) (m : ℕ) : (ℂ × ℂ) ⊕ ℂ → C.LPt
  | Sum.inl q => h' ++ [(m + 1, q.1), (1, q.2)]
  | Sum.inr z => h' ++ [(m + 2, z)]

def yG {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (β : ℂ) (m : ℕ) (Φ : G.Mat (m + 2) → V) :
    (ℂ × ℂ) ⊕ ℂ → V
  | Sum.inl q => ((kapB m : ℝ) : ℂ) • G.OmBlock β (m + 1) Φ q.1 q.2
  | Sum.inr z => ((Real.pi ^ ((m + 2) * (m + 1) / 2) : ℝ) : ℂ) • G.OmLong β (m + 1) Φ z

def okG (m : ℕ) (Kc : Set ℂ) : (ℂ × ℂ) ⊕ ℂ → Prop
  | Sum.inl q => q.1 ≠ 0 ∧ q.2 * q.1 ^ (m + 1) ∈ Kc
  | Sum.inr z => ∃ D ∈ Kc, z ^ (m + 2) = (-1) ^ (m + 3) * D

theorem ptSize_ptG (h' : C.LPt) (m : ℕ) (q : (ℂ × ℂ) ⊕ ℂ) : D.ptSize (ptG h' m q) = D.ptSize h' + (m + 2) := by
  cases q <;> simp [ptG, D.ptSize, List.map_append, List.sum_append] <;> omega

def GermPlace : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (sg : ℂ) (w : List C.Letter) (f : B.Mat P0.k P0.r → (Wq →L[ℂ] Wp))
    (χ : ℝ → ℝ) (ε : ℝ) (h' : C.LPt) (m i : ℕ) (hi : i ≤ P0.r) (hsz : D.ptSize h' + (m + 2) = i),
    B.CkOn ⊤ (B.GV P0.k P0.r) f → (∃ R : ℝ, ∀ g ∈ B.GV P0.k P0.r, f g ≠ 0 → B.gN g ≤ R) → C6.IsCut0 χ →
    0 < ε → 2 ≤ P0.k → D.IsLocPt h' (D.ptSize h') →
    ∀ Kc : Set ℂ, IsCompact Kc → (0 : ℂ) ∉ Kc →
    ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : NormedSpace ℂ V) (_ : CompleteSpace V)
      (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (Φ : G.Mat (m + 2) → V) (Cp Cst : ℝ),
      0 ≤ Cp ∧ (∀ u, (Bf u u).re ≤ (Cp * ‖u‖) ^ 2) ∧
      (∀ q1 q2, okG m Kc q1 → okG m Kc q2 →
        D.formLev T sg ⟨i, by omega⟩ w
          (KB.slv T (D.cutF T.base χ f ε) i hi w (ptG h' m q1) (by rw [ptSize_ptG, hsz]))
          (KB.slv T (D.cutF T.base χ f ε) i hi w (ptG h' m q2) (by rw [ptSize_ptG, hsz])) =
        Bf (yG U.betaU m Φ q1) (yG U.betaU m Φ q2)) ∧
      ∀ t D : ℂ, t ≠ 0 → D ∈ Kc →
        ‖U.uD U.betaU m (U.Mlev P0.k (P0.r - i)) Φ t D - U.aD U.betaU m (U.Mlev P0.k (P0.r - i)) Φ t D‖ ≤
          Cst * ‖t‖

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities
