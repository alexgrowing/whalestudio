import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabEqStabilizer

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.CxUnfold

variable {p : ℕ} [Fact p.Prime]

def PLv (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) : Type := Projectivization ℂ (Fin G.n → ℂ)

theorem toV_injective (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (y : grp G β) :
    Function.Injective (Matrix.toLin' (toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ)) := by
  intro a b h
  have h' := congrArg (Matrix.toLin' (((toV G v β y)⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ)) h
  simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec] using h'

instance (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) : MulAction (grp G β) (PLv G v β) where
  smul y l := Projectivization.map (Matrix.toLin' (toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ))
    (toV_injective G v β y) (l : Projectivization ℂ (Fin G.n → ℂ))
  one_smul l := by
    change Projectivization.map _ _ (l : Projectivization ℂ (Fin G.n → ℂ)) = l
    induction (l : Projectivization ℂ (Fin G.n → ℂ)) using Projectivization.ind with
    | h w hw =>
      rw [Projectivization.map_mk]
      congr 1
      simp [Matrix.toLin'_apply]
  mul_smul y y' l := by
    change Projectivization.map _ _ (l : Projectivization ℂ (Fin G.n → ℂ)) =
      Projectivization.map _ _ (Projectivization.map _ _ (l : Projectivization ℂ (Fin G.n → ℂ)))
    induction (l : Projectivization ℂ (Fin G.n → ℂ)) using Projectivization.ind with
    | h w hw =>
      rw [Projectivization.map_mk, Projectivization.map_mk, Projectivization.map_mk]
      congr 1
      simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec]

abbrev Ys (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (Kf : Subgroup G.GAf) (K' : Subgroup (Gr G 1)) : Type :=
  LeftCosets ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') × PLv G v β

def cxF (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (β : G.Cˣ)
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ)
    (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ) (a : Ys G v β x t hx Kf K') (y : grp G β) : ℂ :=
  if 0 < (star (Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ))) ⬝ᵥ
        (herm G v β *ᵥ Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ)))).re ∧
      FixL G v β y (Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ))) then
    f ((LeftCosets.rep _ _ a.1).1⁻¹ * toAfF G β x t hx y * (LeftCosets.rep _ _ a.1).1) *
      f' ((LeftCosets.rep _ _ a.1).2⁻¹ * toP1 G β y * (LeftCosets.rep _ _ a.1).2) *
      wt (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))
  else 0

example (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (Kf : Subgroup G.GAf) (K' : Subgroup (Gr G 1)) :
    Nonempty (Ys G v β x t hx Kf K') :=
  ⟨(LeftCosets.mk _ _ 1, (Projectivization.mk ℂ (Pi.single ⟨0, G.n_pos⟩ 1)
    (by simp [Pi.single_eq_zero_iff]) : Projectivization ℂ (Fin G.n → ℂ)))⟩

end GlobalTheory.CxUnfold
