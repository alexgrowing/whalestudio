import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasWtZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasTorusWeightIffTorusEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

namespace GlobalTheory.ZH.UFib

theorem pure_of_red : ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (π : Φ.E.B.left ⟶ Y) (N : ℕ) (c : ChartPull Φ.N₀ (npw L N) π) (K K' : Type) [Fintype K] [Fintype K'] (ψ : K → (Φ.E.B.left ⟶ Y)) (ε : K → ℤ) (φt : K' → (Φ.G.left ⟶ Y)) (εt : K' → ℤ) (t : LB.Gen (LB.LinComb L φt εt)), t.IsGen → ∀ α : Φ.E.X, UFib.GenWt Φ.D.i t α → ∀ (b : LB.Sec (LB.LinComb L ψ ε)) (φ : (Φ.H 1).Sec), UFib.Red Φ c t b φ → Φ.Pure α φ := by
  intro k _ _ Φ Y L hL π N c K K' _ _ ψ ε φt εt t _ α hw b φ hr
  rintro χ ⟨l, hl⟩
  by_contra hne
  refine hl ((GlobalTheory.T.hasTorusWeight_iff_torusEquivariant k Φ.E Φ.G Φ.D (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l) (φ.f l) α).1 ?_ χ hne)
  intro Z τ g z hz
  have := Φ.D.q_hom
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (K := Unit) (fun _ => g.left ≫ Φ.D.q.left ≫ π) (fun _ => c.idx l)
    (fun _ _ _ => rfl) (fun _ => c.le l hz)
  have hq : ((τ ≫ Φ.D.i) * g).left ≫ Φ.D.q.left = g.left ≫ Φ.D.q.left :=
    congrArg (fun x => x.left) (GtBaseChange.translate_comp Φ.D.q Φ.D.i Φ.D.isKernel τ g)
  have h₁ := hr _ g.left z J hJ l hz (e ())
  have h₂ := hr _ ((τ ≫ Φ.D.i) * g).left z J hJ l
    (GtBaseChange.translate_mem Φ.D.q Φ.D.i Φ.D.isKernel τ g _ z hz)
    (by rw [← Category.assoc, hq, Category.assoc]; exact e ())
  rw [hq, hw Z τ g z J hJ, Units.val_mul, mul_left_comm, ← h₁] at h₂
  exact h₂

end GlobalTheory.ZH.UFib
