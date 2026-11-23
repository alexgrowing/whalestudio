import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Rigid0
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries

noncomputable section

namespace UpperTheory.V.U3

open Matrix IsLocalRing UpperTheory.V.Alg

section Coord

variable {O G R : Type} [CommRing O] [Group G] [CommRing R] [Algebra O R] (η : G →* ℤˣ) (Ψ : G →* Oˣ)
  (r : G →* GG 3 R) (W : WPres O ℤ R)

def IsCoord (s : W.σ) : Prop :=
  ∃ g a b, W.wt s = wt6 a - wt6 b ∧ W.z s = emb (r g) a b - algebraMap O R (emb (r0 η Ψ g) a b)

def EntHomog : Prop := ∀ g a b, emb (r g) a b ∈ W.part (wt6 a - wt6 b)

end Coord

def boxDef (j : ℤ) : ℕ := if |j| ≤ 1 then 1 else 0

variable {O : Type} [CommRing O] [IsLocalRing O] {Γ H : Type} [Group Γ] [TopologicalSpace Γ]
  [Group H] [TopologicalSpace H]

def IsLocPres {η : H →* ℤˣ} {Ψ : H →* Oˣ} (U : Univ (GCond.noCondition O η Ψ)) (I : Ideal U.R) (WB : WPres O ℤ (U.R ⧸ I)) :
    Prop :=
  (∀ s, IsCoord η Ψ (push (Ideal.Quotient.mkₐ O I) U.r.hom) WB s) ∧ EntHomog (push (Ideal.Quotient.mkₐ O I) U.r.hom) WB

variable {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {N : Set Γ} {ι : H →* Γ} {hι : Continuous ι}
  {U : Univ (GCond.noCondition O (η.comp ι) (Ψ.comp ι))} {I : Ideal U.R}

def BoxPres (B : Univ (BoxCond N ι hι U I)) (WB : WPres O ℤ (U.R ⧸ I)) : Prop :=
  ∃ (W : WPres O ℤ B.R) (i : (U.R ⧸ I) →ₐ[O] B.R) (τ κ : Type) (_ : Fintype τ) (_ : Fintype κ) (e : WB.σ ⊕ τ ≃ W.σ)
    (f : κ → MvPowerSeries W.σ O) (wf : κ → ℤ),
    IsRelPres WB i W e f wf ∧ push (i.comp (Ideal.Quotient.mkₐ O I)) U.r.hom = B.r.hom.comp ι ∧
    (∀ t, IsCoord η Ψ B.r.hom W (e (.inr t))) ∧ EntHomog B.r.hom W ∧
    ∀ j, Nat.card {u // wf u = j} = Nat.card {t // W.wt (e (.inr t)) = j} + boxDef j

end UpperTheory.V.U3
