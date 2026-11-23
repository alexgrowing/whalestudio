import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.EquivFunOM
import Formalism.LocalToGlobal.IndefiniteReal.PrimitiveStatementsWithPassage

open Module NumberField IsDedekindDomain Polynomial
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx.GroupActionMatrices

section Inst3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty : Type}

theorem okOp_opAll {B : BlockDat K G Pl0} {D : InertDat3 B I0 Ty} {s : ℕ} (h : B.Ok s) (hD : D.Ok3) (hH : B.OkH)
    (hH3 : D.InertRationalAdjoint) : OkOp B D.opAll where
  rat i a b := by
    rcases i with p | k
    · exact hH.rat p a b
    · exact hH3.rat k a b
  adj i := by
    rcases i with p | k
    · obtain ⟨p', hp'⟩ := hH.adj p
      exact ⟨Sum.inl p', hp'⟩
    · obtain ⟨k', hk'⟩ := hH3.adj k
      exact ⟨Sum.inr k', hk'⟩
  comm := hD.comm
  split := InertDat3.splitOver_opAll D h hD
  opG i g := by
    rcases i with p | k
    · exact h.opG p g
    · exact hD.opG k g

end Inst3

section Main3

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
variable (A3 : FamIn3 K G Pl0 I0 Ty T m) (X : CxData A3.fam3.amb3)

theorem proviso_of_lift_eigenvalues {s : ℕ} (hOk : A3.fam3.Ok3 s) (hH : ∀ j, (A3.A.fam.L j A3.A.fam.μ0).OkH ∧ (A3.liftI j A3.A.fam.μ0).InertRationalAdjoint)
    (P : Subgroup G) (ψ : P →* Kˣ) {C : ∀ j : Fin m, ((A3.liftI j A3.A.fam.μ0).OpIx → K) → Prop}
    (hC : LiftsEig3 A3 X P ψ C) : (A3.side3 P ψ X.zs).Proviso := by
  intro j
  have hB := DefFam.blockHyp_lift A3.A.fam hOk.ok2 P ψ j A3.A.fam.μ0
  have hO : OkOp _ (A3.liftI j A3.A.fam.μ0).opAll :=
    okOp_opAll (hOk.ok2.lifts j A3.A.fam.μ0) (hOk.lifts j A3.A.fam.μ0) (hH j).1 (hH j).2
  have hr := eig_ratG hB hO (C j)
  rw [← hC j] at hr
  exact CyclotomicLifting.xq_rat hB hr

theorem types_of_lift_eigenvalues {s : ℕ} (hOk : A3.fam3.Ok3 s) (hsep : A3.fam3.TypesSep3) (hst : X.zs.Stable) (P : Subgroup G)
    (ψ : P →* Kˣ) {C : ∀ j : Fin m, ((A3.liftI j A3.A.fam.μ0).OpIx → K) → Prop} (hC : LiftsEig3 A3 X P ψ C)
    (hT : LiftsTyp3 A3 C) : (A3.side3 P ψ X.zs).Types := by
  intro j
  refine (A3.fam3.LI j A3.A.fam.μ0).inert_parts_span_top (ℓ := A3.A.fam.lvlA P ψ) (Z := X.Zl j A3.A.fam.μ0)
    hOk.ok2.conj (hOk.ok2.lifts j A3.A.fam.μ0) (hOk.lifts j A3.A.fam.μ0)
    hOk.ok2.irr ?_ (fun p : A3.fam3.base3.Ix => A3.fam3.tr3 j p.1) ?_ ?_
  · intro i
    exact Submodule.map_le_iff_le_comap.1 (hst.2 j A3.A.fam.μ0 (Sum.inl i))
  · intro p q hpq
    exact hsep p.1 p.2 q.1 q.2 (fun h => hpq (Subtype.ext h)) j
  · refine (hC j).le.trans ?_
    apply BlockDat.good_part_coordinates_mono
    refine Col.eigSum_mono fun x hx => ?_
    obtain ⟨p, hp, hx'⟩ := hT j x hx
    exact ⟨⟨p, hp⟩, hx'⟩

theorem majAt_eq_zero_of_mem_Qp_of_ne {s : ℕ} (hOk : A3.fam3.Ok3 s) (hH : (A3.A.fam.R A3.A.fam.μ0).OkH ∧ (A3.rowI A3.A.fam.μ0).InertRationalAdjoint)
    (hst : X.zs.Stable) (P : Subgroup G) (ψ : P →* Kˣ) (v : InfinitePlace K) (p q : A3.fam3.base3.Ix) (hpq : p ≠ q)
    (x : Fin ((A3.side3 P ψ X.zs).dQ A3.A.fam.μ0) → K) (hx : x ∈ (A3.side3 P ψ X.zs).Qp A3.A.fam.μ0 p)
    (y : Fin ((A3.side3 P ψ X.zs).dQ A3.A.fam.μ0) → K) (hy : y ∈ (A3.side3 P ψ X.zs).Qp A3.A.fam.μ0 q) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((A3.side3 P ψ X.zs).XQ A3.A.fam.μ0) v x y = 0 := by
  have hB : BlockHyp (A3.A.fam.R A3.A.fam.μ0) (A3.A.fam.lvl P ψ) A3.A.fam.v0 s :=
    ⟨hOk.ok2.conj, hOk.ok2.irr, hOk.ok2.what₂ A3.A.fam.μ0⟩
  have hO : OkOp (A3.A.fam.R A3.A.fam.μ0) (A3.fam3.RI A3.A.fam.μ0).opAll :=
    okOp_opAll (hOk.ok2.what₂ A3.A.fam.μ0) (hOk.what₂ A3.A.fam.μ0) hH.1 hH.2
  refine part_orthg hB hO (fun i => Submodule.map_le_iff_le_comap.1 (hst.1 A3.A.fam.μ0 (Sum.inl i))) v
    (C := (A3.fam3.RI A3.A.fam.μ0).HasRes3 p.1) (C' := (A3.fam3.RI A3.A.fam.μ0).HasRes3 q.1) ?_ hx hy
  intro z hz
  exact (A3.fam3.RI A3.A.fam.μ0).excl3
    ((A3.fam3.RI A3.A.fam.μ0).diffAt_of_mem_ixFin3 q.2 p.2 (fun h => hpq (Subtype.ext h).symm)) z hz

end Main3

end Formalism.IndefR.Cx
