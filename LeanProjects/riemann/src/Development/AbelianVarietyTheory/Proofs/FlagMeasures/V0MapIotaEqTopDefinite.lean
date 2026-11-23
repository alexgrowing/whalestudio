import Mathlib
import Formalism.LocalToGlobal.Divisibility.DivisionCompatibleToSub2Indef2
import Formalism.LocalToGlobal.GroupLattices.JointServices.LevelOperatorFixesImage
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowSideIotaMapsFixedColumnsOntoOfMatrices

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef NumberField

theorem GlobalTheory.V0_map_iota_eq_top_of_definite : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 Ty T : Type) (m : ℕ) (A3 : FamIn3 D.what₂.LL G Pl0 I0 Ty T m) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Ps : Subgroup G) (ψs : Ps →* D.what₂.LLˣ) (Zs : DefSub A3.fam3.amb3) (S0 : IndefData (A3.side3 P0 ψ0 Zs)) (S1 : IndefData (A3.side3 Ps ψs Zs)) (X0 : BaseLevelRowSide D) (Dc : DefCols (A3.side3 Ps ψs Zs)) (Sp : SPer Dc) (C : ColData Dc Sp S1) (NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL)) (I : DivisionCompatibilityDataThreeSided D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc), DivDef3 D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 C NuC I → (∃ s, A3.A.fam.Ok s) → Function.Surjective ((A3.side3 Ps ψs Zs).Pq A3.A.μ0).mulVec → Function.Surjective (S1.ι A3.A.μ0).mulVec → (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  intro D G _ _ Pl0 I0 Ty T m A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc Sp C NuC I hD hOk hPq hι
  obtain ⟨s, hs⟩ := hOk

  have key := GlobalTheory.rowSide_iota_maps_fixedColumns_onto_of_matrices D (I.tup A3.A.μ0) _ _ _ _
    (I.jA A3.A.μ0) (rE D A3.A Ps ψs A3.A.μ0) (rV0 D A3.A Ps ψs A3.A.μ0)
    ((A3.side3 Ps ψs Zs).Pq A3.A.μ0) (S1.ι A3.A.μ0) I.eRR
    (fun x => (hD.sharp.forms A3.A.μ0).op_eq x)
    (fun F => Formalism.L2.G.ServJoint.level_operator_fixes_image hs Ps ψs (A3.fam3.toSub2 Zs) A3.A.μ0 F)
    hPq hι (fun F => hD.sharp.iota A3.A.μ0 F)
  rw [hD.tup.mu0] at key
  exact key
