import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftCuspFormSpaceThetaMapEqDataStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ZeroSubspaceSpannedByDataZeroSubspaceLiftsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeTjEqImageOfCoordinateLatticeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeJwIndexEqConcreteLiftIndexStatement
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.ReadIndexNumerics

theorem ijIdx_eq (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup)
    (eMt : ∀ (i : Fin D.R.m) (t : T), (Fin (lDim D A P0 ψ0 i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1))
    (S0 : IndefData (A.side P0 ψ0 Zs)) (Xd : DivX D)
    (jW : ∀ i : Fin D.R.m, (Fin (S0.dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1))
    (i : Fin D.R.m) (t : T) (eW : (Fin (S0.dW i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Xd.MjH ((i : ℕ) + 1)).V)
    (hP : Formalism.DivisionValues.IsOrthProj (lH D A P0 ψ0 i t) (lZ0 D A P0 ψ0 Zs i t) (lPrj D A P0 ψ0 Zs i t))
    (hθ : ∀ x, D.what₂.thetaP (tup t) ((i : ℕ) + 1) (D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t x)) =
      jW i ((S0.θ i t).mulVec ((lPrj D A P0 ψ0 Zs i t).mulVec x)))
    (hj : ∀ x, Xd.jM ((i : ℕ) + 1) (eW x) = jW i x)
    (hl : (Xd.MjH ((i : ℕ) + 1)).L = (S0.M i).map ((eW : (Fin (S0.dW i) → D.what₂.LL) →ₗ[D.what₂.LL] (Xd.MjH ((i : ℕ) + 1)).V).restrictScalars (𝓞 D.what₂.LL)))
    (hT : Idx.TjL D (tup t) ((i : ℕ) + 1) = (Formalism.DivisionValues.matLat (lZ0 D A P0 ψ0 Zs i t) ((A.side P0 ψ0 Zs).Tl i t)).map
      ((eMt i t).toLinearMap.restrictScalars (𝓞 D.what₂.LL)))
    (w : D.what₂.places.Pl) :
    Idx.IjIdx Xd (tup t) ((i : ℕ) + 1) w = S0.Iw i t (D.plEq w) := by
  have hPE : ∀ z, lPrj D A P0 ψ0 Zs i t *ᵥ (lZ0 D A P0 ψ0 Zs i t *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec]; erw [hP.1]; exact Matrix.one_mulVec z
  have hth : Idx.thTj Xd (tup t) ((i : ℕ) + 1) = (Formalism.DivisionValues.matLat (S0.θ i t) ((A.side P0 ψ0 Zs).Tl i t)).map
      ((eW : (Fin (S0.dW i) → D.what₂.LL) →ₗ[D.what₂.LL] (Xd.MjH ((i : ℕ) + 1)).V).restrictScalars (𝓞 D.what₂.LL)) := by
    ext y
    have key : y ∈ Idx.thTj Xd (tup t) ((i : ℕ) + 1) ↔ ∃ x ∈ Idx.TjL D (tup t) ((i : ℕ) + 1),
        Xd.jM ((i : ℕ) + 1) y = D.what₂.thetaP (tup t) ((i : ℕ) + 1) (D.what₂.jMt (tup t) ((i : ℕ) + 1) x) := Iff.rfl
    rw [key, hT]
    constructor
    · rintro ⟨x, hx, hxy⟩
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 hx
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hu
      refine Submodule.mem_map.2 ⟨S0.θ i t *ᵥ z, Submodule.mem_map.2 ⟨z, hz, rfl⟩, ?_⟩
      apply Idx.jM_inj Xd
      have h1 := hθ (lZ0 D A P0 ψ0 Zs i t *ᵥ z)
      erw [hPE] at h1
      refine (hj _).trans ?_
      rw [hxy]
      exact h1.symm
    · intro hy
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 hy
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hu
      refine ⟨eMt i t (lZ0 D A P0 ψ0 Zs i t *ᵥ z), Submodule.mem_map.2 ⟨lZ0 D A P0 ψ0 Zs i t *ᵥ z,
        Submodule.mem_map.2 ⟨z, hz, rfl⟩, rfl⟩, ?_⟩
      have h1 := hθ (lZ0 D A P0 ψ0 Zs i t *ᵥ z)
      erw [hPE] at h1
      refine (hj _).trans ?_
      exact h1.symm
  unfold Idx.IjIdx
  rw [hth, hl, SkeletonIndexLemmas.lidx_map _ _ eW.injective]
  rfl

theorem numTie_of_read : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (Xd : DivX D) (JM : MjHIds D A3.A Xd (A3.indefDown (s0Of R F))), Pins R F cG → Holds R F → MjHTie D A3.A Xd (A3.indefDown (s0Of R F)) Z.jW JM → IdxDefs D Xd → NumTie D A3.A (A3.indefDown (s0Of R F)) Y.tup := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z Xd JM hP hH hM hI
  obtain ⟨-, hθ⟩ := GlobalTheory.T.liftCuspFormSpace_thetaMap_eq_data D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  have hZ0 := GlobalTheory.T.zeroSubspace_spanned_by_dataZeroSubspace_lifts D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  have hok := hH.ok.ok2
  have hB : ∀ i t, BlockHyp (A3.A.fam.L i t) (A3.A.fam.lvlA F.P0 F.ψ0) A3.A.fam.v0 1 :=
    fun i t => ⟨hok.conj, hok.irr, hok.lifts i t⟩
  have hOP : ∀ i t, Formalism.DivisionValues.IsOrthProj (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t)
      (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t) :=
    fun i t => BlockDat.lf_l_proj (Z := (A3.fam3.toSub2 (zsOf R F)).Zl i t) (hB i t)
  have hT := fun i t => GlobalTheory.T.lattice_Tj_eq_image_of_coordinate_lattice D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) Y.tup Y.eMt i t (hOP i t) (Y.formsL i t) (Y.latL i t)
    (hZ0 i t) (fun x => by
      have e : ∀ v, lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ v) = v :=
        fun v => by rw [Matrix.mulVec_mulVec]; erw [(hOP i t).1]; exact Matrix.one_mulVec v
      have h2 := hθ i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ x))
      erw [e] at h2
      exact (hθ i t x).trans h2.symm)
  refine ⟨fun i t w => ?_, fun i t w => ?_, fun i w => ?_⟩
  · rw [hI.Ij_def _ _ _ (by omega) (by omega)]
    exact ijIdx_eq D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) Y.tup Y.eMt (A3.indefDown (s0Of R F)) Xd Z.jW i t (JM.eW i)
      (hOP i t) (hθ i t) (hM.j_eq i) (hM.hlat i).lat (hT i t) w
  · rw [hI.jw_def _ _ _ (by omega) (by omega)]
    exact GlobalTheory.T.lattice_jw_index_eq_concrete_lift_index D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) Y.tup Y.eMt i t (hOP i t) (Y.formsL i t)
      (BlockDat.lf_lE_form (hB i t)) (BlockDat.lf_Tl_isLattice (hB i t)).span_eq_top (hT i t) w
  · rw [Z.etaJ]
    by_cases h : D.plEq w ∈ R.twPl
    · rw [if_pos h, if_pos (show D.plEq w ∈ (A3.indefDown (s0Of R F)).Tw from h)]; rfl
    · rw [if_neg h, if_neg (show D.plEq w ∉ (A3.indefDown (s0Of R F)).Tw from h)]

end GlobalTheory.Mem.ReadIndexNumerics

end
