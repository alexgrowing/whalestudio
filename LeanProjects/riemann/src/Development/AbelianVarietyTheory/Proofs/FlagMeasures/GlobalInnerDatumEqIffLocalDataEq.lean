import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericDatumLatticeEqPerpQuotientImageTermStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalInnerLatticeEqOfInnerPreimageEqStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerPreimageEqOfLocalInnerLatticeEqStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalIdentificationEqOfGlobalLatticesEqStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalGraphEqOfLocalIotaAgreeStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.InnerDict

theorem inner_of_term : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (r : ℕ) (P : LocNG.FPair H r) (d : LocNG.Datum P) (τ : Loc.Term V M r), LocNG.IsTermOver P d τ → (d.L : Set (H.Wb P.A.f)) = H.Lset τ.abelian₂ P.A.f ∧ (d.L' : Set (H.Wb P.B.f)) = H.Lset τ.abelian₂ P.B.f := GlobalTheory.T.nonGenericDatum_lattice_eq_perpQuotientImage_term

theorem lset_eq_of_lsub_eq : ∀ (D : D7) (Z : LocDat D) (p : PlF D) {T : D.host.E} (G : LFlag (VS D) D.R.rS T) (Fr : LocNG.FrameD (locH Z p) D.R.rS), Fr.f = (fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → Lsub Λ₁ G = Lsub Λ₂ G → (locH Z p).Lset (lattice₂ D Z.M p Λ₁) Fr.f = (locH Z p).Lset (lattice₂ D Z.M p Λ₂) Fr.f := GlobalTheory.T.localInnerLattice_eq_of_innerPreimage_eq

theorem lsub_eq_of_lset_eq : ∀ (D : D7) (Z : LocDat D) {T : D.host.E} (G : LFlag (VS D) D.R.rS T) (Fr : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (Fr p).f = (fun a => frFac Z.δ p a • baseChange₂ D p (frame G a))) → ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → (∀ p, (locH Z p).Lset (lattice₂ D Z.M p Λ₁) (Fr p).f = (locH Z p).Lset (lattice₂ D Z.M p Λ₂) (Fr p).f) → Lsub Λ₁ G = Lsub Λ₂ G := GlobalTheory.T.innerPreimage_eq_of_local_innerLattice_eq

theorem iota_eq_of_graph_eq : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ) (F : LFlag (VS D) D.R.rS (Tn : D.host.E)) (F' : LFlag (VS D) D.R.rS (T'n : D.host.E)), Based Z FP Tn T'n F F' → ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → Lsub Λ₁ F = Lsub Λ₂ F → Lsub Λ₁ F' = Lsub Λ₂ F' → (gdat F F' Λ₁).2.2 = (gdat F F' Λ₂).2.2 → ∀ (p : PlF D) (g : Loc.SplitG (Z.M p).L), (Z.M p).split = some g → (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₁, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ = (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₂, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ := GlobalTheory.T.local_identification_eq_of_global_lattices_eq

theorem graph_eq_of_iota_eq : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ) (F : LFlag (VS D) D.R.rS (Tn : D.host.E)) (F' : LFlag (VS D) D.R.rS (T'n : D.host.E)), Based Z FP Tn T'n F F' → ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → Lsub Λ₁ F = Lsub Λ₂ F → Lsub Λ₁ F' = Lsub Λ₂ F' → (∀ (p : PlF D) (g : Loc.SplitG (Z.M p).L), (Z.M p).split = some g → (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₁, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ = (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₂, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩) → (gdat F F' Λ₁).2.2 = (gdat F F' Λ₂).2.2 := GlobalTheory.T.global_graph_eq_of_local_iota_agree

theorem datum_ext {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : Loc.HermSp M V} {r : ℕ} {P : LocNG.FPair H r} (d d' : LocNG.Datum P) (h1 : d.L = d'.L) (h2 : d.L' = d'.L') (h3 : d.io = d'.io) : d = d' := by
  cases d; cases d'; simp only at h1 h2 h3; subst h1 h2 h3; rfl

theorem gdat_eq_iff : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ₁ Λ₂ : LV D) (y₁ y₂ : Dat Z FP), LocOver Λ₁ y₁ → LocOver Λ₂ y₂ → (gdat F F' Λ₁ = gdat F F' Λ₂ ↔ y₁ = y₂) := by
  intro D X Y u u' F F' w _ _ Z FP hB _ Λ₁ Λ₂ y₁ y₂ h₁ h₂
  have hL : ∀ (Λ : LV D) (y : Dat Z FP), LocOver Λ y → ∀ p,
      ((y p).L : Set _) = (locH Z p).Lset (lattice₂ D Z.M p Λ) (FP p).A.f ∧
      ((y p).L' : Set _) = (locH Z p).Lset (lattice₂ D Z.M p Λ) (FP p).B.f ∧
      ∀ g, (Z.M p).split = some g → (y p).io = (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ := by
    intro Λ y hy p
    obtain ⟨τ, hτ, hlam⟩ := hy.2 p
    have h1 := inner_of_term (locH Z p) D.R.rS (FP p) (y p) τ hτ
    refine ⟨h1.1.trans (congrArg (fun L => (locH Z p).Lset L (FP p).A.f) hlam),
      h1.2.trans (congrArg (fun L => (locH Z p).Lset L (FP p).B.f) hlam), fun g hg => ?_⟩
    have h2 := (hτ.2.2.2.2 g hg).2
    have e4 : ∀ (L : Submodule (Z.M p).L.O (Vp D p)) (a b c e : (D.s.atP p).Fp), L = lattice₂ D Z.M p Λ →
        (locH Z p).iotaGraph g ⟨L, (FP p).A.f, (FP p).B.f, a, b⟩ =
          (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ, (FP p).A.f, (FP p).B.f, c, e⟩ := by
      intro L a b c e hL; subst hL; rfl
    exact h2.symm.trans (e4 _ _ _ _ _ hlam)
  constructor
  · intro hg
    have hF : Lsub Λ₁ F = Lsub Λ₂ F := congrArg (fun t => t.1) hg
    have hF' : Lsub Λ₁ F' = Lsub Λ₂ F' := congrArg (fun t => t.2.1) hg
    have hΓ := congrArg (fun t => t.2.2) hg
    funext p
    apply datum_ext
    · apply SetLike.coe_injective
      exact (hL Λ₁ y₁ h₁ p).1.trans ((lset_eq_of_lsub_eq D Z p F (FP p).A (hB p).1 Λ₁ Λ₂ h₁.1 h₂.1 hF).trans (hL Λ₂ y₂ h₂ p).1.symm)
    · apply SetLike.coe_injective
      exact (hL Λ₁ y₁ h₁ p).2.1.trans ((lset_eq_of_lsub_eq D Z p F' (FP p).B (hB p).2.1 Λ₁ Λ₂ h₁.1 h₂.1 hF').trans (hL Λ₂ y₂ h₂ p).2.1.symm)
    · cases hs : (Z.M p).split with
      | none => exact ((y₁ p).io_L hs).trans ((y₂ p).io_L hs).symm
      | some g =>
        exact ((hL Λ₁ y₁ h₁ p).2.2 g hs).trans ((iota_eq_of_graph_eq D Z FP _ _ F F' hB Λ₁ Λ₂ h₁.1 h₂.1 hF hF' hΓ p g hs).trans
          ((hL Λ₂ y₂ h₂ p).2.2 g hs).symm)
  · intro hy
    subst hy
    have hF : Lsub Λ₁ F = Lsub Λ₂ F :=
      lsub_eq_of_lset_eq D Z F (fun p => (FP p).A) (fun p => (hB p).1) Λ₁ Λ₂ h₁.1 h₂.1
        (fun p => (hL Λ₁ y₁ h₁ p).1.symm.trans (hL Λ₂ y₁ h₂ p).1)
    have hF' : Lsub Λ₁ F' = Lsub Λ₂ F' :=
      lsub_eq_of_lset_eq D Z F' (fun p => (FP p).B) (fun p => (hB p).2.1) Λ₁ Λ₂ h₁.1 h₂.1
        (fun p => (hL Λ₁ y₁ h₁ p).2.1.symm.trans (hL Λ₂ y₁ h₂ p).2.1)
    have hΓ := graph_eq_of_iota_eq D Z FP _ _ F F' hB Λ₁ Λ₂ h₁.1 h₂.1 hF hF'
      (fun p g hs => ((hL Λ₁ y₁ h₁ p).2.2 g hs).symm.trans ((hL Λ₂ y₁ h₂ p).2.2 g hs))
    exact Prod.ext hF (Prod.ext hF' hΓ)

end GlobalTheory.Unfold.InnerDict
