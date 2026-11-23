import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HeckePin
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie.LevKProof

variable {D : D7}

theorem blkOf_zero_of_le {n r t : ℕ} (h : n ≤ r) : (blkOf r t : Fin n → ℕ) = fun _ => 0 := by
  funext a
  have := a.2
  simp only [blkOf]
  rw [if_pos (by omega)]

theorem secondBlockIndex_eq_zero_of_dim_le {n r : ℕ} (h : n ≤ r) : (blk2 r : Fin n → ℕ) = fun _ => 0 := by
  funext a
  have := a.2
  simp only [blk2]
  rw [if_pos (by omega)]

theorem mem_blockTriangular_singleBlock_of_le {n r : ℕ} {κ : Type} [CommRing κ] (h : n ≤ r) (g : GL (Fin n) κ) :
    g ∈ blockTri (blk2 r) := by
  intro i k hik
  rw [secondBlockIndex_eq_zero_of_dim_le h] at hik
  exact absurd hik (lt_irrefl _)

end GlobalTheory.SeriesTie.LevKProof

namespace GlobalTheory.SeriesTie

open LevKProof in

theorem levK_eq_levG_triv : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ : Setup D.ntw}, RealPin Rl cG ρ → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), ρ.levK i j b = levG (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl cG ρ hp i j b
  unfold Setup.levK levG
  rw [hp.frT]
  congr 1
  have hr : (Wc D j).rank ≤ D.R.r := (FWT.rank_Wc j).le
  have hpar : parLev D.sp.cm (Wc D j).gram (Rl.βW j) (flag1L (ρ.B i j b).G.levT) =
      parLev D.sp.cm (Wc D j).gram (Rl.βW j) (Rl.datWp j Rl.triv) := by
    unfold parLev
    have hP : (flag1L (ρ.B i j b).G.levT).Pg = (Rl.datWp j Rl.triv).Pg := hp.Pg i j b
    have hb : (blkOf (flag1L (ρ.B i j b).G.levT).r (flag1L (ρ.B i j b).G.levT).t : Fin (Wc D j).rank → ℕ) =
        blkOf (Rl.datWp j Rl.triv).r (Rl.datWp j Rl.triv).t :=
      (blkOf_zero_of_le le_rfl).trans (blkOf_zero_of_le hr).symm
    have hb2 : (blk2 (flag1L (ρ.B i j b).G.levT).r : Fin (Wc D j).rank → ℕ) = blk2 (Rl.datWp j Rl.triv).r :=
      (secondBlockIndex_eq_zero_of_dim_le le_rfl).trans (secondBlockIndex_eq_zero_of_dim_le hr).symm
    rw [hP, hb, hb2]
    rfl
  have h1 : (flag1L (ρ.B i j b).G.levT).P.H = ⊥ := rfl
  have h2 : (Rl.datWp j Rl.triv).P.H = ⊥ := rfl

  have key : ∀ (x : GL (Fin (Wc D j).rank) (Lev.EAf D)) (PP : Pl D.host.E) (e1 : PP ∈ (flag1L (ρ.B i j b).G.levT).Pg)
      (e2 : PP ∈ (Rl.datWp j Rl.triv).Pg) (a c : Fin (Wc D j).rank),
      (rTup (Rl.βW j) (flag1L (ρ.B i j b).G.levT) x ⟨PP, e1⟩).val a c =
        (rTup (Rl.βW j) (Rl.datWp j Rl.triv) x ⟨PP, e2⟩).val
          (Fin.cast (FWT.rank_Wc j) a) (Fin.cast (FWT.rank_Wc j) c) := by
    intro x PP e1 e2 a c
    unfold rTup
    erw [upper_block_val_submatrix _ (mem_blockTriangular_singleBlock_of_le hr _), upper_block_val_submatrix _ (mem_blockTriangular_singleBlock_of_le le_rfl _)]
    rfl
  have hiff : ∀ x : GL (Fin (Wc D j).rank) (Lev.EAf D),
      rTup (Rl.βW j) (flag1L (ρ.B i j b).G.levT) x = 1 ↔ rTup (Rl.βW j) (Rl.datWp j Rl.triv) x = 1 := by
    intro x
    constructor
    · intro h
      funext PP
      apply Units.ext
      ext a c
      have e1 : PP.1 ∈ (flag1L (ρ.B i j b).G.levT).Pg := by
        show PP.1 ∈ (ρ.B i j b).G.Pg
        rw [hp.Pg i j b]
        exact PP.2
      have hk := key x PP.1 e1 PP.2 (Fin.cast (FWT.rank_Wc j).symm a) (Fin.cast (FWT.rank_Wc j).symm c)
      rw [h] at hk
      refine hk.symm.trans ?_
      simp [Matrix.one_apply, Fin.ext_iff]
      erw [Matrix.one_apply]
      simp [Fin.ext_iff]
      rfl
    · intro h
      funext PP
      apply Units.ext
      ext a c
      have e2 : PP.1 ∈ (Rl.datWp j Rl.triv).Pg := by
        show PP.1 ∈ Rl.Pg
        rw [← hp.Pg i j b]
        exact PP.2
      have hk := key x PP.1 PP.2 e2 a c
      rw [h] at hk
      refine hk.trans ?_
      simp [Matrix.one_apply, Fin.ext_iff]
      rfl
  ext x
  change (x ∈ parLev _ _ _ _ ∧ rTup _ _ x ∈ _) ↔ (x ∈ parLev _ _ _ _ ∧ rTup _ _ x ∈ _)
  rw [hpar, h1, h2, Subgroup.mem_bot, Subgroup.mem_bot, hiff]

end GlobalTheory.SeriesTie
