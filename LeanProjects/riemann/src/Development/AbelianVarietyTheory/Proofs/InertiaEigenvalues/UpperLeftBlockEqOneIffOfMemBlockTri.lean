import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PrincipalLevel

theorem upperLeftBlock_eq_one_iff_of_mem_blockTri {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (h : r = n) (g : GL (Fin n) κ) :
    upperLeftBlock hr g = 1 ↔ g = 1 := by
  subst h
  have hg : g ∈ blockTri (κ := κ) (blk2 r) := fun i j hij => by
    simp [blk2, i.2, j.2] at hij
  constructor
  · intro h1
    apply Units.ext
    ext i j
    have := congrArg (fun u : GL (Fin r) κ => (u : Matrix (Fin r) (Fin r) κ) i j) h1
    simp only [upper_block_val_submatrix hr hg, Matrix.submatrix_apply] at this
    have ei : Fin.castLE hr i = i := Fin.ext rfl
    have ej : Fin.castLE hr j = j := Fin.ext rfl
    rw [ei, ej] at this
    simpa using this
  · rintro rfl
    exact blockDiagonalExtendByOnePrimeField_one _ _

theorem mem_lev_whole {D : D7} {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (β : GL (Fin n) (Lev.EAf D))
    (L : LevDat D.host.E ℂ n) (hr : L.r = n) (hQ : L.Q = ∅) (hP : L.P.H = ⊥) (x : GL (Fin n) (Lev.EAf D)) :
    x ∈ lev D.sp.cm J β L ↔ x ∈ UA D.sp.cm J ∧ x ∈ St β ∧ ∀ PP ∈ L.Pg, redFn β PP x = 1 := by
  have h0 : ∀ a : Fin n, blkOf L.r L.t a = 0 := fun a => by
    unfold blkOf
    rw [if_pos (by rw [hr]; exact a.2)]
  rw [mem_lev, mem_parLev, hP, Subgroup.mem_bot]
  constructor
  · rintro ⟨⟨h1, h2, -, -⟩, h3⟩
    exact ⟨h1, h2, fun PP hPP => (upperLeftBlock_eq_one_iff_of_mem_blockTri L.hr hr _).1 (congrFun h3 ⟨PP, hPP⟩)⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2, fun PP _ i j hij => ?_, fun PP hPP => ?_⟩, funext fun PP => (upperLeftBlock_eq_one_iff_of_mem_blockTri L.hr hr _).2 (h3 PP.1 PP.2)⟩
    · rw [h0, h0] at hij
      exact absurd hij (lt_irrefl 0)
    · rw [hQ] at hPP
      exact absurd hPP (Finset.notMem_empty _)

theorem levK_eq_levG : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ : GlobalTheory.SeriesTie.Setup D.ntw}, GlobalTheory.SeriesTie.RealPin Rl cG ρ → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), ρ.levK i j b = Formalism.IndefR.Lev.levG (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl cG ρ hpin i j b
  show Lev.levG (Wc D j) (ρ.B i j b).F.βT (Lev.flag1L (ρ.B i j b).G.levT) = _
  rw [hpin.frT i j b]
  unfold Lev.levG
  congr 1
  ext x
  rw [mem_lev_whole _ _ _ rfl rfl rfl, mem_lev_whole _ _ _ (FWT.rank_Wc j).symm rfl rfl]
  have hg : (Lev.flag1L (ρ.B i j b).G.levT).Pg = (Rl.datWp j Rl.triv).Pg := hpin.Pg i j b
  rw [hg]

end GlobalTheory.PrincipalLevel
