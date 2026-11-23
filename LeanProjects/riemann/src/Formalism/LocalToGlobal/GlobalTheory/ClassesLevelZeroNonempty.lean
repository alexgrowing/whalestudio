import Formalism.LocalToGlobal.GlobalTheory.ColValS
import Formalism.LocalToGlobal.GlobalTheory.LevelZeroClassLatticeIntegral
import Formalism.LocalToGlobal.HermitianForms.BothSym

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.UG Formalism.UG.CS Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Herm Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.Comp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem class_lattice_eq_global {D : D7} (Lv : LevelData D) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) :
    (K0 D).lat (D.clsLat u 0 c) = globLat ((Lv u).y c).1 (Lv u).Lb :=
  eq_glob_of_hat ((K0 D).isLat_lat (D.clsLat_lat u 0 c)) _ (fun v => by exact (Lv u).y_lat c v)

theorem Lb_le_dl_lv {D : D7} (Lv : LevelData D) (u : D.what₂.Word) :
    (Lv u).Lb ≤ dl D.sp.cm.sig (K0 D).J (Lv u).Lb := by
  intro x hx
  exact Submodule.subset_span ((Lv u).Lb_int x hx)

theorem class_lattice_integral {D : D7} (Lv : LevelData D) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) :
    D.clsLat u 0 c ≤ Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT (D.clsLat u 0 c) := by
  have h1 : (K0 D).lat (D.clsLat u 0 c) ≤ (K0 D).lat (Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT (D.clsLat u 0 c)) := by
    rw [(K0 D).lat_dual, class_lattice_eq_global Lv u c]
    exact le_trans (glob_mono _ (Lb_le_dl_lv Lv u)) (glob_dl_le _ _ _ _ (by exact ((Lv u).y c).2))
  intro x hx
  have h2 := h1 ⟨x, hx, rfl⟩
  rw [(K0 D).mem_lat] at h2
  simpa using h2

theorem latT_of_sym {D : D7} (F : Formalism.L2.Forms.ColsTiedSym D) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) :
    flipTwoThree.LatT (D.sp.X 0) (flipTwoThree.Tu D u ^ (2 * D.R.f)) (D.clsLat u 0 c) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [dualSub_eq]
    exact class_lattice_integral F.herm.base.lev0 u c hx
  · obtain ⟨e⟩ := (F.herm.atT u).disc 0 (Nat.zero_le _) c
    rw [dualSub_eq, AddSubgroup.relIndex, ← card_ringOfIntegers_quot_natCast_eq_pow D (flipTwoThree.Tu D u)]
    have := Nat.card_congr e.toEquiv
    have hT : flipTwoThree.Tu D u = (D.mem u).A.T := rfl
    rw [hT, ← this]
    rfl

theorem classes_level_zero_nonempty {D : D7} (F : Formalism.L2.Forms.ColsTiedSym D) (u : D.what₂.Word) :
    Nonempty ((D.mem u).C.cls 0) := by
  obtain ⟨c, -⟩ := (F.herm.base.lev0 u).y_bij.2 (Quotient.mk'' 1)
  exact ⟨c⟩

def ColRest {D : D7} {u : D.what₂.Word} (B : Formalism.MainNotions.GlobalTheoryTheory.Inhab.ColBase D u) : Prop :=
  ∃ co : ((D.fm u).lat 0).V →ₗ[D.what₂.LL]
      ((D.mem u).C.cls 0 → MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) D.what₂.LL),
    Function.Injective co ∧
    (∀ F, (∃ x, co x = F) ↔ ∀ c, F c ∈ flipTwoThree.TSpan D.what₂.LL ((D.fm u).lam 0)) ∧
    (∀ w : D.what₂.places.Pl, ∃ γ : (D.mem u).C.cls 0 → D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL,
      (∀ c τ, flipTwoThree.LocBasis D w (B.Q c τ) (B.eQ c τ) (γ c τ)) ∧
      ∀ x, x ∈ locW D.what₂.places w ((D.fm u).lat 0).L ↔
        ∀ c, flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => (γ c τ)⁻¹) (co x c) ∈ flipTwoThree.IntSpanAt D w ((D.fm u).lam 0)) ∧
    ∀ (v : NumberField.InfinitePlace D.what₂.LL) x,
      (Formalism.HermitianLatticesTheory.majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x x).re =
        ∑ c, (flipTwoThree.nfAll ((D.fm u).lam 0)
          (flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹)
            (MvPolynomial.map v.embedding (co x c)))
          (flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹)
            (MvPolynomial.map v.embedding (co x c)))).re

theorem colValOfTiedS_of_rest
    (h : ∀ D : D7, Formalism.L2.Forms.ColsTiedSym D → flipTwoThree.adm3 D →
      ∀ u : D.what₂.Word, ∃ B : Formalism.MainNotions.GlobalTheoryTheory.Inhab.ColBase D u, ColRest B) :
    Formalism.MainNotions.RT.ColumnValuationFromTwistCompatibility :=
  column_value_of_tie_local_bases fun D F h3 u => by
    obtain ⟨B, co, h1, h2, h3', h4⟩ := h D F h3 u
    exact ⟨B, classes_level_zero_nonempty F u, latT_of_sym F u, co, h1, h2, h3', h4⟩

end Formalism.L2.GlobalTheoryTheory.ColValS
