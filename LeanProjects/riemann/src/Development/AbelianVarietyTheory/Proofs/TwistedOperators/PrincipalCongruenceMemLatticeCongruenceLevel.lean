import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelA
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CongLevelInst

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem mem_hatL_iff (Λ : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E ⊗[F] Formalism.MainNotions.S.Af F) :
    x ∈ Formalism.L2.Herm.hatL (F := F) Λ ↔ x ∈ Formalism.MainNotions.S.lamAf (F := F) Λ := by
  show x ∈ Submodule.span _ _ ↔ x ∈ Submodule.span _ _
  rw [Set.image_eq_range]
  rfl

theorem natCast_smul_mem_hatL (Λ : Submodule (𝓞 E) (Fin n → E)) (g : ℕ)
    (z : Fin n → E ⊗[F] Formalism.MainNotions.S.Af F) (hz : z ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    ((g : E ⊗[F] Formalism.MainNotions.S.Af F)) • z ∈ Formalism.L2.Herm.hatL (F := F) (Ideal.span {((g : ℕ) : 𝓞 E)} • Λ) := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS at hz ⊢
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨((g : ℕ) : 𝓞 E) • l, Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hl, ?_⟩
    funext i
    have h1 : ((g : ℕ) : 𝓞 E) • l i = (g : E) * l i := by
      rw [Algebra.smul_def]; simp
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h1, map_mul, map_natCast]
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul a y _ hy =>
    rw [smul_comm]
    exact Submodule.smul_mem _ a hy

theorem mem_congLev (hc : Formalism.BasicNotions.CMData F E) (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) (g : ℕ)
    (k : GL (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F)) (hU : k ∈ Formalism.UG.UPts hc.sig J (Formalism.MainNotions.S.Af F))
    (hs : k ∈ Formalism.UG.stabGL (Formalism.MainNotions.S.lamAf (F := F) Λ))
    (hd : ∀ y ∈ Formalism.MainNotions.S.lamAf (F := F) Λ, ∃ z ∈ Formalism.MainNotions.S.lamAf (F := F) Λ,
      ((k : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F)) - 1) *ᵥ y = (g : E ⊗[F] Formalism.MainNotions.S.Af F) • z) :
    k ∈ congLev hc J Λ (Ideal.span {((g : ℕ) : 𝓞 E)}) := by
  refine ⟨hU, ?_, ?_⟩
  · intro x
    rw [mem_hatL_iff, mem_hatL_iff]
    exact hs x
  · intro x hx
    obtain ⟨z, hz, e⟩ := hd x ((mem_hatL_iff Λ x).1 hx)
    have e2 : (k : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F)) *ᵥ x - x = (g : E ⊗[F] Formalism.MainNotions.S.Af F) • z := by
      rw [← e, Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [e2]
    exact natCast_smul_mem_hatL Λ g z ((mem_hatL_iff Λ z).2 hz)

end GlobalTheory.CongLevelInst

namespace GlobalTheory.CongLevelInst

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem kg_mem_levA : ∀ (D : D7) (V : HSp D) (fr : Formalism.IndefR.Eqv.UI.Frames D V) (g : ℕ), 1 ≤ g → ∀ k ∈ (Formalism.IndefR.Eqv.UI.instV fr).Kg g, Formalism.IndefR.Eqv.UI.brg fr (1, k) ∈ Formalism.IndefR.Lev.levA V (congLev D.sp.cm V.gram fr.Λ (Ideal.span {((g : ℕ) : 𝓞 D.host.E)})) := by
  intro D V fr g _ k hk
  rw [Formalism.IndefR.Eqv.brg_mem_levA]
  exact ⟨rfl, mem_congLev D.sp.cm V.gram fr.Λ g k.1 k.2 hk.1 hk.2⟩

end GlobalTheory.CongLevelInst
