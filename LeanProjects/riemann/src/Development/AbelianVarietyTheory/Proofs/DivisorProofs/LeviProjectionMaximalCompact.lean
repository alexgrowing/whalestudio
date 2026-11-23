import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UNInjective
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LeviFubini

theorem levH_fst_entry {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ} (h : a + b = n) (w : Pl E)
    (p : parB h w) (i j : Fin a) :
    ((levH h w p).1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j =
      ((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
        (GlobalTheory.SmGL.stdSum h (Sum.inl i)) (GlobalTheory.SmGL.stdSum h (Sum.inl j)) := rfl

theorem levH_snd_entry {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ} (h : a + b = n) (w : Pl E)
    (p : parB h w) (i j : Fin b) :
    ((levH h w p).2 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j =
      ((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
        (GlobalTheory.SmGL.stdSum h (Sum.inr i)) (GlobalTheory.SmGL.stdSum h (Sum.inr j)) := rfl

theorem levH_mem_KGL_of_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (p : GlobalTheory.LeviFubini.parB h w), (p : GLw n w) ∈ GlobalTheory.LFun.KGL w n →
      (GlobalTheory.LeviFubini.levH h w p).1 ∈ GlobalTheory.LFun.KGL w a ∧ (GlobalTheory.LeviFubini.levH h w p).2 ∈ GlobalTheory.LFun.KGL w b := by
  intro E _ _ _ a b n h w p hp
  have hp' := GlobalTheory.AdelicU.mem_GLint_iff.1 hp
  have hinv1 : ((levH h w p).1)⁻¹ = (levH h w p⁻¹).1 := by rw [map_inv, Prod.fst_inv]
  have hinv2 : ((levH h w p).2)⁻¹ = (levH h w p⁻¹).2 := by rw [map_inv, Prod.snd_inv]
  refine ⟨GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩,
    GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩⟩
  · rw [levH_fst_entry]; exact hp'.1 _ _
  · rw [hinv1, levH_fst_entry]; exact hp'.2 _ _
  · rw [levH_snd_entry]; exact hp'.1 _ _
  · rw [hinv2, levH_snd_entry]; exact hp'.2 _ _

end GlobalTheory.LeviFubini
