import Formalism.LocalToGlobal.GlobalTheory.GL6.DiamondPreservesRationalFormZero
import Formalism.LocalToGlobal.GlobalTheory.GL6.AdelicFunctionRightTranslateDiamond

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG

variable {D : D7} {u : D.what₂.Word}

theorem diamond_preserves_forms (Tf : FormsTied D u) (hE : DiamondElementsExist Tf) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT)
    (a : ((D.mem u).A.Fv v)ˣ) (φ : Formalism.MainNotions.product_first_zeroth_parts.Fn D u i) (hφ : φ ∈ (D.fm u).Fi i) :
    Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ ∈ (D.fm u).Fi i := by
  obtain ⟨g, hg, hgφ⟩ := ((Tf.val i hi).Fi φ).1 hφ
  have hval : ∀ c, φ c = fun z => g ((Tf.cls i hi).y c) ((Tf.val i hi).eY z) := by
    intro c; funext z
    have := congrFun (congrFun hgφ c) ((Tf.val i hi).eY z)
    simp only [Equiv.symm_apply_apply] at this
    exact this.symm
  have hgA : g ∈ AdFun (Tf.cls i hi).lev (embT D) := (Submodule.mem_inf.1 hg).1
  have hgV := Submodule.mem_pi.1 (Submodule.mem_inf.1 hg).2
  obtain ⟨k, hk, δ, hδ⟩ := hE i hi v a
  have hg' := adelic_function_right_translate_diamond (Tf.cls i hi).lev (embT D) _ _ (level_places_not_bad Tf.atT v) hδ hgA
  refine ((Tf.val i hi).Fi _).2 ⟨fun x => g (x * δ), Submodule.mem_inf.2 ⟨hg', Submodule.mem_pi.2
    (fun x _ => hgV (x * δ) (Set.mem_univ _))⟩, ?_⟩
  funext c z
  show g ((Tf.cls i hi).y c * δ) z = (D.fm u).dilT i v a c (φ ((D.fm u).dil i v a c)) ((Tf.val i hi).eY.symm z)
  rw [hval, (Tf.val i hi).dilT v a k hk c δ hδ g hgA]
  simp only [Equiv.apply_symm_apply]

theorem diamond_comm_same_place (Tf : FormsTied D u) (hE : DiamondElementsExist Tf) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT)
    (a b : ((D.mem u).A.Fv v)ˣ) (φ : Formalism.MainNotions.product_first_zeroth_parts.Fn D u i) (hφ : φ ∈ (D.fm u).Fi i) :
    Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v b φ) = Formalism.MainNotions.product_first_zeroth_parts.dia D u i v b (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ) := by
  have hM := diamond_mul_of_diamond_elements Tf hE
  rw [← (hM i hi v φ hφ).2 a b, ← (hM i hi v φ hφ).2 b a, mul_comm]

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
