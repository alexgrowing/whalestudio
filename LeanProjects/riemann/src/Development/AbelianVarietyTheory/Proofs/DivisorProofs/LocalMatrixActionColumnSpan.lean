import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockCentre
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
open scoped TensorProduct
open Matrix

namespace GlobalTheory.EmbColSpan

open GlobalTheory.AdelicU.Supp (singleTens compFin_singleTens_self compFin_singleTens_ne compInf_singleTens singleTens_mul
  compFin_one_tmul adTens_ext)

theorem single_mem_colSpan {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n r : ℕ}
    (X : Matrix (Fin n) (Fin r) E) (v : HeightOneSpectrum (𝓞 F)) (I : Set (Fin r)) (y : Fin n → Fv F v ⊗[F] E)
    (hy : y ∈ Submodule.span (Fv F v ⊗[F] E) ((fun l a => inclR (F := F) (Fv F v) (X a l)) '' I)) :
    (fun a => singleTens E v (y a)) ∈ GlobalTheory.StdPar.colSpan F X I := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    have h : (adMat F X)ᵀ l ∈ GlobalTheory.StdPar.colSpan F X I := Submodule.subset_span ⟨l, hl, rfl⟩
    have e : (fun a => singleTens E v (inclR (F := F) (Fv F v) (X a l))) = singleTens E v 1 • (adMat F X)ᵀ l := by
      funext a
      rw [Pi.smul_apply, smul_eq_mul, singleTens_mul, one_mul]
      exact congrArg _ (compFin_one_tmul v (X a l)).symm
    rw [e]
    exact Submodule.smul_mem _ _ h
  | zero =>
    have e : (fun a => singleTens E v ((0 : Fin n → Fv F v ⊗[F] E) a)) = 0 := by
      funext a; exact map_zero _
    rw [e]; exact zero_mem _
  | add y y' _ _ h h' =>
    have e : (fun a => singleTens E v ((y + y') a)) =
        (fun a => singleTens E v (y a)) + fun a => singleTens E v (y' a) := by
      funext a; exact map_add _ _ _
    rw [e]; exact add_mem h h'
  | smul c y _ h =>
    have e : (fun a => singleTens E v ((c • y) a)) = singleTens E v c • fun a => singleTens E v (y a) := by
      funext a; exact map_mul _ _ _
    rw [e]; exact Submodule.smul_mem _ _ h

theorem emb_mulVec_sub_mem_colSpan : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X : Matrix (Fin n) (Fin r) E)
    (v : HeightOneSpectrum (𝓞 F)) (x : GLoc σ J v) (z : Fin n → AF F ⊗[F] E) (I : Set (Fin r)),
    (matHom _ σ J x).1 *ᵥ (fun a => compFin F E v (z a)) - (fun a => compFin F E v (z a)) ∈
      Submodule.span (Fv F v ⊗[F] E) ((fun l a => inclR (F := F) (Fv F v) (X a l)) '' I) →
    (matHom _ σ J (emb σ J v x)).1 *ᵥ z - z ∈ GlobalTheory.StdPar.colSpan F X I := by
  intro F E _ _ _ _ _ σ n J r X v x z I h
  have key := single_mem_colSpan X v I _ h
  have hf : ∀ (u : HeightOneSpectrum (𝓞 F)) (g : GAd σ J) (a : Fin n),
      compFin F E u (((matHom _ σ J g).1 *ᵥ z) a) =
        ((matHom _ σ J (proj σ J u g)).1 *ᵥ fun b => compFin F E u (z b)) a := fun u g a =>
    RingHom.map_mulVec (compFin F E u) _ z a
  have hi : ∀ (w : InfinitePlace F) (g : GAd σ J) (a : Fin n),
      compInf F E w (((matHom _ σ J g).1 *ᵥ z) a) =
        ((matHom _ σ J (projArch σ J w g)).1 *ᵥ fun b => compInf F E w (z b)) a := fun w g a =>
    RingHom.map_mulVec (compInf F E w) _ z a
  convert key using 1
  funext a
  refine adTens_ext (fun w => ?_) fun u => ?_
  · rw [compInf_singleTens, Pi.sub_apply, map_sub, hi, projArch_emb, map_one, Units.val_one, one_mulVec, sub_self]
  · by_cases e : u = v
    · subst e
      rw [compFin_singleTens_self, Pi.sub_apply, map_sub, hf, proj_emb_self, Pi.sub_apply]
    · rw [compFin_singleTens_ne e, Pi.sub_apply, map_sub, hf, proj_emb_ne σ J e, map_one, Units.val_one, one_mulVec,
        sub_self]

end GlobalTheory.EmbColSpan
