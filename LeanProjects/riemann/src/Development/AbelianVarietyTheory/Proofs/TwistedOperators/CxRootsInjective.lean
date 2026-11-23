import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEll.RealTorus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ}
  (P : PPol σ r) {w : InfinitePlace F} (τ : EmbOver E w)

theorem cxRoots_root (i : Fin r) : eval₂ τ.1 (cxRoots τ.1 P i) P.1 = 0 := by
  rw [← eval_map, cxRoots_spec, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

theorem cxRoots_injective : Function.Injective (cxRoots τ.1 P) := by
  have hs : (P.1.map τ.1).Separable := (PerfectField.separable_of_irreducible P.2.2.1).map
  have hn := nodup_roots hs
  rw [cxRoots_spec, ← Finset.prod_map_val,
    show Multiset.map (fun i => X - C (cxRoots τ.1 P i)) Finset.univ.val =
      Multiset.map (fun a => X - C a) (Finset.univ.val.map (cxRoots τ.1 P)) by rw [Multiset.map_map]; rfl,
    roots_multiset_prod_X_sub_C] at hn
  exact fun i j h => (Multiset.nodup_map_iff_inj_on Finset.univ.nodup).1 hn i (by simp) j (by simp) h

theorem finrank_Fld : Module.finrank E (Fld P) = r :=
  ((AdjoinRoot.powerBasis P.2.2.1.ne_zero).finrank.trans (AdjoinRoot.powerBasis_dim _)).trans P.2.2.2.1

def psiL (i : Fin r) : Fld P →+* ℂ := AdjoinRoot.lift τ.1 (cxRoots τ.1 P i) (cxRoots_root P τ i)

@[simp] theorem psiL_algebraMap (i : Fin r) (e : E) : psiL P τ i (algebraMap E (Fld P) e) = τ.1 e :=
  AdjoinRoot.lift_of _

@[simp] theorem psiL_alpha (i : Fin r) : psiL P τ i (alpha P) = cxRoots τ.1 P i := AdjoinRoot.lift_root _

theorem psiL_algebraMap_F (i : Fin r) (a : F) : psiL P τ i (algebraMap F (Fld P) a) = w.embedding a := by
  rw [IsScalarTower.algebraMap_apply F E (Fld P), psiL_algebraMap]
  exact RingHom.congr_fun τ.2 a

def Psi (i : Fin r) : w.Completion ⊗[F] Fld P →+* ℂ :=
  letI : Algebra F ℂ := w.embedding.toAlgebra
  (Algebra.TensorProduct.productMap
    ({ InfinitePlace.Completion.extensionEmbedding w with
        commutes' := fun a => InfinitePlace.Completion.extensionEmbedding_coe w ((WithAbs.equiv w.1).symm a) } :
      w.Completion →ₐ[F] ℂ)
    ({ psiL P τ i with commutes' := fun a => psiL_algebraMap_F P τ i a } : Fld P →ₐ[F] ℂ)).toRingHom

@[simp] theorem Psi_tmul (i : Fin r) (a : w.Completion) (y : Fld P) :
    Psi P τ i (a ⊗ₜ[F] y) = InfinitePlace.Completion.extensionEmbedding w a * psiL P τ i y := rfl

def PsiAll : w.Completion ⊗[F] Fld P →+* (Fin r → ℂ) := Pi.ringHom (Psi P τ)

@[simp] theorem PsiAll_apply (y : w.Completion ⊗[F] Fld P) (i : Fin r) : PsiAll P τ y i = Psi P τ i y := rfl

end GlobalTheory.TrEll.RealTorus
