import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

namespace GlobalTheory.SchurExt

variable {E : Type} [Field E] [NumberField E]

theorem coe_cornerGL_idemHom_apply {R : Type} [CommRing R] {a : ℕ} (e : R) (he : IsIdempotentElem e)
    (g : GL (Fin a) R) (i j : Fin a) :
    ((cornerGL a (idemHom e he) g : GL (Fin a) R) : Matrix (Fin a) (Fin a) R) i j =
      (1 : Matrix (Fin a) (Fin a) R) i j - e * (1 : Matrix (Fin a) (Fin a) R) i j + e * (g : Matrix (Fin a) (Fin a) R) i j :=
  rfl

theorem cornerGL_idemHom_mem_NA {a : ℕ} (e : Ad E) (he : IsIdempotentElem e) {u : GA E a}
    (hu : u ∈ GlobalTheory.JSW.NA E a) : cornerGL a (idemHom e he) u ∈ GlobalTheory.JSW.NA E a := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [coe_cornerGL_idemHom_apply, hu.1 i j hij, Matrix.one_apply_ne (ne_of_lt hij).symm]
    ring
  · rw [coe_cornerGL_idemHom_apply, hu.2 i, Matrix.one_apply_eq]
    ring

theorem cornerGL_idemHom_add_apply {R : Type} [CommRing R] {a : ℕ} (e : R) (he : IsIdempotentElem e)
    (g : GL (Fin a) R) {i j : Fin a} (hij : i ≠ j) :
    ((cornerGL a (idemHom e he) g : GL (Fin a) R) : Matrix (Fin a) (Fin a) R) i j +
      ((cornerGL a (idemHom (1 - e) he.one_sub) g : GL (Fin a) R) : Matrix (Fin a) (Fin a) R) i j =
      (g : Matrix (Fin a) (Fin a) R) i j := by
  rw [coe_cornerGL_idemHom_apply, coe_cornerGL_idemHom_apply, Matrix.one_apply_ne hij]
  ring

theorem superDiag_cornerGL_idemHom_add {R : Type} [CommRing R] {a : ℕ} (e : R) (he : IsIdempotentElem e)
    (g : GL (Fin a) R) :
    GlobalTheory.Whittaker.superDiag (cornerGL a (idemHom e he) g) +
      GlobalTheory.Whittaker.superDiag (cornerGL a (idemHom (1 - e) he.one_sub) g) = GlobalTheory.Whittaker.superDiag g := by
  unfold GlobalTheory.Whittaker.superDiag
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j.val = i.val + 1 := (Finset.mem_filter.1 hj).2
  have hij : i ≠ j := fun h => by rw [h] at hj'; omega
  exact cornerGL_idemHom_add_apply e he g hij

theorem prS_prO_NA_psiN :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
      ∀ u ∈ GlobalTheory.JSW.NA E a, prS S a u ∈ GlobalTheory.JSW.NA E a ∧ prO S a u ∈ GlobalTheory.JSW.NA E a ∧
        GlobalTheory.JSW.psiN (prS S a u) * GlobalTheory.JSW.psiN (prO S a u) = GlobalTheory.JSW.psiN u := by
  intro E _ _ _ a S u hu
  refine ⟨cornerGL_idemHom_mem_NA _ _ hu, cornerGL_idemHom_mem_NA _ _ hu, ?_⟩
  unfold GlobalTheory.JSW.psiN
  rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  exact congrArg (fun x => ((GroundTheory.Global.adelicChar E x : Circle) : ℂ))
    (superDiag_cornerGL_idemHom_add (idemS S) (isIdempotentElem_idemS S) u)

end GlobalTheory.SchurExt
