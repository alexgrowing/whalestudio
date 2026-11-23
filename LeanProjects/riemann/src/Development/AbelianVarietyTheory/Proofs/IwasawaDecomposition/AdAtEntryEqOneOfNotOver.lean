import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceProjectionZeroIntegralIffComponentsAbove
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.AdSupport

theorem adAt_entry_eq_one_of_not_over {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (z : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (v : HeightOneSpectrum (𝓞 F))
    (hz : ∀ v', v' ≠ v → bc (prV (E := E) v') z = 1) (P : HeightOneSpectrum (𝓞 E)) (hP : ¬ Formalism.L2.Col.IsOver v P)
    (r s : Fin n) :
    adAt F P ((z : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) r s) =
      (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s := by
  have hne : P.under (𝓞 F) ≠ v := by
    intro h
    apply hP
    rw [← h]
    rfl
  have h2 := congrArg (fun g : GL (Fin n) (E ⊗[F] (P.under (𝓞 F)).adicCompletion F) =>
    (g : Matrix (Fin n) (Fin n) (E ⊗[F] (P.under (𝓞 F)).adicCompletion F)) r s) (hz _ hne)
  have h3 : prV (E := E) (P.under (𝓞 F)) ((z : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) r s) =
      (1 : Matrix (Fin n) (Fin n) (E ⊗[F] (P.under (𝓞 F)).adicCompletion F)) r s := h2
  have h4 : prV (E := E) (P.under (𝓞 F)) ((z : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) r s -
      (1 : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) r s) = 0 := by
    rw [map_sub, h3, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h5 := ((GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff F E (P.under (𝓞 F)) _).1.1 h4) P rfl
  rw [map_sub, sub_eq_zero] at h5
  rw [h5, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory.Mem.Col2.AdSupport
