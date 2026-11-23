import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormOneIdeleOrderOneTrivialElsewhere
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

namespace GlobalTheory.TwV.Xc.Unif

theorem exists_h90_eq_oneOff_of_normOne_at_split_place : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)) (spl : E ⊗[F] w.adicCompletion F ≃+* w.adicCompletion F × w.adicCompletion F), (∀ x, spl (sigR σ (w.adicCompletion F) x) = swapR (w.adicCompletion F) (spl x)) → ∀ (π : (AfE F E)ˣ), π ∈ U1 σ → OneOff w π → ∃ x : (AfE F E)ˣ, h90 σ x = π ∧ OneOff w x := by
  intro F E _ _ _ _ _ σ w spl hsig π hπ hoff
  set p : E ⊗[F] w.adicCompletion F := prV (E := E) w (π : AfE F E) with hp
  have hπe : (π : AfE F E) = oneAt w p := ext_prV fun w' => by
    by_cases h : w' = w
    · subst h; rw [prV_oneAt_self]
    · rw [prV_oneAt_ne w w' h]; exact hoff w' h
  have hU : (π : AfE F E) * sigR σ (FiniteAdeleRing (𝓞 F) F) (π : AfE F E) = 1 := by
    have := congrArg (fun u : (AfE F E)ˣ => (u : AfE F E)) ((MonoidHom.mem_ker).1 hπ)
    simpa [conjId] using this
  have hp1 : p * sigR σ (w.adicCompletion F) p = 1 := by
    have h2 := congrArg (prV (E := E) w) hU
    rw [hπe, sigR_oneAt, oneAt_mul, prV_oneAt_self, map_one] at h2
    exact h2
  have hab : (spl p).1 * (spl p).2 = 1 ∧ (spl p).2 * (spl p).1 = 1 := by
    have h3 := congrArg spl hp1
    rw [map_mul, hsig, map_one] at h3
    exact ⟨congrArg Prod.fst h3, congrArg Prod.snd h3⟩
  let c : (E ⊗[F] w.adicCompletion F)ˣ :=
    ⟨spl.symm ((spl p).1, 1), spl.symm ((spl p).2, 1),
      by rw [← map_mul]; apply spl.injective; rw [RingEquiv.apply_symm_apply, map_one]; exact Prod.ext hab.1 (mul_one _),
      by rw [← map_mul]; apply spl.injective; rw [RingEquiv.apply_symm_apply, map_one]; exact Prod.ext hab.2 (mul_one _)⟩
  refine ⟨oneAtU w c, ?_, fun w' hw' => prV_oneAt_ne w w' hw' _⟩
  apply Units.ext
  have hval : ((h90 σ (oneAtU w c) : (AfE F E)ˣ) : AfE F E) =
      oneAt w (c : E ⊗[F] w.adicCompletion F) *
        sigR σ (FiniteAdeleRing (𝓞 F) F) (oneAt w ((c⁻¹ : (E ⊗[F] w.adicCompletion F)ˣ) : E ⊗[F] w.adicCompletion F)) := by
    simp only [h90, MonoidHom.div_apply, MonoidHom.id_apply, div_eq_mul_inv, Units.val_mul, conjId, map_inv]
    rfl
  rw [hval, sigR_oneAt, oneAt_mul, hπe]
  congr 1
  apply spl.injective
  rw [map_mul, hsig]
  show spl (spl.symm ((spl p).1, 1)) * swapR (w.adicCompletion F) (spl (spl.symm ((spl p).2, 1))) = spl p
  rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  show ((spl p).1 * 1, 1 * (spl p).2) = spl p
  rw [mul_one, one_mul]

end GlobalTheory.TwV.Xc.Unif
